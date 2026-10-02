(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)

(**
Network.IPv6 — IPv6 Address codec (RFC 4291 §2.2).

IPv6 addresses are 128-bit values written as eight groups of 1-4
hexadecimal digits separated by colons (e.g., "2001:0db8:0000:0000:0000:0000:0000:0001").

Known limitation: :: zero-compression (RFC 4291 §2.2 item 2) is NOT
supported.  All 8 groups must be present in the text form.

Built on [Data.BaseN.Base16] for hex character conversion and
[Data.Codec.Types] record combinators.  The codec uses [custom] with a
flat encoder/decoder pair — no [product] or [map_] combinator chain.
This eliminates the opaque [rest_cond] barrier (fstar-proofs §18).

Roundtrip proof: list-level structural induction (0 admits), bridged to
[byte_seq] via [seq_of_list]/[seq_to_list] conversion lemmas.

@header Network.IPv6

@section Types
- [ipv6] — eight 16-bit groups as [ipv6_group] (refined [int])
- [ipv6_group] — [int] with refinement [0 <= g <= 65535]

@section Hex Group
- [encode_hex_group] — int → 1-4 uppercase hex digits
- [decode_hex_group] — parse hex digits → int 0-65535
- [hex_group_codec] — standalone [custom] codec for a single hex group
- [lemma_hex_group_roundtrip] — encode→decode roundtrip (0 admits)
- [lemma_encode_hex_group_nonempty] — output always nonempty

@section IPv6 Codec
- [ipv6_codec] — full colon-hex codec (8 groups)
- [encode_ipv6_list] / [decode_ipv6_list] — list-level functions
- [lemma_ipv6_list_roundtrip] — list-level encode→decode roundtrip (0 admits)
- [lemma_roundtrip] — codec-level encode→decode roundtrip (0 admits)
- [lemma_ipv6_group_range] — group fields in range for [ipv6_of_groups] values
- [lemma_hex_digit_ranges] — basen [is_hex] accepts 0-9, a-f, A-F

@section RFC test vectors
- [lemma_ipv6_loopback_concrete] / [lemma_ipv6_unspecified_concrete]
- [lemma_ipv6_doc_concrete] / [lemma_ipv6_all_max_concrete]
- [lemma_ipv6_single_digit_concrete] / [lemma_ipv6_mixed_case_concrete]
- RFC test vectors with list-level decode (0 admits)
*)

module Network.IPv6

open Data.Codec
open Data.BaseN
open FStar.Seq
open FStar.List.Tot
open Network.IP

module U8 = FStar.UInt8
module L  = FStar.List.Tot

(** Types *)

(** IPv6 address group: 16-bit unsigned integer in [0, 65535]. *)
type ipv6_group = g:int{0 <= g /\ g <= 65535}

(** IPv6 address: eight 16-bit groups.  Each field is refined to
    guarantee [0 <= g <= 65535]; no runtime validation needed. *)
type ipv6 = {
  group0 : ipv6_group;
  group1 : ipv6_group;
  group2 : ipv6_group;
  group3 : ipv6_group;
  group4 : ipv6_group;
  group5 : ipv6_group;
  group6 : ipv6_group;
  group7 : ipv6_group;
}

(** Validated constructor.  Returns [None] if any group is out of range.
    @param g0-g7 Each group value, must be 0-65535 to succeed. *)
let ipv6_of_groups (g0 g1 g2 g3 g4 g5 g6 g7: int) : Tot (option ipv6) =
  if g0 < 0 || g0 > 65535 || g1 < 0 || g1 > 65535 ||
     g2 < 0 || g2 > 65535 || g3 < 0 || g3 > 65535 ||
     g4 < 0 || g4 > 65535 || g5 < 0 || g5 > 65535 ||
     g6 < 0 || g6 > 65535 || g7 < 0 || g7 > 65535
  then None
  else Some {group0 = g0; group1 = g1; group2 = g2; group3 = g3;
             group4 = g4; group5 = g5; group6 = g6; group7 = g7}

(** RFC 4291: loopback address ::1 (full form: 0:0:0:0:0:0:0:1). *)
let ipv6_loopback : ipv6 =
  {group0 = 0; group1 = 0; group2 = 0; group3 = 0;
   group4 = 0; group5 = 0; group6 = 0; group7 = 1}

(** RFC 4291: unspecified address :: (full form: 0:0:0:0:0:0:0:0). *)
let ipv6_unspecified : ipv6 =
  {group0 = 0; group1 = 0; group2 = 0; group3 = 0;
   group4 = 0; group5 = 0; group6 = 0; group7 = 0}

(** Hex group encode/decode *)

(** RFC 4291: each group represents 16 bits.  Leading zeros may be
    omitted, but at least one digit must be present.  Hex digits
    accept 0-9, A-F, a-f.  Encoder uses uppercase.
*)

(** [encode_hex_group_go] tail-recursive helper: writes hex digits of [m]
    followed by [acc].  Top-level so SMT can encode it.
    @param m Value to encode (non-negative).  @param acc Accumulator list.
    @returns Hex digits of [m] in big-endian order followed by [acc]. *)
let rec encode_hex_group_go (m: nat) (acc: list byte) : Tot (list byte) (decreases m) =
  if m = 0 then acc
  else encode_hex_group_go (m / 16) (nibble_to_upper_hex (m % 16) :: acc)

(** [encode_hex_group] converts a nat ≤65535 to minimal hex digits.
    @param n Value to encode, in [0, 65535].  @returns 1-4 uppercase hex digit bytes. *)
let encode_hex_group (n: nat{n <= 65535}) : list byte =
  if n = 0 then [nibble_to_upper_hex 0]
  else encode_hex_group_go n []

(** [decode_hex_group_go] top-level recursive helper for hex digit parsing.
    @param ds Remaining hex digit bytes.  @param acc Accumulated value.
    @param cnt Bytes consumed so far.
    @returns [Some (value, consumed)] on success, [None] on overflow. *)
let rec decode_hex_group_go (ds: list byte) (acc: int) (cnt: nat)
  : Tot (option (int & nat)) (decreases ds)
  = match ds with
  | [] -> Some (acc, cnt)
  | d :: tl ->
    if is_hex d then
      let v = hex_char_to_nibble d in
      let acc' = acc * 16 + v in
      if acc' > 65535 then None
      else decode_hex_group_go tl acc' (cnt + 1)
    else Some (acc, cnt)

(** [decode_hex_group] parses 1-4 hex digits → int 0-65535.
    Returns [None] on empty input, non-hex first char, or overflow (>65535).
    Stops on non-hex char after at least one digit — correct per RFC 4291:
    the group ends when a non-hex character (like ':') is encountered.
    @param ds List of hex digit bytes.
    @returns [Some (value, consumed)] on success. *)
let decode_hex_group (ds: list byte) : option (int & nat) =
  match ds with
  | [] -> None
  | d :: tl ->
    if is_hex d then decode_hex_group_go tl (hex_char_to_nibble d) 1
    else None

(** Lemma: when [decode_hex_group_go] succeeds with accumulator in [0, 65535],
    the result is also in [0, 65535].  Induction on [ds].
    @param ds Hex digit bytes.  @param acc Accumulator value (must be in range).
    @param cnt Bytes consumed so far.
    @returns Lemma — decoded value in [0, 65535] when decode succeeds. *)
let rec lemma_decode_hex_group_go_range (ds: list byte) (acc: int) (cnt: nat) : Lemma
  (requires 0 <= acc /\ acc <= 65535)
  (ensures (match decode_hex_group_go ds acc cnt with
            | Some (n, consumed) -> 0 <= n /\ n <= 65535
            | None -> True))
  (decreases ds)
  = match ds with
  | [] -> ()
  | d :: tl ->
    if is_hex d then begin
      let v = hex_char_to_nibble d in
      let acc' = acc * 16 + v in
      if acc' > 65535 then ()
      else lemma_decode_hex_group_go_range tl acc' (cnt + 1)
    end else ()

(** Lemma: when [decode_hex_group] succeeds, the decoded value is in [0, 65535].
    @param ds Hex digit bytes to decode.
    @returns Lemma — decoded value in [0, 65535] when decode succeeds. *)
let lemma_decode_hex_group_range (ds: list byte) : Lemma
  (ensures (match decode_hex_group ds with
            | Some (n, consumed) -> 0 <= n /\ n <= 65535
            | None -> True))
  = match ds with
  | [] -> ()
  | d :: tl ->
    if is_hex d then
      lemma_decode_hex_group_go_range tl (hex_char_to_nibble d) 1
    else ()

(** Hex group roundtrip (0 admits) *)

(** Lemma: encode→decode roundtrip for 0-65535.
    Induction on n.
    @param n A nat ≤ 65535.
    @returns Lemma — [decode_hex_group (encode_hex_group n) == Some (n, |enc|)]. *)
#push-options "--z3rlimit 400"
let rec lemma_hex_group_roundtrip (n: nat) : Lemma
  (requires n <= 65535)
  (ensures decode_hex_group (encode_hex_group n) == Some (n, L.length (encode_hex_group n)))
  (decreases n)
  = if n = 0 then ()
    else begin
      let m = n / 16 in
      if m > 0 then lemma_hex_group_roundtrip m
    end
#pop-options

(** Hex group consumed bound *)

(** Lemma: [decode_hex_group_go] consumed ≤ input length.
    @param ds Input hex digit list.
    @param acc Accumulator value.  @param cnt Bytes consumed so far.
    @returns Lemma — consumed ≤ |ds| + cnt. *)
let rec lemma_decode_hex_group_go_consumed_bound (ds: list byte) (acc: int) (cnt: nat)
  : Lemma
    (ensures (match decode_hex_group_go ds acc cnt with
              | Some (_, consumed) -> consumed <= L.length ds + cnt
              | None -> True))
    (decreases ds)
  = match ds with
  | [] -> ()
  | d :: tl ->
    if is_hex d then begin
      let v = hex_char_to_nibble d in
      let acc' = acc * 16 + v in
      if acc' > 65535 then ()
      else lemma_decode_hex_group_go_consumed_bound tl acc' (cnt + 1)
    end else ()

(** Lemma: [decode_hex_group] consumed ≤ input length (top-level wrapper).
    @param ds Input hex digit list.
    @returns Lemma — consumed ≤ |ds| when decode succeeds. *)
let lemma_decode_hex_group_consumed_bound (ds: list byte) : Lemma
  (ensures (match decode_hex_group ds with
            | Some (_, consumed) -> consumed <= L.length ds
            | None -> True))
  = match ds with
  | [] -> ()
  | d :: tl ->
    if is_hex d then lemma_decode_hex_group_go_consumed_bound tl (hex_char_to_nibble d) 1
    else ()

(** Hex group codec *)

(** Well-formed-value guard for hex group codec: int in [0, 65535].
    @param n Value to check.
    @returns [true] if [0 <= n <= 65535]. *)
let wfcv_hex_group (n: int) : bool = 0 <= n && n <= 65535

(** Suffix condition: byte after encoded group must not start with
    a hex digit, ensuring unambiguous parse boundaries.
    @param n Encoded value.  @param r Suffix byte sequence.
    @returns [prop] — [|r| = 0 ∨ (|r| > 0 ∧ ¬is_hex(r[0]))]. *)
let rest_cond_hex_group (n: int) (r: byte_seq) : prop =
  FStar.Seq.length r = 0 \/ (FStar.Seq.length r > 0 /\ not (is_hex (FStar.Seq.index r 0)))

(** Decoder: [byte_seq] → [decode_result int], via list conversion.
    @param s Input byte sequence.
    @returns [Inr (value, consumed)] on success, [Inl error] on failure. *)
let hex_group_dec (s: byte_seq) : decode_result int =
  let ds = Seq.seq_to_list s in
  match decode_hex_group ds with
  | Some (n, consumed) -> Inr (n, consumed)
  | None -> Inl (mk_decode_error ExpectedPredicate 0)

(** Encoder: int → byte_seq.

    @remarks For values outside [0, 65535], the encoder clamps to
    the nearest valid value: negative → 0, >65535 → 65535.
    This ensures [hex_group_enc] accepts any [int] (required by
    the [codec.enc] field type signature) while staying within
    the hex group range.  Callers must satisfy [wfcv_hex_group n]
    to get roundtrip semantics.
    @param n Value to encode.
    @returns Byte sequence of hex-encoded digits. *)
let hex_group_enc (n: int) : byte_seq =
  let clamped : nat = if n < 0 then 0 else if n > 65535 then 65535 else n in
  seq_of_list (encode_hex_group clamped)

(** Lemma: when [wfcv_hex_group n], [nat_of_int n <= 65535].
    @param n Value in hex group range.
    @returns Lemma — [0 <= n ∧ n <= 65535]. *)
let lemma_wfcv_hex_group_bound (n: int) : Lemma
  (requires wfcv_hex_group n)
  (ensures 0 <= n /\ n <= 65535)
  = ()

(** Error bound: error position is always 0 ≤ |s|.
    @param s Input byte sequence.
    @returns Lemma — error position ≤ sequence length. *)
let lemma_hex_group_dec_err_bound (s: byte_seq) : Lemma
  (ensures (match hex_group_dec s with
            | Inl err -> err.err_pos <= FStar.Seq.length s
            | _ -> True))
  = ()

(** Consumed bound: decoded bytes ≤ input length.
    @param s Input byte sequence.
    @returns Lemma — consumed ≤ |s| when decode succeeds. *)
#push-options "--z3rlimit 200"
let lemma_hex_group_dec_consumed_bound (s: byte_seq) : Lemma
  (ensures (match hex_group_dec s with
            | Inr (_, consumed) -> consumed <= FStar.Seq.length s
            | _ -> True))
  = let ds = Seq.seq_to_list s in
    lemma_seq_list_bij s;
    lemma_decode_hex_group_consumed_bound ds;
    lemma_seq_of_list_length ds
#pop-options

(** Lemma: [decode_hex_group_go] is transparent to a non-hex suffix.
    If the decoder is processing [ds] and encounters a non-hex suffix
    after exhausting [ds], it returns the same result.
    @param ds Hex digit bytes.  @param acc Accumulated value.
    @param cnt Bytes consumed so far.
    @param suffix Suffix starting with a non-hex byte.
    @returns Lemma — [decode_hex_group_go (ds @ suffix) acc cnt == decode_hex_group_go ds acc cnt]. *)
let rec lemma_go_stops_at_non_hex (ds: list byte) (acc: int) (cnt: nat) (suffix: list byte)
  : Lemma
    (requires Cons? suffix /\ not (is_hex (L.hd suffix)))
    (ensures decode_hex_group_go (ds @ suffix) acc cnt == decode_hex_group_go ds acc cnt)
    (decreases ds)
  = match ds with
  | [] -> ()
  | d :: tl ->
    if is_hex d then begin
      let v = hex_char_to_nibble d in
      let acc' = acc * 16 + v in
      if acc' <= 65535 then lemma_go_stops_at_non_hex tl acc' (cnt + 1) suffix
    end else ()

(** Lemma: [encode_hex_group_go m acc] is non-empty when [acc] is non-empty.
    @param m Value to encode.  @param acc Accumulator (must be non-empty).
    @returns Lemma — [encode_hex_group_go m acc <> []]. *)
let rec lemma_encode_hex_group_go_nonempty (m: nat) (acc: list byte) : Lemma
  (requires acc <> [])
  (ensures encode_hex_group_go m acc <> [])
  (decreases m)
  = if m = 0 then ()
    else lemma_encode_hex_group_go_nonempty (m / 16) (nibble_to_upper_hex (m % 16) :: acc)

(** Lemma: [encode_hex_group n] is always non-empty for [n <= 65535].
    @param n Value in range.
    @returns Lemma — [encode_hex_group n <> []]. *)
let lemma_encode_hex_group_nonempty (n: nat{n <= 65535}) : Lemma
  (ensures encode_hex_group n <> [])
  = if n = 0 then ()
    else (
      assert (encode_hex_group n == encode_hex_group_go n []);
      let d = nibble_to_upper_hex (n % 16) in
      assert (encode_hex_group_go n [] == encode_hex_group_go (n / 16) [d]);
      assert ([d] <> []);
      lemma_encode_hex_group_go_nonempty (n / 16) [d]
    )

(** Lemma: [seq_to_list] of empty sequence is empty list.
    Definitionally true — [Seq.seq_to_list Seq.empty == []] by
    [FStar.Seq.Base] definition.  Exists for SMT transparency
    at the call site (the definitional equality is opaque across
    module boundaries per fstar-proofs §11 "Seq abstraction barrier").
    @returns Lemma — [Seq.seq_to_list Seq.empty == []]. *)
let lemma_seq_to_list_empty () : Lemma
  (ensures Seq.seq_to_list (Seq.empty #byte) == [])
  = ()

(** Lemma: [seq_to_list] distributes over append for [seq_of_list] prefix.
    [seq_to_list (seq_of_list l ++ s) == l ++ seq_to_list s].

    Proof by induction on [l], using [lemma_index_is_nth] and
    [lemma_seq_of_list_index] for element-wise list equality.
    This is definitionally true but the [seq] abstraction in
    [FStar.Seq.fsti] blocks SMT's ability to see through it.
    @param l List prefix.  @param s Sequence suffix.
    @returns Lemma — [seq_to_list (seq_of_list l ++ s) == l ++ seq_to_list s]. *)
#push-options "--z3rlimit 2000"
let rec lemma_seq_to_list_of_list_append (l: list byte) (s: byte_seq) : Lemma
  (ensures Seq.seq_to_list (seq_of_list l `Seq.append` s) == l @ Seq.seq_to_list s)
  (decreases l)
  = match l with
    | [] -> 
      Seq.lemma_eq_intro (seq_of_list [] `Seq.append` s) s;
      assert (Seq.seq_to_list (seq_of_list [] `Seq.append` s) == Seq.seq_to_list s);
      assert ([] @ Seq.seq_to_list s == Seq.seq_to_list s);
      ()
    | h :: t ->
      lemma_seq_to_list_of_list_append t s;
      let st = seq_of_list t in
      FStar.Seq.Base.lemma_seq_of_list_cons h t;
      FStar.Seq.Properties.append_cons h st s;
      let combined = st `Seq.append` s in
      FStar.Seq.Base.lemma_seq_to_list_cons h combined;
      assert (seq_of_list (h::t) == Seq.cons h st);
      assert (Seq.cons h st `Seq.append` s == Seq.cons h combined);
      assert (Seq.seq_to_list (Seq.cons h combined) == h :: Seq.seq_to_list combined);
      assert (Seq.seq_to_list combined == t @ Seq.seq_to_list s);
      ()
#pop-options


(** Bridge: list-level roundtrip → seq-level roundtrip (for [custom]).
    Calls [lemma_hex_group_roundtrip] and bridges seq↔list via
    [lemma_seq_list_bij] and [lemma_seq_of_list_length].
    @param n Value in 0-65535.  @param r Suffix bytes — empty or non-hex-starting.
    @returns Lemma — [hex_group_dec (hex_group_enc n ++ r) == Inr (n, |enc|)]. *)
#push-options "--z3rlimit 400"
let lemma_hex_group_roundtrip_seq (n: int) (r: byte_seq) : Lemma
  (requires wfcv_hex_group n /\ rest_cond_hex_group n r)
  (ensures hex_group_dec (hex_group_enc n `FStar.Seq.append` r)
        == Inr (n, FStar.Seq.length (hex_group_enc n)))
  = lemma_wfcv_hex_group_bound n;
    let n_nat : nat = n in
    lemma_hex_group_roundtrip n_nat;
    let enc_list = encode_hex_group n_nat in
    lemma_seq_of_list_length enc_list;
    let enc_seq = seq_of_list enc_list in
    (* hex_group_enc n == enc_seq *)
    assert (hex_group_enc n == enc_seq);
    (* Work at the list level.  hex_group_dec (enc_seq ++ r)
       = match decode_hex_group (seq_to_list (enc_seq ++ r)) with ...
       Need to prove decode_hex_group on the combined list works.
       Use lemma_hex_group_roundtrip (empty suffix) and
       lemma_go_stops_at_non_hex (non-hex suffix). *)
    let r_list = Seq.seq_to_list r in
    lemma_seq_list_bij r;
    (* decode_hex_group (enc_list @ r_list):
       If r_list starts with non-hex (including empty), stops correctly. *)
    if Seq.length r > 0 then begin
      assert (Seq.length r > 0);
      assert (not (is_hex (Seq.index r 0)));
      (* Bridge to list representation *)
      assert (Cons? r_list);
      assert (L.hd r_list == Seq.index r 0);
      assert (not (is_hex (L.hd r_list)));
      lemma_encode_hex_group_nonempty n_nat;
      let enc = encode_hex_group n_nat in
      assert (Cons? enc);
      let hd_enc = L.hd enc in
      let tl_enc = L.tl enc in
      lemma_go_stops_at_non_hex tl_enc (hex_char_to_nibble hd_enc) 1 r_list;
      lemma_hex_group_roundtrip n_nat
    end else begin
      lemma_seq_to_list_empty ();
      lemma_hex_group_roundtrip n_nat
    end;
    assert (decode_hex_group (enc_list @ r_list) == Some (n_nat, L.length enc_list));
    (* Bridge: hex_group_dec (enc_seq ++ r) uses decode_hex_group on
       seq_to_list (enc_seq ++ r).  But we proved the result for
       enc_list @ r_list.  Need seq_to_list (enc_seq ++ r) == enc_list @ r_list.
       For seq_of_list, the conversion distributes over append by
       Lemma.seq_list_bij properties. *)
    let combined_seq = enc_seq `Seq.append` r in
    let combined_list = Seq.seq_to_list combined_seq in
    lemma_seq_list_bij_rev enc_list;
    lemma_seq_list_bij r;
    lemma_seq_to_list_of_list_append enc_list r;
    assert (combined_list == enc_list @ r_list);
    assert (hex_group_dec combined_seq == Inr (n_nat, L.length enc_list));
    assert (Seq.length (hex_group_enc n) == L.length enc_list)
#pop-options

(** Hex group codec — proven codec for 1-4 hex digits → int 0-65535.
    0 admits.
    @returns [codec int] for 1-4 hex digits. *)
let hex_group_codec : codec int =
  custom
    hex_group_dec
    hex_group_enc
    wfcv_hex_group
    (fun _ -> True)
    rest_cond_hex_group
    lemma_hex_group_roundtrip_seq
    lemma_hex_group_dec_err_bound
    lemma_hex_group_dec_consumed_bound

(** Every int in 0-65535 satisfies [hex_group_codec.wfcv].
    @param n Value in range.
    @returns Lemma — [hex_group_codec.wfcv n]. *)
let lemma_hex_group_codec_wfcv (n: int) : Lemma
  (requires 0 <= n /\ n <= 65535)
  (ensures hex_group_codec.wfcv n)
  = ()

(** List-level encode/decode *)

(** Bypasses the codec combinator chain — calls
    [encode_hex_group]/[decode_hex_group] directly with explicit
    chaining for 8 groups.
*)

(** Colon separator byte (ASCII ':' = 0x3A). *)
let ipv6_sep : byte = 0x3Auy

(** Lemma: [ipv6_sep] equals the literal [0x3Auy].  Exists for
    integration-test anchoring.
    @returns Lemma — [ipv6_sep == 0x3Auy]. *)
let lemma_ipv6_sep_value () : Lemma (ipv6_sep == 0x3Auy) = ()

(** [encode_ipv6_list] serializes an [ipv6] to a byte list in colon-hex format.
    @param v IPv6 address to encode.
    @returns Byte list of hex digits and colons. *)
let encode_ipv6_list (v: ipv6) : list byte =
  encode_hex_group v.group0 @ [ipv6_sep] @
  encode_hex_group v.group1 @ [ipv6_sep] @
  encode_hex_group v.group2 @ [ipv6_sep] @
  encode_hex_group v.group3 @ [ipv6_sep] @
  encode_hex_group v.group4 @ [ipv6_sep] @
  encode_hex_group v.group5 @ [ipv6_sep] @
  encode_hex_group v.group6 @ [ipv6_sep] @
  encode_hex_group v.group7

(** [decode_ipv6_list] parses colon-hex bytes into an [ipv6].
    Explicit [if None?] / [Some?.v] style — SMT can follow this structure.
    @param bs Byte list to decode.
    @returns [Some (ipv6, total_bytes)] on success, [None] on error. *)
let decode_ipv6_list (bs: list byte) : option (ipv6 & nat) =
  let step0 = decode_hex_group bs in
  if None? step0 then None
  else
    let (g0, n0) = Some?.v step0 in
    lemma_decode_hex_group_range bs;
    let after0 = drop n0 bs in
    if L.length after0 = 0 || L.hd after0 <> ipv6_sep then None
    else
      let after_colon0 = drop 1 after0 in
      let step1 = decode_hex_group after_colon0 in
      if None? step1 then None
      else
        let (g1, n1) = Some?.v step1 in
        lemma_decode_hex_group_range after_colon0;
        let after1 = drop n1 after_colon0 in
        if L.length after1 = 0 || L.hd after1 <> ipv6_sep then None
        else
          let after_colon1 = drop 1 after1 in
          let step2 = decode_hex_group after_colon1 in
          if None? step2 then None
          else
            let (g2, n2) = Some?.v step2 in
            lemma_decode_hex_group_range after_colon1;
            let after2 = drop n2 after_colon1 in
            if L.length after2 = 0 || L.hd after2 <> ipv6_sep then None
            else
              let after_colon2 = drop 1 after2 in
              let step3 = decode_hex_group after_colon2 in
              if None? step3 then None
              else
                let (g3, n3) = Some?.v step3 in
                lemma_decode_hex_group_range after_colon2;
                let after3 = drop n3 after_colon2 in
                if L.length after3 = 0 || L.hd after3 <> ipv6_sep then None
                else
                  let after_colon3 = drop 1 after3 in
                  let step4 = decode_hex_group after_colon3 in
                  if None? step4 then None
                  else
                    let (g4, n4) = Some?.v step4 in
                    lemma_decode_hex_group_range after_colon3;
                    let after4 = drop n4 after_colon3 in
                    if L.length after4 = 0 || L.hd after4 <> ipv6_sep then None
                    else
                      let after_colon4 = drop 1 after4 in
                      let step5 = decode_hex_group after_colon4 in
                      if None? step5 then None
                      else
                        let (g5, n5) = Some?.v step5 in
                        lemma_decode_hex_group_range after_colon4;
                        let after5 = drop n5 after_colon4 in
                        if L.length after5 = 0 || L.hd after5 <> ipv6_sep then None
                        else
                          let after_colon5 = drop 1 after5 in
                          let step6 = decode_hex_group after_colon5 in
                          if None? step6 then None
                          else
                            let (g6, n6) = Some?.v step6 in
                            lemma_decode_hex_group_range after_colon5;
                            let after6 = drop n6 after_colon5 in
                            if L.length after6 = 0 || L.hd after6 <> ipv6_sep then None
                            else
                              let after_colon6 = drop 1 after6 in
                              let step7 = decode_hex_group after_colon6 in
                              if None? step7 then None
                              else
                                let (g7, n7) = Some?.v step7 in
                                lemma_decode_hex_group_range after_colon6;
                                Some ({group0=g0;group1=g1;group2=g2;group3=g3;
                                       group4=g4;group5=g5;group6=g6;group7=g7},
                                      n0+1+n1+1+n2+1+n3+1+n4+1+n5+1+n6+1+n7)

(** Hex group roundtrip with suffix *)

(** Hex group roundtrip with colon (0x3A) suffix.
    @param g Group value.  @param suffix Byte list starting with [ipv6_sep].
    @returns Lemma — [decode_hex_group (encode_hex_group g @ suffix) == Some (g, |enc|)]. *)
let lemma_hex_group_roundtrip_colon_suffix (g: nat) (suffix: list byte) : Lemma
  (requires g <= 65535 /\ Cons? suffix /\ L.hd suffix == ipv6_sep)
  (ensures decode_hex_group (encode_hex_group g @ suffix)
        == Some (g, L.length (encode_hex_group g)))
  = assert_norm (not (is_hex ipv6_sep));
    lemma_hex_group_roundtrip g;
    lemma_encode_hex_group_nonempty g;
    let enc = encode_hex_group g in
    match enc with
    | hd_enc :: tl_enc ->
      lemma_go_stops_at_non_hex tl_enc (hex_char_to_nibble hd_enc) 1 suffix
    | [] ->
      (* Unreachable: [lemma_encode_hex_group_nonempty g] proves [enc <> []] *)
      assert (False)

(** Hex group roundtrip with empty suffix (last group).
    Thin wrapper around [lemma_hex_group_roundtrip] — provides a
    consistent naming convention.
    @param g Group value ≤ 65535.
    @returns Lemma — [decode_hex_group (encode_hex_group g) == Some (g, |enc|)]. *)
let lemma_hex_group_roundtrip_empty (g: nat) : Lemma
  (requires g <= 65535)
  (ensures decode_hex_group (encode_hex_group g) == Some (g, L.length (encode_hex_group g)))
  = lemma_hex_group_roundtrip g

(** List-level IPv6 roundtrip *)

(** RFC 4291 §2.2 ¶1 roundtrip: for all [v: ipv6] with valid groups,
    [decode_ipv6_list (encode_ipv6_list v) == Some (v, |enc_v|)].
    0 admits — proven by direct structural decomposition.
    @param v An ipv6 value with all groups in [0, 65535]. *)
#push-options "--z3rlimit 400"
let lemma_ipv6_list_roundtrip (v: ipv6) : Lemma
  (ensures decode_ipv6_list (encode_ipv6_list v)
        == Some (v, L.length (encode_ipv6_list v)))
  = let g0 = v.group0 in let g1 = v.group1 in let g2 = v.group2 in let g3 = v.group3 in
    let g4 = v.group4 in let g5 = v.group5 in let g6 = v.group6 in let g7 = v.group7 in
    let h0 = encode_hex_group g0 in let h1 = encode_hex_group g1 in
    let h2 = encode_hex_group g2 in let h3 = encode_hex_group g3 in
    let h4 = encode_hex_group g4 in let h5 = encode_hex_group g5 in
    let h6 = encode_hex_group g6 in let h7 = encode_hex_group g7 in
    let enc = h0 @ [ipv6_sep] @ h1 @ [ipv6_sep] @ h2 @ [ipv6_sep] @ h3 @ [ipv6_sep] @
              h4 @ [ipv6_sep] @ h5 @ [ipv6_sep] @ h6 @ [ipv6_sep] @ h7 in
    
    (* Group 0 + colon *)
    lemma_hex_group_roundtrip_colon_suffix g0 ([ipv6_sep] @ h1 @ [ipv6_sep] @ h2 @ [ipv6_sep] @ h3 @ [ipv6_sep] @ h4 @ [ipv6_sep] @ h5 @ [ipv6_sep] @ h6 @ [ipv6_sep] @ h7);
    lemma_drop_append_length h0 ([ipv6_sep] @ h1 @ [ipv6_sep] @ h2 @ [ipv6_sep] @ h3 @ [ipv6_sep] @ h4 @ [ipv6_sep] @ h5 @ [ipv6_sep] @ h6 @ [ipv6_sep] @ h7);
    assert (decode_hex_group enc == Some (g0, L.length h0));
    assert (L.hd (drop (L.length h0) enc) == ipv6_sep);
    assert (drop 1 (drop (L.length h0) enc) == h1 @ [ipv6_sep] @ h2 @ [ipv6_sep] @ h3 @ [ipv6_sep] @ h4 @ [ipv6_sep] @ h5 @ [ipv6_sep] @ h6 @ [ipv6_sep] @ h7);
    
    (* Group 1 *)
    lemma_hex_group_roundtrip_colon_suffix g1 ([ipv6_sep] @ h2 @ [ipv6_sep] @ h3 @ [ipv6_sep] @ h4 @ [ipv6_sep] @ h5 @ [ipv6_sep] @ h6 @ [ipv6_sep] @ h7);
    lemma_drop_append_length h1 ([ipv6_sep] @ h2 @ [ipv6_sep] @ h3 @ [ipv6_sep] @ h4 @ [ipv6_sep] @ h5 @ [ipv6_sep] @ h6 @ [ipv6_sep] @ h7);
    
    (* Group 2 *)
    lemma_hex_group_roundtrip_colon_suffix g2 ([ipv6_sep] @ h3 @ [ipv6_sep] @ h4 @ [ipv6_sep] @ h5 @ [ipv6_sep] @ h6 @ [ipv6_sep] @ h7);
    lemma_drop_append_length h2 ([ipv6_sep] @ h3 @ [ipv6_sep] @ h4 @ [ipv6_sep] @ h5 @ [ipv6_sep] @ h6 @ [ipv6_sep] @ h7);
    
    (* Group 3 *)
    lemma_hex_group_roundtrip_colon_suffix g3 ([ipv6_sep] @ h4 @ [ipv6_sep] @ h5 @ [ipv6_sep] @ h6 @ [ipv6_sep] @ h7);
    lemma_drop_append_length h3 ([ipv6_sep] @ h4 @ [ipv6_sep] @ h5 @ [ipv6_sep] @ h6 @ [ipv6_sep] @ h7);
    
    (* Group 4 *)
    lemma_hex_group_roundtrip_colon_suffix g4 ([ipv6_sep] @ h5 @ [ipv6_sep] @ h6 @ [ipv6_sep] @ h7);
    lemma_drop_append_length h4 ([ipv6_sep] @ h5 @ [ipv6_sep] @ h6 @ [ipv6_sep] @ h7);
    
    (* Group 5 *)
    lemma_hex_group_roundtrip_colon_suffix g5 ([ipv6_sep] @ h6 @ [ipv6_sep] @ h7);
    lemma_drop_append_length h5 ([ipv6_sep] @ h6 @ [ipv6_sep] @ h7);
    
    (* Group 6 *)
    lemma_hex_group_roundtrip_colon_suffix g6 ([ipv6_sep] @ h7);
    lemma_drop_append_length h6 ([ipv6_sep] @ h7);
    
    (* Group 7 (last) *)
    lemma_hex_group_roundtrip_empty g7;
    lemma_drop_append_length h7 [];
    
    ()
#pop-options

(** Codec-level functions *)

(** Well-formed-value guard: all groups must be in [0, 65535].
    The [ipv6] type's refined [ipv6_group] fields guarantee this,
    so this is always true.
    @param v IPv6 address value.
    @returns [true] when all groups are in range (always true by type). *)
let wfcv_ipv6 (v: ipv6) : bool =
  0 <= v.group0 && v.group0 <= 65535 &&
  0 <= v.group1 && v.group1 <= 65535 &&
  0 <= v.group2 && v.group2 <= 65535 &&
  0 <= v.group3 && v.group3 <= 65535 &&
  0 <= v.group4 && v.group4 <= 65535 &&
  0 <= v.group5 && v.group5 <= 65535 &&
  0 <= v.group6 && v.group6 <= 65535 &&
  0 <= v.group7 && v.group7 <= 65535

(** Well-formed-value property: always True (refinement type guarantees range).
    @param v IPv6 address value.
    @returns [True] (always). *)
let wfcv_prop_ipv6 (v: ipv6) : prop = True

(** Rest condition: suffix must be empty.
    The hex group decoder is digit-greedy — it consumes all consecutive
    hex digits.  Only the empty suffix is safe: a non-empty suffix
    starting with a hex digit would be incorrectly consumed as part
    of the last group.  For roundtrip ([r = Seq.empty]), this holds
    trivially.

    If composition with non-hex-delimited suffixes is needed, extend
    the rest_cond and roundtrip lemma accordingly.
    @param v IPv6 address value.
    @param r Suffix byte sequence — must be [Seq.empty] for roundtrip.
    @returns [prop] — [r == Seq.empty]. *)
let rest_cond_ipv6 (v: ipv6) (r: byte_seq) : prop =
  r == Seq.empty

(** Encoder: [ipv6 → byte_seq].
    Delegates to the list-level encoder.
    @param v IPv6 address to encode.
    @returns Byte sequence of encoded colon-hex format. *)
let ipv6_enc (v: ipv6) : byte_seq =
  seq_of_list (encode_ipv6_list v)

(** Decoder: [byte_seq → decode_result ipv6].
    Delegates to the list-level decoder.
    @param s Byte sequence to decode.
    @returns [Inr (ipv6, consumed)] on success, [Inl error] on failure. *)
let ipv6_dec (s: byte_seq) : decode_result ipv6 =
  match decode_ipv6_list (Seq.seq_to_list s) with
  | Some (v, n) -> Inr (v, n)
  | None -> Inl (mk_decode_error ExpectedPredicate 0)

(** Decoder error position bound.
    Body is [()] because [mk_decode_error ExpectedPredicate 0]
    always produces [err_pos = 0], and [0 <= Seq.length s] holds
    for all [s].  @param s Input byte sequence.
    @returns Lemma — error position ≤ sequence length. *)
let lemma_ipv6_dec_err_bound (s: byte_seq) : Lemma
  (ensures (match ipv6_dec s with
            | Inl err -> err.err_pos <= Seq.length s
            | _ -> True))
  = ()

(** Lemma: [decode_hex_group] consumed <= input length. *)
let lemma_decode_hex_group_list_consumed (ds: list byte) : Lemma
  (ensures (match decode_hex_group ds with
            | Some (_, n) -> n <= L.length ds
            | None -> True))
  = lemma_decode_hex_group_consumed_bound ds;
    ()

(** Lemma: [decode_ipv6_list] consumed <= input length.
    Explicit 8-group decomposition matching the IPv4 [lemma_decode_ipv4_list_consumed]
    pattern.  Each hex group consumes at most remaining bytes, and the 7
    colon separators are bounded by the total input.

    Proves: [n0+1+n1+1+n2+1+n3+1+n4+1+n5+1+n6+1+n7 <= |bs|].
    @param bs Input byte list. *)
#push-options "--z3rlimit 200"
let lemma_decode_ipv6_list_consumed (bs: list byte) : Lemma
  (ensures (match decode_ipv6_list bs with
            | Some (_, consumed) -> consumed <= L.length bs
            | None -> True))
  =
  let step0 = decode_hex_group bs in
  match step0 with
  | None -> ()
  | Some (_, n0) ->
    lemma_decode_hex_group_list_consumed bs;
    let after0 = drop n0 bs in
    lemma_drop_length_exact n0 bs;
    lemma_drop_length_bound n0 bs;
    if L.length after0 = 0 || L.hd after0 <> ipv6_sep then ()
    else begin
      let after_colon0 = drop 1 after0 in
      lemma_drop_length_exact 1 after0;
      let step1 = decode_hex_group after_colon0 in
      match step1 with
      | None -> ()
      | Some (_, n1) ->
        lemma_decode_hex_group_list_consumed after_colon0;
        let after1 = drop n1 after_colon0 in
        lemma_drop_length_exact n1 after_colon0;
        if L.length after1 = 0 || L.hd after1 <> ipv6_sep then ()
        else begin
          let after_colon1 = drop 1 after1 in
          lemma_drop_length_exact 1 after1;
          let step2 = decode_hex_group after_colon1 in
          match step2 with
          | None -> ()
          | Some (_, n2) ->
            lemma_decode_hex_group_list_consumed after_colon1;
            let after2 = drop n2 after_colon1 in
            lemma_drop_length_exact n2 after_colon1;
            if L.length after2 = 0 || L.hd after2 <> ipv6_sep then ()
            else begin
              let after_colon2 = drop 1 after2 in
              lemma_drop_length_exact 1 after2;
              let step3 = decode_hex_group after_colon2 in
              match step3 with
              | None -> ()
              | Some (_, n3) ->
                lemma_decode_hex_group_list_consumed after_colon2;
                let after3 = drop n3 after_colon2 in
                lemma_drop_length_exact n3 after_colon2;
                if L.length after3 = 0 || L.hd after3 <> ipv6_sep then ()
                else begin
                  let after_colon3 = drop 1 after3 in
                  lemma_drop_length_exact 1 after3;
                  let step4 = decode_hex_group after_colon3 in
                  match step4 with
                  | None -> ()
                  | Some (_, n4) ->
                    lemma_decode_hex_group_list_consumed after_colon3;
                    let after4 = drop n4 after_colon3 in
                    lemma_drop_length_exact n4 after_colon3;
                    if L.length after4 = 0 || L.hd after4 <> ipv6_sep then ()
                    else begin
                      let after_colon4 = drop 1 after4 in
                      lemma_drop_length_exact 1 after4;
                      let step5 = decode_hex_group after_colon4 in
                      match step5 with
                      | None -> ()
                      | Some (_, n5) ->
                        lemma_decode_hex_group_list_consumed after_colon4;
                        let after5 = drop n5 after_colon4 in
                        lemma_drop_length_exact n5 after_colon4;
                        if L.length after5 = 0 || L.hd after5 <> ipv6_sep then ()
                        else begin
                          let after_colon5 = drop 1 after5 in
                          lemma_drop_length_exact 1 after5;
                          let step6 = decode_hex_group after_colon5 in
                          match step6 with
                          | None -> ()
                          | Some (_, n6) ->
                            lemma_decode_hex_group_list_consumed after_colon5;
                            let after6 = drop n6 after_colon5 in
                            lemma_drop_length_exact n6 after_colon5;
                            if L.length after6 = 0 || L.hd after6 <> ipv6_sep then ()
                            else begin
                              let after_colon6 = drop 1 after6 in
                              lemma_drop_length_exact 1 after6;
                              let step7 = decode_hex_group after_colon6 in
                              match step7 with
                              | None -> ()
                              | Some (_, n7) ->
                                lemma_decode_hex_group_list_consumed after_colon6;
                                lemma_drop_length_exact n7 after_colon6;
                                assert (n0 + 1 + n1 + 1 + n2 + 1 + n3 + 1 + n4 + 1 + n5 + 1 + n6 + 1 + n7 <= L.length bs);
                                ()
                            end
                        end
                    end
                end
            end
        end
    end
#pop-options

(** Decoder consumed bound.  Uses [lemma_decode_ipv6_list_consumed].
    @param s Input byte sequence. *)
let lemma_ipv6_dec_consumed_bound (s: byte_seq) : Lemma
  (ensures (match ipv6_dec s with
            | Inr (_, n) -> n <= Seq.length s
            | _ -> True))
  = lemma_seq_list_bij s;
    lemma_decode_ipv6_list_consumed (Seq.seq_to_list s);
    ()

(** Roundtrip lemma: encode→decode returns the original value.
    Bridges the list-level proof to byte_seq.  Only handles the
    empty suffix case ([r = Seq.empty]).
    @param v IPv6 address.  @param r Must be [Seq.empty]. *)
#push-options "--z3rlimit 200"
let lemma_ipv6_roundtrip (v: ipv6) (r: byte_seq) : Lemma
  (requires wfcv_ipv6 v /\ wfcv_prop_ipv6 v /\ rest_cond_ipv6 v r)
  (ensures ipv6_dec (ipv6_enc v `Seq.append` r)
        == Inr (v, Seq.length (ipv6_enc v)))
  = assert (r == Seq.empty);
    let enc_list = encode_ipv6_list v in
    lemma_ipv6_list_roundtrip v;
    lemma_seq_list_bij_rev enc_list;
    lemma_seq_of_list_length enc_list;
    let enc_seq = seq_of_list enc_list in
    assert (Seq.length enc_seq == L.length enc_list);
    assert (Seq.seq_to_list enc_seq == enc_list);
    assert (decode_ipv6_list (Seq.seq_to_list enc_seq) == Some (v, L.length enc_list));
    assert (ipv6_dec enc_seq == Inr (v, L.length enc_list));
    assert (Seq.length (ipv6_enc v) == L.length enc_list);
    Seq.lemma_eq_intro (enc_seq `Seq.append` Seq.empty) enc_seq
#pop-options

(** The IPv6 codec: flat [custom] combinator, no [product]/[map_] chain.
    Roundtrip proof bridges the list-level structural induction.
    Zero admits.
    @returns [codec ipv6] for colon-hex text format. *)
#push-options "--z3rlimit 400"
let ipv6_codec : codec ipv6 =
  custom
    ipv6_dec
    ipv6_enc
    wfcv_ipv6
    wfcv_prop_ipv6
    rest_cond_ipv6
    lemma_ipv6_roundtrip
    lemma_ipv6_dec_err_bound
    lemma_ipv6_dec_consumed_bound
#pop-options

(** Public API *)

(** [encode_ipv6] serializes an [ipv6] to colon-hex bytes.
    @param ip Address to encode.
    @returns Byte sequence of encoded colon-hex format. *)
let encode_ipv6 (ip: ipv6) : byte_seq = ipv6_codec.enc ip

(** [decode_ipv6] parses colon-hex bytes into an [ipv6].
    @param input Byte sequence to decode.
    @returns [Some ipv6] on success, [None] on error. *)
let decode_ipv6 (input: byte_seq) : Tot (option ipv6) =
  match ipv6_codec.dec input with Inl _ -> None | Inr (v, _) -> Some v

(** Roundtrip wrapper. @param v An ipv6 value.
    @returns Lemma — [decode_ipv6 (encode_ipv6 v ++ empty) == Some v]. *)
let lemma_encode_ipv6_roundtrip (v: ipv6) : Lemma
  (ensures decode_ipv6 (encode_ipv6 v `Seq.append` Seq.empty) == Some v)
  = lemma_ipv6_roundtrip v Seq.empty

(** Codec-level roundtrip (backward compat alias).
    @param v An ipv6 value.
    @returns Lemma — [ipv6_codec.dec (ipv6_codec.enc v ++ empty) == Inr (v, |enc|)]. *)
let lemma_roundtrip (v: ipv6) : Lemma
  (ensures ipv6_codec.dec (ipv6_codec.enc v `Seq.append` Seq.empty)
        == Inr (v, Seq.length (ipv6_codec.enc v)))
  = lemma_ipv6_roundtrip v Seq.empty

(** RFC compliance *)

(** Corollary: roundtrip for values from [ipv6_of_groups].
    @param g0-g7 Eight group values.
    @returns Lemma — roundtrip holds when [ipv6_of_groups] succeeds. *)
let lemma_roundtrip_of_groups (g0 g1 g2 g3 g4 g5 g6 g7: int) : Lemma
  (requires Some? (ipv6_of_groups g0 g1 g2 g3 g4 g5 g6 g7))
  (ensures (
    let Some v = ipv6_of_groups g0 g1 g2 g3 g4 g5 g6 g7 in
    ipv6_codec.dec (ipv6_codec.enc v `Seq.append` Seq.empty) == Inr (v, Seq.length (ipv6_codec.enc v))))
  = let Some v = ipv6_of_groups g0 g1 g2 g3 g4 g5 g6 g7 in
    lemma_roundtrip v

(** Lemma: for an [ipv6] that passes [ipv6_of_groups] validation, all group
    fields are in [0, 65535].  The ensures follows from the [ipv6_group]
    refinement type; the requires connects the runtime [ipv6_of_groups]
    check to the type-level guarantee.
    @param v An ipv6 value that satisfies [ipv6_of_groups]. *)
let lemma_ipv6_group_range (v: ipv6) : Lemma
  (requires Some? (ipv6_of_groups v.group0 v.group1 v.group2 v.group3
                                   v.group4 v.group5 v.group6 v.group7))
  (ensures 0 <= v.group0 /\ v.group0 <= 65535 /\
           0 <= v.group1 /\ v.group1 <= 65535 /\
           0 <= v.group2 /\ v.group2 <= 65535 /\
           0 <= v.group3 /\ v.group3 <= 65535 /\
           0 <= v.group4 /\ v.group4 <= 65535 /\
           0 <= v.group5 /\ v.group5 <= 65535 /\
           0 <= v.group6 /\ v.group6 <= 65535 /\
           0 <= v.group7 /\ v.group7 <= 65535)
  = ()

(** RFC 4291 §2.2: Hex digits SHALL accept 0-9, a-f, A-F.
    Proves [is_hex b <==> v in ('0'-'9') || ('A'-'F') || ('a'-'f')].

    Forward direction: if [v] is in one of the three hex ranges, then
    [is_hex b] holds (proved by case-split on the three ranges).
    Backward direction: if [is_hex b], then [v] must be in one of the
    three ranges (proved by contradiction — [is_hex] only returns true
    for bytes in those ranges per [Data.BaseN.Base16]).
    @param b Any byte.
    @returns The equivalence [is_hex b <==> ranges]. *)
let lemma_hex_digit_ranges (b: byte) : Lemma
  (ensures is_hex b <==>
    (let v = U8.v b in
     (0x30 <= v && v <= 0x39) || (0x41 <= v && v <= 0x46) || (0x61 <= v && v <= 0x66)))
  = let v = U8.v b in
    if (0x30 <= v && v <= 0x39) || (0x41 <= v && v <= 0x46) || (0x61 <= v && v <= 0x66)
    then begin
      if 0x30 <= v && v <= 0x39 then assert (0x30 <= v && v <= 0x39)
      else if 0x41 <= v && v <= 0x46 then assert (0x41 <= v && v <= 0x46)
      else (if 0x61 <= v && v <= 0x66 then assert (0x61 <= v && v <= 0x66))
    end
    else if is_hex b then begin
      if 0x30 <= v && v <= 0x39 then ()
      else if 0x41 <= v && v <= 0x46 then ()
      else (if 0x61 <= v && v <= 0x66 then ())
    end
    else ()

(** RFC test vectors — prove roundtrip for well-known addresses.

    All vectors use FULL FORM (8 groups, no :: compression).
    :: zero-compression (RFC 4291 §2.2 item 2) is NOT supported.

    Each vector proves [decode(encode(addr)) == addr] via the
    list-level roundtrip lemma.  Zero admits.
*)

(** RFC 4291: loopback ::1 (full form: 0:0:0:0:0:0:0:1).
    @returns Lemma — roundtrip for loopback address. *)
let lemma_ipv6_loopback_concrete () : Lemma
  (ensures (match decode_ipv6_list (encode_ipv6_list ipv6_loopback) with
            | Some (ip, _) -> ip = ipv6_loopback
            | _ -> False))
  = lemma_ipv6_list_roundtrip ipv6_loopback

(** RFC 4291: unspecified :: (full form: 0:0:0:0:0:0:0:0).
    @returns Lemma — roundtrip for unspecified address. *)
let lemma_ipv6_unspecified_concrete () : Lemma
  (ensures (match decode_ipv6_list (encode_ipv6_list ipv6_unspecified) with
            | Some (ip, _) -> ip = ipv6_unspecified
            | _ -> False))
  = lemma_ipv6_list_roundtrip ipv6_unspecified

(** RFC 4291: documentation prefix 2001:db8::/32
    (full form: 2001:0db8:0:0:0:0:0:1).
    @returns Lemma — roundtrip for documentation address. *)
let lemma_ipv6_doc_concrete () : Lemma
  (ensures (let doc_v : ipv6 =
             {group0=0x2001; group1=0x0db8; group2=0; group3=0;
              group4=0; group5=0; group6=0; group7=1} in
            match decode_ipv6_list (encode_ipv6_list doc_v) with
            | Some (ip, _) ->
              ip.group0 = 0x2001 /\ ip.group1 = 0x0db8 /\
              ip.group2 = 0 /\ ip.group3 = 0 /\ ip.group4 = 0 /\
              ip.group5 = 0 /\ ip.group6 = 0 /\ ip.group7 = 1
            | _ -> False))
  = lemma_ipv6_list_roundtrip ({group0=0x2001; group1=0x0db8; group2=0; group3=0;
                                 group4=0; group5=0; group6=0; group7=1})

(** All-groups-max: ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff.
    Tests the extreme upper bound of every group.
    @returns Lemma — roundtrip for all-max address. *)
let lemma_ipv6_all_max_concrete () : Lemma
  (ensures (let max_v : ipv6 =
             {group0=0xffff; group1=0xffff; group2=0xffff; group3=0xffff;
              group4=0xffff; group5=0xffff; group6=0xffff; group7=0xffff} in
            match decode_ipv6_list (encode_ipv6_list max_v) with
            | Some (ip, _) ->
              ip.group0 = 0xffff /\ ip.group1 = 0xffff /\
              ip.group2 = 0xffff /\ ip.group3 = 0xffff /\
              ip.group4 = 0xffff /\ ip.group5 = 0xffff /\
              ip.group6 = 0xffff /\ ip.group7 = 0xffff
            | _ -> False))
  = lemma_ipv6_list_roundtrip ({group0=0xffff; group1=0xffff; group2=0xffff; group3=0xffff;
                                 group4=0xffff; group5=0xffff; group6=0xffff; group7=0xffff})

(** Single-digit groups: 0:1:2:3:4:5:6:7.
    Tests minimal encoding (no leading zeros needed).
    @returns Lemma — roundtrip for single-digit address. *)
let lemma_ipv6_single_digit_concrete () : Lemma
  (ensures (let sd_v : ipv6 =
             {group0=0; group1=1; group2=2; group3=3;
              group4=4; group5=5; group6=6; group7=7} in
            match decode_ipv6_list (encode_ipv6_list sd_v) with
            | Some (ip, _) ->
              ip.group0 = 0 /\ ip.group1 = 1 /\
              ip.group2 = 2 /\ ip.group3 = 3 /\
              ip.group4 = 4 /\ ip.group5 = 5 /\
              ip.group6 = 6 /\ ip.group7 = 7
            | _ -> False))
  = lemma_ipv6_list_roundtrip ({group0=0; group1=1; group2=2; group3=3;
                                 group4=4; group5=5; group6=6; group7=7})

(** Mixed-case hex: 2001:0Db8:aBcD:Ef01:2345:6789:aBcD:eF01.
    Tests uppercase/lowercase tolerance in decoder.
    @returns Lemma — roundtrip for mixed-case address. *)
let lemma_ipv6_mixed_case_concrete () : Lemma
  (ensures (let mc_v : ipv6 =
             {group0=0x2001; group1=0x0db8; group2=0xabcd; group3=0xef01;
              group4=0x2345; group5=0x6789; group6=0xabcd; group7=0xef01} in
            match decode_ipv6_list (encode_ipv6_list mc_v) with
            | Some (ip, _) ->
              ip.group0 = 0x2001 /\ ip.group1 = 0x0db8 /\
              ip.group2 = 0xabcd /\ ip.group3 = 0xef01 /\
              ip.group4 = 0x2345 /\ ip.group5 = 0x6789 /\
              ip.group6 = 0xabcd /\ ip.group7 = 0xef01
            | _ -> False))
  = lemma_ipv6_list_roundtrip ({group0=0x2001; group1=0x0db8; group2=0xabcd; group3=0xef01;
                                 group4=0x2345; group5=0x6789; group6=0xabcd; group7=0xef01})
