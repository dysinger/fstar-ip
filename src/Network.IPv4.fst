(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)

(**
Network.IPv4 — IPv4 Address codec (RFC 791 §3.1).

IPv4 addresses are 32-bit values written in "dotted decimal" notation:
four decimal integers 0-255 separated by periods (e.g., "127.0.0.1").

Built on [digits_to_int] from [Data.Codec.Types] for decimal-octet parsing.
The codec uses [custom] with a flat encoder/decoder pair — no [product]
or [map_] combinator chain.  This eliminates the opaque [rest_cond]
barrier (fstar-proofs §18) and the non-self-delimiting digit-suffix
problem in middle octets.

Roundtrip proof: list-level structural induction (0 admits), bridged to
[byte_seq] via [seq_of_list]/[seq_to_list] conversion lemmas.

@header Network.IPv4

@section Types
- [ipv4] — four octets as [UInt8.t] (byte)

@section Codec
- [ipv4_codec] — full dotted-decimal codec ([custom] combinator)

@section Lemmas
- [lemma_ipv4_list_roundtrip] — list-level encode→decode roundtrip (0 admits)
- [lemma_roundtrip] — codec-level encode→decode roundtrip (0 admits)
- [lemma_octet_range] — each octet is in 0-255
- RFC test vectors with list-level decode (0 admits)
*)

module Network.IPv4

open Data.Codec
open Data.BaseN
open FStar.Seq
open FStar.List.Tot
module U8 = FStar.UInt8
open Network.IP

(** Types *)

(** IPv4 address: four octets in network byte order (RFC 791 §3.1). *)
type ipv4 = {
  octet0 : byte;
  octet1 : byte;
  octet2 : byte;
  octet3 : byte;
}

(** [ipv4_of_octets] constructs an [ipv4] from four octets.
    @param octet0 First octet.  @param octet1 Second octet.
    @param octet2 Third octet.  @param octet3 Fourth octet.
    @returns An [ipv4] record with the given octet values. *)
let ipv4_of_octets (octet0 octet1 octet2 octet3: byte) : ipv4 =
  {octet0; octet1; octet2; octet3}

(** Digit helper *)

(** [lemma_digits_encode_length] proves [digits_encode n] has at most 3 digits
    for any [n <= 255].  Required by the [wfcv] guard.
    @param n A natural number ≤ 255.
    @returns Unit lemma.  Adds [length (digits_encode n) <= 3] to SMT context. *)
let lemma_digits_encode_length (n: nat) : Lemma
  (requires n <= 255)
  (ensures List.Tot.length (digits_encode n) <= 3)
  = if n < 10 then () else if n < 100 then () else ()

(** Dot separator byte (ASCII '.' = 0x2E). *)
let ipv4_sep : byte = 0x2Euy

(** Lemma: [ipv4_sep] equals the literal [0x2Euy].  Connects the named
    constant with the concrete literal for SMT transparency and serves
    as an integration-test anchor.
    @returns Lemma — [ipv4_sep == 0x2Euy]. *)
let lemma_ipv4_sep_value () : Lemma (ipv4_sep == 0x2Euy) = ()

(** List-level encode/decode *)

(** The list-level functions use explicit [digits_encode] /
    [digits_to_int_decode_go] — no codec combinators.  Roundtrip
    is proven by direct structural decomposition (fstar-proofs §14).
*)

(** [encode_ipv4_list] serializes an [ipv4] to a byte list in dotted-decimal
    format.
    @param v IPv4 address to encode.
    @returns Byte list of ASCII digits and dots. *)
let encode_ipv4_list (v: ipv4) : list byte =
  digits_encode (U8.v v.octet0) @ [ipv4_sep] @
  digits_encode (U8.v v.octet1) @ [ipv4_sep] @
  digits_encode (U8.v v.octet2) @ [ipv4_sep] @
  digits_encode (U8.v v.octet3)

(** [decode_octet_list] parses 1-3 decimal digits from a byte list into a byte.
    Uses [digits_to_int_decode_go] directly — no codec combinators.

    The [0 <= n && n <= 255] range check is redundant with the
    [digits_to_int_decode_go] predicate; it exists as a safety double-check.
    @param ds Byte list to parse.
    @returns [Some (byte, n)] where [n <= 3] bytes consumed, [None] on error. *)
let decode_octet_list (ds: list byte) : option (byte & n:nat{n <= 3}) =
  let s = seq_of_list ds in
  match digits_to_int_decode_go (fun v -> 0 <= v && v <= 255) s 3 0 0 with
  | Inr (n, consumed) ->
    if 0 <= n && n <= 255 then Some (U8.uint_to_t n, consumed)
    else None
  | Inl _ -> None

(** [decode_ipv4_list] parses dotted-decimal bytes into an [ipv4].
    Explicit [if None?] / [Some?.v] style — SMT can follow this structure.
    @param bs Byte list to decode.
    @returns [Some (ipv4, total_bytes)] on success, [None] on error.
             [total_bytes] is non-negative (consumed count). *)
let decode_ipv4_list (bs: list byte) : option (ipv4 & nat) =
  let step0 = decode_octet_list bs in
  if None? step0 then None
  else
    let (o0, n0) = Some?.v step0 in
    let after0 = drop n0 bs in
    if length after0 = 0 || hd after0 <> ipv4_sep then None
    else
      let after_dot0 = drop 1 after0 in
      let step1 = decode_octet_list after_dot0 in
      if None? step1 then None
      else
        let (o1, n1) = Some?.v step1 in
        let after1 = drop n1 after_dot0 in
        if length after1 = 0 || hd after1 <> ipv4_sep then None
        else
          let after_dot1 = drop 1 after1 in
          let step2 = decode_octet_list after_dot1 in
          if None? step2 then None
          else
            let (o2, n2) = Some?.v step2 in
            let after2 = drop n2 after_dot1 in
            if length after2 = 0 || hd after2 <> ipv4_sep then None
            else
              let after_dot2 = drop 1 after2 in
              let step3 = decode_octet_list after_dot2 in
              if None? step3 then None
              else
                let (o3, n3) = Some?.v step3 in
                Some ({octet0=o0;octet1=o1;octet2=o2;octet3=o3}, n0+1+n1+1+n2+1+n3)

(** Octet roundtrip lemmas *)

(** Note: [lemma_octet_roundtrip_empty] and [lemma_octet_roundtrip_dot]
    use [lemma_acc_digits_encode_helper] and [lemma_digits_encode_all_digits_helper]
    from [Data.Codec.Types] to expose digit-encoding properties to SMT.
    These are not just documentation — without them, SMT cannot
    see that [digits_encode] output consists of all-digit bytes. *)

(** Single octet roundtrip with no suffix (last octet in the address).
    @param b A byte value.
    @returns Lemma — [decode_octet_list (digits_encode (U8.v b)) == Some (b, |digits_encode|)]. *)
#push-options "--z3rlimit 400"
let lemma_octet_roundtrip_empty (b: byte) : Lemma
  (ensures decode_octet_list (digits_encode (U8.v b))
        == Some (b, length (digits_encode (U8.v b))))
  = let n = U8.v b in
    lemma_acc_digits_encode_helper n;
    lemma_digits_encode_all_digits_helper n;
    lemma_digits_encode_length n;
    lemma_digits_decode_encode_roundtrip (fun v -> 0 <= v && v <= 255) 3 n FStar.Seq.empty;
    lemma_seq_of_list_length (digits_encode n)
#pop-options

(** Single octet roundtrip with suffix starting with dot (0x2E).
    The suffix starts with the dot separator, which is not a digit,
    so [digits_to_int_decode_go] stops parsing at the correct boundary.
    @param b A byte value.  @param suffix Byte list starting with [ipv4_sep].
    @returns Lemma — [decode_octet_list (digits_encode (U8.v b) @ suffix) == Some (b, |digits_encode|)]. *)
#push-options "--z3rlimit 400"
let lemma_octet_roundtrip_dot (b: byte) (suffix: list byte) : Lemma
  (requires Cons? suffix /\ hd suffix == ipv4_sep)
  (ensures decode_octet_list (digits_encode (U8.v b) @ suffix)
        == Some (b, length (digits_encode (U8.v b))))
  = let n = U8.v b in
    lemma_acc_digits_encode_helper n;
    lemma_digits_encode_all_digits_helper n;
    lemma_digits_encode_length n;
    assert_norm (not (is_digit ipv4_sep));
    let r = seq_of_list suffix in
    assert (FStar.Seq.length r > 0);
    assert (FStar.Seq.index r 0 == ipv4_sep);
    assert (not (is_digit (FStar.Seq.index r 0)));
    lemma_digits_decode_encode_roundtrip (fun v -> 0 <= v && v <= 255) 3 n r;
    lemma_seq_of_list_length (digits_encode n)
#pop-options

(** List-level IPv4 roundtrip *)

(** RFC 791 §3.1 ¶1 roundtrip: for all [v: ipv4],
    [decode_ipv4_list (encode_ipv4_list v) == Some (v, |enc_v|)].
    Proven by direct structural decomposition — four octet roundtrips
    chained through explicit [drop] / [hd] assertions.  0 admits.
    @param v An ipv4 value. *)
#push-options "--z3rlimit 400"
let lemma_ipv4_list_roundtrip (v: ipv4) : Lemma
  (decode_ipv4_list (encode_ipv4_list v) == Some (v, length (encode_ipv4_list v)))
  = let d0 = digits_encode (U8.v v.octet0) in
    let d1 = digits_encode (U8.v v.octet1) in
    let d2 = digits_encode (U8.v v.octet2) in
    let d3 = digits_encode (U8.v v.octet3) in
    let enc = d0 @ [ipv4_sep] @ d1 @ [ipv4_sep] @ d2 @ [ipv4_sep] @ d3 in

    (* Octet 0 + dot *)
    lemma_octet_roundtrip_dot v.octet0 ([ipv4_sep] @ d1 @ [ipv4_sep] @ d2 @ [ipv4_sep] @ d3);
    lemma_drop_append_length d0 ([ipv4_sep] @ d1 @ [ipv4_sep] @ d2 @ [ipv4_sep] @ d3);
    assert (decode_octet_list enc == Some (v.octet0, length d0));
    assert (drop (length d0) enc == [ipv4_sep] @ d1 @ [ipv4_sep] @ d2 @ [ipv4_sep] @ d3);
    assert (hd (drop (length d0) enc) == ipv4_sep);
    assert (drop 1 (drop (length d0) enc) == d1 @ [ipv4_sep] @ d2 @ [ipv4_sep] @ d3);

    (* Octet 1 + dot *)
    lemma_octet_roundtrip_dot v.octet1 ([ipv4_sep] @ d2 @ [ipv4_sep] @ d3);
    lemma_drop_append_length d1 ([ipv4_sep] @ d2 @ [ipv4_sep] @ d3);
    assert (decode_octet_list (d1 @ [ipv4_sep] @ d2 @ [ipv4_sep] @ d3) == Some (v.octet1, length d1));
    assert (drop (length d1) (d1 @ [ipv4_sep] @ d2 @ [ipv4_sep] @ d3) == [ipv4_sep] @ d2 @ [ipv4_sep] @ d3);
    assert (hd ([ipv4_sep] @ d2 @ [ipv4_sep] @ d3) == ipv4_sep);
    assert (drop 1 ([ipv4_sep] @ d2 @ [ipv4_sep] @ d3) == d2 @ [ipv4_sep] @ d3);

    (* Octet 2 + dot *)
    lemma_octet_roundtrip_dot v.octet2 ([ipv4_sep] @ d3);
    lemma_drop_append_length d2 ([ipv4_sep] @ d3);
    assert (decode_octet_list (d2 @ [ipv4_sep] @ d3) == Some (v.octet2, length d2));
    assert (drop (length d2) (d2 @ [ipv4_sep] @ d3) == [ipv4_sep] @ d3);
    assert (hd ([ipv4_sep] @ d3) == ipv4_sep);
    assert (drop 1 ([ipv4_sep] @ d3) == d3);

    (* Octet 3 (last) *)
    lemma_octet_roundtrip_empty v.octet3;
    lemma_drop_append_length d3 [];
    assert (decode_octet_list d3 == Some (v.octet3, length d3));
    assert (drop (length d3) d3 == []);

    ()
#pop-options

(** Codec-level functions *)

(** Well-formed-value guard: always true for [ipv4] — every field is
    [UInt8.t] which guarantees [v ∈ 0..255] by type definition.
    Exists for RFC 791 §3.1 ¶2 traceability — each octet SHALL be 0-255.
    @param v IPv4 address value.
    @returns [true] when all octets are ≤ 255 (always true by type). *)
let wfcv_ipv4 (v: ipv4) : bool =
  U8.v v.octet0 <= 255 &&
  U8.v v.octet1 <= 255 &&
  U8.v v.octet2 <= 255 &&
  U8.v v.octet3 <= 255

(** Well-formed-value property: always True (refinement type guarantees range).
    @param v IPv4 address value.
    @returns True — octet range enforced by [ipv4] refinement type. *)
let wfcv_prop_ipv4 (v: ipv4) : prop = True

(** Rest condition: suffix must be empty.
    The [digits_to_int]-based octet decoder is digit-greedy — it consumes
    all consecutive digits.  Only the empty suffix is safe: a non-empty
    suffix starting with a digit would be incorrectly consumed as part
    of the last octet, and proving the general non-digit case requires
    structural extension of the list roundtrip proof.

    For roundtrip ([r = Seq.empty]), this holds trivially.
    If composition with non-digit-delimited suffixes is needed, extend
    the rest_cond and roundtrip lemma accordingly.
    @param v IPv4 address value.
    @param r Suffix byte sequence — must be [Seq.empty] for roundtrip.
    @returns [r == Seq.empty] — no trailing data allowed. *)
let rest_cond_ipv4 (v: ipv4) (r: byte_seq) : prop =
  r == Seq.empty

(** Encoder: [ipv4 → byte_seq].
    Delegates to the list-level encoder.
    @param v IPv4 address to encode.
    @returns Byte sequence of encoded dotted-decimal format. *)
let ipv4_enc (v: ipv4) : byte_seq =
  seq_of_list (encode_ipv4_list v)

(** Decoder: [byte_seq → decode_result ipv4].
    Delegates to the list-level decoder.
    @param s Byte sequence to decode.
    @returns [Inr (v, n)] on success, [Inl err] on failure. *)
let ipv4_dec (s: byte_seq) : decode_result ipv4 =
  match decode_ipv4_list (Seq.seq_to_list s) with
  | Some (v, n) -> Inr (v, n)
  | None -> Inl (mk_decode_error ExpectedPredicate 0)

(** Decoder error position bound.
    Body is [()] because [mk_decode_error ExpectedPredicate 0]
    always produces [err_pos = 0], and [0 <= Seq.length s] holds
    for all [s].  @param s Input byte sequence.
    @returns Lemma — error position ≤ sequence length. *)
let lemma_ipv4_dec_err_bound (s: byte_seq) : Lemma
  (ensures (match ipv4_dec s with
            | Inl err -> err.err_pos <= Seq.length s
            | _ -> True))
  = ()

(** Lemma: [decode_octet_list] consumed <= input length.
    Follows from the seq decoder bound [lemma_digits_decode_go_len_bound]
    in [Data.Codec.Types].
    @param ds Input byte list.
    @returns Lemma — consumed bytes ≤ input length when decode succeeds. *)
let lemma_decode_octet_list_consumed (ds: list byte) : Lemma
  (ensures (match decode_octet_list ds with
            | Some (_, n) -> n <= List.Tot.length ds
            | None -> True))
  = let s = seq_of_list ds in
    lemma_seq_of_list_length ds;
    lemma_digits_decode_go_len_bound (fun v -> 0 <= v && v <= 255) s 3 0 0;
    ()

(** Lemma: [decode_ipv4_list] consumed is bounded by input length.
    Proves the telescoping bound: each octet at index [i] consumes
    [ni] bytes (ni ≤ 3), and 7 separator bytes are consumed.
    The exact bound is [n0+1+n1+1+n2+1+n3 <= |bs|].
    @param bs Input byte list.
    @returns Lemma — consumed bytes ≤ input length when decode succeeds. *)
let lemma_decode_ipv4_list_consumed (bs: list byte) : Lemma
  (ensures (match decode_ipv4_list bs with
            | Some (_, consumed) -> consumed <= List.Tot.length bs
            | None -> True))
  =
  let step0 = decode_octet_list bs in
  match step0 with
  | None -> ()
  | Some (_, n0) ->
    lemma_decode_octet_list_consumed bs;
    let after0 = drop n0 bs in
    if length after0 = 0 || hd after0 <> ipv4_sep then ()
    else begin
      lemma_drop_length_exact n0 bs;
      lemma_drop_length_bound n0 bs;
      let after_dot0 = drop 1 after0 in
      lemma_drop_length_exact 1 after0;
      let step1 = decode_octet_list after_dot0 in
      match step1 with
      | None -> ()
      | Some (_, n1) ->
        lemma_decode_octet_list_consumed after_dot0;
        let after1 = drop n1 after_dot0 in
        if length after1 = 0 || hd after1 <> ipv4_sep then ()
        else begin
          lemma_drop_length_exact n1 after_dot0;
          let after_dot1 = drop 1 after1 in
          lemma_drop_length_exact 1 after1;
          let step2 = decode_octet_list after_dot1 in
          match step2 with
          | None -> ()
          | Some (_, n2) ->
            lemma_decode_octet_list_consumed after_dot1;
            let after2 = drop n2 after_dot1 in
            if length after2 = 0 || hd after2 <> ipv4_sep then ()
            else begin
              lemma_drop_length_exact n2 after_dot1;
              let after_dot2 = drop 1 after2 in
              lemma_drop_length_exact 1 after2;
              let step3 = decode_octet_list after_dot2 in
              match step3 with
              | None -> ()
              | Some (_, n3) ->
                lemma_decode_octet_list_consumed after_dot2;
                assert (n0 + 1 + n1 + 1 + n2 + 1 + n3 <= List.Tot.length bs);
                ()
            end
        end
    end

(** Decoder consumed bound.  Uses [lemma_decode_ipv4_list_consumed].
    @param s Input byte sequence.
    @returns Lemma — consumed bytes ≤ sequence length when decode succeeds. *)
let lemma_ipv4_dec_consumed_bound (s: byte_seq) : Lemma
  (ensures (match ipv4_dec s with
            | Inr (_, n) -> n <= Seq.length s
            | _ -> True))
  = lemma_seq_list_bij s;
    lemma_decode_ipv4_list_consumed (Seq.seq_to_list s);
    ()

(** Roundtrip lemma: encode→decode returns the original value.
    Bridges the list-level proof to byte_seq.  Only handles the
    empty suffix case ([r = Seq.empty]) because the digit-greedy
    decoder requires the suffix to be empty.
    @param v IPv4 address.  @param r Must be [Seq.empty].
    @returns Lemma — [ipv4_dec (ipv4_enc v) == Inr (v, |ipv4_enc v|)]. *)
#push-options "--z3rlimit 200"
let lemma_ipv4_roundtrip (v: ipv4) (r: byte_seq) : Lemma
  (requires wfcv_ipv4 v /\ wfcv_prop_ipv4 v /\ rest_cond_ipv4 v r)
  (ensures ipv4_dec (ipv4_enc v `Seq.append` r)
        == Inr (v, Seq.length (ipv4_enc v)))
  = assert (r == Seq.empty);
    let enc_list = encode_ipv4_list v in
    lemma_ipv4_list_roundtrip v;
    lemma_seq_list_bij_rev enc_list;
    lemma_seq_of_list_length enc_list;
    let enc_seq = seq_of_list enc_list in
    assert (Seq.length enc_seq == List.Tot.length enc_list);
    assert (Seq.seq_to_list enc_seq == enc_list);
    assert (decode_ipv4_list (Seq.seq_to_list enc_seq) == Some (v, List.Tot.length enc_list));
    assert (ipv4_dec enc_seq == Inr (v, List.Tot.length enc_list));
    assert (Seq.length (ipv4_enc v) == List.Tot.length enc_list);
    Seq.lemma_eq_intro (enc_seq `Seq.append` Seq.empty) enc_seq
#pop-options

(** The IPv4 codec: flat [custom] combinator, no [product]/[map_] chain.
    Roundtrip proof bridges the list-level structural induction.
    Zero admits.
    @returns [codec ipv4] for dotted-decimal text format. *)
#push-options "--z3rlimit 400"
let ipv4_codec : codec ipv4 =
  custom
    ipv4_dec
    ipv4_enc
    wfcv_ipv4
    wfcv_prop_ipv4
    rest_cond_ipv4
    lemma_ipv4_roundtrip
    lemma_ipv4_dec_err_bound
    lemma_ipv4_dec_consumed_bound
#pop-options

(** Public API *)

(** [encode_ipv4] serializes an [ipv4] to dotted-decimal bytes.
    @param ip Address to encode.
    @returns Byte sequence of encoded dotted-decimal format. *)
let encode_ipv4 (ip: ipv4) : byte_seq = ipv4_codec.enc ip

(** [decode_ipv4] parses dotted-decimal bytes into an [ipv4].
    @param input Byte sequence to decode.
    @returns [Some ip] on success, [None] on error. *)
let decode_ipv4 (input: byte_seq) : Tot (option ipv4) =
  match ipv4_codec.dec input with Inl _ -> None | Inr (v, _) -> Some v

(** Roundtrip wrapper: [decode_ipv4 (encode_ipv4 v) == Some v].
    @param v An ipv4 value.
    @returns Lemma — [decode_ipv4 (encode_ipv4 v) == Some v]. *)
let lemma_encode_ipv4_roundtrip (v: ipv4) : Lemma
  (ensures decode_ipv4 (encode_ipv4 v `FStar.Seq.append` FStar.Seq.empty) == Some v)
  = lemma_ipv4_roundtrip v Seq.empty

(** Codec-level roundtrip (backward compat alias).
    @param v An ipv4 value.
    @returns Lemma — [ipv4_codec.dec (ipv4_codec.enc v ++ empty) == Inr (v, |enc|)]. *)
let lemma_roundtrip (v: ipv4) : Lemma
  (ensures ipv4_codec.dec (ipv4_codec.enc v `FStar.Seq.append` FStar.Seq.empty)
        == Inr (v, FStar.Seq.length (ipv4_codec.enc v)))
  = lemma_ipv4_roundtrip v Seq.empty

(** RFC compliance *)

(** RFC 791 §3.1 ¶2: Each octet SHALL be in the range 0-255.
    Proves: for all [b: byte], [U8.v b ∈ [0, 255]].
    Follows from [FStar.UInt8]'s type definition — [UInt8.t] is an
    unsigned 8-bit integer.  Exists for RFC traceability.
    @param b Any byte value.
    @returns Lemma — [U8.v b >= 0 /\ U8.v b <= 255]. *)
let lemma_octet_range (b: byte) : Lemma
  (ensures U8.v b >= 0 /\ U8.v b <= 255)
  = ()

(** RFC test vectors *)

(** Test vectors use list-level decode — the [assert_norm]-computed
    encoding combined with [lemma_ipv4_list_roundtrip] proves the
    decode result.  Zero admits.

    Vectors span the valid octet range (0, 127, 192, 255) and
    cover:
    - Loopback (RFC 1122 §3.2.1.3)
    - Private network (RFC 1918)
    - Unspecified (RFC 1122 §3.2.1.3)
    - Limited broadcast (RFC 919)
*)

(** Loopback: 127.0.0.1 (RFC 1122 §3.2.1.3).
    @returns Lemma — roundtrip for [127.0.0.1]. *)
let lemma_ipv4_localhost_concrete () : Lemma
  (ensures (let v = {octet0=127uy;octet1=0uy;octet2=0uy;octet3=1uy} in
            match decode_ipv4_list (encode_ipv4_list v) with
            | Some (ip, _) -> ip.octet0 = 127uy /\ ip.octet1 = 0uy
                           /\ ip.octet2 = 0uy /\ ip.octet3 = 1uy
            | _ -> False))
  = lemma_ipv4_list_roundtrip ({octet0=127uy;octet1=0uy;octet2=0uy;octet3=1uy})

(** Private network: 192.168.1.1 (RFC 1918).
    @returns Lemma — roundtrip for [192.168.1.1]. *)
let lemma_ipv4_private_concrete () : Lemma
  (ensures (let v = {octet0=192uy;octet1=168uy;octet2=1uy;octet3=1uy} in
            match decode_ipv4_list (encode_ipv4_list v) with
            | Some (ip, _) -> ip.octet0 = 192uy /\ ip.octet1 = 168uy
                           /\ ip.octet2 = 1uy /\ ip.octet3 = 1uy
            | _ -> False))
  = lemma_ipv4_list_roundtrip ({octet0=192uy;octet1=168uy;octet2=1uy;octet3=1uy})

(** Unspecified: 0.0.0.0 (RFC 1122 §3.2.1.3).
    @returns Lemma — roundtrip for [0.0.0.0]. *)
let lemma_ipv4_zero_concrete () : Lemma
  (ensures (let v = {octet0=0uy;octet1=0uy;octet2=0uy;octet3=0uy} in
            match decode_ipv4_list (encode_ipv4_list v) with
            | Some (ip, _) -> ip.octet0 = 0uy /\ ip.octet1 = 0uy
                           /\ ip.octet2 = 0uy /\ ip.octet3 = 0uy
            | _ -> False))
  = lemma_ipv4_list_roundtrip ({octet0=0uy;octet1=0uy;octet2=0uy;octet3=0uy})

(** Limited broadcast: 255.255.255.255 (RFC 919).
    @returns Lemma — roundtrip for [255.255.255.255]. *)
let lemma_ipv4_max_concrete () : Lemma
  (ensures (let v = {octet0=255uy;octet1=255uy;octet2=255uy;octet3=255uy} in
            match decode_ipv4_list (encode_ipv4_list v) with
            | Some (ip, _) -> ip.octet0 = 255uy /\ ip.octet1 = 255uy
                           /\ ip.octet2 = 255uy /\ ip.octet3 = 255uy
            | _ -> False))
  = lemma_ipv4_list_roundtrip ({octet0=255uy;octet1=255uy;octet2=255uy;octet3=255uy})
