(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)


(**
Network.IPv6.Pulse — C-extractable IPv6 wire codec via Pulse + Custard.

A 16-byte (128-bit) wire format:
sixteen octets in network byte order, written/read through a
[Pulse.Lib.Array.array].

This module handles the 128-bit binary wire format, NOT the colon-hex
text representation (the text codec is in [Network.IPv6]).

Each encode/decode `fn` carries a byte-level post-condition tied to the
pure spec [encode_spec]/[decode_spec] (both `noextract`).  Buffer writes
are lossless in Pulse, so individual index post-conditions per byte prove
cleanly here; the earlier 16-write SMT-scaling concern collapses to a direct
Pulse [Seq.index] correspondence.

Written for F* v2026.09.20 (Custard `--custard_backend C`).  Zero admits.

@header Network.IPv6.Pulse

@section Types
- [ipv6_wire] — sixteen [U8.t] fields (128-bit wire format)
- [opt_ipv6_wire] — optional ipv6_wire with bytes-consumed count

@section Encode
- [encode] — write [addr] at [off], returns 16ul

@section Decode
- [decode] — read 16 bytes at [off] into [opt_ipv6_wire]

@section Specs
- [encode_spec] / [decode_spec] — pure list-of-bytes specification

@section Roundtrip lemmas
- [lemma_roundtrip] — pure [decode_spec]∘[encode_spec] roundtrip
- [lemma_pulse_roundtrip] — buffer-level encode→decode roundtrip
- [lemma_pulse_encode_decode_match] — master roundtrip
*)
module Network.IPv6.Pulse
#lang-pulse


open Pulse
open Pulse.Lib.Reference
module A = Pulse.Lib.Array
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Seq = FStar.Seq


open FStar.Seq


(* ── Types (alphabetical) ──────────────────────────────────────────── *)


(** IPv6 wire format size in bytes (128 bits / 8). *)
let ipv6_wire_size : U32.t = 16ul


(** [ipv6_wire] — sixteen octets (128-bit wire format). *)
type ipv6_wire = {
  octet0: U8.t; octet1: U8.t; octet2: U8.t; octet3: U8.t;
  octet4: U8.t; octet5: U8.t; octet6: U8.t; octet7: U8.t;
  octet8: U8.t; octet9: U8.t; octet10: U8.t; octet11: U8.t;
  octet12: U8.t; octet13: U8.t; octet14: U8.t; octet15: U8.t;
}


(** [opt_ipv6_wire] — option wrapper for the decode result (C-friendly, no
    [option]). *)
type opt_ipv6_wire =
  | OIPv6_None
  | OIPv6_Some of (ipv6_wire & U32.t)


(* ── Pure spec (noextract: not C-representable) ─────────────────────── *)


(** [encode_spec addr] — serialize [addr] to a 16-byte list in wire order. *)
noextract
let encode_spec (addr: ipv6_wire) : list U8.t =
  [addr.octet0; addr.octet1; addr.octet2; addr.octet3;
   addr.octet4; addr.octet5; addr.octet6; addr.octet7;
   addr.octet8; addr.octet9; addr.octet10; addr.octet11;
   addr.octet12; addr.octet13; addr.octet14; addr.octet15]


(** [decode_spec bs] — deserialize a 16-byte list to [ipv6_wire] plus
    wire size.  Returns [None] unless [bs] has exactly 16 bytes. *)
noextract
let decode_spec (bs: list U8.t) : option (ipv6_wire & U32.t) =
  match bs with
  | [b0;b1;b2;b3; b4;b5;b6;b7; b8;b9;b10;b11; b12;b13;b14;b15] ->
    Some ({octet0=b0;octet1=b1;octet2=b2;octet3=b3;
           octet4=b4;octet5=b5;octet6=b6;octet7=b7;
           octet8=b8;octet9=b9;octet10=b10;octet11=b11;
           octet12=b12;octet13=b13;octet14=b14;octet15=b15}, ipv6_wire_size)
  | _ -> None


(* ── Encode ─────────────────────────────────────────────────────────── *)


(** [encode addr buf off] — encode an IPv6 address into [buf] at [off];
    returns 16 (bytes written).

    @param addr The IPv6 address to write.
    @param buf The destination buffer (must hold at least 16 bytes at [off]).
    @param off The write offset.
    @returns The number of bytes written (always [16ul]).
    Each buffer position [off + k] holds the corresponding octet. *)
fn encode (addr: ipv6_wire) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 16 <= A.length buf /\ U32.v off + 15 < 4294967296)
    returns w: U32.t
    ensures
      (exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1 **
        pure (U32.v off + 16 <= A.length buf /\
              Seq.length s1 == A.length buf /\
              Seq.index s1 (U32.v off) == addr.octet0 /\
              Seq.index s1 (U32.v off + 1) == addr.octet1 /\
              Seq.index s1 (U32.v off + 2) == addr.octet2 /\
              Seq.index s1 (U32.v off + 3) == addr.octet3 /\
              Seq.index s1 (U32.v off + 4) == addr.octet4 /\
              Seq.index s1 (U32.v off + 5) == addr.octet5 /\
              Seq.index s1 (U32.v off + 6) == addr.octet6 /\
              Seq.index s1 (U32.v off + 7) == addr.octet7 /\
              Seq.index s1 (U32.v off + 8) == addr.octet8 /\
              Seq.index s1 (U32.v off + 9) == addr.octet9 /\
              Seq.index s1 (U32.v off + 10) == addr.octet10 /\
              Seq.index s1 (U32.v off + 11) == addr.octet11 /\
              Seq.index s1 (U32.v off + 12) == addr.octet12 /\
              Seq.index s1 (U32.v off + 13) == addr.octet13 /\
              Seq.index s1 (U32.v off + 14) == addr.octet14 /\
              Seq.index s1 (U32.v off + 15) == addr.octet15)) **
      pure (w == 16ul)
{
  let j0 = US.uint32_to_sizet off;
  let j1 = US.uint32_to_sizet (U32.add off 1ul);
  let j2 = US.uint32_to_sizet (U32.add off 2ul);
  let j3 = US.uint32_to_sizet (U32.add off 3ul);
  let j4 = US.uint32_to_sizet (U32.add off 4ul);
  let j5 = US.uint32_to_sizet (U32.add off 5ul);
  let j6 = US.uint32_to_sizet (U32.add off 6ul);
  let j7 = US.uint32_to_sizet (U32.add off 7ul);
  let j8 = US.uint32_to_sizet (U32.add off 8ul);
  let j9 = US.uint32_to_sizet (U32.add off 9ul);
  let j10 = US.uint32_to_sizet (U32.add off 10ul);
  let j11 = US.uint32_to_sizet (U32.add off 11ul);
  let j12 = US.uint32_to_sizet (U32.add off 12ul);
  let j13 = US.uint32_to_sizet (U32.add off 13ul);
  let j14 = US.uint32_to_sizet (U32.add off 14ul);
  let j15 = US.uint32_to_sizet (U32.add off 15ul);
  A.pts_to_len buf;
  buf.(j0) <- addr.octet0;
  buf.(j1) <- addr.octet1;
  buf.(j2) <- addr.octet2;
  buf.(j3) <- addr.octet3;
  buf.(j4) <- addr.octet4;
  buf.(j5) <- addr.octet5;
  buf.(j6) <- addr.octet6;
  buf.(j7) <- addr.octet7;
  buf.(j8) <- addr.octet8;
  buf.(j9) <- addr.octet9;
  buf.(j10) <- addr.octet10;
  buf.(j11) <- addr.octet11;
  buf.(j12) <- addr.octet12;
  buf.(j13) <- addr.octet13;
  buf.(j14) <- addr.octet14;
  buf.(j15) <- addr.octet15;
  16ul
}


(* ── Decode ─────────────────────────────────────────────────────────── *)


(** [decode buf off len] — decode an IPv6 address from [buf] at [off].

    @param buf The source buffer.
    @param off The read offset.
    @param len The number of available bytes from [off].
    @returns [OIPv6_Some (addr, 16ul)] when at least 16 bytes are available,
             else [OIPv6_None]. *)
fn decode (buf: A.array U8.t) (off: U32.t) (len: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + U32.v len <= A.length buf /\ U32.v off + 15 < 4294967296)
    returns r: opt_ipv6_wire
    ensures
      A.pts_to buf s0 **
      pure (
        A.length buf == Seq.length s0 /\
        U32.v off + U32.v len <= A.length buf /\
        U32.v off + 15 < 4294967296 /\
        (if U32.v ipv6_wire_size <= U32.v len
         then r == OIPv6_Some ({octet0 = Seq.index s0 (U32.v off);
                                octet1 = Seq.index s0 (U32.v off + 1);
                                octet2 = Seq.index s0 (U32.v off + 2);
                                octet3 = Seq.index s0 (U32.v off + 3);
                                octet4 = Seq.index s0 (U32.v off + 4);
                                octet5 = Seq.index s0 (U32.v off + 5);
                                octet6 = Seq.index s0 (U32.v off + 6);
                                octet7 = Seq.index s0 (U32.v off + 7);
                                octet8 = Seq.index s0 (U32.v off + 8);
                                octet9 = Seq.index s0 (U32.v off + 9);
                                octet10 = Seq.index s0 (U32.v off + 10);
                                octet11 = Seq.index s0 (U32.v off + 11);
                                octet12 = Seq.index s0 (U32.v off + 12);
                                octet13 = Seq.index s0 (U32.v off + 13);
                                octet14 = Seq.index s0 (U32.v off + 14);
                                octet15 = Seq.index s0 (U32.v off + 15)}, 16ul)
         else r == OIPv6_None))
{
  A.pts_to_len buf;
  if U32.lte ipv6_wire_size len {
    let j0 = US.uint32_to_sizet off;
    let j1 = US.uint32_to_sizet (U32.add off 1ul);
    let j2 = US.uint32_to_sizet (U32.add off 2ul);
    let j3 = US.uint32_to_sizet (U32.add off 3ul);
    let j4 = US.uint32_to_sizet (U32.add off 4ul);
    let j5 = US.uint32_to_sizet (U32.add off 5ul);
    let j6 = US.uint32_to_sizet (U32.add off 6ul);
    let j7 = US.uint32_to_sizet (U32.add off 7ul);
    let j8 = US.uint32_to_sizet (U32.add off 8ul);
    let j9 = US.uint32_to_sizet (U32.add off 9ul);
    let j10 = US.uint32_to_sizet (U32.add off 10ul);
    let j11 = US.uint32_to_sizet (U32.add off 11ul);
    let j12 = US.uint32_to_sizet (U32.add off 12ul);
    let j13 = US.uint32_to_sizet (U32.add off 13ul);
    let j14 = US.uint32_to_sizet (U32.add off 14ul);
    let j15 = US.uint32_to_sizet (U32.add off 15ul);
    let b0 = buf.(j0);
    let b1 = buf.(j1);
    let b2 = buf.(j2);
    let b3 = buf.(j3);
    let b4 = buf.(j4);
    let b5 = buf.(j5);
    let b6 = buf.(j6);
    let b7 = buf.(j7);
    let b8 = buf.(j8);
    let b9 = buf.(j9);
    let b10 = buf.(j10);
    let b11 = buf.(j11);
    let b12 = buf.(j12);
    let b13 = buf.(j13);
    let b14 = buf.(j14);
    let b15 = buf.(j15);
    OIPv6_Some ({octet0=b0;octet1=b1;octet2=b2;octet3=b3;
                 octet4=b4;octet5=b5;octet6=b6;octet7=b7;
                 octet8=b8;octet9=b9;octet10=b10;octet11=b11;
                 octet12=b12;octet13=b13;octet14=b14;octet15=b15}, ipv6_wire_size)
  } else {
    OIPv6_None
  }
}


(* ── Roundtrip lemmas (alphabetical) ────────────────────────────────── *)


(** [lemma_roundtrip addr] — pure roundtrip: encoding then decoding returns
    the original address. *)
let lemma_roundtrip (addr: ipv6_wire)
  : Lemma (decode_spec (encode_spec addr) == Some (addr, ipv6_wire_size))
  = ()


(** [lemma_pulse_roundtrip addr buf off] — encode then decode an IPv6
    address roundtrips.

    @param addr The IPv6 address to roundtrip.
    @param buf The buffer.
    @param off The offset.
    Proves [decode buf off 16ul] after [encode addr buf off] returns
    [OIPv6_Some (addr, 16ul)]. *)
fn lemma_pulse_roundtrip (addr: ipv6_wire) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 16 <= A.length buf /\ U32.v off + 15 < 4294967296)
    returns res: (U32.t & opt_ipv6_wire)
    ensures
      (exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1) **
      pure (fst res == 16ul /\ snd res == OIPv6_Some (addr, 16ul))
{
  let n = encode addr buf off;
  let r = decode buf off ipv6_wire_size;
  (n, r)
}


(** [lemma_pulse_encode_decode_match addr buf off] — master roundtrip for
    IPv6.

    @param addr The IPv6 address.
    @param buf The buffer.
    @param off The offset.
    Proves [decode]∘[encode] returns [OIPv6_Some (addr, 16ul)]. *)
fn lemma_pulse_encode_decode_match (addr: ipv6_wire) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 16 <= A.length buf /\ U32.v off + 15 < 4294967296)
    returns res: (U32.t & opt_ipv6_wire)
    ensures
      (exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1) **
      pure (fst res == 16ul /\ snd res == OIPv6_Some (addr, 16ul))
{
  lemma_pulse_roundtrip addr buf off
}
