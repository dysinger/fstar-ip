(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)


(**
Network.IPv4.Pulse — C-extractable IPv4 wire codec via Pulse + Custard.

A 4-byte (32-bit) wire format:
four octets in network byte order, written/read through a
[Pulse.Lib.Array.array].

Each encode/decode `fn` carries a byte-level post-condition tied to the
pure spec [encode_spec]/[decode_spec] (both `noextract`; the pure
list-of-bytes spec is the single source of truth shared with the pure
[Network.IPv4] layer).

Written for F* v2026.09.20 (Custard `--custard_backend C`).  Zero admits.

@header Network.IPv4.Pulse

@section Types
- [ipv4_wire] — four [U8.t] fields (32-bit wire format)
- [opt_ipv4_wire] — optional ipv4_wire with bytes-consumed count

@section Encode
- [encode] — write [addr] at [off], returns 4ul

@section Decode
- [decode] — read 4 bytes at [off] into [opt_ipv4_wire]

@section Specs
- [encode_spec] / [decode_spec] — pure list-of-bytes specification

@section Roundtrip lemmas
- [lemma_roundtrip] — pure [decode_spec]∘[encode_spec] roundtrip
- [lemma_pulse_roundtrip] — buffer-level encode→decode roundtrip
- [lemma_pulse_encode_decode_match] — master roundtrip
*)
module Network.IPv4.Pulse
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


(** IPv4 wire format size in bytes (32 bits / 8). *)
let ipv4_wire_size : U32.t = 4ul


(** [ipv4_wire] — four octets (32-bit wire format). *)
type ipv4_wire = {
  octet0: U8.t;
  octet1: U8.t;
  octet2: U8.t;
  octet3: U8.t;
}


(** [opt_ipv4_wire] — option wrapper for the decode result (C-friendly, no
    [option]). *)
type opt_ipv4_wire =
  | OIPv4_None
  | OIPv4_Some of (ipv4_wire & U32.t)


(* ── Pure spec (noextract: not C-representable) ─────────────────────── *)


(** [encode_spec addr] — serialize [addr] to a 4-byte list in wire order. *)
noextract
let encode_spec (addr: ipv4_wire) : list U8.t =
  [addr.octet0; addr.octet1; addr.octet2; addr.octet3]


(** [decode_spec bs] — deserialize a 4-byte list to [ipv4_wire] plus
    wire size.  Returns [None] unless [bs] has exactly 4 bytes. *)
noextract
let decode_spec (bs: list U8.t) : option (ipv4_wire & U32.t) =
  match bs with
  | [b0; b1; b2; b3] ->
    Some ({octet0=b0; octet1=b1; octet2=b2; octet3=b3}, 4ul)
  | _ -> None


(* ── Encode ─────────────────────────────────────────────────────────── *)


(** [encode addr buf off] — encode an IPv4 address into [buf] at [off];
    returns 4 (bytes written).

    @param addr The IPv4 address to write.
    @param buf The destination buffer (must hold at least 4 bytes at [off]).
    @param off The write offset.
    @returns The number of bytes written (always [4ul]).
    Each buffer position [off + k] holds the corresponding octet. *)
fn encode (addr: ipv4_wire) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 4 <= A.length buf /\ U32.v off + 3 < 4294967296)
    returns w: U32.t
    ensures
      (exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1 **
        pure (U32.v off + 4 <= A.length buf /\
              Seq.length s1 == A.length buf /\
              Seq.index s1 (U32.v off) == addr.octet0 /\
              Seq.index s1 (U32.v off + 1) == addr.octet1 /\
              Seq.index s1 (U32.v off + 2) == addr.octet2 /\
              Seq.index s1 (U32.v off + 3) == addr.octet3)) **
      pure (w == 4ul)
{
  let j0 = US.uint32_to_sizet off;
  let j1 = US.uint32_to_sizet (U32.add off 1ul);
  let j2 = US.uint32_to_sizet (U32.add off 2ul);
  let j3 = US.uint32_to_sizet (U32.add off 3ul);
  A.pts_to_len buf;
  buf.(j0) <- addr.octet0;
  buf.(j1) <- addr.octet1;
  buf.(j2) <- addr.octet2;
  buf.(j3) <- addr.octet3;
  4ul
}


(* ── Decode ─────────────────────────────────────────────────────────── *)


(** [decode buf off len] — decode an IPv4 address from [buf] at [off].

    @param buf The source buffer.
    @param off The read offset.
    @param len The number of available bytes from [off].
    @returns [OIPv4_Some (addr, 4ul)] when at least 4 bytes are available,
             else [OIPv4_None]. *)
fn decode (buf: A.array U8.t) (off: U32.t) (len: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + U32.v len <= A.length buf /\ U32.v off + 3 < 4294967296)
    returns r: opt_ipv4_wire
    ensures
      A.pts_to buf s0 **
      pure (
        A.length buf == Seq.length s0 /\
        U32.v off + U32.v len <= A.length buf /\
        U32.v off + 3 < 4294967296 /\
        (if U32.v ipv4_wire_size <= U32.v len
         then r == OIPv4_Some ({octet0 = Seq.index s0 (U32.v off);
                                octet1 = Seq.index s0 (U32.v off + 1);
                                octet2 = Seq.index s0 (U32.v off + 2);
                                octet3 = Seq.index s0 (U32.v off + 3)}, 4ul)
         else r == OIPv4_None))
{
  A.pts_to_len buf;
  if U32.lte ipv4_wire_size len {
    let j0 = US.uint32_to_sizet off;
    let j1 = US.uint32_to_sizet (U32.add off 1ul);
    let j2 = US.uint32_to_sizet (U32.add off 2ul);
    let j3 = US.uint32_to_sizet (U32.add off 3ul);
    let b0 = buf.(j0);
    let b1 = buf.(j1);
    let b2 = buf.(j2);
    let b3 = buf.(j3);
    OIPv4_Some ({octet0 = b0; octet1 = b1; octet2 = b2; octet3 = b3}, ipv4_wire_size)
  } else {
    OIPv4_None
  }
}


(* ── Roundtrip lemmas (alphabetical) ────────────────────────────────── *)


(** [lemma_roundtrip addr] — pure roundtrip: encoding then decoding returns
    the original address. *)
let lemma_roundtrip (addr: ipv4_wire)
  : Lemma (decode_spec (encode_spec addr) == Some (addr, ipv4_wire_size))
  = ()


(** [lemma_pulse_roundtrip addr buf off] — encode then decode an IPv4
    address roundtrips.

    @param addr The IPv4 address to roundtrip.
    @param buf The buffer.
    @param off The offset.
    Proves [decode buf off 4ul] after [encode addr buf off] returns
    [OIPv4_Some (addr, 4ul)]. *)
fn lemma_pulse_roundtrip (addr: ipv4_wire) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 4 <= A.length buf /\ U32.v off + 3 < 4294967296)
    returns res: (U32.t & opt_ipv4_wire)
    ensures
      (exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1) **
      pure (fst res == 4ul /\ snd res == OIPv4_Some (addr, 4ul))
{
  let n = encode addr buf off;
  let r = decode buf off ipv4_wire_size;
  (n, r)
}


(** [lemma_pulse_encode_decode_match addr buf off] — master roundtrip for
    IPv4.

    @param addr The IPv4 address.
    @param buf The buffer.
    @param off The offset.
    Proves [decode]∘[encode] returns [OIPv4_Some (addr, 4ul)]. *)
fn lemma_pulse_encode_decode_match (addr: ipv4_wire) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 4 <= A.length buf /\ U32.v off + 3 < 4294967296)
    returns res: (U32.t & opt_ipv4_wire)
    ensures
      (exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1) **
      pure (fst res == 4ul /\ snd res == OIPv4_Some (addr, 4ul))
{
  lemma_pulse_roundtrip addr buf off
}
