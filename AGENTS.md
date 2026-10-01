# fstar-ip — Agent Guide & Handoff

`Network.IP` / `Network.IPv4` / `Network.IPv6` — verified IP address codecs,
extracted from the xeno monorepo (`ip/`) as a standalone repo.  Depends on
`fstar-codec` (`Data.Codec`) AND `fstar-basen` (`Data.BaseN`).  F* source is
0-admit.

## ⛔ MANDATES (binding — read before doing anything)

1. **NEVER run `fstar.exe`, `nix build`, or `make` in the foreground.**  They
   can hang forever.  **Always** run them **detached** and poll the log:

   ```bash
   cd /Users/user/_/fstar-ip
   rm -f /tmp/ip-build.log
   nohup nix build .#checked --print-out-paths --no-link > /tmp/ip-build.log 2>&1 &
   # … poll: tail /tmp/ip-build.log ; ps -p $!
   ```

   A stuck process (0% CPU `stopped`, or 100% CPU spin) is a hang — kill it,
   diagnose, don't wait.  Per-step budgets: fstar verify ≤ 10 min, `nix build`
   ≤ 15 min (but the F\* bootstrap itself takes ~20 min *only on first build*;
   it is now cached).

2. **The F\* overlay in `flake.nix` MUST stay byte-identical to
   `fstar-codec`/`fstar-basen`'s.**  Any comment/whitespace change to the
   `buildPhase`/`installPhase` strings changes the derivation hash and forces a
   full F\* bootstrap.  Do NOT touch those strings.

3. **The dependency pins.**  `flake.nix` consumes `fstar-codec` AND
   `fstar-basen` from the published `github:dysinger/*` repos (pinned to HEAD in
   `flake.lock`).  Both are pinned to the SAME `fstar` commit (`cf84795`,
   `v2026.09.20+lsp`) as fstar-basen, so the F\* bootstrap stays cached.

## ✅ Current state — Pulse port DONE, 4/4 targets GREEN (this session)

The KaRaMeL→Custard port is complete and verified 0-admit.  The old
`src/Network.{IPv4,IPv6}.Low` (KaRaMeL Low\*: `FStar.HyperStack.ST`,
`LowStar.Buffer`, `Stack`) were **deleted** (Low\* stdlib removed in
`v2026.09.20`), replaced by `src/Network.{IPv4,IPv6}.Pulse.fst`
(`#lang-pulse`).

### Build matrix (verified this session, F* `v2026.09.20+lsp`)

| Target | Status | Output |
|---|---|---|
| `checked` | ✅ GREEN 0-admit | 6 modules verified (5 src + 1 test) |
| `native` (C) | ✅ GREEN | `Custard.c`/`Custard.h`/`ip.h`, `libip.{dylib,a}` (C11, no karamel) |
| `ocaml` | ✅ GREEN | findlib `ip-ocaml` |
| `fsharp` (.NET) | ✅ GREEN | `Custard.dll` (.NET 10) |

Target names: `default = native`, `checked`, `ocaml`, `native`, `fsharp`.
`nix fmt` is GREEN.

### The TWO-Pulse-leaf Custard extraction (this session — the hard part)

All three reference repos (`fstar-codec`, `fstar-basen`, `fstar-text`) have
exactly ONE Pulse leaf.  ip has TWO (`Network.IPv4.Pulse` + `Network.IPv6.Pulse`).
Custard's whole-program `--codegen Custard` (a.k.a. `--ext fly_deps`) takes
**exactly one `.fst` input file** — passing both fails with `Error 10: When
using --ext fly_deps, only one file can be provided.`

**Fix (landed):** pass just ONE `.fst` (`src/Network.IPv4.Pulse.fst`) and list
`--custard_entry` roots from BOTH modules.  `fly_deps` resolves
`Network.IPv6.Pulse.encode`/`decode` from the `.checked` cache and pulls the
second module into the program.  The emitted `Custard.{c,h,ml,fs}` carries
module-prefixed symbols (`Network_IPv4_Pulse_*` / `Network_IPv6_Pulse_*`), so
there is no name collision.  `--custard_split` does NOT split the C backend
(it only splits OCaml/karamel), so the single-input + cross-module-entries
trick is the required shape.

### Pulse idiom notes (carried from fstar-codec/fstar-text)

- **Direct `Seq.index` post-conditions, not `Seq.slice == seq_of_list`.**  The
  encode `fn` posts `Seq.index s1 (off+k) == addr.octet_k` directly; the decode
  `fn` posts a reconstruction from `Seq.index s0 (off+k)`.  This makes the
  buffer-level roundtrip prove by simple SMT chaining (both sides reference the
  same `Seq.index` terms) — no slice→index bridge lemma needed.  (The
  KaRaMeL-era `Seq.slice == seq_of_list (encode_spec addr)` + `lemma_slice_index_match`
  approach did NOT survive: `Seq.seq_to_list`/`seq_of_list` don't unfold for SMT.)
- **`U32.add off k` needs `U32.v off + k < 4294967296`** in `requires` for the
  hottest `U32.add off k` (k = 3 for IPv4, 15 for IPv6), matching the codec's
  overflow preconditions.
- **The pure list-based `encode_spec`/`decode_spec`/`lemma_roundtrip` are
  preserved** as `noextract` (the task requires them); the `fn` post-conditions
  use the direct `Seq.index` form instead of them for SMT-provability.

### Roll-forward fixes (landed, 0-admit preserved)

- `src/Network.IPv6.fst`: removed `open FStar.Mul` (deleted in v2026.09.20;
  `*` is natively multiplication) and all `--split_queries always` options
  (`--split_queries` deleted).  `--z3rlimit` values were kept.
- `src/Network.IPv4.fst`: removed all `--split_queries always` options.
- `test/Network.IP.Test.Integration.fst`: `.Low`→`.Pulse` opens + anchors
  (`encode`/`decode`/`encode_spec`/`decode_spec`/`lemma_roundtrip`/
  `lemma_pulse_roundtrip`/`lemma_pulse_encode_decode_match`/`ipv*_wire_size`);
  dropped the retired `lemma_encode_match`/`lemma_decode_match`/
  `lemma_stack_roundtrip`/`lemma_slice_index_match*`/`lemma_16_writes` anchors;
  added copyright header.

## Architecture (post-port)

```
Network.IP               — shared drop/list lemmas (pure leaf)
Network.IPv4             — dotted-decimal codec (RFC 791); opens Data.Codec + Data.BaseN
Network.IPv6             — colon-hex codec (RFC 4291); opens Data.Codec + Data.BaseN
Network.IPv4.Pulse       — C-extractable 32-bit wire codec (Custard)
Network.IPv6.Pulse       — C-extractable 128-bit wire codec (Custard)
```

The Pulse leaves are trivial tag/byte codecs: 4 (IPv4) / 16 (IPv6) byte
writes/reads through `Pulse.Lib.Array.array`, `encode`/`decode`, plus
`lemma_roundtrip` (pure) / `lemma_pulse_roundtrip` /
`lemma_pulse_encode_decode_match`.  No varint or multi-byte arithmetic, so the
word16/word32 SMT-hang complexity from `fstar-codec` does not apply.

## Dependencies (two flake inputs)

- `fstar-codec` — provides `codec-src`/`codec-checked`.  `Data.Codec` /
  `Data.Codec.Types` (`byte`, `digits_to_int_decode_go`).
- `fstar-basen` — provides `basen-src`/`basen-checked`.  `Data.BaseN` /
  `Data.BaseN.Base16` (`is_hex`, `nibble_to_upper_hex`, `hex_char_to_nibble`).

Both are needed for **verification** (IPv4/IPv6 `open` them).  For **OCaml
extraction** of ip's own pure spec, BOTH pure specs are extracted locally
unwrapped (the `ocaml-src` derivation extracts `Data.Codec.Types`+`Data.Codec`
AND `Data.BaseN.Base08/16/32/64`+`Data.BaseN`), because `Network.IPv6.ml`
references `Data_BaseN_Base16.*` and the codec/basen findlib packages wrap their
modules into namespaces, leaving the bare names unbound.

## Build commands

```bash
nix build .#checked    # F* verification gate (0-admit)
nix build .#native     # C11 shared/static lib (default)
nix build .#ocaml      # OCaml findlib package
nix build .#fsharp     # .NET library
nix fmt                 # format nix files (treefmt)
nix develop && make check   # dev loop (no nix)
```

## Reference

- Canonical references: `../fstar-codec` (its `Data.Codec.Pulse`,
  `flake.nix`, `default.nix` are the Custard-era shape), `../fstar-basen` (the
  downstream-dependency shape this repo mirrors), `../fstar-text` (the Pulse
  tag-codec idiom).
- The F\* skill: `~/.pi/agent/skills/fstar/fstar-2026.09.20/SKILL.md`
  (Custard, Pulse idiom, `U8.v`/`U32.v` → `Int.Cast`, the dead-Low\* delta).
