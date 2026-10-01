# Network.IP — Verified IPv4/IPv6 Address Codecs

A formally verified IP address codec library in F*, built on the record-based
[Data.Codec] combinator framework and the [Data.BaseN] base encodings.
Provides IPv4 dotted-decimal (RFC 791 §3.1) and IPv6 colon-hex (RFC 4291
§2.2) text codecs, plus C-extractable 4-byte/16-byte wire-format Pulse
leaves via Custard.

Zero admits.  Zero magic.  All roundtrip proofs are structural.

## Architecture

```
Network.IP               — shared drop/list lemmas
Network.IPv4             — dotted-decimal codec (RFC 791)
Network.IPv6             — colon-hex codec (RFC 4291)
Network.IPv4.Pulse       — C-extractable 32-bit wire codec
Network.IPv6.Pulse       — C-extractable 128-bit wire codec
```

The pure spec modules (`Network.IP`, `Network.IPv4`, `Network.IPv6`) open
`Data.Codec` and `Data.BaseN`; the Pulse leaves (`Network.IPv4.Pulse`,
`Network.IPv6.Pulse`) encode/decode the binary wire format through a
`Pulse.Lib.Array.array`, with byte-level post-conditions tied to the pure
`encode_spec`/`decode_spec`.

## Key properties

- **Zero admits / zero magic.**  Every module verifies with structural
  roundtrip proofs; no `admit()`, no `magic ()`.
- **RFC 791 / RFC 4291 compliance.**  IPv4 dotted-decimal (four 0–255 octets)
  and IPv6 colon-hex (eight 1–4 hex-digit groups).
- **IPv6 colon-hex only.**  `::` zero-compression (RFC 4291 §2.2 item 2) is
  NOT supported; all 8 groups must be present in text form.
- **C extraction.**  The Pulse leaves extract to C11 (and OCaml, F#) via
  Custard (`--custard_backend C`, no KaRaMeL).

## Wire format

| Format | Bytes | Layout |
|--------|-------|--------|
| `ipv4_wire` | 4 | four octets, network byte order |
| `ipv6_wire` | 16 | sixteen octets, network byte order |

## Dependencies

- [fstar-codec] — `Data.Codec` / `Data.Codec.Types` (record codec framework)
- [fstar-basen] — `Data.BaseN` (RFC 4648 base encodings; `Base16` for hex)

Both consumed as flake inputs (`github:dysinger/fstar-codec`,
`github:dysinger/fstar-basen`), pinned in `flake.lock`.

## Build

```sh
nix develop
make check    # Verify all modules (src + test)
```

Or via nix:

```sh
nix build .#checked  # F* verification gate (0-admit)
nix build .#native   # C11 shared/static lib (default)
nix build .#ocaml    # OCaml findlib package
nix build .#fsharp   # .NET library
```

## License

AGPL-3.0-or-later.
