# Network.IP API Reference

## Types

| Type | Description |
|------|-------------|
| `ipv4` | Four octets: `octet0..octet3: UInt8.t` |
| `ipv4_wire` | IPv4 wire format (32-bit, 4 bytes) |
| `ipv6_group` | 16-bit group: `int{0 <= g <= 65535}` |
| `ipv6` | Eight groups: `group0..group7: ipv6_group` |
| `ipv6_wire` | IPv6 wire format (128-bit, 16 bytes) |
| `opt_ipv4_wire` | `OIPv4_None \| OIPv4_Some of (ipv4_wire & U32.t)` |
| `opt_ipv6_wire` | `OIPv6_None \| OIPv6_Some of (ipv6_wire & U32.t)` |

## Codecs

### Network.IPv4 — Dotted-Decimal (RFC 791)
| Function | Signature | Description |
|----------|-----------|-------------|
| `ipv4_codec` | `codec ipv4` | Full dotted-decimal codec |
| `encode_ipv4` | `ipv4 -> byte_seq` | Address → bytes |
| `decode_ipv4` | `byte_seq -> option ipv4` | Bytes → address |
| `encode_ipv4_list` | `ipv4 -> list byte` | List-level encoder |
| `decode_ipv4_list` | `list byte -> option (ipv4 & nat)` | List-level decoder |
| `decode_octet_list` | `list byte -> option (byte & nat)` | 0-3 digits → byte |
| `ipv4_of_octets` | `byte -> byte -> byte -> byte -> ipv4` | Constructor |

### Network.IPv6 — Colon-Hex (RFC 4291)
| Function | Signature | Description |
|----------|-----------|-------------|
| `ipv6_codec` | `codec ipv6` | Full colon-hex codec |
| `encode_ipv6` | `ipv6 -> byte_seq` | Address → bytes |
| `decode_ipv6` | `byte_seq -> option ipv6` | Bytes → address |
| `encode_ipv6_list` | `ipv6 -> list byte` | List-level encoder |
| `decode_ipv6_list` | `list byte -> option (ipv6 & nat)` | List-level decoder |
| `encode_hex_group` | `nat{n <= 65535} -> list byte` | Value → 1-4 hex digits |
| `decode_hex_group` | `list byte -> option (int & nat)` | Hex digits → value |
| `ipv6_of_groups` | `int -> ... -> option ipv6` | Constructor (8 groups) |

### Network.IPv4.Pulse — 32-bit Wire Format (C-extractable)
| Function | Signature | Description |
|----------|-----------|-------------|
| `encode` | `ipv4_wire -> A.array U8.t -> U32.t -> stk U32.t` | Write 4 bytes |
| `decode` | `A.array U8.t -> U32.t -> U32.t -> stk opt_ipv4_wire` | Read 4 bytes |
| `encode_spec` | `ipv4_wire -> list U8.t` | Pure specification |
| `decode_spec` | `list U8.t -> option (ipv4_wire & U32.t)` | Pure specification |
| `lemma_roundtrip` | Lemma | `decode_spec (encode_spec a) == Some (a, 4ul)` |

### Network.IPv6.Pulse — 128-bit Wire Format (C-extractable)
| Function | Signature | Description |
|----------|-----------|-------------|
| `encode` | `ipv6_wire -> A.array U8.t -> U32.t -> stk U32.t` | Write 16 bytes |
| `decode` | `A.array U8.t -> U32.t -> U32.t -> stk opt_ipv6_wire` | Read 16 bytes |
| `encode_spec` | `ipv6_wire -> list U8.t` | Pure specification |
| `decode_spec` | `list U8.t -> option (ipv6_wire & U32.t)` | Pure specification |
| `lemma_roundtrip` | Lemma | `decode_spec (encode_spec a) == Some (a, 16ul)` |

### Network.IP — Shared Utilities
| Function | Signature | Description |
|----------|-----------|-------------|
| `drop` | `nat -> list a -> list a` | Drop n elements |
| `lemma_drop_append_length` | Lemma | `drop(|ds|)(ds @ suffix) == suffix` |
