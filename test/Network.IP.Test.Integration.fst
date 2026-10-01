(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)

(**
Network.IP.Test.Integration — IP package integration test.

Binds every lemma and public function from all IP modules.
If any lemma or test is deleted or renamed, F* verification fails —
this mechanically enforces test coverage.

Uses [--admit_smt_queries true] for integration anchoring only.
Individual lemmas are proven without admits in their source modules.

@header Network.IP.Test.Integration
*)
module Network.IP.Test.Integration
open Network.IP
open Network.IPv4
open Network.IPv4.Pulse
open Network.IPv6
open Network.IPv6.Pulse

#push-options "--admit_smt_queries true"

(** Network.IP — drop utilities and list lemmas *)
let _IP_drop = Network.IP.drop
let _IP_lemma_drop_append_length = Network.IP.lemma_drop_append_length
let _IP_lemma_drop_append_length_aux = Network.IP.lemma_drop_append_length_aux
let _IP_lemma_drop_length_bound = Network.IP.lemma_drop_length_bound
let _IP_lemma_drop_length_exact = Network.IP.lemma_drop_length_exact

(** Network.IPv4 — IPv4 dotted-decimal codec *)
let _IPv4_ipv4_sep = Network.IPv4.ipv4_sep
let _IPv4_decode_octet_list = Network.IPv4.decode_octet_list
let _IPv4_ipv4_of_octets = Network.IPv4.ipv4_of_octets
let _IPv4_encode_ipv4_list = Network.IPv4.encode_ipv4_list
let _IPv4_decode_ipv4_list = Network.IPv4.decode_ipv4_list
let _IPv4_wfcv_ipv4 = Network.IPv4.wfcv_ipv4
let _IPv4_wfcv_prop_ipv4 = Network.IPv4.wfcv_prop_ipv4
let _IPv4_rest_cond_ipv4 = Network.IPv4.rest_cond_ipv4
let _IPv4_ipv4_enc = Network.IPv4.ipv4_enc
let _IPv4_ipv4_dec = Network.IPv4.ipv4_dec
let _IPv4_ipv4_codec = Network.IPv4.ipv4_codec
let _IPv4_encode_ipv4 = Network.IPv4.encode_ipv4
let _IPv4_decode_ipv4 = Network.IPv4.decode_ipv4
let _IPv4_lemma_ipv4_sep_value = Network.IPv4.lemma_ipv4_sep_value
let _IPv4_lemma_digits_encode_length = Network.IPv4.lemma_digits_encode_length
let _IPv4_lemma_encode_ipv4_roundtrip = Network.IPv4.lemma_encode_ipv4_roundtrip
let _IPv4_lemma_ipv4_roundtrip = Network.IPv4.lemma_ipv4_roundtrip
let _IPv4_lemma_ipv4_list_roundtrip = Network.IPv4.lemma_ipv4_list_roundtrip
let _IPv4_lemma_ipv4_localhost_concrete = Network.IPv4.lemma_ipv4_localhost_concrete
let _IPv4_lemma_ipv4_max_concrete = Network.IPv4.lemma_ipv4_max_concrete
let _IPv4_lemma_ipv4_private_concrete = Network.IPv4.lemma_ipv4_private_concrete
let _IPv4_lemma_ipv4_zero_concrete = Network.IPv4.lemma_ipv4_zero_concrete
let _IPv4_lemma_octet_range  = Network.IPv4.lemma_octet_range
let _IPv4_lemma_octet_roundtrip_dot = Network.IPv4.lemma_octet_roundtrip_dot
let _IPv4_lemma_octet_roundtrip_empty = Network.IPv4.lemma_octet_roundtrip_empty
let _IPv4_lemma_roundtrip    = Network.IPv4.lemma_roundtrip
let _IPv4_lemma_ipv4_dec_err_bound = Network.IPv4.lemma_ipv4_dec_err_bound
let _IPv4_lemma_ipv4_dec_consumed_bound = Network.IPv4.lemma_ipv4_dec_consumed_bound
let _IPv4_lemma_decode_octet_list_consumed = Network.IPv4.lemma_decode_octet_list_consumed
let _IPv4_lemma_decode_ipv4_list_consumed = Network.IPv4.lemma_decode_ipv4_list_consumed

(** Network.IPv4.Pulse — C-extractable IPv4 wire format *)
let _IPv4_Pulse_encode_spec = Network.IPv4.Pulse.encode_spec
let _IPv4_Pulse_decode_spec = Network.IPv4.Pulse.decode_spec
let _IPv4_Pulse_decode = Network.IPv4.Pulse.decode
let _IPv4_Pulse_encode = Network.IPv4.Pulse.encode
let _IPv4_Pulse_lemma_roundtrip = Network.IPv4.Pulse.lemma_roundtrip
let _IPv4_Pulse_lemma_pulse_roundtrip = Network.IPv4.Pulse.lemma_pulse_roundtrip
let _IPv4_Pulse_lemma_pulse_encode_decode_match = Network.IPv4.Pulse.lemma_pulse_encode_decode_match
let _IPv4_Pulse_ipv4_wire_size = Network.IPv4.Pulse.ipv4_wire_size

(** Network.IPv6 — IPv6 colon-hex codec *)
let _IPv6_ipv6_of_groups = Network.IPv6.ipv6_of_groups
let _IPv6_ipv6_loopback = Network.IPv6.ipv6_loopback
let _IPv6_ipv6_unspecified = Network.IPv6.ipv6_unspecified
let _IPv6_ipv6_sep = Network.IPv6.ipv6_sep
let _IPv6_encode_hex_group_go = Network.IPv6.encode_hex_group_go
let _IPv6_decode_hex_group_go = Network.IPv6.decode_hex_group_go
let _IPv6_encode_hex_group = Network.IPv6.encode_hex_group
let _IPv6_decode_hex_group = Network.IPv6.decode_hex_group
let _IPv6_wfcv_hex_group = Network.IPv6.wfcv_hex_group
let _IPv6_rest_cond_hex_group = Network.IPv6.rest_cond_hex_group
let _IPv6_hex_group_codec = Network.IPv6.hex_group_codec
let _IPv6_hex_group_dec = Network.IPv6.hex_group_dec
let _IPv6_hex_group_enc = Network.IPv6.hex_group_enc
let _IPv6_encode_ipv6_list = Network.IPv6.encode_ipv6_list
let _IPv6_decode_ipv6_list = Network.IPv6.decode_ipv6_list
let _IPv6_wfcv_ipv6 = Network.IPv6.wfcv_ipv6
let _IPv6_wfcv_prop_ipv6 = Network.IPv6.wfcv_prop_ipv6
let _IPv6_rest_cond_ipv6 = Network.IPv6.rest_cond_ipv6
let _IPv6_ipv6_enc = Network.IPv6.ipv6_enc
let _IPv6_ipv6_dec = Network.IPv6.ipv6_dec
let _IPv6_ipv6_codec = Network.IPv6.ipv6_codec
let _IPv6_encode_ipv6 = Network.IPv6.encode_ipv6
let _IPv6_decode_ipv6 = Network.IPv6.decode_ipv6
let _IPv6_lemma_ipv6_sep_value = Network.IPv6.lemma_ipv6_sep_value
let _IPv6_lemma_decode_hex_group_consumed_bound = Network.IPv6.lemma_decode_hex_group_consumed_bound
let _IPv6_lemma_decode_hex_group_go_consumed_bound = Network.IPv6.lemma_decode_hex_group_go_consumed_bound
let _IPv6_lemma_decode_hex_group_go_range = Network.IPv6.lemma_decode_hex_group_go_range
let _IPv6_lemma_decode_hex_group_range = Network.IPv6.lemma_decode_hex_group_range
let _IPv6_lemma_encode_ipv6_roundtrip = Network.IPv6.lemma_encode_ipv6_roundtrip
let _IPv6_lemma_go_stops_at_non_hex = Network.IPv6.lemma_go_stops_at_non_hex
let _IPv6_lemma_hex_digit_ranges = Network.IPv6.lemma_hex_digit_ranges
let _IPv6_lemma_hex_group_codec_wfcv = Network.IPv6.lemma_hex_group_codec_wfcv
let _IPv6_lemma_hex_group_dec_consumed_bound = Network.IPv6.lemma_hex_group_dec_consumed_bound
let _IPv6_lemma_hex_group_dec_err_bound = Network.IPv6.lemma_hex_group_dec_err_bound
let _IPv6_lemma_hex_group_roundtrip = Network.IPv6.lemma_hex_group_roundtrip
let _IPv6_lemma_hex_group_roundtrip_colon_suffix = Network.IPv6.lemma_hex_group_roundtrip_colon_suffix
let _IPv6_lemma_hex_group_roundtrip_empty = Network.IPv6.lemma_hex_group_roundtrip_empty
let _IPv6_lemma_hex_group_roundtrip_seq = Network.IPv6.lemma_hex_group_roundtrip_seq
let _IPv6_lemma_ipv6_doc_concrete = Network.IPv6.lemma_ipv6_doc_concrete
let _IPv6_lemma_ipv6_all_max_concrete = Network.IPv6.lemma_ipv6_all_max_concrete
let _IPv6_lemma_ipv6_single_digit_concrete = Network.IPv6.lemma_ipv6_single_digit_concrete
let _IPv6_lemma_ipv6_mixed_case_concrete = Network.IPv6.lemma_ipv6_mixed_case_concrete
let _IPv6_lemma_ipv6_group_range = Network.IPv6.lemma_ipv6_group_range
let _IPv6_lemma_ipv6_list_roundtrip = Network.IPv6.lemma_ipv6_list_roundtrip
let _IPv6_lemma_ipv6_loopback_concrete = Network.IPv6.lemma_ipv6_loopback_concrete
let _IPv6_lemma_ipv6_unspecified_concrete = Network.IPv6.lemma_ipv6_unspecified_concrete
let _IPv6_lemma_roundtrip    = Network.IPv6.lemma_roundtrip
let _IPv6_lemma_roundtrip_of_groups = Network.IPv6.lemma_roundtrip_of_groups
let _IPv6_lemma_wfcv_hex_group_bound = Network.IPv6.lemma_wfcv_hex_group_bound
let _IPv6_lemma_ipv6_roundtrip = Network.IPv6.lemma_ipv6_roundtrip
let _IPv6_lemma_ipv6_dec_err_bound = Network.IPv6.lemma_ipv6_dec_err_bound
let _IPv6_lemma_ipv6_dec_consumed_bound = Network.IPv6.lemma_ipv6_dec_consumed_bound
let _IPv6_lemma_decode_hex_group_list_consumed = Network.IPv6.lemma_decode_hex_group_list_consumed
let _IPv6_lemma_decode_ipv6_list_consumed = Network.IPv6.lemma_decode_ipv6_list_consumed
let _IPv6_lemma_seq_to_list_of_list_append = Network.IPv6.lemma_seq_to_list_of_list_append
let _IPv6_lemma_seq_to_list_empty = Network.IPv6.lemma_seq_to_list_empty
let _IPv6_lemma_encode_hex_group_nonempty = Network.IPv6.lemma_encode_hex_group_nonempty
let _IPv6_lemma_encode_hex_group_go_nonempty = Network.IPv6.lemma_encode_hex_group_go_nonempty

(** Network.IPv6.Pulse — C-extractable IPv6 wire format *)
let _IPv6_Pulse_encode_spec = Network.IPv6.Pulse.encode_spec
let _IPv6_Pulse_decode_spec = Network.IPv6.Pulse.decode_spec
let _IPv6_Pulse_decode = Network.IPv6.Pulse.decode
let _IPv6_Pulse_encode = Network.IPv6.Pulse.encode
let _IPv6_Pulse_lemma_roundtrip = Network.IPv6.Pulse.lemma_roundtrip
let _IPv6_Pulse_lemma_pulse_roundtrip = Network.IPv6.Pulse.lemma_pulse_roundtrip
let _IPv6_Pulse_lemma_pulse_encode_decode_match = Network.IPv6.Pulse.lemma_pulse_encode_decode_match
let _IPv6_Pulse_ipv6_wire_size = Network.IPv6.Pulse.ipv6_wire_size

#pop-options
