# Copyright 2026 Department of Code LLC.
# SPDX-License-Identifier: AGPL-3.0-or-later

# F* dev-loop build (verify).
#
# Usage: nix develop, then `make check`.
#
# FSTAR_CHECKED / CODEC_SRC / CODEC_CHECKED / BASEN_SRC / BASEN_CHECKED are
# exported by the flake devShell (see flake.nix shellHook).  Override them
# here if needed.

# ── Tools ──────────────────────────────────────────────────────────

# Build output directory.  Defaults to `./out` for the dev loop; nix
# derivations (default.nix) override it to `$out` so the Makefile writes
# straight into the nix store output path.
OUT ?= out

FSTAR ?= fstar.exe

# The codec dependency's source dir + pre-verified `.checked` cache (injected
# by the flake/derivation as absolute paths; `codec` lives in the separate
# `fstar-codec` repo).
CODEC_SRC ?= $(error CODEC_SRC is not set; run \`nix develop\` (or export it yourself) before \`make check\`)
CODEC_CHECKED ?= $(error CODEC_CHECKED is not set; run \`nix develop\` (or export it yourself) before \`make check\`)

# The base-N dependency's source dir + pre-verified `.checked` cache (injected
# by the flake/derivation as absolute paths; `basen` lives in the separate
# `fstar-basen` repo).
BASEN_SRC ?= $(error BASEN_SRC is not set; run \`nix develop\` (or export it yourself) before \`make check\`)
BASEN_CHECKED ?= $(error BASEN_CHECKED is not set; run \`nix develop\` (or export it yourself) before \`make check\`)

FLIB := $(shell $(FSTAR) --locate_lib 2>/dev/null || echo /none)
ULIB := $(FLIB)/ulib

# Pulse ships in the install under $(locate_lib)/pulse (sources under
# pulse/{common,pulse/lib}, `.checked` under pulse/{common.checked,
# pulse.checked}).  The Pulse leaves need these, since FSTAR_FLAGS uses
# --no_default_includes.
PULSE_DIRS := $(FLIB)/pulse/common\
  $(FLIB)/pulse/common.checked\
  $(FLIB)/pulse/pulse/lib\
  $(FLIB)/pulse/pulse.checked

# Three benign CWarnings are silenced (they are structural, not defects):
#   274 -- `X.Pulse` namespace shadows upstream `Pulse` (case-insensitive).
#   288 -- deprecated A.alloc/A.free (the F* upstream test idiom; "model
#          implementations only", which our test modules are).
#   249 -- precision loss when the coverage-anchor module references a Pulse
#          `fn` from a non-#lang-pulse context (inherent to the anchor pattern).

FSTAR_FLAGS = --no_default_includes --warn_error -274 --warn_error -288 --warn_error -249 \
  --include $(ULIB) \
  $(foreach d,$(PULSE_DIRS),--include $(d)) \
  --include $(CODEC_SRC)/src \
  --include $(BASEN_SRC)/src \
  --include ./src

# ── F* verification ───────────────────────────────────────────────

# Source modules in DEPENDENCY ORDER (leaf modules first).
#
# Network.IP is the shared leaf (drop/list lemmas).  Network.IPv4 and
# Network.IPv6 open Data.Codec + Data.BaseN + Network.IP.  The .Pulse
# modules are the Custard-era Pulse leaves (the old KaRaMeL .Low modules
# were deleted with the Low* stdlib in v2026.09.20).
SRC_MODS := Network.IP Network.IPv4 Network.IPv6 \
            Network.IPv4.Pulse Network.IPv6.Pulse

# Pulse-only modules skip re-verification (they ship pre-verified in the F*
# install); the Pulse leaves open Pulse.Lib.* which would otherwise time out
# re-verifying the whole Pulse stdlib on every `make check`.
ALREADY_CACHED := Prims,FStar,Pulse.Nolib,Pulse.Lib,Pulse.Class,PulseCore

TST_MODS := Network.IP.Test.Integration

.PHONY: check clean

check: $(addprefix $(OUT)/checked/,$(addsuffix .fst.checked,$(SRC_MODS))) \
       $(addprefix $(OUT)/checked/,$(addsuffix .fst.checked,$(TST_MODS)))

$(OUT)/checked/%.fst.checked: src/%.fst
	@mkdir -p $(OUT)/checked
	@test -n "$(FSTAR_CHECKED)" || { \
	  echo "ERROR: FSTAR_CHECKED is not set; run \`nix develop\` (or export it yourself) before \`make check\`" >&2; \
	  exit 1; }
	@cp $(FSTAR_CHECKED)/*.checked $(OUT)/checked/ 2>/dev/null || true
	@cp $(CODEC_CHECKED)/*.checked $(OUT)/checked/ 2>/dev/null || true
	@cp $(BASEN_CHECKED)/*.checked $(OUT)/checked/ 2>/dev/null || true
	@echo "=== $* ==="
	$(FSTAR) $(FSTAR_FLAGS) \
	  --z3rlimit 120 \
	  --already_cached $(ALREADY_CACHED) \
	  --cache_checked_modules --cache_dir $(OUT)/checked \
	  --odir $(OUT)/checked $<

$(OUT)/checked/%.fst.checked: test/%.fst
	@mkdir -p $(OUT)/checked
	@test -n "$(FSTAR_CHECKED)" || { \
	  echo "ERROR: FSTAR_CHECKED is not set; run \`nix develop\` first" >&2; \
	  exit 1; }
	@cp $(FSTAR_CHECKED)/*.checked $(OUT)/checked/ 2>/dev/null || true
	@cp $(CODEC_CHECKED)/*.checked $(OUT)/checked/ 2>/dev/null || true
	@cp $(BASEN_CHECKED)/*.checked $(OUT)/checked/ 2>/dev/null || true
	@echo "=== $* ==="
	$(FSTAR) $(FSTAR_FLAGS) --include ./test \
	  --z3rlimit 120 \
	  --already_cached $(ALREADY_CACHED) \
	  --cache_checked_modules --cache_dir $(OUT)/checked \
	  --odir $(OUT)/checked $<

# ── Clean ─────────────────────────────────────────────────────────────

clean:
	rm -rf $(OUT) cache result result-*
