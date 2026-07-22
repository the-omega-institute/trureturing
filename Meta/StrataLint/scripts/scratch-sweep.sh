#!/usr/bin/env bash
# Phase-1 stop-the-bleeding sweep of leaked StrataLint ceremony scratch checkouts.
#
# The frozen conservative / C0 controllers still create these directories flat under the
# temp roots (Path.GetTempPath() and /tmp) and leak them on SIGKILL / timeout / crash, at
# multiple gigabytes each. They carry no owner marker, so age is the only safe signal: a
# directory older than the TTL is abandoned, because no ceremony runs a fraction that long.
# Active ceremonies are minutes-to-an-hour, so the 24h floor never reclaims a live checkout.
#
# The canonical owner-aware (pid marker OR TTL) sweep lives in
# Meta/StrataLint/StrataLint.Cli/Runtime/ScratchWorkspace.cs. Phase 2 wires the controllers
# to it (relocating creation under the .noindex root and sweeping on reserve, which covers
# every invocation path) and retires this bridge. Keep TTL_HOURS and PREFIXES in sync with
# ScratchWorkspace.DefaultStaleAfter and ScratchWorkspace.LegacyPrefixes; a test pins them.
#
# Best-effort and macOS /bin/bash 3.2 compatible: it never fails its caller and never
# touches a directory younger than the TTL.
set -u
shopt -s nullglob

TTL_HOURS=24
PREFIXES=("stratalint-c0-renew-" "stratalint-conservative-")
ROOTS=("${TMPDIR:-/tmp}" "/tmp")

now="$(date +%s)"
ttl_seconds=$(( TTL_HOURS * 3600 ))

mtime_of() { stat -f %m "$1" 2>/dev/null || stat -c %Y "$1" 2>/dev/null; }

for root in "${ROOTS[@]}"; do
  [[ -d "$root" ]] || continue
  real="$(cd "$root" 2>/dev/null && pwd -P)" || continue
  for prefix in "${PREFIXES[@]}"; do
    # Reprocessing a root (when TMPDIR resolves to /tmp) is harmless: rm is idempotent.
    for dir in "$real/$prefix"*; do
      [[ -d "$dir" ]] || continue
      mtime="$(mtime_of "$dir")"
      [[ -n "$mtime" ]] || continue
      if (( now - mtime > ttl_seconds )); then
        rm -rf -- "$dir" 2>/dev/null || true
      fi
    done
  done
done

exit 0
