#!/bin/bash
# Download one volume of an open-access integer-sequences journal and extract the text of
# every paper, so that end-of-paper conjecture and open-question lists can be screened
# offline. Screening itself is left to the caller; this script only produces "<TAG>_<id>.txt".
#
# usage: fetch-journal.sh <jis|integers> <volume> [output-directory]
#
# Requires curl and pdftotext (poppler) on PATH. Writes only inside the output directory,
# which defaults to the current working directory. Re-running skips papers already extracted.
set -euo pipefail

die() { printf '%s\n' "$*" >&2; exit 2; }

[ $# -ge 2 ] || die "usage: fetch-journal.sh <jis|integers> <volume> [output-directory]"
journal=$1
volume=$2
outdir=${3:-.}

case "$volume" in
    ''|*[!0-9]*) die "volume must be a positive integer, got: $volume" ;;
esac

for tool in curl pdftotext; do
    command -v "$tool" >/dev/null 2>&1 || die "required tool not found on PATH: $tool"
done

mkdir -p "$outdir"
cd "$outdir"

case "$journal" in
    jis)
        base="https://cs.uwaterloo.ca/journals/JIS"
        index="vol${volume}.html"
        tag="JIS${volume}"
        curl -sL --max-time 120 "$base/$index" -o "$index" || die "cannot fetch $base/$index"
        # Paper pages are listed as VOL<n>/<Author>/<stem>.html; the PDF sits beside them.
        grep -oE "VOL${volume}/[A-Za-z0-9]+/[A-Za-z0-9]+\.html" "$index" \
            | sort -u | sed 's/\.html$/.pdf/' > "${tag}.paths"
        while read -r rel; do
            stem=$(printf '%s' "$rel" | tr '/' '_' | sed 's/\.pdf$//')
            out="${tag}_${stem}"
            [ -s "$out.txt" ] && continue
            curl -sL --max-time 90 "$base/$rel" -o "$out.pdf" || continue
            pdftotext "$out.pdf" "$out.txt" 2>/dev/null || { rm -f "$out.pdf"; continue; }
            rm -f "$out.pdf"
        done < "${tag}.paths"
        ;;
    integers)
        base="https://math.colgate.edu/~integers"
        index="int${volume}.html"
        tag="INTEGERS${volume}"
        curl -sL --max-time 120 "$base/vol${volume}.html" -o "$index" \
            || die "cannot fetch $base/vol${volume}.html"
        # Every paper is linked as an absolute .pdf URL under a per-paper directory.
        grep -oE "https://math\.colgate\.edu/~integers/[a-z]+[0-9]+/[a-z]+[0-9]+\.pdf" "$index" \
            | sort -u > "${tag}.paths"
        while read -r url; do
            stem=$(printf '%s' "$url" | sed 's|.*/\([a-z]*[0-9]*\)\.pdf|\1|')
            out="${tag}_${stem}"
            [ -s "$out.txt" ] && continue
            curl -sL --max-time 90 "$url" -o "$out.pdf" || continue
            pdftotext "$out.pdf" "$out.txt" 2>/dev/null || { rm -f "$out.pdf"; continue; }
            rm -f "$out.pdf"
        done < "${tag}.paths"
        ;;
    *)
        die "unknown journal: $journal (expected jis or integers)"
        ;;
esac

printf 'extracted=%s directory=%s\n' "$(ls -1 "${tag}"_*.txt 2>/dev/null | wc -l | tr -d ' ')" "$(pwd)"
