#!/usr/bin/env bash
# Render the open-problem search brief.
# usage: render-search-brief.sh SEAT_ID OUT
#   SEAT_ID  seat identifier written into the brief, e.g. nyxid-oracle:s1234-gptpro-search-r7
#   OUT      output path for the rendered brief
# Substitutes __SEAT_ID__, __SHA__ (current origin/dev) and __OPEN_PREREGISTRATIONS__
# (open GitHub issues whose title contains "Preregister"). Requires git and gh.
set -euo pipefail
if [[ $# -ne 2 || -z "$1" || -z "$2" ]]; then
  echo "usage: render-search-brief.sh SEAT_ID OUT" >&2
  exit 2
fi
seat_id="$1"
out="$2"
command -v git >/dev/null || { echo "render-search-brief: git not found" >&2; exit 2; }
command -v gh >/dev/null || { echo "render-search-brief: gh not found" >&2; exit 2; }
command -v python3 >/dev/null || { echo "render-search-brief: python3 not found" >&2; exit 2; }
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(git -C "$script_dir" rev-parse --show-toplevel)"
template="$script_dir/templates/search-brief.md"
[[ -f "$template" ]] || { echo "render-search-brief: missing $template" >&2; exit 2; }
git -C "$repo_root" fetch -q origin dev
sha="$(git -C "$repo_root" rev-parse origin/dev)"
prereg="$(mktemp)"
trap 'rm -f "$prereg"' EXIT
(cd "$repo_root" && gh issue list --state open --search "Preregister in:title" --limit 500 \
  --json number,title --jq '.[] | "#\(.number) \(.title)"') > "$prereg"
[[ -s "$prereg" ]] || echo "(none)" > "$prereg"
python3 - "$template" "$out" "$seat_id" "$sha" "$prereg" <<'PY'
import pathlib, sys
template, out, seat_id, sha, prereg = sys.argv[1:6]
text = pathlib.Path(template).read_text()
for placeholder in ("__SEAT_ID__", "__SHA__", "__OPEN_PREREGISTRATIONS__"):
    if placeholder not in text:
        sys.exit(f"render-search-brief: placeholder {placeholder} missing from template")
text = (text.replace("__SEAT_ID__", seat_id)
            .replace("__SHA__", sha)
            .replace("__OPEN_PREREGISTRATIONS__", pathlib.Path(prereg).read_text().rstrip("\n")))
pathlib.Path(out).write_text(text)
print(f"RENDERED out={out} sha={sha} bytes={len(text.encode())}")
PY
