#!/usr/bin/env bash
# Render an open-problem search brief.
# usage: render-search-brief.sh SEAT_ID OUT [deep|quick] [WINDOW]
#   SEAT_ID  seat identifier written into the brief, e.g. nyxid-oracle:s1234-gptpro-search-r7
#   OUT      output path for the rendered brief
#   TRACK    deep (default; templates/search-brief.md) or quick (templates/search-brief-quick.md)
#   WINDOW   quick track only: the arXiv listing window to scan, as YYMM or YYMM-YYMM
#            (default: the previous and the current month)
# Substitutes __SEAT_ID__, __SHA__ (current origin/dev), __OPEN_PREREGISTRATIONS__
# (open GitHub issues whose title contains "Preregister") and, for the quick track, __WINDOW__.
# Requires git, gh and python3.
set -euo pipefail
if [[ $# -lt 2 || $# -gt 4 || -z "$1" || -z "$2" ]]; then
  echo "usage: render-search-brief.sh SEAT_ID OUT [deep|quick] [WINDOW]" >&2
  exit 2
fi
seat_id="$1"
out="$2"
track="${3:-deep}"
window="${4:-}"
case "$track" in
  deep) template_name="search-brief.md" ;;
  quick) template_name="search-brief-quick.md" ;;
  *) echo "render-search-brief: TRACK must be deep or quick, got '$track'" >&2; exit 2 ;;
esac
if [[ "$track" == deep && -n "$window" ]]; then
  echo "render-search-brief: WINDOW applies only to the quick track" >&2
  exit 2
fi
if [[ -n "$window" && ! "$window" =~ ^[0-9]{4}(-[0-9]{4})?$ ]]; then
  echo "render-search-brief: WINDOW must be YYMM or YYMM-YYMM, got '$window'" >&2
  exit 2
fi
command -v git >/dev/null || { echo "render-search-brief: git not found" >&2; exit 2; }
command -v gh >/dev/null || { echo "render-search-brief: gh not found" >&2; exit 2; }
command -v python3 >/dev/null || { echo "render-search-brief: python3 not found" >&2; exit 2; }
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(git -C "$script_dir" rev-parse --show-toplevel)"
template="$script_dir/templates/$template_name"
[[ -f "$template" ]] || { echo "render-search-brief: missing $template" >&2; exit 2; }
git -C "$repo_root" fetch -q origin dev
sha="$(git -C "$repo_root" rev-parse origin/dev)"
prereg="$(mktemp)"
trap 'rm -f "$prereg"' EXIT
(cd "$repo_root" && gh issue list --state open --search "Preregister in:title" --limit 500 \
  --json number,title --jq '.[] | "#\(.number) \(.title)"') > "$prereg"
[[ -s "$prereg" ]] || echo "(none)" > "$prereg"
python3 - "$template" "$out" "$seat_id" "$sha" "$prereg" "$track" "$window" <<'PY'
import datetime, pathlib, sys
template, out, seat_id, sha, prereg, track, window = sys.argv[1:8]
text = pathlib.Path(template).read_text()
placeholders = ["__SEAT_ID__", "__SHA__", "__OPEN_PREREGISTRATIONS__"]
if track == "quick":
    placeholders.append("__WINDOW__")
for placeholder in placeholders:
    if placeholder not in text:
        sys.exit(f"render-search-brief: placeholder {placeholder} missing from {template}")
def month_name(yymm):
    return datetime.date(2000 + int(yymm[:2]), int(yymm[2:]), 1).strftime("%B %Y")
if track == "quick":
    if not window:
        today = datetime.date.today()
        first = today.replace(day=1)
        previous = (first - datetime.timedelta(days=1)).replace(day=1)
        window = f"{previous:%y%m}-{today:%y%m}"
    start, _, end = window.partition("-")
    end = end or start
    if end < start:
        print(f"render-search-brief: WINDOW end {end} precedes start {start}", file=sys.stderr)
        sys.exit(2)
    phrase = (f"{month_name(start)} (arXiv identifiers {start}.*)" if start == end else
              f"{month_name(start)} to {month_name(end)} (arXiv identifiers {start}.* to {end}.*)")
    text = text.replace("__WINDOW__", phrase)
text = (text.replace("__SEAT_ID__", seat_id)
            .replace("__SHA__", sha)
            .replace("__OPEN_PREREGISTRATIONS__", pathlib.Path(prereg).read_text().rstrip("\n")))
pathlib.Path(out).write_text(text)
print(f"RENDERED track={track} out={out} sha={sha} bytes={len(text.encode())}")
PY
