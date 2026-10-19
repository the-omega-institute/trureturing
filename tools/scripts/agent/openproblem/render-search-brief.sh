#!/usr/bin/env bash
# Render an open-problem search brief.
# usage: render-search-brief.sh SEAT_ID OUT [deep|quick] [WINDOW]
#   SEAT_ID  seat identifier written into the brief, e.g. nyxid-oracle:s1234-gptpro-search-r7
#   OUT      output path for the rendered brief
#   TRACK    deep (default; templates/search-brief.md) or quick (templates/search-brief-quick.md)
#   WINDOW   quick track only: the arXiv listing window to scan, as YYMM or YYMM-YYMM
#            (default: the previous and the current month)
# Substitutes __SEAT_ID__, __SHA__ (current origin/dev), __OPEN_PREREGISTRATIONS__
# (open GitHub issues whose title contains "Preregister" or "preregistration", deduplicated by number;
# for nyxid-oracle seats each issue is named by the source identifiers in its title) and, for the quick track, __WINDOW__.
# Requires git, gh and python3.
set -euo pipefail
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if [[ "${1:-}" == --selftest ]]; then
  exec python3 "$script_dir/briefgen/selftest.py" "${BASH_SOURCE[0]}"
fi
if [[ "${1:-}" == --codex ]]; then
  shift
  exec python3 "$script_dir/briefgen/codex_search.py" "$@"
fi
if [[ $# -lt 2 || $# -gt 4 || -z "$1" || -z "$2" ]]; then
  echo "usage: render-search-brief.sh SEAT_ID OUT [deep|quick] [WINDOW]" >&2
  exit 10
fi
seat_id="$1"
out="$2"
track="${3:-deep}"
window="${4:-}"
case "$track" in
  deep) template_name="search-brief.md" ;;
  quick) template_name="search-brief-quick.md" ;;
  *) echo "render-search-brief: TRACK must be deep or quick, got '$track'" >&2; exit 13 ;;
esac
if [[ "$track" == deep && -n "$window" ]]; then
  echo "render-search-brief: WINDOW applies only to the quick track" >&2
  exit 13
fi
if [[ -n "$window" && ! "$window" =~ ^[0-9]{4}(-[0-9]{4})?$ ]]; then
  echo "render-search-brief: WINDOW must be YYMM or YYMM-YYMM, got '$window'" >&2
  exit 13
fi
command -v git >/dev/null || { echo "render-search-brief: git not found" >&2; exit 12; }
command -v gh >/dev/null || { echo "render-search-brief: gh not found" >&2; exit 12; }
command -v python3 >/dev/null || { echo "render-search-brief: python3 not found" >&2; exit 12; }
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(git -C "$script_dir" rev-parse --show-toplevel)"
template="$script_dir/templates/$template_name"
[[ -f "$template" ]] || { echo "render-search-brief: missing $template" >&2; exit 11; }
git -C "$repo_root" fetch -q origin dev
sha="$(git -C "$repo_root" rev-parse origin/dev)"
prereg="$(mktemp)"
trap 'rm -f "$prereg"' EXIT
# GitHub title search matches whole words, so "Preregister" misses "Open problem (preregistration): …"; query both.
(cd "$repo_root" && for query in "Preregister in:title" "preregistration in:title"; do
  gh issue list --state open --search "$query" --limit 500 --json number,title --jq '.[] | "#\(.number) \(.title)"'
done) | awk '!seen[$1]++' > "$prereg"
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
        sys.exit(13)
    phrase = (f"{month_name(start)} (arXiv identifiers {start}.*)" if start == end else
              f"{month_name(start)} to {month_name(end)} (arXiv identifiers {start}.* to {end}.*)")
    text = text.replace("__WINDOW__", phrase)
listing = pathlib.Path(prereg).read_text().rstrip("\n")
if seat_id.startswith("nyxid-oracle:"):
    # The oracle broker drops briefs above about 40 KB, so name each issue by the source identifiers in its title
    # (modern and legacy arXiv numbers, OEIS A-numbers, MathOverflow numbers, DOIs).
    import re
    rows = []
    for line in listing.splitlines():
        match = re.match(r"#(\d+) (.*)", line)
        if not match:
            rows.append(line)
            continue
        number, title = match.groups()
        ids = sorted(set(re.findall(r"(?<![\d.])(\d{4}\.\d{4,5})(?!\d)", title))
                     | set(re.findall(r"(?<![\w.-])([a-z]+(?:-[a-z]+)*(?:\.[A-Z]{2})?/\d{7})(?!\d)", title))
                     | set(re.findall(r"\bA\d{6}\b", title))
                     | set(re.findall(r"\bMO ?\d{5,6}\b", title))
                     | set(match.rstrip("):.,;") for match in re.findall(r"\b10\.\d{4,9}/[^\s,;]+", title)))
        rows.append(f"#{number} " + (", ".join(ids) if ids else title[:70]))
    listing = "\n".join(rows)
    text = text.replace("Open preregistration issues (number and title, one per line):",
                        "Open preregistration issues (number, then the source identifiers its title names, or its title cut to 70 characters):")
text = (text.replace("__SEAT_ID__", seat_id)
            .replace("__SHA__", sha)
            .replace("__OPEN_PREREGISTRATIONS__", listing))
pathlib.Path(out).write_text(text)
print(f"RENDERED track={track} out={out} sha={sha} bytes={len(text.encode())}")
PY
