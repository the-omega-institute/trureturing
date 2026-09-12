# S20 whole-section verification

This page checks the complete original S20 report through the published `S20Evidence.section(anchor)` API. The original report has 58191 bytes, 792 LF bytes and SHA256 `29d239c8f3f0bb3cde6bc8fb780360856955846ecc8c48ffe1f7f16b218a73c6`.

## Reproduce the section check

Save the entire Python block below outside the repository, for example as `/tmp/s20-public-section-check.py`, and run it with Python 3.9 or later:

```sh
python3 -B /tmp/s20-public-section-check.py /path/to/checkout
```

The block loads the complete current S19 and S20 public API blocks verbatim in memory. It reads the original report, independently determines every heading interval through the next heading of equal or higher level while respecting code fences, and compares the real public reader's bytes with those intervals. It covers all 33 anchors, 78 ancestor/descendant pairs and the three repaired parent sections. It uses only the standard library and performs fixed text, JSON and byte verification; it does not execute an archived mathematical program.

```python
"""Check fixed report sections through the published S19/S20 byte APIs.

Run: python3 -B s20-public-section-recipe-c193-0912.py /path/to/checkout
No mathematical certificate or archived program is executed.
"""
from pathlib import Path
import hashlib
import json
import re
import sys
import types


def public_module(root, stage, class_name):
    path = root / f"docs/reports/quantized-gh/{stage}-evidence/README.md"
    blocks = re.findall(rb"^```python\n(.*?)^```[ \t]*$", path.read_bytes(), re.M | re.S)
    selected = [b for b in blocks if ("class " + class_name + ":").encode() in b]
    if len(selected) != 1:
        raise ValueError(f"expected one complete public {stage} API block")
    module = types.ModuleType(stage + "_evidence")
    module.__file__ = str(path)
    sys.modules[module.__name__] = module
    exec(compile(selected[0], str(path) + "#public-api", "exec"), module.__dict__)
    return module


def report_headings(data):
    headings, offset, fence = [], 0, None
    for line in data.splitlines(keepends=True):
        text = line.removesuffix(b"\n")
        if fence is not None:
            char, size = fence
            closing = rb" {0,3}" + re.escape(char) + b"{" + str(size).encode() + rb",}[ \t]*"
            if re.fullmatch(closing, text):
                fence = None
        else:
            opening = re.match(rb" {0,3}(`{3,}|~{3,})(.*)$", text)
            if opening:
                fence = (opening[1][:1], len(opening[1]))
            else:
                heading = re.fullmatch(rb" {0,3}(#{1,6})(?:[ \t]+(.*))?", text)
                if heading:
                    title = re.sub(rb"[ \t]+#+[ \t]*$", b"", heading[2] or b"").strip()
                    headings.append({"start": offset, "level": len(heading[1]),
                                     "heading": title.decode("utf-8")})
        offset += len(line)
    if fence is not None:
        raise ValueError("the fixed original report has an unclosed code fence")
    for index, heading in enumerate(headings):
        heading["end"] = next((following["start"] for following in headings[index + 1:]
                               if following["level"] <= heading["level"]), len(data))
    return headings


def main(root):
    report_path = root / "docs/reports/quantized-gh/balanced-prime-237-all-slabs-0910.md"
    report = report_path.read_bytes()
    if hashlib.sha256(report).hexdigest() != "29d239c8f3f0bb3cde6bc8fb780360856955846ecc8c48ffe1f7f16b218a73c6":
        raise ValueError("this recipe requires the exact original S20 report")
    s19 = public_module(root, "s19", "Evidence")
    s20 = public_module(root, "s20", "S20Evidence")
    reader = s20.S20Evidence(root, s19.Evidence(root))
    nav_path = root / "docs/reports/quantized-gh/s20-evidence/navigation.json"
    rows = s19.strict_json(nav_path.read_bytes())["report_sections"]
    headings = report_headings(report)
    by_title = {h["heading"]: h for h in headings}
    if len(headings) != 33 or len(by_title) != 33 or len(rows) != 33:
        raise ValueError("the fixed report must have 33 unique headings and section rows")
    if {r["heading"] for r in rows} != set(by_title) or len({r["anchor"] for r in rows}) != 33:
        raise ValueError("navigation does not cover all original headings exactly once")
    intervals, descendant_pairs = {}, 0
    for row in rows:
        heading = by_title[row["heading"]]
        start, end = heading["start"], heading["end"]
        if row["byte_span"] != [start, end]:
            raise ValueError("incomplete declared section: " + row["anchor"])
        if reader.section(row["anchor"]) != report[start:end]:
            raise ValueError("public consumer returned different bytes: " + row["anchor"])
        intervals[row["anchor"]] = [start, end]
        for child in headings:
            if start < child["start"] < end:
                if child["level"] <= heading["level"] or child["end"] > end:
                    raise ValueError("descendant escapes its complete parent interval")
                descendant_pairs += 1
    regressions = {
        "balanced-237-whole-box-all-real-slab-fixed-certificate-s20--c43": [0, 58191],
        "c85--s20-section-31-archival-representation-i29-2026-09-10": [39336, 58191],
        "verbatim-relocated-source-payloads": [42664, 50745],
    }
    if any(intervals[anchor] != span for anchor, span in regressions.items()):
        raise ValueError("one of the three known parent-section regressions remains")
    print(json.dumps({"result": "PASS", "headings": len(headings), "anchors_checked": len(rows),
                      "descendant_pairs_checked": descendant_pairs, "regressions": regressions,
                      "public_consumer": "S20Evidence.section", "report_sha256": hashlib.sha256(report).hexdigest()},
                     sort_keys=True))


if __name__ == "__main__":
    main(Path(sys.argv[1]).resolve())
```

A successful run prints a JSON object with `result=PASS`, `headings=33`, `anchors_checked=33`, `descendant_pairs_checked=78`, and these original byte intervals:

| Anchor | Complete interval |
| --- | --- |
| balanced-237-whole-box-all-real-slab-fixed-certificate-s20--c43 | [0,58191) |
| c85--s20-section-31-archival-representation-i29-2026-09-10 | [39336,58191) |
| verbatim-relocated-source-payloads | [42664,50745) |

## Original evidence and publication

I52 corrected the three original navigation declarations, which returned 2394, 3328 and 40 bytes. Its original implementation reported successful S20 and S23 public checks and retained all original mathematical/report/API bytes. Its verification page omitted its temporary checker body. The exact original [verification page](before-I53/navigation-repair-verification-I52.md), [binding record](before-I53/navigation-repair-I52.json), [implementation result](before-I53/implementation-I52-result.json) and [completion sentinel](before-I53/implementation-I52-completion.txt) preserve that history.

The complete public block above was supplied separately after the omission was identified; the caller's run checked all 33 anchors and 78 ancestor/descendant pairs. The [I53 publication record](recipe-publication-I53.json) records the actual check of the newly published block, its exact identity and the preserved originals. The current [navigation repair record](navigation-repair-I52.json) retains the original navigation repair and its updated public verification binding.

## Scope

These are representation checks. No mathematical proof, source-review approval, CI success or merge follows from their passing. The original R1 architecture `approve`, quality `comment` and tests `reject` remain attributed to their original snapshots in [before-I52](before-I52/). Full quality source reading, fresh complete reviews and ordered delivery remain outstanding. No canonical producer, historical certificate, mathematical search or GPU task is run by this recipe.
