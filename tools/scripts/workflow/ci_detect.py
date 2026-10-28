#!/usr/bin/env python3
"""Decide which CI units a change hits from the sole unit contract.

--contract reads Meta/ci-units.json for hosted execution. The standalone pattern
test interface accepts CI_UNITS. GITHUB_OUTPUT receives
`hits=<JSON object>` mapping each unit, in specification order, to true or false.

Specification: `[unit-id]` opens a unit section and `[*]` the shared section,
whose patterns apply to every unit. Each other non-blank line not starting with
`#` is one pattern matched against the whole path; `*` matches any text,
including `/`, `?` matches one character, and a leading `!` excludes. A path
hits a unit when it matches an including pattern of the unit or of the shared
section and no excluding pattern of the unit.

--changed names the NUL-terminated changed-path list. When it does not exist
the change has no base commit and every unit hits. Every supplied changed path
is validated and available for matching, with no path-count cutoff. Any error exits 2.
"""
import argparse
import json
import os
from pathlib import Path
import re
import sys

UNIT_ID = re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*")


class DetectError(ValueError):
    pass


def pattern_regex(pattern):
    if (pattern in ("", "!") or any(ord(char) < 32 or ord(char) == 127 for char in pattern)):
        raise DetectError(f"invalid pattern: {pattern!r}")
    if any(char in "[]{}()|\\@" for char in pattern):
        raise DetectError(f"unsupported pattern syntax: {pattern!r}")
    # DOTALL: paths may contain newlines, which `*` and `?` match like any character.
    return re.compile(re.escape(pattern).replace(r"\*", ".*").replace(r"\?", "."), re.DOTALL)


def parse(spec):
    sections, current = {}, None
    for raw in spec.splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("["):
            name = line[1:-1] if line.endswith("]") else ""
            if name != "*" and not UNIT_ID.fullmatch(name):
                raise DetectError(f"invalid section header: {line!r}")
            if name in sections:
                raise DetectError(f"duplicate section [{name}]")
            current = sections[name] = []
            continue
        if current is None:
            raise DetectError(f"pattern before the first section: {line!r}")
        if line in current:
            raise DetectError(f"duplicate pattern: {line!r}")
        current.append(line)
    shared = sections.pop("*", [])
    if any(pattern.startswith("!") for pattern in shared):
        raise DetectError("shared section cannot exclude")
    if not sections:
        raise DetectError("specification has no unit")
    units = {}
    for name, patterns in sections.items():
        includes = [(pattern, pattern_regex(pattern))
                    for pattern in shared + [p for p in patterns if not p.startswith("!")]]
        excludes = [pattern_regex(pattern[1:]) for pattern in patterns if pattern.startswith("!")]
        if not any(not p.startswith("!") for p in patterns) and not shared:
            raise DetectError(f"unit {name} has no including pattern")
        units[name] = (includes, excludes)
    return units


def read_changed(path):
    try:
        data = path.read_bytes()
    except FileNotFoundError:
        return None
    except OSError as error:
        raise DetectError(f"cannot read {path}: {error}") from error
    if data and not data.endswith(b"\0"):
        raise DetectError("changed-path list must be NUL-terminated")
    try:
        paths = [item.decode("utf-8") for item in data.split(b"\0")[:-1]] if data else []
    except UnicodeDecodeError as error:
        raise DetectError(f"cannot read {path}: {error}") from error
    for item in paths:
        if not item or item.startswith("/") or any(p in ("", ".", "..") for p in item.split("/")):
            raise DetectError(f"invalid changed path: {item!r}")
    return paths


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--changed", type=Path, required=True)
    parser.add_argument("--contract", action="store_true")
    args = parser.parse_args()
    try:
        spec = os.environ.get("CI_UNITS")
        output = os.environ.get("GITHUB_OUTPUT")
        if args.contract:
            from ci_contract import git, load, selection
            data, revision = load(Path.cwd())
            purpose = "pull-request" if os.environ.get("GITHUB_EVENT_NAME") == "pull_request" else "push"
            plan = selection(data, read_changed(args.changed), purpose)
            if not output:
                raise DetectError("GITHUB_OUTPUT is required")
            with open(output, "a", encoding="utf-8") as stream:
                for key, value in plan.items():
                    stream.write(key + "=" + json.dumps(value, separators=(",", ":")) + "\n")
                stream.write("contract_revision=" + revision + "\n")
            print("CI_SELECTION " + json.dumps(dict(plan, contract_revision=revision, purpose=purpose,
                  base=os.environ.get("CI_BASE") or None,
                  candidate=git(Path.cwd(), "rev-parse", "HEAD^{tree}").decode().strip())))
            return 0
        if spec is None:
            raise DetectError("CI_UNITS is required")
        if not output:
            raise DetectError("GITHUB_OUTPUT is required")
        units = parse(spec)
        changed = read_changed(args.changed)
        hits = {}
        for name, (includes, excludes) in units.items():
            if changed is None:
                hits[name] = True
                print(f"CI_DETECT unit={name} hit=true reason=no base commit")
                continue
            match = next(((path, pattern) for path in changed
                          if not any(regex.fullmatch(path) for regex in excludes)
                          for pattern, regex in includes if regex.fullmatch(path)), None)
            hits[name] = match is not None
            if match is None:
                print(f"CI_DETECT unit={name} hit=false changed={len(changed)}")
            else:
                print(f"CI_DETECT unit={name} hit=true path={match[0]} pattern={match[1]}")
        with open(output, "a", encoding="utf-8") as stream:
            stream.write("hits=" + json.dumps(hits, separators=(",", ":")) + "\n")
        return 0
    except (ValueError, TypeError, OSError) as error:
        print(f"CI_DETECT_ERROR {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
