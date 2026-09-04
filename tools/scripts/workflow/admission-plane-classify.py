#!/usr/bin/env python3
import argparse
import json
from pathlib import Path
import re
import sys

try:
    import tomllib
except ImportError:
    tomllib = None


FILEMAP_PATH = "Meta/FILEMAP.toml"

REPAIR_PATHS = frozenset(
    {
        ".github/workflows/ci.yml",
        FILEMAP_PATH,
    }
)


def parse_arguments():
    parser = argparse.ArgumentParser()
    parser.add_argument("--delta-file", required=True)
    parser.add_argument("--filemap", required=True)
    parser.add_argument("--filemap-fetched", choices=("true", "false"), required=True)
    parser.add_argument("--candidate-filemap")
    parser.add_argument(
        "--candidate-filemap-fetched", choices=("true", "false"), default="false"
    )
    parser.add_argument("--github-output")
    return parser.parse_args()


def read_delta(path):
    raw = Path(path).read_bytes()
    parts = raw.split(b"\0")
    if parts[-1:] == [b""]:
        parts.pop()
    return [part.decode("utf-8", errors="strict") for part in parts]


def detail_suffix(detail):
    return "" if detail is None else f" detail={json.dumps(detail)}"


def publish_plane(path, plane):
    if path is None:
        return
    with Path(path).open("a", encoding="utf-8") as stream:
        stream.write(f"plane={plane}\n")


def policy_unavailable(reason, is_repair, github_output, detail=None):
    suffix = detail_suffix(detail)
    if is_repair:
        print(
            "ADMISSION_PLANE_PARTITION status=policy-unavailable "
            f"reason={reason} self-repair=bootstrap{suffix}"
        )
        publish_plane(github_output, "bootstrap")
        raise SystemExit(0)
    print(
        "ADMISSION_PLANE_PARTITION status=policy-unavailable "
        f"reason={reason}{suffix}",
        file=sys.stderr,
    )
    raise SystemExit(1)


def classification_failed(reason, detail=None):
    print(
        "ADMISSION_PLANE_PARTITION status=classification-failed "
        f"reason={reason}{detail_suffix(detail)}",
        file=sys.stderr,
    )
    raise SystemExit(1)


def compile_glob(pattern):
    expression = [r"\A"]
    cursor = 0
    while cursor < len(pattern):
        character = pattern[cursor]
        if character == "*" and cursor + 1 < len(pattern) and pattern[cursor + 1] == "*":
            if cursor + 2 < len(pattern) and pattern[cursor + 2] == "/":
                expression.append(r"(?:.*/)?")
                cursor += 3
            else:
                expression.append(r".*")
                cursor += 2
            continue
        if character == "*":
            expression.append(r"[^/]*")
            cursor += 1
            continue
        expression.append(re.escape(character))
        cursor += 1
    expression.append(r"\Z")
    return re.compile("".join(expression))


def load_entries(path, fetched, unavailable, label="base"):
    if not fetched:
        unavailable(f"{label}-filemap-unavailable")
    if tomllib is None:
        unavailable("tomllib-unavailable")

    try:
        with Path(path).open("rb") as stream:
            document = tomllib.load(stream)
    except (OSError, UnicodeError, tomllib.TOMLDecodeError) as exception:
        unavailable(f"{label}-filemap-parse-failed", str(exception))

    entries = document.get("files", [])
    if not isinstance(entries, list):
        classification_failed(f"{label}-filemap-entries-unavailable")

    compiled = []
    for index, entry in enumerate(entries):
        if not isinstance(entry, dict):
            classification_failed(f"{label}-filemap-entry-unavailable", f"files[{index}]")
        pattern = entry.get("pattern")
        plane = entry.get("admission_plane")
        if not isinstance(pattern, str):
            classification_failed(
                f"{label}-filemap-pattern-unavailable", f"files[{index}]"
            )
        if "?" in pattern:
            classification_failed(f"{label}-filemap-pattern-unsafe", pattern)
        if plane not in {"judge", "content"}:
            classification_failed(
                f"{label}-filemap-admission-plane-unavailable",
                f"files[{index}] pattern={pattern}",
            )
        compiled.append((pattern, plane, compile_glob(pattern)))
    return compiled


def matching_entries(entries, path):
    return [entry for entry in entries if entry[2].match(path)]


def main():
    arguments = parse_arguments()
    try:
        changed_paths = read_delta(arguments.delta_file)
    except (OSError, UnicodeError) as exception:
        print(
            "ADMISSION_PLANE_PARTITION status=policy-unavailable "
            f"reason=delta-invalid detail={json.dumps(str(exception))}",
            file=sys.stderr,
        )
        return 1

    if not changed_paths:
        print("ADMISSION_PLANE_PARTITION status=empty judge=0 content=0")
        publish_plane(arguments.github_output, "empty")
        return 0

    is_repair = set(changed_paths).issubset(REPAIR_PATHS)
    entries = load_entries(
        arguments.filemap,
        arguments.filemap_fetched == "true",
        lambda reason, detail=None: policy_unavailable(
            reason, is_repair, arguments.github_output, detail
        ),
    )

    # A path the base manifest does not govern cannot be classified from the base
    # alone, which makes every new path family unlandable: entry-first is refused
    # by filemap-conform (empty pattern), entry-and-file-together is refused here.
    # The candidate manifest breaks that tie, but only for paths the base leaves
    # entirely unmatched, and only when this delta actually edits the manifest.
    # A path the base already governs keeps the base plane, so a candidate can
    # never relabel what the base has classified.
    candidate_entries = None
    if arguments.candidate_filemap is not None and FILEMAP_PATH in changed_paths:
        candidate_entries = load_entries(
            arguments.candidate_filemap,
            arguments.candidate_filemap_fetched == "true",
            classification_failed,
            "candidate",
        )

    by_plane = {"judge": [], "content": []}
    for path in changed_paths:
        matches = matching_entries(entries, path)
        if len(matches) == 1:
            by_plane[matches[0][1]].append(path)
            continue
        if len(matches) > 1 or candidate_entries is None:
            classification_failed(
                "path-match-count-not-one",
                f"path={path} matches={len(matches)}",
            )
        candidate_matches = matching_entries(candidate_entries, path)
        if len(candidate_matches) != 1:
            classification_failed(
                "candidate-path-match-count-not-one",
                f"path={path} candidate_matches={len(candidate_matches)}",
            )
        by_plane[candidate_matches[0][1]].append(path)

    if is_repair:
        for repair_path in sorted(REPAIR_PATHS):
            matches = matching_entries(entries, repair_path)
            if len(matches) != 1 or matches[0][1] != "judge":
                classification_failed(
                    "self-repair-path-not-judge",
                    f"path={repair_path} matches={len(matches)}",
                )

    judge_paths = by_plane["judge"]
    content_paths = by_plane["content"]
    if judge_paths and content_paths:
        print(
            "ADMISSION_PLANE_PARTITION status=mixed "
            f"judge={len(judge_paths)} content={len(content_paths)}",
            file=sys.stderr,
        )
        for path in judge_paths[:20]:
            print(f"judge_path={json.dumps(path)}", file=sys.stderr)
        for path in content_paths[:20]:
            print(f"content_path={json.dumps(path)}", file=sys.stderr)
        return 1
    if judge_paths:
        repair_suffix = " self-repair=reserved-paths-judge" if is_repair else ""
        print(
            "ADMISSION_PLANE_PARTITION status=judge-only "
            f"judge={len(judge_paths)} content=0{repair_suffix}"
        )
        publish_plane(arguments.github_output, "judge-only")
        return 0
    if content_paths:
        print(
            "ADMISSION_PLANE_PARTITION status=content-only "
            f"judge=0 content={len(content_paths)}"
        )
        publish_plane(arguments.github_output, "content-only")
        return 0
    classification_failed("no-classified-paths")


if __name__ == "__main__":
    raise SystemExit(main())
