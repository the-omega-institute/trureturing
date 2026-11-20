"""The CI unit contract and endpoint/path adapters; no workflow interpretation."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import sys

from ci_detect import DetectError, parse, read_changed

CONTRACT = Path("Meta/ci-units.json")
SHA = re.compile(r"[0-9a-f]{40}")
ZERO = "0" * 40
PUSH_COMMIT_LIMIT = 2048


def unique(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise DetectError(f"duplicate contract member {key}")
        result[key] = value
    return result


def load(root):
    raw = (root / CONTRACT).read_bytes()
    data = json.loads(raw, object_pairs_hook=unique)
    if not isinstance(data, dict) or set(data) != {"CI_UNITS", "units", "current"}:
        raise DetectError("invalid contract members")
    if not isinstance(data["CI_UNITS"], list) or not all(isinstance(p, str) for p in data["CI_UNITS"]):
        raise DetectError("CI_UNITS must be pattern lines")
    selected = parse("\n".join(data["CI_UNITS"]))
    if (not isinstance(data["units"], dict) or "current" in data["units"]
            or set(selected) != set(data["units"]) | {"current"}):
        raise DetectError("CI_UNITS and executable units differ")
    for name, unit in data["units"].items():
        if not isinstance(unit, dict) or set(unit) != {"project", "command", "dotnet", "lean", "cache-dependency-path"}:
            raise DetectError(f"invalid unit fields: {name}")
        if type(unit["dotnet"]) is not bool or unit["lean"] not in ("none", "toolchain", "build"):
            raise DetectError(f"invalid unit preparation: {name}")
        if not all(isinstance(unit[k], str) for k in ("project", "command", "cache-dependency-path")):
            raise DetectError(f"invalid unit strings: {name}")
        if bool(unit["project"].strip()) == bool(unit["command"].strip()):
            raise DetectError(f"set exactly one of project and command: {name}")
    current = data["current"]
    if not isinstance(current, dict) or set(current) != {"report_paths", "delta_paths", "judge_build_args"}:
        raise DetectError("invalid current fields")
    for key in ("report_paths", "delta_paths"):
        if not isinstance(current[key], str):
            raise DetectError(f"invalid current {key}")
        parse("[scope]\n" + current[key])
    if not isinstance(current["judge_build_args"], list) or not current["judge_build_args"] or not all(
            isinstance(x, str) and x for x in current["judge_build_args"]):
        raise DetectError("invalid judge recipe")
    return data, hashlib.sha256(raw).hexdigest()


def matches(units, paths):
    return {name: any(
        not any(regex.fullmatch(path) for regex in excludes)
        and any(regex.fullmatch(path) for _, regex in includes) for path in paths)
        for name, (includes, excludes) in units.items()}


def selection(data, paths, purpose):
    if purpose not in ("pull-request", "push"):
        raise DetectError(f"invalid validation purpose: {purpose}")
    if paths is None:
        raise DetectError("missing changed-path manifest")
    hits = matches(parse("\n".join(data["CI_UNITS"])), paths)
    report = hits["current"] and matches(parse("[scope]\n" + data["current"]["report_paths"]), paths)["scope"]
    source_delta = hits["current"] and matches(parse("[scope]\n" + data["current"]["delta_paths"]), paths)["scope"]
    return {"hits": hits, "report": report, "delta": report and source_delta,
            "source-delta": source_delta, "full-report": False,
            "compiled-audit": report and hits["tests-lean"],
            "source-evidence": report and hits["tests-declared-template"]}


def git(root, *args):
    result = subprocess.run(["git", "-C", str(root), *args], capture_output=True,
                            env=dict(os.environ, GIT_OPTIONAL_LOCKS="0"))
    if result.returncode:
        raise DetectError(result.stderr.decode(errors="replace").strip())
    return result.stdout


def base_commit(root, value):
    return git(root, "rev-parse", "--verify", "--end-of-options", value + "^{commit}").decode().strip()


def compare_push(repository, before, head, commits):
    """Confirm the complete set given by the event against its immutable comparison."""
    page_size = 100
    observed = []
    base = None
    for offset in range(0, max(1, len(commits)), page_size):
        result = subprocess.run([
            "gh", "api", "--method", "GET", f"repos/{repository}/compare/{before}...{head}",
            "-F", f"per_page={page_size}", "-F", f"page={offset // page_size + 1}",
            "--jq", "{base: .merge_base_commit.sha, total: .total_commits, commits: [.commits[].sha]}",
        ], capture_output=True, text=True)
        if result.returncode:
            raise DetectError(f"cannot verify pinned comparison {before}...{head}: {result.stderr.strip()}")
        page = json.loads(result.stdout)
        if page["total"] != len(commits):
            raise DetectError("truncated or inconsistent commits in push payload")
        if not isinstance(page["base"], str) or not SHA.fullmatch(page["base"]) or page["base"] == ZERO:
            raise DetectError("pinned push comparison has no merge base")
        if base is not None and base != page["base"]:
            raise DetectError("inconsistent merge base in pinned push comparison")
        base = page["base"]
        observed.extend(page["commits"])
    if len(observed) != len(commits) or set(observed) != commits or (not commits and base != head):
        raise DetectError("push payload commits differ from the pinned comparison")
    return base


def new_branch_base(root, head, event_path, ref, server, repository):
    if not event_path:
        raise DetectError("GITHUB_EVENT_PATH is required for a new branch")
    event = json.loads(Path(event_path).read_bytes(), object_pairs_hook=unique)
    if (not isinstance(event, dict) or not ref.startswith("refs/heads/") or event.get("ref") != ref
            or event.get("before") != ZERO or event.get("after") != head
            or event.get("created") is not True or event.get("deleted") is not False):
        raise DetectError("push payload does not identify the triggering branch creation")
    entries = event.get("commits")
    if not isinstance(entries, list) or len(entries) >= PUSH_COMMIT_LIMIT:
        raise DetectError("missing or potentially truncated commits in push payload")
    if "size" in event and (type(event["size"]) is not int or event["size"] != len(entries)):
        raise DetectError("push payload commit count differs from commits array")
    if "distinct_size" in event and (type(event["distinct_size"]) is not int
                                     or not 0 <= event["distinct_size"] <= len(entries)):
        raise DetectError("push payload distinct commit count exceeds commits array")
    commits = set()
    for entry in entries:
        sha = entry.get("id") if isinstance(entry, dict) else None
        if not isinstance(sha, str) or not SHA.fullmatch(sha) or sha == ZERO or sha in commits:
            raise DetectError("invalid or duplicate commit in push payload")
        commits.add(sha)
    tip = event.get("head_commit")
    if (commits and head not in commits
            or tip is not None and (not isinstance(tip, dict) or tip.get("id") != head
                                    or not commits and tip.get("distinct") is True)):
        raise DetectError("push payload commits do not match the triggering tip")

    if not server or not re.fullmatch(r"[\w.-]+/[\w.-]+", repository, flags=re.ASCII):
        raise DetectError("missing GitHub repository identity for a new branch")
    prefix = f"{server}/{repository}/"
    compare = event.get("compare")
    if compare == f"{prefix}commit/{head}":
        if not commits:
            return head
        if commits != {head}:
            raise DetectError("single-commit comparison disagrees with push payload")
        # Read the commit object because shallow Git omits boundary parents in rev-list.
        headers = git(root, "cat-file", "commit", head).split(b"\n\n", 1)[0]
        parent = next((line[7:] for line in headers.splitlines() if line.startswith(b"parent ")), None)
        if parent is None:
            raise DetectError("introduced root commit has no comparison base")
        return parent.decode("ascii")
    match = re.fullmatch(re.escape(prefix) + r"compare/([0-9a-f]{40})\.\.\." + head,
                         compare if isinstance(compare, str) else "")
    if match and match[1] != ZERO:
        before = match[1]
        if before != head:
            return compare_push(repository, before, head, commits)
        if not commits:
            return head
    raise DetectError("new branch payload has no consistent immutable comparison")


def changed_paths(root, base, head=None):
    # Name-status explicitly retains both endpoints of renames and copies.
    fields = iter(git(root, "diff", "--no-ext-diff", "--no-textconv", "--name-status", "-z",
                      "--find-renames", base, *([head] if head else []), "--").split(b"\0"))
    paths = []
    for status in fields:
        if not status:
            break
        for _ in range(2 if status.startswith((b"R", b"C")) else 1):
            paths.append(next(fields).decode("utf-8"))
    if head is None:
        # The candidate consists of cached paths (including tracked paths that
        # are missing from the worktree) and ordinary, nonignored untracked
        # paths.  In particular, an ignored file left on disk after a staged
        # removal is not part of that candidate merely because it is physical.
        candidate_list = [
            p.decode("utf-8") for p in git(
                root, "ls-files", "--cached", "--others", "--exclude-standard", "-z"
            ).split(b"\0") if p
        ]
        candidate_paths = set(candidate_list)
        untracked_list = [
            p.decode("utf-8") for p in git(
                root, "ls-files", "--others", "--exclude-standard", "-z"
            ).split(b"\0") if p
        ]
        # Tracked paths are already covered by the base-to-worktree diff;
        # inspect only ordinary untracked paths as additional candidates.
        known_paths = set(paths)
        paths.extend(path for path in untracked_list if path not in known_paths)
        known_paths.update(untracked_list)
        # The comparison base can contain paths absent from the real index.
        # Compare their actual entries too, without staging or writing objects.
        baseline = {}
        for entry in git(root, "ls-tree", "-r", "-z", base).split(b"\0"):
            if not entry:
                continue
            header, raw = entry.split(b"\t", 1)
            path = raw.decode("utf-8")
            mode, _, identity = header.split()
            baseline[path] = (mode, bytes.fromhex(identity.decode("ascii")))
        # Include baseline paths missing from the candidate, such as a tracked
        # file removed from the index while its ignored bytes remain on disk.
        paths.extend(path for path in baseline if path not in candidate_paths and path not in known_paths)
        paths = [
            path for path in paths
            if (candidate_entry(root / path) if path in candidate_paths else None)
            != baseline.get(path)
        ]
    return list(dict.fromkeys(paths))


def write_paths(path, paths):
    path.write_bytes(b"".join(p.encode() + b"\0" for p in paths))


def object_id(kind, content):
    return hashlib.sha1(kind + b" " + str(len(content)).encode() + b"\0" + content).digest()


def candidate_entry(path):
    try:
        info = path.lstat()
    except FileNotFoundError:
        return None
    if stat.S_ISLNK(info.st_mode):
        mode, content = b"120000", os.readlink(path).encode()
    elif stat.S_ISREG(info.st_mode):
        mode, content = (b"100755" if info.st_mode & 0o111 else b"100644"), path.read_bytes()
    else:
        raise DetectError(f"unsupported candidate entry: {path}")
    return mode, object_id(b"blob", content)


def candidate_identity(root):
    """Git tree identity of actual bytes without writing objects, index or refs."""
    paths = set(git(root, "ls-files", "-z", "--cached", "--others", "--exclude-standard").split(b"\0")) - {b""}
    tree = {}
    for raw in sorted(paths):
        entry = candidate_entry(root / raw.decode("utf-8"))
        if entry is None:
            continue
        node = tree
        parts = raw.split(b"/")
        for part in parts[:-1]:
            node = node.setdefault(part, {})
        node[parts[-1]] = entry
    def tree_id(node):
        entries = []
        for name, value in sorted(node.items(), key=lambda pair: pair[0] + (b"/" if isinstance(pair[1], dict) else b"")):
            mode, identity = (b"40000", tree_id(value)) if isinstance(value, dict) else value
            entries.append(mode + b" " + name + b"\0" + identity)
        return object_id(b"tree", b"".join(entries))
    return tree_id(tree).hex()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", type=Path, default=Path.cwd())
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--base")
    mode.add_argument("--new-branch", action="store_true")
    parser.add_argument("--head")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        if args.new_branch:
            if not args.head or not SHA.fullmatch(args.head) or args.head == ZERO:
                raise DetectError("new branch requires a nonzero full head SHA")
            print(new_branch_base(args.repository, args.head, os.environ.get("GITHUB_EVENT_PATH"),
                                  os.environ.get("GITHUB_REF", ""), os.environ.get("GITHUB_SERVER_URL", ""),
                                  os.environ.get("GITHUB_REPOSITORY", "")))
        else:
            if args.output is None:
                raise DetectError("path comparison requires --output")
            write_paths(args.output, changed_paths(args.repository, base_commit(args.repository, args.base), args.head))
    except (ValueError, OSError, TypeError, KeyError) as error:
        print(f"CI_RANGE_ERROR {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
