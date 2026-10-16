"""The CI unit contract and endpoint/path adapters; no workflow interpretation."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess

from ci_detect import DetectError, parse, read_changed

CONTRACT = Path("Meta/ci-units.json")


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
    return {name: paths is None or any(
        not any(regex.fullmatch(path) for regex in excludes)
        and any(regex.fullmatch(path) for _, regex in includes) for path in paths)
        for name, (includes, excludes) in units.items()}


def selection(data, paths, purpose):
    if purpose not in ("pull-request", "push"):
        raise DetectError(f"invalid validation purpose: {purpose}")
    hits = matches(parse("\n".join(data["CI_UNITS"])), paths)
    report = hits["current"] and matches(parse("[scope]\n" + data["current"]["report_paths"]), paths)["scope"]
    # A readable, nonempty, entirely theoretical diff alone earns the fast path.
    theory = hits["current"] and paths is not None and bool(paths) and not report
    delta = hits["current"] and (theory or (purpose == "pull-request" and matches(
        parse("[scope]\n" + data["current"]["delta_paths"]), paths)["scope"]))
    return {"hits": hits, "report": report, "theory": theory, "delta": delta,
            "compiled-audit": report and hits["tests-lean"],
            "fib-regressions": report and hits.get("tests-fib", False),
            "source-evidence": report and hits["tests-declared-template"]}


def git(root, *args):
    result = subprocess.run(["git", "-C", str(root), *args], capture_output=True,
                            env=dict(os.environ, GIT_OPTIONAL_LOCKS="0"))
    if result.returncode:
        raise DetectError(result.stderr.decode(errors="replace").strip())
    return result.stdout


def base_commit(root, value):
    return git(root, "rev-parse", "--verify", "--end-of-options", value + "^{commit}").decode().strip()


def changed_paths(root, base, head=None):
    # Name-status explicitly retains both endpoints of renames and copies.
    fields = git(root, "diff", "--no-ext-diff", "--no-textconv", "--name-status", "-z",
                 "--find-renames", base, *([head] if head else []), "--").split(b"\0")
    paths = []
    while fields and fields[0]:
        status = fields.pop(0).decode("ascii")
        for _ in range(2 if status[0] in "RC" else 1):
            paths.append(fields.pop(0).decode("utf-8"))
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
        paths += [path for path in untracked_list if path not in paths]
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
        paths += [path for path in baseline if path not in candidate_paths and path not in paths]
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
    parser.add_argument("--base", required=True)
    parser.add_argument("--head")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    write_paths(args.output, changed_paths(args.repository, base_commit(args.repository, args.base), args.head))


if __name__ == "__main__":
    main()
