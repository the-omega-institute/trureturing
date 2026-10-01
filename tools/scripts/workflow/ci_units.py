#!/usr/bin/env python3
"""Resolve explicitly registered CI inputs using Python 3's standard library."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys


class RegistrationError(ValueError):
    pass


def object_pairs(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise RegistrationError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def read_json(path):
    try:
        return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=object_pairs)
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise RegistrationError(f"cannot read JSON {path}: {error}") from error


def exact_keys(value, keys, label):
    if not isinstance(value, dict) or set(value) != set(keys):
        raise RegistrationError(f"invalid {label} keys; expected {', '.join(sorted(keys))}")


def patterns(value, label, ordered=True, includes_only=False):
    if not isinstance(value, list):
        raise RegistrationError(f"{label} patterns must be a list")
    for pattern in value:
        if (not isinstance(pattern, str) or not pattern.strip() or pattern != pattern.strip()
                or pattern == "!" or pattern.startswith("#")
                or any(ord(char) < 32 or ord(char) == 127 for char in pattern)):
            raise RegistrationError(f"invalid {label} pattern: {pattern!r}")
        # Only `*` (crossing /) and `?` are pattern syntax: the entry matches with
        # bash and the fingerprint with an equivalent translation of these two.
        if any(char in "[]{}\\" for char in pattern):
            raise RegistrationError(f"unsupported {label} pattern syntax: {pattern!r}")
        if includes_only and pattern.startswith("!"):
            raise RegistrationError(f"{label} include cannot be an exclusion: {pattern}")
    if len(set(value)) != len(value):
        raise RegistrationError(f"duplicate {label} pattern")
    if ordered and value != sorted(value):
        raise RegistrationError(f"{label} patterns must be sorted")
    return value


def repo_path(value, label, suffix):
    if (not isinstance(value, str) or not value or value != value.strip()
            or any(ord(char) < 32 or ord(char) == 127 for char in value)
            or any(char in value for char in "\\:*?[]!")
            or PurePosixPath(value).is_absolute() or ".." in value.split("/")
            or str(PurePosixPath(value)) != value or not value.endswith(suffix)):
        raise RegistrationError(f"invalid {label} path: {value!r}")
    return value


def project_registry(root):
    manifest = read_json(root / "Meta/engineering-projects.json")
    if not isinstance(manifest, dict) or type(manifest.get("version")) is not int or manifest["version"] != 1:
        raise RegistrationError("invalid engineering project registry version")
    if not isinstance(manifest.get("projects"), list):
        raise RegistrationError("engineering projects must be a list")
    projects = {}
    for project in manifest["projects"]:
        if not isinstance(project, dict):
            raise RegistrationError("invalid project registration")
        path = repo_path(project.get("path"), "project", ".csproj")
        if path in projects:
            raise RegistrationError(f"duplicate project: {path}")
        if project.get("role") not in ("production", "owned-test", "cross-cutting-test", "test-support", "compile-fail-proof"):
            raise RegistrationError(f"invalid project role: {path}")
        patterns(project.get("include"), f"{path} include", ordered=False, includes_only=True)
        patterns(project.get("exclude"), f"{path} exclude", ordered=False, includes_only=True)
        references = project.get("references")
        if not isinstance(references, list):
            raise RegistrationError(f"invalid project references: {path}")
        for reference in references:
            repo_path(reference, "project reference", ".csproj")
        if len(set(references)) != len(references):
            raise RegistrationError(f"duplicate project references: {path}")
        projects[path] = project
    return projects


def project_closure(projects, path, closure_excludes=()):
    inputs, visited, active = set(), set(), set()

    def visit(current):
        if current not in projects:
            raise RegistrationError(f"unregistered project: {current}")
        if current in active:
            raise RegistrationError(f"cyclic project reference: {current}")
        if current in visited:
            return
        active.add(current)
        project = projects[current]
        inputs.add(current)
        inputs.add(str(PurePosixPath(current).parent / "packages.lock.json"))
        inputs.update(pattern.replace("**/", "*").replace("**", "*") for pattern in project["include"]
                      if not pattern.startswith(tuple(closure_excludes)))
        # Exclude does not narrow CI inputs: linked and removed sources remain in scope.
        for reference in project["references"]:
            visit(reference)
        active.remove(current)
        visited.add(current)

    if path is not None:
        visit(path)
    return inputs


def load_units(root):
    manifest = read_json(root / "Meta/ci-units.json")
    exact_keys(manifest, ("schema", "shared_inputs", "closure_excludes", "units", "caches"), "CI manifest")
    if manifest["schema"] != "ci-units-v1":
        raise RegistrationError("invalid CI unit schema")
    shared = patterns(manifest["shared_inputs"], "shared_inputs")
    # Registered includes under these prefixes are content that units do not
    # re-run for; a unit lists such paths in its own inputs when it needs them.
    closure_excludes = manifest["closure_excludes"]
    if (not isinstance(closure_excludes, list)
            or any(not isinstance(prefix, str) or prefix in ("", "/") or not prefix.endswith("/")
                   or "*" in prefix or prefix.startswith("/") for prefix in closure_excludes)
            or closure_excludes != sorted(set(closure_excludes))):
        raise RegistrationError("closure_excludes must be a sorted unique list of directory prefixes ending in /")
    if not isinstance(manifest["units"], list) or not manifest["units"]:
        raise RegistrationError("units must be a nonempty list")
    projects = project_registry(root)
    units, closures = {}, {}
    for unit in manifest["units"]:
        exact_keys(unit, ("id", "workflow", "project", "test", "lean", "dotnet", "inputs"), "unit")
        unit_id = unit["id"]
        if not isinstance(unit_id, str) or not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", unit_id):
            raise RegistrationError(f"invalid unit id: {unit_id!r}")
        if unit_id in units:
            raise RegistrationError(f"duplicate unit id: {unit_id}")
        workflow = repo_path(unit["workflow"], "workflow", ".yml")
        workflow_path = root / workflow
        if (not workflow.startswith(".github/workflows/") or not workflow_path.is_file()
                or not workflow_path.resolve().is_relative_to(root.resolve())):
            raise RegistrationError(f"workflow does not exist inside repository: {workflow}")
        for field in ("test", "dotnet"):
            if type(unit[field]) is not bool:
                raise RegistrationError(f"{unit_id}: {field} must be boolean")
        if unit["lean"] not in ("none", "toolchain", "build"):
            raise RegistrationError(f"{unit_id}: invalid lean mode")
        project = unit["project"]
        if project is not None:
            repo_path(project, "project", ".csproj")
        if unit["test"] and project is None:
            raise RegistrationError(f"{unit_id}: test requires project")
        if project is not None and project not in projects:
            raise RegistrationError(f"{unit_id}: unregistered project: {project}")
        if unit["test"] and projects[project]["role"] not in ("owned-test", "cross-cutting-test"):
            raise RegistrationError(f"{unit_id}: project requires a test role: {project}")
        patterns(unit["inputs"], f"{unit_id} inputs")
        if project not in closures:
            closures[project] = project_closure(projects, project, closure_excludes)
        units[unit_id] = (unit, set(shared) | {workflow} | closures[project] | set(unit["inputs"]))
    if list(units) != sorted(units):
        raise RegistrationError("units must be sorted by id")
    return units, load_caches(manifest["caches"], projects)


def load_caches(caches, projects):
    """Build caches keyed by the full compile closure of a registered project.

    closure_excludes does not apply: content compiled into the build is an input
    of its outputs even when units do not re-run for it.
    """
    if not isinstance(caches, dict):
        raise RegistrationError("caches must be an object")
    result = {}
    for name, cache in caches.items():
        if not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", name):
            raise RegistrationError(f"invalid cache name: {name!r}")
        exact_keys(cache, ("project", "inputs"), f"cache {name}")
        project = repo_path(cache["project"], "project", ".csproj")
        if project not in projects:
            raise RegistrationError(f"cache {name}: unregistered project: {project}")
        patterns(cache["inputs"], f"cache {name} inputs", includes_only=True)
        result[name] = project_closure(projects, project) | set(cache["inputs"])
    if list(result) != sorted(result):
        raise RegistrationError("caches must be sorted by name")
    return result


def pattern_regex(pattern):
    return re.compile(re.escape(pattern).replace(r"\*", ".*").replace(r"\?", "."))


def fingerprint(root, inputs):
    """sha256 over (path, blob id) of every tracked file the patterns select."""
    listing = subprocess.run(["git", "-C", str(root), "ls-files", "-s", "-z"],
                             capture_output=True, check=False)
    if listing.returncode != 0:
        raise RegistrationError("cannot list tracked files: " + listing.stderr.decode(errors="replace").strip())
    selected = [pattern_regex(pattern) for pattern in sorted(inputs)]
    digest = hashlib.sha256()
    count = 0
    for record in sorted(listing.stdout.split(b"\0")):
        if not record:
            continue
        meta, _, path_bytes = record.partition(b"\t")
        path = path_bytes.decode("utf-8", errors="strict")
        if any(regex.fullmatch(path) for regex in selected):
            digest.update(path_bytes + b"\0" + meta.split()[1] + b"\n")
            count += 1
    if count == 0:
        raise RegistrationError("cache inputs select no tracked file")
    return digest.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    resolve = commands.add_parser("resolve")
    resolve.add_argument("unit")
    resolve.add_argument("--paths-file", type=Path, required=True)
    # github.workflow_ref of the run: the calling workflow must be the one registered for the unit.
    resolve.add_argument("--workflow-ref", required=True)
    cache = commands.add_parser("fingerprint")
    cache.add_argument("name")
    args = parser.parse_args()
    try:
        root = Path(__file__).resolve().parents[3]
        units, caches = load_units(root)
        if args.command == "fingerprint":
            if args.name not in caches:
                raise RegistrationError(f"unknown cache: {args.name}")
            print(fingerprint(root, caches[args.name]))
            return 0
        if args.unit not in units:
            raise RegistrationError(f"unknown unit: {args.unit}")
        unit, inputs = units[args.unit]
        caller = re.fullmatch(r"[^/@]+/[^/@]+/(\.github/workflows/[^/@]+\.yml)@\S+", args.workflow_ref)
        if caller is None:
            raise RegistrationError(f"invalid workflow ref: {args.workflow_ref!r}")
        if caller.group(1) != unit["workflow"]:
            raise RegistrationError(
                f"workflow {caller.group(1)} does not own unit {args.unit} (registered {unit['workflow']})")
        includes = sorted(pattern for pattern in inputs if not pattern.startswith("!"))
        excludes = sorted(pattern for pattern in inputs if pattern.startswith("!"))
        args.paths_file.write_text("\n".join(includes + excludes) + "\n", encoding="utf-8")
        print(f"project={unit['project'] or ''}")
        print(f"test={str(unit['test']).lower()}")
        print(f"lean={unit['lean']}")
        print(f"dotnet={str(unit['dotnet']).lower()}")
        return 0
    except (RegistrationError, OSError, UnicodeError) as error:
        print(f"CI_UNITS_ERROR {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
