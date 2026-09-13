"""Required script inputs and project roots from registered report producer scopes."""
import sys

# Addressing inputs must not write bytecode beside the sources.
sys.dont_write_bytecode = True

import hashlib
import json
import pathlib
from dotnet_producer import project_inputs, project_registry, unique_object


def required_path(root, value):
    if (not isinstance(value, str) or not value
            or any(character in value for character in "\\:*?[]")
            or any(ord(character) < 32 for character in value)):
        raise ValueError(f"invalid registered path: {value!r}")
    path = pathlib.PurePosixPath(value)
    if path.is_absolute() or path.as_posix() != value or ".." in path.parts:
        raise ValueError(f"registered path must be canonical and repository-relative: {value}")
    source = (root / path).resolve()
    if not source.is_relative_to(root):
        raise ValueError(f"registered input escaped repository: {value}")
    if not source.is_file():
        raise ValueError(f"required registered input is absent: {value}")
    return pathlib.Path(value)


def runtime_registration(data):
    runtime = data.get("runtime")
    if not isinstance(runtime, dict) or set(runtime) != {"lean", "python"}:
        raise ValueError("runtime must declare lean and python material lists")
    for field in ("lean", "python"):
        values = runtime[field]
        if not isinstance(values, list) or not values:
            raise ValueError(f"runtime.{field} must be a nonempty material list")
        seen = set()
        for value in values:
            if not isinstance(value, str) or not value:
                raise ValueError(f"invalid runtime.{field} material: {value!r}")
            if value in seen:
                raise ValueError(f"duplicate runtime.{field} material: {value}")
            seen.add(value)
            if field == "python":
                if value != "executable":
                    raise ValueError(f"unknown runtime.python material: {value}")
                continue
            path = pathlib.PurePosixPath(value)
            if (path.is_absolute() or path.as_posix() != value or ".." in path.parts
                    or any(character in value for character in "\\:")
                    or any(ord(character) < 32 for character in value)
                    or "**" in value or any(character in str(path.parent) for character in "*?[]")):
                raise ValueError(f"runtime.lean material must name a relative file or filename glob: {value}")
    if "bin/lean" not in runtime["lean"]:
        raise ValueError("runtime.lean is missing required declaration: bin/lean")
    return runtime


def load_scope(root, scope):
    if scope not in ("lean-report", "scribe-content"):
        raise ValueError(f"unknown producer scope registration: {scope}")
    registration = f"Meta/ReportProducers/{scope}.json"
    manifest = required_path(root, registration)
    data = json.loads((root / manifest).read_text(encoding="utf-8"), object_pairs_hook=unique_object)
    fields = {"schema", "scripts", "projects", "materials"}
    if (not isinstance(data, dict) or not fields.issubset(data)
            or set(data) - fields - ({"runtime"} if scope == "lean-report" else set())
            or data["schema"] != "report-producer-scope-v1"):
        raise ValueError(f"registration {registration}: expected report-producer-scope-v1 with schema, scripts, projects and materials")
    if "runtime" in data:
        runtime_registration(data)
    return manifest, data


def scope_inputs(root, scope):
    registration = f"Meta/ReportProducers/{scope}.json"
    try:
        manifest, data = load_scope(root, scope)
        paths = {manifest}
        registered = set()
        for field in ("scripts", "projects", "materials"):
            if not isinstance(data[field], list):
                raise ValueError(f"{field} must be a list of registered paths")
            for value in data[field]:
                path = required_path(root, value)
                if path in registered:
                    raise ValueError(f"duplicate registered input: {value}")
                if field == "projects" and path.suffix != ".csproj":
                    raise ValueError(f"registered project must be a .csproj: {value}")
                if field == "scripts" and path.suffix not in (".sh", ".py", ".lean"):
                    raise ValueError(f"registered script must be .sh, .py or .lean: {value}")
                registered.add(path)
                paths.add(path)
        semantics = {}
        registry = project_registry(root)
        for project in data["projects"]:
            inputs, values = project_inputs(root, pathlib.Path(project), registry)
            paths.update(required_path(root, path.as_posix()) for path in inputs)
            semantics.update(values)
        return paths, semantics
    except (ValueError, TypeError, KeyError, OSError) as error:
        raise ValueError(f"registration {registration}: {error}") from error


def main():
    if len(sys.argv) not in (3, 4):
        raise SystemExit("usage: producer_paths.py REPOSITORY SCOPE [SEMANTICS_OUTPUT]")
    try:
        paths, semantics = scope_inputs(pathlib.Path(sys.argv[1]).resolve(), sys.argv[2])
        if len(sys.argv) == 4:
            value = json.dumps([semantics[path] for path in sorted(semantics)], sort_keys=True, separators=(",", ":")).encode("utf-8")
            pathlib.Path(sys.argv[3]).write_text(
                hashlib.sha256(value).hexdigest() + "  @engineering-projects\n", encoding="utf-8")
        for path in sorted(paths, key=lambda path: path.as_posix().encode("utf-8")):
            print(path.as_posix())
    except (ValueError, OSError) as error:
        raise SystemExit(f"lean-report-input: {error}") from error


if __name__ == "__main__":
    main()
