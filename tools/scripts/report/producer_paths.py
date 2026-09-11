"""Required script inputs and project roots from registered report producer scopes."""
import sys

# Addressing inputs must not write bytecode beside the sources.
sys.dont_write_bytecode = True

import hashlib
import json
import pathlib
from dotnet_producer import project_inputs


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate registration field: {key}")
        result[key] = value
    return result


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


def scope_inputs(root, scope):
    if scope not in ("lean-report", "scribe-content"):
        raise ValueError(f"unknown producer scope registration: {scope}")
    registration = f"Meta/ReportProducers/{scope}.json"
    try:
        manifest = required_path(root, registration)
        data = json.loads((root / manifest).read_text(encoding="utf-8"), object_pairs_hook=unique_object)
        if (not isinstance(data, dict) or set(data) != {"schema", "scripts", "projects"}
                or data["schema"] != "report-producer-scope-v1"):
            raise ValueError("expected report-producer-scope-v1 with schema, scripts and projects")
        paths = {manifest}
        registered = set()
        for field in ("scripts", "projects"):
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
        semantics = set()
        for project in data["projects"]:
            # Temporary migration boundary: this API still discovers project
            # Compile/import/reference inputs until its own registration layer lands.
            inputs, values = project_inputs(root, pathlib.Path(project))
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
            value = json.dumps(sorted(semantics), separators=(",", ":")).encode("utf-8")
            pathlib.Path(sys.argv[3]).write_text(
                hashlib.sha256(value).hexdigest() + "  @msbuild-semantics\n", encoding="utf-8")
        for path in sorted(paths, key=lambda path: path.as_posix().encode("utf-8")):
            print(path.as_posix())
    except (ValueError, OSError) as error:
        raise SystemExit(f"lean-report-input: {error}") from error


if __name__ == "__main__":
    main()
