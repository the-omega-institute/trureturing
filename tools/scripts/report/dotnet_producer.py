"""MSBuild-owned source and semantic inputs of an executable project graph."""
import hashlib
import json
import pathlib
import subprocess
import tempfile
import time
import xml.etree.ElementTree as ET


def project_inputs(root, project, evaluation_cache=None, *, recursive=True):
    evaluation_cache = {} if evaluation_cache is None else evaluation_cache
    paths = set()
    semantics = set()

    def add_file(path):
        path = path.resolve()
        if not path.is_file():
            raise ValueError(f"required producer input is absent: {path}")
        paths.add(path.relative_to(root))

    def query(project, *arguments):
        key = (str(project), arguments)
        if key in evaluation_cache:
            return evaluation_cache[key]
        started = time.perf_counter()
        result = subprocess.run([
            "dotnet", "msbuild", str(root / project), "-nologo", "-noAutoResponse",
            "-nodeReuse:false", "-verbosity:quiet", "-property:Configuration=Release", *arguments,
        ], cwd=root, text=True, capture_output=True)
        evaluation_cache[("_measure", "query_seconds")] = evaluation_cache.get(("_measure", "query_seconds"), 0) + time.perf_counter() - started
        if result.returncode:
            raise ValueError(f"MSBuild producer evaluation failed: {root / project}\n{result.stdout}{result.stderr}")
        evaluation_cache[key] = result.stdout
        return result.stdout

    def digest(path):
        key = (str(path), "sha256")
        if key not in evaluation_cache:
            started = time.perf_counter()
            evaluation_cache[key] = hashlib.sha256(path.read_bytes()).hexdigest()
            evaluation_cache[("_measure", "hash_seconds")] = evaluation_cache.get(("_measure", "hash_seconds"), 0) + time.perf_counter() - started
        return evaluation_cache[key]

    add_file(root / "global.json")
    pending = [project]
    visited = set()
    properties = ("NETCoreSdkVersion", "TargetFramework", "RuntimeIdentifier", "DefineConstants",
                  "LangVersion", "Nullable", "ImplicitUsings", "Optimize", "AllowUnsafeBlocks",
                  "CheckForOverflowUnderflow", "PlatformTarget", "RestorePackagesWithLockFile",
                  "NuGetLockFilePath", "AssemblyName", "TargetPath")
    while pending:
        project = pathlib.Path(pending.pop())
        if project in visited:
            continue
        visited.add(project)
        add_file(root / project)
        evaluated = json.loads(query(project,
            "-getItem:Compile,ProjectReference,AdditionalFiles,EmbeddedResource,Analyzer",
            "-getProperty:" + ",".join(properties)))
        if not evaluated["Items"]["Compile"]:
            raise ValueError(f"MSBuild returned no Compile inputs: {project}")
        for kind, items in evaluated["Items"].items():
            for item in items:
                path = pathlib.Path(item["FullPath"]).resolve()
                if kind == "Analyzer" and not path.is_relative_to(root):
                    semantics.add(("external-analyzer:" + str(path), digest(path)))
                    continue
                add_file(path)
                if kind == "ProjectReference" and recursive:
                    pending.append(path.relative_to(root))
        values = evaluated["Properties"]
        for name, value in values.items():
            semantics.add((f"{project}:{name}", value.replace(str(root), "@repository")))
        if values["RestorePackagesWithLockFile"].lower() == "true":
            add_file(root / project.parent / (values["NuGetLockFilePath"] or "packages.lock.json"))
        # /preprocess records the imports MSBuild actually evaluated, including
        # property-only imports absent from MSBuildAllProjects and item metadata.
        import_key = (str(project), "imports")
        if import_key not in evaluation_cache:
            evaluation_cache[import_key] = imported_paths(project, query)
        imported = evaluation_cache[import_key]
        imports = 0
        for value in imported:
            path = pathlib.Path(value)
            imports += 1
            path = path.resolve()
            if path.is_relative_to(root):
                if "obj" not in path.relative_to(root).parts:
                    add_file(path)
            else:
                semantics.add(("external-build-input:" + str(path), digest(path)))
        if not imports:
            raise ValueError(f"MSBuild returned no import provenance: {project}")
    return paths, semantics


def imported_paths(project, query):
        with tempfile.TemporaryDirectory(prefix="report-msbuild-") as temporary:
            expanded = pathlib.Path(temporary) / "project.xml"
            query(project, f"-preprocess:{expanded}")
            parser = ET.XMLParser(target=ET.TreeBuilder(insert_comments=True))
            document = ET.parse(expanded, parser=parser)
        result = []
        for node in document.iter(ET.Comment):
            lines = (node.text or "").strip().splitlines()
            if len(lines) < 3 or set(lines[0].strip()) != {"="} or lines[0] != lines[-1]:
                continue
            path = pathlib.Path(lines[-2].strip())
            if path.is_absolute():
                result.append(str(path))
        return result


def export_ci_inputs(root):
    """One evaluated graph per shared build; no consumer repeats MSBuild queries."""
    started = time.perf_counter()
    root = root.resolve()
    directory = root / "build/ci/build-outputs"
    cache, result = {}, []
    for inventory in sorted(directory.rglob("*.outputs")):
        project = pathlib.Path(inventory.read_text().splitlines()[0]).resolve().relative_to(root)
        paths, semantics = project_inputs(root, project, cache, recursive=False)
        evaluated = next(json.loads(value) for key, value in cache.items()
                         if key[0] == str(project) and isinstance(key[1], tuple)
                         and key[1][0].startswith("-getItem:"))
        native = inventory.with_suffix(".native").read_text().splitlines()
        # These are the actual post-build Compile/ReferencePath items, including
        # generated sources and resolved SDK/package metadata.
        items = {kind: [line.split("=", 1)[1] for line in native if line.startswith(kind + "=")]
                 for kind in ("compile", "reference", "project", "argument", "generated")}
        result.append({"project": project.as_posix(), "inputs": sorted(path.as_posix() for path in paths),
                       "semantics": [list(item) for item in sorted(semantics)],
                       "properties": evaluated["Properties"],
                       "generated_provenance": next((line.split("=", 1)[1] for line in native
                                                     if line.startswith("generated_provenance=")), "unavailable"),
                       **{("project_references" if kind == "project" else kind): value for kind, value in items.items()}})
    destination = directory / "native-inputs.json"
    serialization_started = time.perf_counter()
    destination.write_text(json.dumps(result, sort_keys=True) + "\n")
    (directory / "native-export-cost.json").write_text(json.dumps({
        "projects": len(result), "project_reference_edges": sum(len(node["project_references"]) for node in result),
        "query_seconds": cache.get(("_measure", "query_seconds"), 0),
        "external_hash_seconds": cache.get(("_measure", "hash_seconds"), 0),
        "external_hashed_files": sum(key[1] == "sha256" for key in cache),
        "serialization_seconds": time.perf_counter() - serialization_started,
        "export_seconds": time.perf_counter() - started,
        "manifest_bytes": destination.stat().st_size}, sort_keys=True) + "\n")


if __name__ == "__main__":
    import sys
    export_ci_inputs(pathlib.Path(sys.argv[1]))
