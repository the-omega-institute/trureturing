"""Registered project inputs and optional compiler-verified incremental seeds."""
import hashlib
import json
import os
import pathlib
import shutil
import re
import subprocess
import sys
import xml.etree.ElementTree as ET

TASK_PROJECT = pathlib.Path(__file__).with_name("JudgeSeedTask.csproj")


PROJECT_MANIFEST = "Meta/engineering-projects.json"
PROJECT_FIELDS = {"path", "assembly", "role", "ci", "include", "exclude", "references",
                  "owner", "owned_test_assembly", "test_partition",
                  "root_namespace", "namespace_exclude", "global_namespace_exceptions",
                  "build_inputs", "execution_inputs", "execution_excludes", "execution_environment"}
TEST_ROLES = {"owned-test", "cross-cutting-test"}


class ProjectRegistrationError(ValueError):
    """Invalid declarations block before any optional seed handling."""


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate registration field: {key}")
        result[key] = value
    return result


def registered_path(value, *, pattern=False):
    if (not isinstance(value, str) or not value or value != value.strip()
            or any(character in value for character in "\\:?" + ("" if pattern else "*"))
            or any(ord(character) < 32 or ord(character) > 126 for character in value)
            or value.startswith("/") or any(part in ("", ".", "..") for part in value.split("/"))):
        raise ValueError(f"invalid registered path: {value!r}")
    return value


def source_glob(value):
    # Same declared glob language as FileMapGlob: *, ** and optional **/.
    registered_path(value, pattern=True)
    if not value.endswith(".cs"):
        raise ValueError(f"invalid registered source pattern: {value}")
    expression = re.escape(value).replace(r"\*\*/", "(?:.*/)?").replace(r"\*\*", ".*").replace(r"\*", "[^/]*")
    return re.compile(expression + r"\Z")


def registered_file(root, value):
    path = root / registered_path(value)
    if not path.resolve().is_relative_to(root) or not path.is_file():
        raise ValueError(f"registered material is absent or outside repository: {value}")
    return pathlib.Path(value)


def project_registry(root):
    """Validate coverage once, independently of any producer's fingerprint."""
    root = root.resolve()
    try:
        data = json.loads((root / PROJECT_MANIFEST).read_text(), object_pairs_hook=unique_object)
        if (not isinstance(data, dict) or set(data) != {"version", "projects", "historical_projects", "rule_build_inputs"}
                or type(data["version"]) is not int or data["version"] != 1
                or not isinstance(data["projects"], list) or not isinstance(data["historical_projects"], list)):
            raise ValueError("invalid engineering manifest schema")
        inputs = data["rule_build_inputs"]
        if not isinstance(inputs, list) or any(not isinstance(value, str) for value in inputs) or len(inputs) != len(set(inputs)):
            raise ValueError("missing or duplicate rule_build_inputs registration")
        for value in inputs:
            registered_file(root, value)
        paths = set()
        for row in data["projects"] + data["historical_projects"]:
            if not isinstance(row, dict) or set(row) != PROJECT_FIELDS:
                raise ValueError("invalid engineering project row fields")
            path = registered_path(row["path"])
            if not path.endswith(".csproj") or path in paths:
                raise ValueError(f"invalid or duplicate project registration: {path}")
            paths.add(path)
            def assembly(value):
                return (isinstance(value, str) and bool(value.strip()) and value == value.strip()
                        and not any(char in value for char in "/\\:") and all(ord(char) >= 32 for char in value))
            role = row["role"]
            if not assembly(row["assembly"]) or role not in TEST_ROLES | {"production", "test-support", "compile-fail-proof"}:
                raise ValueError(f"invalid registered assembly or role: {path}")
            if type(row["ci"]) is not bool or row["ci"] and role not in TEST_ROLES:
                raise ValueError(f"invalid registered CI execution: {path}")
            if (not assembly(row["owned_test_assembly"]) if role == "production" else row["owned_test_assembly"] is not None):
                raise ValueError(f"invalid registered owned test assembly: {path}")
            owner = row["owner"]
            if role == "owned-test":
                if not isinstance(owner, dict) or set(owner) != {"path", "assembly"} or not assembly(owner["assembly"]):
                    raise ValueError(f"invalid registered owner: {path}")
                if not registered_path(owner["path"]).endswith(".csproj"):
                    raise ValueError(f"invalid registered owner path: {path}")
            elif owner is not None:
                raise ValueError(f"unexpected registered owner: {path}")
            partition = row["test_partition"]
            valid_partition = isinstance(partition, str) and bool(partition.strip()) and partition == partition.strip()
            if (role in TEST_ROLES and not valid_partition) or (role not in TEST_ROLES and partition is not None):
                raise ValueError(f"invalid registered test partition: {path}")
            for field in ("include", "exclude", "references", "namespace_exclude", "global_namespace_exceptions"):
                values = row[field]
                if not isinstance(values, list) or any(not isinstance(value, str) for value in values) or len(values) != len(set(values)):
                    raise ValueError(f"invalid or duplicate registered {field}: {path}")
                for value in values:
                    if field == "references":
                        if not registered_path(value).endswith(".csproj"):
                            raise ValueError(f"invalid registered reference: {path}: {value}")
                    else:
                        source_glob(value)
            # Execution declarations are validated but never enter compile_projection.
            for field in ("build_inputs", "execution_inputs", "execution_excludes", "execution_environment"):
                values = row[field]
                if field != "build_inputs" and role not in TEST_ROLES:
                    if values is not None:
                        raise ValueError(f"unexpected registered {field}: {path}")
                    continue
                if not isinstance(values, list) or any(not isinstance(value, str) for value in values) or len(values) != len(set(values)):
                    raise ValueError(f"invalid or duplicate registered {field}: {path}")
                for value in values:
                    if field == "execution_environment":
                        if not re.fullmatch(r"[A-Z_][A-Z0-9_]*", value):
                            raise ValueError(f"invalid registered execution environment: {path}: {value}")
                    else:
                        registered_path(value, pattern=True)
            namespace = row["root_namespace"]
            if not isinstance(namespace, str) or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*", namespace):
                raise ValueError(f"invalid registered root_namespace: {path}")
            if any("*" in value for value in row["global_namespace_exceptions"]):
                raise ValueError(f"registered global namespace exceptions must be exact source paths: {path}")
        rows = {row["path"]: row for row in data["projects"]}
        # The index checks registration coverage; it never selects a producer.
        result = subprocess.run(["git", "-C", str(root), "ls-files", "-z", "--cached"], capture_output=True, text=True)
        if result.returncode:
            raise ValueError("tracked input inventory unavailable: " + result.stderr)
        tracked = set(result.stdout.rstrip("\0").split("\0"))
        projects = {path for path in tracked if path.endswith(".csproj")}
        if projects != set(rows):
            raise ValueError(f"project coverage: unregistered={sorted(projects - set(rows))}; absent={sorted(set(rows) - projects)}")
        assemblies, partitions, covered = set(), set(), set()
        sources = {path for path in tracked if path.endswith(".cs")}
        materials, namespaces = {}, {}
        for path, row in rows.items():
            registered_file(root, path)
            if row["assembly"] in assemblies:
                raise ValueError(f"conflicting registered assembly: {path}: {row['assembly']}")
            assemblies.add(row["assembly"])
            if row["role"] in TEST_ROLES:
                if row["test_partition"] in partitions:
                    raise ValueError(f"duplicate registered test partition: {path}")
                partitions.add(row["test_partition"])
            for reference in row["references"]:
                if reference not in rows:
                    raise ValueError(f"unregistered project reference: {path}: {reference}")
            if row["owner"] is not None:
                owner = rows.get(row["owner"]["path"])
                if owner is None or owner["assembly"] != row["owner"]["assembly"] or owner["role"] != "production" or owner["owned_test_assembly"] != row["assembly"]:
                    raise ValueError(f"conflicting registered owner: {path}")
            includes = [source_glob(pattern) for pattern in row["include"]]
            excludes = [source_glob(pattern) for pattern in row["exclude"]]
            for pattern in row["include"]:
                if "*" not in pattern and pattern not in sources:
                    raise ValueError(f"registered Compile input is absent: {path}: {pattern}")
            selected = {source for source in sources if any(glob.fullmatch(source) for glob in includes)}
            excluded = {source for source in sources if any(glob.fullmatch(source) for glob in excludes)}
            covered.update(selected | excluded)
            members = selected - excluded
            namespace_excludes = [source_glob(pattern) for pattern in row["namespace_exclude"]]
            for glob in namespace_excludes:
                if not any(glob.fullmatch(source) for source in members):
                    raise ValueError(f"registered namespace exclusion has no owned source: {path}: {glob.pattern}")
            checked = {source for source in members if not any(glob.fullmatch(source) for glob in namespace_excludes)}
            if set(row["global_namespace_exceptions"]) - checked:
                raise ValueError(f"registered global namespace exception is not a checked source: {path}")
            for source in checked:
                policy = (row["root_namespace"], source in row["global_namespace_exceptions"])
                if source in namespaces and namespaces[source] != policy:
                    raise ValueError(f"conflicting namespace registration: {source}")
                namespaces[source] = policy
            materials[path] = {registered_file(root, source) for source in members}
        if sources - covered:
            raise ValueError("unregistered engineering source: " + sorted(sources - covered)[0])
        project_closure(rows, rows)  # Reject cycles even outside the selected scope.
        return rows, materials
    except (OSError, ValueError, KeyError, TypeError) as error:
        raise ProjectRegistrationError(f"ENGINEERING_PROJECT_REGISTRATION {PROJECT_MANIFEST}: {error}") from error


def project_closure(rows, selected):
    visited, active = set(), set()
    def visit(path):
        if path not in rows:
            raise ProjectRegistrationError(f"ENGINEERING_PROJECT_REGISTRATION {PROJECT_MANIFEST}: unregistered selected project: {path}")
        if path in active:
            raise ValueError(f"cyclic registered project reference: {path}")
        if path in visited:
            return
        active.add(path)
        for reference in rows[path]["references"]:
            visit(reference)
        active.remove(path)
        visited.add(path)
    for path in selected:
        visit(str(path))
    return {path: rows[path] for path in sorted(visited)}


def compile_projection(rows):
    # Only the selected registered compilation contract belongs to producer/compiler
    # identity. Namespace and test execution/ownership policy have different consumers.
    return {path: {field: row[field] for field in ("path", "assembly", "include", "exclude", "references")}
            for path, row in rows.items()}


def project_inputs(root, project, registry=None):
    rows, sources = registry if registry is not None else project_registry(root)
    selected = project_closure(rows, [project])
    paths = {pathlib.Path(path) for path in selected}
    for path in selected:
        paths.update(sources[path])
    return paths, compile_projection(selected)


# Compiled seeds belong to the shared build producer. Report identity above
# continues to describe report production, not this optional material layer.
def seed_files(directory, **options):
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "worktree"))
    from cache_material import files
    return files(directory, **options)


def install_material(source, destination, expected):
    material = seed_files(source, expected=expected)
    shutil.rmtree(destination, ignore_errors=True)
    for item in material:
        target = destination / item["path"]
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source / item["path"], target)


def write_if_changed(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    if not path.is_file() or path.read_bytes() != value:
        path.write_bytes(value)


def seed_receipt(status, **fields):
    print("JUDGE_SEED " + json.dumps({"status": status, **fields}, sort_keys=True))


def solution_projects(root, registry=None):
    rows, _ = registry if registry is not None else project_registry(root)
    # Build participation is separate from CI test execution (including ScriptTests).
    return [pathlib.Path(path) for path in sorted(rows) if rows[path]["role"] != "compile-fail-proof"]


def receipt_path(root, project):
    return root / "build/judge-seed/receipts" / (project.relative_to(root).as_posix() + ".seed.json")


def registration_path(root, project):
    return root / "build/judge-seed/registrations" / (project.relative_to(root).as_posix() + ".json")


class SeedRegistrationError(ValueError):
    """Registration errors block preparation; cache transport errors do not."""


def seed_registration(root, sdk_root=None):
    """Read declared paths only. DOTNET_ROOT is a supplied location, not a probe."""
    def unique_fields(pairs):
        fields = {}
        for name, value in pairs:
            if name in fields:
                raise ValueError(f"duplicate JSON field: {name}")
            fields[name] = value
        return fields

    try:
        path = root / "Meta/judge-seed.json"
        registration = json.loads(path.read_text(), object_pairs_hook=unique_fields)
        if (set(registration) != {"version", "sdk_version", "target_framework", "sdk_files", "repository_files"} or
                type(registration["version"]) is not int or registration["version"] != 1):
            raise ValueError("invalid judge seed manifest schema")
        version = json.loads((root / "global.json").read_text(), object_pairs_hook=unique_fields)["sdk"]["version"]
        if not isinstance(version, str) or version != registration["sdk_version"]:
            raise ValueError("judge seed SDK registration differs from global.json")
        if not registration["sdk_files"] or registration["target_framework"] != "net10.0":
            raise ValueError("missing SDK materials or unsupported registered framework")
        location = sdk_root or os.environ.get("DOTNET_ROOT")
        if not location:
            raise ValueError("supply DOTNET_ROOT for the pinned SDK")
        sdk = pathlib.Path(location).resolve() / "sdk" / version

        def expand(base, patterns):
            if not isinstance(patterns, list) or any(not isinstance(item, str) or not item or
                    pathlib.Path(item).is_absolute() or ".." in pathlib.Path(item).parts for item in patterns):
                raise ValueError("registered material paths must be relative paths or explicit globs")
            result = set()
            seen = set()
            for pattern in patterns:
                if pattern in seen:
                    raise ValueError(f"duplicate registered material pattern: {pattern}")
                seen.add(pattern)
                matches = sorted(base.glob(pattern))
                if not matches or any(not file.is_file() for file in matches):
                    raise ValueError(f"required registered material is absent: {base / pattern}")
                result.update(matches)
            return result

        repository = expand(root, registration["repository_files"])
        declared = expand(sdk, registration["sdk_files"]) | repository
        declared.update((path, root / "global.json", TASK_PROJECT,
                         TASK_PROJECT.with_suffix(".cs"), TASK_PROJECT.with_name("JudgeSeed.targets")))
        compiler = {str(file): hashlib.sha256(file.read_bytes()).hexdigest() for file in sorted(declared)}
        return registration, sdk, repository, compiler
    except (OSError, ValueError, KeyError, TypeError) as error:
        raise SeedRegistrationError("JUDGE_SEED_REGISTRATION: " + str(error)) from error


def prepare_seed(root, sdk_root=None):
    root = root.resolve()
    # Validate before touching existing outputs. Missing registration must never
    # be converted into an optional cache miss or unregistered SDK fallback.
    registration, sdk, repository, compiler = seed_registration(root, sdk_root)
    registry = project_registry(root)
    projects = solution_projects(root, registry)
    for project in projects:
        selected = compile_projection(project_closure(registry[0], [project]))
        write_if_changed(registration_path(root, root / project),
                         json.dumps(list(selected.values()), sort_keys=True, separators=(",", ":")).encode())
    write_if_changed(root / "build/judge-seed/compiler.json", json.dumps(compiler, sort_keys=True).encode())
    try:
        return _prepare_seed(root, projects, registration, sdk, repository)
    except SeedRegistrationError:
        raise
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        for project in projects:
            for kind in ("bin", "obj"):
                shutil.rmtree(root / project.parent / kind, ignore_errors=True)
        shutil.rmtree(root / "build/judge-seed/receipts", ignore_errors=True)
        seed_receipt("miss", reason=str(error))
        target = root / "build/judge-seed/seed.targets"
        write_if_changed(target, b"<Project />")
        return target


def _prepare_seed(root, projects, registration, sdk, repository):
    """Install private validated material and the fixed registered SDK hook."""
    state = root / "build/judge-seed"
    cached = root / ".judge-binaries"
    if cached.exists():
        try:
            manifest = json.loads((cached / "material.json").read_text())
            if not isinstance(manifest, dict) or set(manifest) != {"root"} or manifest["root"] != str(root):
                raise ValueError("unsupported checkout relocation")
            for relative in projects:
                source = cached / "data" / (str(relative) + ".seed")
                project = root / relative
                destination = project.parent / "obj"
                receipt = source.read_bytes()
                install_material(source.parent / "obj", destination, json.loads(receipt)["material"])
                write_if_changed(receipt_path(root, project), receipt)
            task = cached / "data/build/judge-seed/task"
            if task.is_dir():
                shutil.rmtree(state / "task", ignore_errors=True)
                stamp = (task / "material.json").read_bytes()
                for kind in ("bin", "obj"):
                    install_material(task / kind, state / "task" / kind, json.loads(stamp)["files"][kind])
                # These two generated bootstrap inputs are checked/recreated by
                # prepare_task; retain their times when their bytes still agree.
                for name in ("JudgeSeedTask.csproj", "packages.lock.json"):
                    shutil.copy2(task / name, state / "task" / name)
                write_if_changed(state / "task/material.json", stamp)
            seed_receipt("installed")
        except (OSError, ValueError, KeyError, TypeError) as error:
            # A failed transfer can leave a partial directory. It is never a
            # usable starting point for timestamp-based MSBuild incrementality.
            for relative in projects:
                for kind in ("bin", "obj"):
                    shutil.rmtree(root / relative.parent / kind, ignore_errors=True)
            shutil.rmtree(state / "receipts", ignore_errors=True)
            seed_receipt("miss", reason=str(error))
        finally:
            shutil.rmtree(cached)
    for relative in projects:
        project = root / relative
        # Runtime directories are cheap local products of locked assets and obj.
        # Recreate them through normal MSBuild rather than transporting duplicate
        # package DLLs or trusting generated deps/runtimeconfig files by mtime.
        shutil.rmtree(project.parent / "bin", ignore_errors=True)
        receipt = receipt_path(root, project)
        if not receipt.is_file():
            continue
        try:
            previous = json.loads(receipt.read_text())
            material = seed_files(project.parent / "obj", expected=previous["material"])
            if previous["material"] != material:
                raise ValueError("local material changed")
        except (OSError, ValueError, KeyError, TypeError):
            for kind in ("bin", "obj"):
                shutil.rmtree(project.parent / kind, ignore_errors=True)
            receipt.unlink(missing_ok=True)
    task = prepare_task(state / "task", sdk, registration)
    target = state / "seed.targets"
    write_if_changed(target, seed_targets(root, sdk, projects, task, registration, repository))
    return target


def prepare_task(directory, sdk, registration):
    """Bootstrap the SDK task using the resolved SDK, with no NuGet packages."""
    framework = registration["target_framework"]
    source = pathlib.Path(__file__).with_name("JudgeSeedTask.cs").resolve()
    template = TASK_PROJECT
    identity = hashlib.sha256(source.read_bytes() + template.read_bytes() + pathlib.Path(__file__).read_bytes()
                              + (directory.parent / "compiler.json").read_bytes()).hexdigest()
    # Reused MSBuild nodes retain loaded task assemblies. A changed helper must
    # get a new assembly name even when its checkout/output directory is reused.
    assembly = "JudgeSeedTask_" + identity[:16]
    stamp = directory / "material.json"
    try:
        previous = json.loads(stamp.read_text())
        if previous["identity"] != identity or previous["files"] != {
                kind: seed_files(directory / kind, expected=previous["files"][kind]) for kind in ("bin", "obj")}:
            raise ValueError("SDK task material changed")
        if source.stat().st_mtime_ns != previous["source_mtime_ns"]:
            os.utime(source, ns=(source.stat().st_atime_ns, previous["source_mtime_ns"]))
    except (OSError, ValueError, KeyError, TypeError):
        for kind in ("bin", "obj"):
            shutil.rmtree(directory / kind, ignore_errors=True)
    project = ET.parse(template).getroot()
    properties = project.find("PropertyGroup")
    properties.find("TargetFramework").text = framework
    ET.SubElement(properties, "AssemblyName").text = assembly
    check = ET.SubElement(project, "Target", Name="JudgeSeedRegisteredSdk", BeforeTargets="PrepareForBuild")
    ET.SubElement(check, "Error", Code="JUDGE_SEED_REGISTRATION",
                  Condition=f"'$(NETCoreSdkVersion)' != '{registration['sdk_version']}'",
                  Text="Build SDK differs from the registered pinned SDK.")
    project.find("ItemGroup/Compile").set("Include", str(source))
    write_if_changed(directory / "JudgeSeedTask.csproj", ET.tostring(project))
    write_if_changed(directory / "packages.lock.json", json.dumps({"version": 1, "dependencies": {framework: {}}}).encode())
    env = {key: value for key, value in os.environ.items() if key != "CustomAfterMicrosoftCSharpTargets"}
    # These captured invocations own their MSBuild nodes through output EOF.
    for arguments in (("restore", "--locked-mode"), ("build", "--no-restore", "--configuration", "Release", "--warnaserror")):
        result = subprocess.run(["dotnet", arguments[0], str(directory / "JudgeSeedTask.csproj"), *arguments[1:],
                                 "-nr:false", "-p:ImportDirectoryBuildProps=false", "-p:ImportDirectoryBuildTargets=false"],
                                env=env, text=True, capture_output=True)
        if result.returncode:
            if "JUDGE_SEED_REGISTRATION" in result.stdout + result.stderr:
                raise SeedRegistrationError(result.stdout + result.stderr)
            raise ValueError(result.stdout + result.stderr)
    stamp.write_text(json.dumps({"identity": identity, "source_mtime_ns": source.stat().st_mtime_ns,
                                 "files": {kind: seed_files(directory / kind) for kind in ("bin", "obj")}}, sort_keys=True))
    return directory / "bin/Release" / framework / (assembly + ".dll")


def seed_targets(root, sdk, projects, task, registration, repository):
    """Bind locations to the checked-in hook; never parse installed SDK targets."""
    hook = TASK_PROJECT.with_name("JudgeSeed.targets").resolve()
    driver = ET.Element("Project")
    enabled = " Or ".join(f"'$(MSBuildProjectFullPath)' == '{root / project}'" for project in projects)
    properties = ET.SubElement(driver, "PropertyGroup")
    for name, value in {
        "JudgeSeedRoot": root, "JudgeSeedTaskAssembly": task, "JudgeSeedOwner": pathlib.Path(__file__).resolve(),
        "JudgeSeedHook": hook, "JudgeSeedSdkVersion": registration["sdk_version"],
        "JudgeSeedTargetFramework": registration["target_framework"], "JudgeSeedSdkPath": sdk,
    }.items():
        ET.SubElement(properties, name).text = str(value)
    materials = ET.SubElement(driver, "ItemGroup")
    # The generated import participates in MSBuild's incremental input check.
    # Reconcile its bytes with the receipt before recovering its previous time,
    # including when preparation recreated it in an empty judge-seed directory.
    ET.SubElement(materials, "_JudgeSeedRegisteredMaterial", Include=str(root / "build/judge-seed/seed.targets"))
    for path in sorted(repository):
        ET.SubElement(materials, "_JudgeSeedRegisteredMaterial", Include=str(path))
    for project in projects:
        group = ET.SubElement(driver, "ItemGroup", Condition=f"'$(MSBuildProjectFullPath)' == '{root / project}'")
        ET.SubElement(group, "_JudgeSeedRegisteredMaterial", Include=str(registration_path(root, root / project)))
    ET.SubElement(driver, "Import", Project=str(hook), Condition=enabled)
    return ET.tostring(driver, encoding="utf-8", xml_declaration=True)


def compile_context(capture):
    context = ET.parse(capture).getroot()
    root = pathlib.Path(context.get("root"))
    project = pathlib.Path(context.get("project"))
    receipt = receipt_path(root, project)
    outputs = [pathlib.Path(item.text) for item in context.findall("outputs/file")]
    return context, root, project, receipt, outputs


def current_compile(context):
    if context.find("unsupported") is not None:
        raise ValueError(context.findtext("unsupported"))
    inputs = {}
    for element in context.findall("inputs/file"):
        path = pathlib.Path(element.text)
        inputs[str(path)] = {"sha256": hashlib.sha256(path.read_bytes()).hexdigest(), "mtime_ns": path.stat().st_mtime_ns}
    return {"semantics": {name: context.findtext(name) for name in ("arguments", "environment", "runtime", "configuration")},
            "inputs": inputs}


def compile_material(directory):
    return [item for item in seed_files(directory) if not item["path"].endswith("judge-seed-inputs.xml")]


def reconcile(capture):
    context, root, project, receipt, outputs = compile_context(capture)
    try:
        current = current_compile(context)
        previous = json.loads(receipt.read_text())
        identity = lambda value: (value["semantics"], {path: item["sha256"] for path, item in value["inputs"].items()})
        # Restore validated every obj byte before MSBuild entered. Resolution
        # may now legitimately refresh its own caches (e.g. AssemblyReference.cache).
        # Recheck emitted material here, not those freshly derived caches.
        emitted = {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in outputs if path.is_file()}
        if identity(current) != identity(previous):
            changed = sorted(name for name in set(current["inputs"]) | set(previous["inputs"])
                             if current["inputs"].get(name, {}).get("sha256") != previous["inputs"].get(name, {}).get("sha256"))
            raise ValueError("compiler semantics or inputs changed: " + ", ".join(changed[:3]))
        if previous["outputs"] != emitted:
            raise ValueError("emitted material changed")
        for name, material in previous["inputs"].items():
            path = pathlib.Path(name)
            # Only byte-validated compiler inputs recover their prior times.
            if path.stat().st_mtime_ns != material["mtime_ns"]:
                os.utime(path, ns=(path.stat().st_atime_ns, material["mtime_ns"]))
        seed_receipt("reused", project=str(project.relative_to(root)))
        return 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        for path in outputs:
            if path.is_relative_to(project.parent) and {"bin", "obj"}.intersection(path.relative_to(project.parent).parts):
                path.unlink(missing_ok=True)
        receipt.unlink(missing_ok=True)
        seed_receipt("rebuild", project=str(project.relative_to(root)), reason=str(error))
        return 3


def seal(capture):
    context, root, project, receipt, outputs = compile_context(capture)
    try:
        value = current_compile(context)
        value["material"] = compile_material(pathlib.Path(context.get("obj")))
        value["outputs"] = {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in outputs if path.is_file()}
        write_if_changed(receipt, (json.dumps(value, sort_keys=True) + "\n").encode())
    except (OSError, ValueError, KeyError, TypeError) as error:
        receipt.unlink(missing_ok=True)
        seed_receipt("save-failed", project=str(project.relative_to(root)), reason=str(error))


def stage_seed(root, destination, registry=None):
    """Only registered build projects; no proofs, TRX, reports or stage verdicts."""
    root = root.resolve()
    for relative in solution_projects(root, registry):
        project = root / relative
        receipt = receipt_path(root, project)
        if not receipt.is_file():
            raise ValueError(f"no successful compiled seed receipt: {relative}")
        target = destination / "data" / relative.parent
        target.mkdir(parents=True, exist_ok=True)
        shutil.copy2(receipt, target / (project.name + ".seed"))
        shutil.copytree(project.parent / "obj", target / "obj", symlinks=True,
                        ignore=shutil.ignore_patterns("judge-seed-inputs.xml"))
    shutil.copytree(root / "build/judge-seed/task", destination / "data/build/judge-seed/task", symlinks=True)
    manifest = {"root": str(root.resolve())}
    (destination / "material.json").write_text(json.dumps(manifest, sort_keys=True) + "\n")


if __name__ == "__main__":
    command, path = sys.argv[1:]
    if command == "prepare":
        print(prepare_seed(pathlib.Path(path)))
    elif command == "reconcile":
        raise SystemExit(reconcile(pathlib.Path(path)))
    elif command == "seal":
        seal(pathlib.Path(path))
    else:
        raise SystemExit(2)
