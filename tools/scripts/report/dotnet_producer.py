"""MSBuild-owned source and semantic inputs of an executable project graph."""
import hashlib
import json
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
import xml.etree.ElementTree as ET

TASK_PROJECT = pathlib.Path(__file__).with_name("JudgeSeedTask.csproj")


def project_inputs(root, project):
    paths = set()
    semantics = set()

    def add_file(path):
        path = path.resolve()
        if not path.is_file():
            raise ValueError(f"required producer input is absent: {path}")
        paths.add(path.relative_to(root))

    def query(project, *arguments):
        result = subprocess.run([
            "dotnet", "msbuild", str(root / project), "-nologo", "-noAutoResponse",
            "-nodeReuse:false", "-verbosity:quiet", "-property:Configuration=Release", *arguments,
        ], cwd=root, text=True, capture_output=True)
        if result.returncode:
            raise ValueError(f"MSBuild producer evaluation failed: {root / project}\n{result.stdout}{result.stderr}")
        return result.stdout

    add_file(root / "global.json")
    pending = [project]
    visited = set()
    properties = ("NETCoreSdkVersion", "TargetFramework", "RuntimeIdentifier", "DefineConstants",
                  "LangVersion", "Nullable", "ImplicitUsings", "Optimize", "AllowUnsafeBlocks",
                  "CheckForOverflowUnderflow", "PlatformTarget", "RestorePackagesWithLockFile",
                  "NuGetLockFilePath")
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
                    semantics.add(("external-analyzer", hashlib.sha256(path.read_bytes()).hexdigest()))
                    continue
                add_file(path)
                if kind == "ProjectReference":
                    pending.append(path.relative_to(root))
        values = evaluated["Properties"]
        for name, value in values.items():
            semantics.add((f"{project}:{name}", value.replace(str(root), "@repository")))
        if values["RestorePackagesWithLockFile"].lower() == "true":
            add_file(root / project.parent / (values["NuGetLockFilePath"] or "packages.lock.json"))
        # /preprocess records the imports MSBuild actually evaluated, including
        # property-only imports absent from MSBuildAllProjects and item metadata.
        with tempfile.TemporaryDirectory(prefix="report-msbuild-") as temporary:
            expanded = pathlib.Path(temporary) / "project.xml"
            query(project, f"-preprocess:{expanded}")
            parser = ET.XMLParser(target=ET.TreeBuilder(insert_comments=True))
            document = ET.parse(expanded, parser=parser)
        imports = 0
        for node in document.iter(ET.Comment):
            lines = (node.text or "").strip().splitlines()
            if len(lines) < 3 or set(lines[0].strip()) != {"="} or lines[0] != lines[-1]:
                continue
            path = pathlib.Path(lines[-2].strip())
            if not path.is_absolute():
                continue
            imports += 1
            path = path.resolve()
            if path.is_relative_to(root):
                if "obj" not in path.relative_to(root).parts:
                    add_file(path)
            else:
                semantics.add(("external-build-input", hashlib.sha256(path.read_bytes()).hexdigest()))
        if not imports:
            raise ValueError(f"MSBuild returned no import provenance: {project}")
    return paths, semantics


# Compiled seeds belong to the shared build producer. Report identity above
# continues to describe report production, not this optional material layer.
def seed_files(directory):
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "worktree"))
    from cache_material import files
    return files(directory)


def write_if_changed(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    if not path.is_file() or path.read_bytes() != value:
        path.write_bytes(value)


def seed_receipt(status, **fields):
    print("JUDGE_SEED " + json.dumps({"status": status, **fields}, sort_keys=True))


def solution_projects(root):
    result = subprocess.run(["dotnet", "sln", "tools/StrataLint.sln", "list"], cwd=root, text=True, capture_output=True)
    if result.returncode:
        raise ValueError(result.stdout + result.stderr)
    projects = [pathlib.Path("tools") / line.strip() for line in result.stdout.splitlines() if line.endswith(".csproj")]
    if not projects or len({path.name for path in projects}) != len(projects):
        raise ValueError("unsupported solution project identities")
    return projects


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
    projects = solution_projects(root)
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
            if manifest["root"] != str(root):
                raise ValueError("unsupported checkout relocation")
            for relative in projects:
                source = cached / "data" / (str(relative) + ".seed")
                project = root / relative
                destination = project.parent / "obj"
                shutil.rmtree(destination, ignore_errors=True)
                shutil.copytree(source.parent / "obj", destination)
                write_if_changed(state / "receipts" / (relative.name + ".seed.json"), source.read_bytes())
            task = cached / "data/build/judge-seed/task"
            if task.is_dir():
                shutil.rmtree(state / "task", ignore_errors=True)
                shutil.copytree(task, state / "task")
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
        receipt = state / "receipts" / (project.name + ".seed.json")
        if not receipt.is_file():
            continue
        try:
            previous = json.loads(receipt.read_text())
            material = compile_material(project.parent / "obj")
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
        if previous["identity"] != identity or previous["files"] != {kind: seed_files(directory / kind) for kind in ("bin", "obj")}:
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
    for arguments in (("restore", "--locked-mode"), ("build", "--no-restore", "--configuration", "Release", "--warnaserror")):
        result = subprocess.run(["dotnet", arguments[0], str(directory / "JudgeSeedTask.csproj"), *arguments[1:],
                                 "-p:ImportDirectoryBuildProps=false", "-p:ImportDirectoryBuildTargets=false"],
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
    for path in sorted(repository):
        ET.SubElement(materials, "_JudgeSeedRegisteredMaterial", Include=str(path))
    ET.SubElement(driver, "Import", Project=str(hook), Condition=enabled)
    return ET.tostring(driver, encoding="utf-8", xml_declaration=True)


def compile_context(capture):
    context = ET.parse(capture).getroot()
    root = pathlib.Path(context.get("root"))
    project = pathlib.Path(context.get("project"))
    receipt = root / "build/judge-seed/receipts" / (project.name + ".seed.json")
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


def stage_seed(root, destination):
    """Only built solution projects; no proofs, TRX, reports or stage verdicts."""
    for relative in solution_projects(root):
        project = root / relative
        receipt = root / "build/judge-seed/receipts" / (project.name + ".seed.json")
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
