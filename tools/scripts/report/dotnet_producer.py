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
    from lean_actions import files
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


def prepare_seed(root):
    try:
        return _prepare_seed(root)
    except (OSError, ValueError, KeyError, TypeError, StopIteration, subprocess.SubprocessError) as error:
        # If this SDK cannot support the adapter, discard the compiled start and
        # enter the unmodified SDK build. Failure of that build remains blocking.
        for project in (root / "tools").rglob("*.csproj"):
            if {"bin", "obj"}.intersection(project.relative_to(root / "tools").parts):
                continue
            for kind in ("bin", "obj"):
                shutil.rmtree(project.parent / kind, ignore_errors=True)
        shutil.rmtree(root / "build/judge-seed/receipts", ignore_errors=True)
        seed_receipt("miss", reason=str(error))
        target = root / "build/judge-seed/seed.targets"
        write_if_changed(target, b"<Project />")
        return target


def _prepare_seed(root):
    """Install private validated material, then derive the hook from this SDK."""
    root = root.resolve()
    state = root / "build/judge-seed"
    cached = root / ".judge-binaries"
    projects = solution_projects(root)
    if cached.exists():
        try:
            manifest = json.loads((cached / "material.json").read_text())
            if manifest["root"] != str(root):
                raise ValueError("unsupported checkout relocation")
            for source in (cached / "data/tools").rglob("*.csproj.seed"):
                relative = source.relative_to(cached / "data")
                project = root / str(relative).removesuffix(".seed")
                if project.relative_to(root) not in projects:
                    continue
                destination = project.parent / "obj"
                shutil.rmtree(destination, ignore_errors=True)
                shutil.copytree(source.parent / "obj", destination)
                write_if_changed(state / "receipts" / (relative.name + ".json"), source.read_bytes())
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
    version = subprocess.check_output(["dotnet", "--version"], cwd=root, text=True).strip()
    sdks = subprocess.check_output(["dotnet", "--list-sdks"], cwd=root, text=True).splitlines()
    sdk = next(pathlib.Path(line.split("[", 1)[1].rstrip("]")) / version for line in sdks if line.startswith(version + " "))
    # Compiler bytes and the resolved host/SDK are internal compatibility inputs.
    compiler = {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                for path in sorted((sdk / "Roslyn/bincore").rglob("*")) if path.is_file()}
    compiler[str(sdk / "dotnet.runtimeconfig.json")] = hashlib.sha256((sdk / "dotnet.runtimeconfig.json").read_bytes()).hexdigest()
    for reference in ET.parse(TASK_PROJECT).findall(".//Reference"):
        path = pathlib.Path(reference.get("HintPath").replace("$(MSBuildToolsPath)", str(sdk)))
        compiler[str(path)] = hashlib.sha256(path.read_bytes()).hexdigest()
    write_if_changed(state / "compiler.json", json.dumps(compiler, sort_keys=True).encode())
    task = prepare_task(state / "task", sdk)
    target = state / "seed.targets"
    write_if_changed(target, seed_targets(root, sdk, projects, task))
    return target


def prepare_task(directory, sdk):
    """Bootstrap the SDK task using the resolved SDK, with no NuGet packages."""
    runtime = json.loads((sdk / "dotnet.runtimeconfig.json").read_text())["runtimeOptions"]
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
    properties.find("TargetFramework").text = runtime["tfm"]
    ET.SubElement(properties, "AssemblyName").text = assembly
    project.find("ItemGroup/Compile").set("Include", str(source))
    write_if_changed(directory / "JudgeSeedTask.csproj", ET.tostring(project))
    write_if_changed(directory / "packages.lock.json", json.dumps({"version": 1, "dependencies": {runtime["tfm"]: {}}}).encode())
    env = {key: value for key, value in os.environ.items() if key != "CustomAfterMicrosoftCSharpTargets"}
    for arguments in (("restore", "--locked-mode"), ("build", "--no-restore", "--configuration", "Release", "--warnaserror")):
        result = subprocess.run(["dotnet", arguments[0], str(directory / "JudgeSeedTask.csproj"), *arguments[1:],
                                 "-p:ImportDirectoryBuildProps=false", "-p:ImportDirectoryBuildTargets=false"],
                                env=env, text=True, capture_output=True)
        if result.returncode:
            raise ValueError(result.stdout + result.stderr)
    stamp.write_text(json.dumps({"identity": identity, "source_mtime_ns": source.stat().st_mtime_ns,
                                 "files": {kind: seed_files(directory / kind) for kind in ("bin", "obj")}}, sort_keys=True))
    return directory / "bin/Release" / runtime["tfm"] / (assembly + ".dll")


def seed_targets(root, sdk, projects, task):
    """Use the installed SDK's Csc wiring and incremental inputs/outputs verbatim."""
    import copy
    namespace = "{http://schemas.microsoft.com/developer/msbuild/2003}"
    compiler = ET.parse(sdk / "Roslyn/Microsoft.CSharp.Core.targets").getroot()
    for element in compiler.iter():
        element.tag = element.tag.removeprefix(namespace)
    core = next(target for target in compiler.findall("Target") if target.get("Name") == "CoreCompile")
    csc = core.find("Csc")
    if csc is None or len(core.findall("Csc")) != 1:
        raise ValueError("unsupported SDK CoreCompile target")
    document = ET.Element("Project")
    enabled = " Or ".join(f"'$(MSBuildProjectFullPath)' == '{root / project}'" for project in projects)
    enabled = "(" + enabled + ")"
    for name in ("JudgeSeedInputs", "JudgeSeedCopies"):
        ET.SubElement(document, "UsingTask", TaskName="StrataLint.JudgeSeed." + name, AssemblyFile=str(task))
    wrapper = ET.SubElement(document, "Target", Name="CoreCompile", DependsOnTargets=core.get("DependsOnTargets", ""),
                            Returns=core.get("Returns", ""))
    call = ET.SubElement(wrapper, "CallTarget", Targets="_JudgeSdkCoreCompile")
    ET.SubElement(call, "Output", TaskParameter="TargetOutputs", ItemName="CscCommandLineArgs")
    # BeforeTargets=CoreCompile hooks resolve analyzers before this call. Put the
    # SDK prelude and capture in a dependency of the incremental target: properties
    # assigned in a CallTarget caller's body do not flow into the called target.
    capture_target = ET.SubElement(document, "Target", Name="_JudgeSeedCapture")
    for child in list(core):
        if child is csc:
            break
        capture_target.append(copy.deepcopy(child))
        core.remove(child)
    paths = ET.SubElement(capture_target, "PropertyGroup")
    ET.SubElement(paths, "_JudgeSeedCaptureFile").text = "$([MSBuild]::NormalizePath('$(MSBuildProjectDirectory)', '$(IntermediateOutputPath)', 'judge-seed-inputs.xml'))"
    capture = "$(_JudgeSeedCaptureFile)"
    probe = copy.deepcopy(csc)
    probe.tag = "JudgeSeedInputs"
    for child in list(probe):
        probe.remove(child)
    probe.attrib.update(JudgeRoot=str(root), JudgeProject="$(MSBuildProjectFullPath)", JudgeCapture=capture,
                        JudgeInputs=core.get("Inputs") + ";" + str(root / "build/judge-seed/compiler.json") + ";" + str(pathlib.Path(__file__).resolve())
                            + ";" + str(pathlib.Path(__file__).with_name("JudgeSeedTask.cs").resolve()), JudgeOutputs=core.get("Outputs"),
                        JudgeCompilerOverrides="$(CscToolPath)$(CscToolExe)$(CompilerResponseFile)",
                        JudgeIntermediate="$(BaseIntermediateOutputPath)", JudgeOutput="$(BaseOutputPath)")
    capture_target.append(probe)
    probe.set("Condition", "(" + probe.get("Condition", "true") + ") And (" + enabled + ")")
    ET.SubElement(probe, "Output", TaskParameter="JudgeCaptured", PropertyName="_JudgeSeedCaptured")
    owner = pathlib.Path(__file__).resolve()
    decision = ET.SubElement(capture_target, "Exec", Condition=f"({enabled}) And '$(_JudgeSeedCaptured)' == 'true'", Command=f'python3 "{owner}" reconcile "{capture}"',
                             IgnoreExitCode="true", IgnoreStandardErrorWarningFormat="true")
    ET.SubElement(decision, "Output", TaskParameter="ExitCode", PropertyName="_JudgeSeedExit")
    force = ET.SubElement(capture_target, "PropertyGroup", Condition=f"({enabled}) And ('$(_JudgeSeedCaptured)' != 'true' Or '$(_JudgeSeedExit)' != '0')")
    ET.SubElement(force, "NonExistentFile").text = "$(IntermediateOutputPath)judge-seed-missing-output"
    core.set("Name", "_JudgeSdkCoreCompile")
    core.set("DependsOnTargets", "_JudgeSeedCapture")
    document.append(core)
    after = ET.SubElement(document, "Target", Name="_JudgeSeedSeal", AfterTargets="Build",
                          Condition=f"({enabled}) And '$(_JudgeSeedCaptured)' == 'true' And Exists('{capture}')")
    ET.SubElement(after, "Exec", Command=f'python3 "{owner}" seal "{capture}"',
                  IgnoreExitCode="true", IgnoreStandardErrorWarningFormat="true")
    common = ET.parse(sdk / "Microsoft.Common.CurrentVersion.targets").getroot()
    for element in common.iter():
        element.tag = element.tag.removeprefix(namespace)
    for name in ("_CopyFilesMarkedCopyLocal", "_CopyOutOfDateSourceItemsToOutputDirectory", "CopyFilesToOutputDirectory"):
        original = next(target for target in common.findall("Target") if target.get("Name") == name)
        before = ET.SubElement(document, "Target", Name="_Judge" + name, BeforeTargets=name, Condition=enabled)
        for copier in original.findall("Copy"):
            attributes = {key: value for key, value in copier.attrib.items()
                          if key in ("SourceFiles", "DestinationFiles", "DestinationFolder", "Condition")}
            ET.SubElement(before, "JudgeSeedCopies", attributes)
    adapter = root / "build/judge-seed/compiler.targets"
    write_if_changed(adapter, ET.tostring(document, encoding="utf-8", xml_declaration=True))
    driver = ET.Element("Project")
    paths = ET.SubElement(driver, "PropertyGroup")
    ET.SubElement(paths, "_JudgeSeedCoreTargetsPath").text = "$([MSBuild]::NormalizePath('$(CSharpCoreTargetsPath)'))"
    supported = f"'$(_JudgeSeedCoreTargetsPath)' == '{sdk / 'Roslyn/Microsoft.CSharp.Core.targets'}'"
    ET.SubElement(driver, "Import", Project=str(adapter), Condition=f"({enabled}) And ({supported})")
    fallback = ET.SubElement(driver, "Target", Name="_JudgeSeedUnsupported", BeforeTargets="PrepareForBuild",
                             Condition=f"({enabled}) And !({supported})")
    # Unsupported targets retain their normal implementation. Remove only the
    # restored per-configuration outputs, preserving the locked restore assets.
    ET.SubElement(fallback, "RemoveDir", Directories="$(OutputPath);$(IntermediateOutputPath)")
    ET.SubElement(fallback, "Delete", Files=str(root / "build/judge-seed/receipts/$(MSBuildProjectFile).seed.json"))
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
