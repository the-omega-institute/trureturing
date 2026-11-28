"""Lake layouts for the trureturing consumer of the pinned omegamath package."""
from functools import cache
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import tomllib

ROOT = Path(__file__).resolve().parents[2]
UPSTREAM = (ROOT / ".lake/packages/omegamath").resolve()
UPSTREAM_SRC = UPSTREAM / "src"
BUILD = ".lake/build/omega-strict"
COMMON_SRC = ROOT / ".lake/omega-common-src"
INSPECTOR = ROOT / "tools/lean-inspector-interface"
OMEGA_ROOTS = {"OmegaInit", "OmegaMathlib", "OmegaMath", "OmegaChecks", "OmegaBuild"}


def load_helper(name, filename):
    path = UPSTREAM_SRC / "OmegaChecks" / filename
    if not path.is_file():
        raise RuntimeError(f"missing pinned omegamath helper: {path}; prepare Lake dependencies")
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


@cache
def foundation():
    return load_helper("omegamath_strict_lake", "strict_lake.py")


@cache
def upstream_portable():
    # The package scripts use sibling imports when run as executables. Bind the
    # package's sibling for this import, without replacing the host's modules.
    original = sys.modules.get("strict_lake")
    sys.modules["strict_lake"] = foundation()
    try:
        return load_helper("omegamath_portable", "portable.py")
    finally:
        if original is None:
            del sys.modules["strict_lake"]
        else:
            sys.modules["strict_lake"] = original


def write_config(name, source):
    config = ROOT / ".lake" / name
    config.parent.mkdir(exist_ok=True)
    if not config.exists() or config.read_text() != source:
        with tempfile.NamedTemporaryFile(mode="w", dir=config.parent, delete=False) as file:
            file.write(source)
        os.replace(file.name, config)
    return config


def isolate_config(directory, build_dir, label):
    source = (directory / "lakefile.toml").read_text()
    expected = tomllib.loads(source)
    if "buildDir" in expected:
        original = json.dumps(expected["buildDir"])
        source = source.replace(f"buildDir = {original}", f"buildDir = {json.dumps(str(build_dir))}")
    else:
        source = f"buildDir = {json.dumps(str(build_dir))}\n" + source
    expected["buildDir"] = str(build_dir)
    if tomllib.loads(source) != expected:
        raise ValueError(f"unable to isolate the Lake build of {directory}")
    return write_config(f"omega-{label}.toml", source)


def lake_layout(strict, with_reg, common_dir=None):
    label = "common" if common_dir is not None else "strict"
    variant = strict or common_dir is not None
    build_dir = ".lake/build/omega-common" if common_dir is not None else BUILD
    if not variant:
        build_dir = ".lake/build"
    root_build = ROOT / build_dir
    package_build = UPSTREAM / build_dir
    libraries = {"": root_build / "lib/lean",
                 **dict.fromkeys(OMEGA_ROOTS, package_build / "lib/lean")}
    configs = {}
    if variant:
        configs["trureturing"] = isolate_config(ROOT, root_build, label)
        configs["omegamath"] = (foundation().strict_config() if strict else
                                foundation().foundation_config(str(common_dir), build_dir, label))
    workspace = ROOT
    command = ["lake"]
    if with_reg:
        workspace = ROOT / "Reg"
        command.extend(["-d", workspace])
        for name, directory, namespace in [("reg", workspace, "Reg"),
                                           ("leanInspectorInterface", INSPECTOR, "LeanInformationAuditInterface")]:
            config = tomllib.loads((directory / "lakefile.toml").read_text())
            build = (directory / config["buildDir"]).resolve()
            if variant:
                build = root_build / name
                configs[name] = isolate_config(directory, build, f"{label}-{name}")
            libraries[namespace] = build / "lib/lean"
    if variant:
        name = "reg" if with_reg else "trureturing"
        command.extend(["-f", configs[name], "--no-cache"])
        manifest = json.loads((workspace / "lake-manifest.json").read_text())
        entries = [{**entry, "configFile": str(configs[entry["name"]])}
                   for entry in manifest["packages"] if entry["name"] in configs]
        if "omegamath" not in {entry["name"] for entry in entries}:
            raise RuntimeError(f"missing pinned omegamath package in {workspace / 'lake-manifest.json'}")
        overrides = write_config(f"omega-{label}-{'reg' if with_reg else 'root'}-packages.json",
                                 json.dumps({"version": manifest["version"], "packages": entries}))
        command.extend(["--packages", overrides])
    return command, libraries


def strict_build(args):
    """Use the official backend plan before compiling selected host targets strictly."""
    import portable

    lake, _ = lake_layout(True, False)
    config = tomllib.loads((ROOT / "lakefile.toml").read_text())
    package = config["name"]
    libraries = {lib["name"] for lib in config["lean_lib"]}
    executables = {exe["name"]: exe["root"] for exe in config.get("lean_exe", [])}
    selections = {}
    options = []
    remaining = iter(args)
    for arg in remaining:
        if arg.startswith("-"):
            options.append(arg)
            if arg in {"-o", "--package", "-K"}:
                value = next(remaining, None)
                if value is None:
                    return subprocess.call([*lake, "build", *args], cwd=ROOT)
                options.append(value)
        else:
            selections[arg] = set()
    if not selections:
        selections.update((target, set()) for target in config["defaultTargets"])
    for target in list(selections):
        if target in {"@", "@/", package, f"@{package}", f"@{package}/"}:
            del selections[target]
            selections.update((name, set()) for name in config["defaultTargets"])
    sources, graph = portable.import_graph("lean")
    by_path = {source.resolve(): name for name, source in sources.items()}
    for target in selections:
        base = target.partition(":")[0]
        name = base.rsplit("/", 1)[-1]
        if name in libraries:
            result = subprocess.check_output([*lake, "--json", "query", base + ":modules"], cwd=ROOT, text=True)
            selections[target].update(json.loads(result))
        elif name in executables:
            selections[target].add(executables[name])
        else:
            query = subprocess.run([*lake, "query", base + ":lean"], cwd=ROOT, text=True, capture_output=True)
            if query.returncode == 0 and (name := by_path.get((ROOT / query.stdout.strip()).resolve())):
                selections[target].add(name)
    roots = set().union(*selections.values()) & graph.keys()
    reachable = {"OmegaBuild.Commands"}
    candidates = []
    for name in portable.closure(graph, roots):
        if graph[name] & reachable:
            reachable.add(name)
            if portable.root(name) != "OmegaBuild":
                candidates.append(name)
    skipped = {}
    if candidates:
        subprocess.run(["lake", "build", *("+" + name for name in terminal_modules(graph, candidates))],
                       cwd=ROOT, check=True)
        path = portable.output("lake", "env", "printenv", "LEAN_PATH").strip()
        skipped = portable.backend_plan(path, candidates)["mathlibOnly"]
    if not skipped:
        return subprocess.call([*lake, "build", *args], cwd=ROOT)
    targets = []
    eligible = set()
    skipped_facets = []
    for target, names in selections.items():
        if names.isdisjoint(skipped):
            targets.append(target)
        else:
            if ":" in target:
                skipped_facets.append(target)
            eligible.update(name for name in portable.closure(graph, names & graph.keys())
                            if name not in skipped and portable.root(name) != "OmegaBuild")
    if skipped_facets:
        result = subprocess.run(["lake", "--no-build", "build", *skipped_facets],
                                cwd=ROOT, capture_output=True, text=True)
        if result.returncode not in (0, 3):
            sys.stderr.write(result.stdout + result.stderr)
            return result.returncode
    targets.extend("+" + name for name in terminal_modules(graph, eligible))
    return subprocess.call([*lake, "build", *options, *targets], cwd=ROOT) if targets else 0


def terminal_modules(graph, names):
    imported = {dep for name in names for dep in graph[name]}
    return sorted(set(names) - imported)


if __name__ == "__main__":
    args = sys.argv[1:]
    if "build" in args and not {"-h", "--help"}.intersection(args):
        index = args.index("build")
        if all(option.startswith("-") for option in args[:index]):
            sys.exit(strict_build([*args[:index], *args[index + 1:]]))
    lake, _ = lake_layout(True, False)
    sys.exit(subprocess.call([*lake, *args], cwd=ROOT))
