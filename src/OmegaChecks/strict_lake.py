"""Build eligible targets with the strict foundations. Other Lake commands inspect the raw overlay."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import tomllib

ROOT = Path(__file__).resolve().parents[2]
BUILD = ".lake/build/omega-strict"
COMMON_SRC = ROOT / ".lake/omega-common-src"
INSPECTOR = ROOT / "tools/lean-inspector-interface"


def foundation_config(source_dir, build_dir, label):
    source = (ROOT / "lakefile.toml").read_text()
    # Preserve the package, compiler options, manifest and all targets of the official build.
    # Verify the generated TOML against the intended configuration before using it.
    expected = tomllib.loads(source)
    expected["buildDir"] = build_dir
    roots = {"OmegaInit", "OmegaMathlib"}
    libraries = [lib for lib in expected["lean_lib"] if lib["name"] in roots]
    if {lib["name"] for lib in libraries} != roots:
        raise ValueError("missing strict foundation library")
    source = f'buildDir = "{build_dir}"\n' + source
    for lib in libraries:
        if lib.get("srcDir") != "src":
            raise ValueError(f"unexpected official source directory for {lib['name']}")
        lib["srcDir"] = source_dir
        header = f'name = "{lib["name"]}"\nsrcDir = '
        source = source.replace(header + '"src"', header + json.dumps(source_dir))
    if source_dir == "strict":
        # The elaborator is a build input. The compiled prelude has no Lean imports.
        omega_init = next(lib for lib in libraries if lib["name"] == "OmegaInit")
        # Build the shared library once before independent module facets load it.
        omega_init["needs"] = ["OmegaChecks.InitCompiler:shared"]
        omega_init["plugins"] = ["OmegaChecks.InitCompiler:shared"]
        source = source.replace('name = "OmegaInit"\n', 'name = "OmegaInit"\n'
                                'needs = ["OmegaChecks.InitCompiler:shared"]\nplugins = ["OmegaChecks.InitCompiler:shared"]\n')
    if tomllib.loads(source) != expected:
        raise ValueError("unexpected strict Lake configuration")
    return write_config(f"omega-{label}.toml", source)


def strict_config():
    return foundation_config("strict", BUILD, "strict")


def write_config(name, source):
    config = ROOT / ".lake" / name
    config.parent.mkdir(exist_ok=True)
    if not config.exists() or config.read_text() != source:
        with tempfile.NamedTemporaryFile(mode="w", dir=config.parent, delete=False) as f:
            f.write(source)
        os.replace(f.name, config)
    return config


def lake_layout(strict, with_reg, common_dir=None):
    label = "common" if common_dir else "strict"
    build_dir = ".lake/build/omega-common" if common_dir else BUILD
    overlay = (foundation_config(str(common_dir), build_dir, label) if common_dir else
               strict_config() if strict else None)
    command = ["lake", "-f", overlay] if overlay else ["lake"]
    libraries = {"": ROOT / (build_dir if overlay else ".lake/build") / "lib/lean"}
    if not with_reg:
        return command, libraries
    reg = ROOT / "Reg"
    command = ["lake", "-d", reg]
    configs = {}
    for name, directory, namespace in [("reg", reg, "Reg"), ("leanInspectorInterface", INSPECTOR, "LeanInformationAuditInterface")]:
        text = (directory / "lakefile.toml").read_text()
        original = tomllib.loads(text)["buildDir"]
        build = (directory / original).resolve()
        if overlay:
            build = ROOT / build_dir / name
            expected = {**tomllib.loads(text), "buildDir": str(build)}
            text = text.replace(f'buildDir = "{original}"', f'buildDir = "{build}"')
            if tomllib.loads(text) != expected:
                raise ValueError(f"unable to isolate the build of {name}")
            configs[name] = write_config(f"omega-{label}-{name}.toml", text)
        libraries[namespace] = build / "lib/lean"
    if overlay:
        # Override both local dependencies inside the genuine Reg workspace.
        # The inspector itself imports D5 and must share its backend.
        manifest = json.loads((reg / "lake-manifest.json").read_text())
        configs["trureturing"] = overlay
        entries = [{**p, "configFile": str(configs[p["name"]])} for p in manifest["packages"]
                   if p["type"] == "path"]
        overrides = write_config(f"omega-{label}-reg-packages.json",
                                 json.dumps({"version": manifest["version"], "packages": entries}))
        command.extend(["-f", configs["reg"], "--packages", overrides])
    return command, libraries


def strict_build(args):
    # Resolve Lake's own module paths and library globs, including package-qualified
    # targets. Other commands continue to expose the raw overlay for inspection.
    from check import library_mathlib_only, strict_import_graph, terminal_modules
    from portable import closure, root
    from scope import module_path

    lake = ["lake", "-f", strict_config()]
    config = tomllib.loads((ROOT / "lakefile.toml").read_text())
    package = config["name"]
    libraries = {lib["name"] for lib in config["lean_lib"]}
    executables = {exe["name"]: exe["root"] for exe in config["lean_exe"]}
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
            if query.returncode == 0:
                source = (ROOT / query.stdout.strip()).resolve()
                if source.is_relative_to(ROOT) and (name := module_path(str(source.relative_to(ROOT)))):
                    selections[target].add(name)
    all_roots = set().union(*selections.values())
    graph = strict_import_graph("lean", all_roots)
    skipped = library_mathlib_only(graph, all_roots & graph.keys())
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
            eligible.update(name for name in closure(graph, names & graph.keys())
                            if name not in skipped and root(name) != "OmegaBuild")
    if skipped_facets:
        # Have Lake validate explicit facets on the official side even when all
        # their strict jobs are skipped. --no-build exits 3 for an unbuilt facet.
        result = subprocess.run(["lake", "--no-build", "build", *skipped_facets],
                                cwd=ROOT, capture_output=True, text=True)
        if result.returncode not in (0, 3):
            sys.stderr.write(result.stdout + result.stderr)
            return result.returncode
    targets.extend("+" + name for name in terminal_modules(graph, eligible))
    return subprocess.call([*lake, "build", *options, *targets], cwd=ROOT) if targets else 0


if __name__ == "__main__":
    args = sys.argv[1:]
    if "build" in args and not {"-h", "--help"}.intersection(args):
        index = args.index("build")
        if all(option.startswith("-") for option in args[:index]):
            sys.exit(strict_build([*args[:index], *args[index + 1:]]))
    sys.exit(subprocess.call(["lake", "-f", strict_config(), *args], cwd=ROOT))
