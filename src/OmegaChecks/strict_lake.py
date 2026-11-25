"""Run Lake with the strict foundations in a separate build directory."""
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
    if tomllib.loads(source) != expected:
        raise ValueError("strict Lake overlay differs outside its foundation source and build directories")
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


if __name__ == "__main__":
    sys.exit(subprocess.call(["lake", "-f", strict_config(), *sys.argv[1:]], cwd=ROOT))
