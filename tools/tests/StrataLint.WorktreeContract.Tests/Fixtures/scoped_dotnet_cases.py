"""Real scoped .NET launches; scope probes run before owned descendant cleanup."""

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import uuid


class ScopedDotnetCases:
    def scoped_dotnet_launch(self):
        fixture = Path(__file__).resolve()
        self.run_owned_command([sys.executable, "-B", fixture, self.source_root,
                                self.scoped_cli, self.root, self.scoped_mode, self.scoped_ambient],
                               self.root, phase="scoped-dotnet", timeout=120)


def exercise(source, cli, root, mode, ambient):
    source, cli, root = map(Path, (source, cli, root))
    main, target = root / "dotnet main", root / "dotnet tree"
    main.mkdir()
    environment = dict(os.environ)
    settings = {"MSBUILDDISABLENODEREUSE": "1", "DOTNET_CLI_USE_MSBUILD_SERVER": "0",
                "UseSharedCompilation": "false", "UseRazorBuildServer": "false",
                "_RazorForceBuildServer": "false"}
    for name in settings:
        environment.pop(name, None)
    if ambient == "unsafe":
        environment.update(MSBUILDDISABLENODEREUSE="0", DOTNET_CLI_USE_MSBUILD_SERVER="1",
                           UseSharedCompilation="true", UseRazorBuildServer="true",
                           _RazorForceBuildServer="true")
    # A unique compiler identity prevents borrowing an unrelated host server.
    environment["SharedCompilationId"] = uuid.uuid4().hex
    environment["_RazorBuildServerPipeName"] = uuid.uuid4().hex
    environment["DOTNET_CLI_HOME"] = str(root / "dotnet-home")
    environment["DOTNET_SKIP_FIRST_TIME_EXPERIENCE"] = "1"
    environment["DOTNET_CLI_TELEMETRY_OPTOUT"] = "1"
    serial = 0

    def run(command, cwd=main, env=environment, expected=0):
        nonlocal serial
        serial += 1
        with (root / ("dotnet-stdout-" + str(serial))).open("w+") as output, \
                (root / ("dotnet-stderr-" + str(serial))).open("w+") as errors:
            result = subprocess.run(list(map(str, command)), cwd=cwd, env=env,
                                    stdout=output, stderr=errors, timeout=90)
            output.seek(0)
            errors.seek(0)
            text, error = output.read(), errors.read()
        assert result.returncode == expected, (command, result.returncode, text, error)
        return text

    def git(*args, cwd=main):
        return run(["git", "-C", cwd, *args], cwd=cwd).strip()

    git("init", "--initial-branch=dev")
    git("config", "user.name", "Scoped Dotnet Tests")
    git("config", "user.email", "scopes@example.invalid")
    shutil.copyfile(source / "global.json", main / "global.json")
    (main / "lean-toolchain").write_text("leanprover/lean4:v4.34.1\n")
    shutil.copyfile(source / "lake-manifest.json", main / "lake-manifest.json")
    (main / ".gitignore").write_text("**/obj/\n**/bin/\n*.policy\n")
    (main / "NuGet.Config").write_text("<configuration><packageSources><clear /></packageSources></configuration>")
    tools = main / "tools"
    tools.mkdir()
    for package in ("Reg", "tools/lean-inspector-reg"):
        for name in ("lakefile.toml", "lake-manifest.json"):
            destination = main / package / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source / package / name, destination)
    projects = []
    for name in ("One", "Two", "Three"):
        project = tools / name
        project.mkdir()
        razor = mode == "razor" and name == "One"
        sdk = "Microsoft.NET.Sdk.Razor" if razor else "Microsoft.NET.Sdk"
        (project / (name + ".csproj")).write_text(
            '<Project Sdk="' + sdk + '"><PropertyGroup><TargetFramework>net10.0</TargetFramework>'
            '<RestorePackagesWithLockFile>true</RestorePackagesWithLockFile>'
            + ('<UseRazorSourceGenerator>false</UseRazorSourceGenerator>'
               '<AddRazorSupportForMvc>true</AddRazorSupportForMvc>' if razor else '')
            + '</PropertyGroup>'
            + ('<ItemGroup><FrameworkReference Include="Microsoft.AspNetCore.App" /></ItemGroup>' if razor else '')
            + '</Project>')
        (project / "Source.cs").write_text("public class " + name + " { public int Value => 42; }\n")
        if razor:
            (project / "Views").mkdir()
            (project / "Views/Index.cshtml").write_text('<p>Scoped Razor @(6 * 7)</p>\n')
        (project / "packages.lock.json").write_text('{"version":1,"dependencies":{"net10.0":{}}}\n')
        projects.append((name, str(uuid.uuid4()).upper()))
    (tools / "StrataLint.sln").write_text(
        "Microsoft Visual Studio Solution File, Format Version 12.00\n"
        + "".join('Project("{FAE04EC0-301F-11D3-BF4B-00C04F79EFBC}") = "' + name + '", "'
                  + name + '/' + name + '.csproj", "{' + identifier + '}"\nEndProject\n'
                  for name, identifier in projects)
        + "Global\nGlobalSection(SolutionConfigurationPlatforms) = preSolution\nDebug|Any CPU = Debug|Any CPU\nEndGlobalSection\n"
        + "GlobalSection(ProjectConfigurationPlatforms) = postSolution\n"
        + "".join("{" + identifier + "}.Debug|Any CPU." + suffix + " = Debug|Any CPU\n"
                  for _, identifier in projects for suffix in ("ActiveCfg", "Build.0"))
        + "EndGlobalSection\nEndGlobal\n")
    (main / "Directory.Build.targets").write_text(
        '<Project><Target Name="ObserveScopedProcess" AfterTargets="Restore;_GenerateRestoreGraphProjectEntry;CoreCompile">'
        '<WriteLinesToFile File="$(MSBuildProjectDirectory)/$(MSBuildProjectName).policy" Overwrite="true" '
        'Lines="$(MSBUILDDISABLENODEREUSE);$(DOTNET_CLI_USE_MSBUILD_SERVER);$(UseSharedCompilation);'
        '$(UseRazorBuildServer);$(_RazorForceBuildServer)" />'
        '</Target></Project>')
    git("add", ".")
    git("commit", "-m", "Scoped restore fixture")
    base = git("rev-parse", "HEAD")
    git("update-ref", "refs/remotes/origin/dev", base)
    branch = "lane/governance/scoped-dotnet"
    entry = ["dotnet", cli, "worktree", "--source", main, "--kind", "governance",
             "--name", "scoped-dotnet", "--base", base, "--path", target]
    script = source / "tools/scripts/worktree/worktree_protocol.py"
    if mode == "claim":
        token = uuid.uuid4().hex
        idle = "lane/governance/idle-" + token
        git("update-ref", "--create-reflog", "-m", "worktree-idle:" + token, "refs/heads/" + idle, base)
        git("worktree", "add", target, idle)
    elif mode == "recovery":
        token = "worktree-init:" + uuid.uuid4().hex
        git("update-ref", "--create-reflog", "-m", token, "refs/heads/" + branch, base, "0" * len(base))
        git("worktree", "add", "--no-checkout", "--lock", "--reason", token, target, branch)
    elif mode in ("build", "razor"):
        git("worktree", "add", "-b", branch, target, base)
        entry = [sys.executable, "-B", script, "--source", main, "with", "--path", target,
                 "--exclusive", "--git", "--operation", "idle-pool", "--", "dotnet", "build",
                 "tools/StrataLint.sln", "-p:RestoreLockedMode=true", "-m:2"]
    run(entry)
    # This child must see locks still held by any leaked nodes: no job-group
    # cleanup or build-server shutdown occurs before the probe.
    run([sys.executable, "-B", script, "--source", main, "with", "--path", target,
         "--exclusive", "--git", "--operation", "idle-pool", "--", "true"])
    probe = ("import fcntl,pathlib,sys; "
             "handles=[p.open('r+b') for p in pathlib.Path(sys.argv[1]).glob('*.lock')]; "
             "assert handles; "
             "[fcntl.flock(h,fcntl.LOCK_EX|fcntl.LOCK_NB) for h in handles]")
    run([sys.executable, "-c", probe, main / ".git/worktree-operations"])
    policies = [(target / "tools" / name / (name + ".policy")).read_text().splitlines()
                for name, _ in projects]
    assert policies == [list(settings.values())] * len(projects), policies
    if mode in ("build", "razor"):
        for name, _ in projects:
            assert (target / "tools" / name / "bin/Debug/net10.0" / (name + ".dll")).is_file()
        if mode == "razor":
            generated = target / "tools/One/obj/Debug/net10.0/Razor/Views/Index.cshtml.g.cs"
            assert "Scoped Razor" in generated.read_text(), generated
    else:
        receipt = json.loads(run(entry))
        assert receipt["status"] == "reused", receipt
    # Keep another idle candidate so preview must actually enter the pool.
    token = uuid.uuid4().hex
    idle = "lane/governance/idle-" + token
    git("update-ref", "--create-reflog", "-m", "worktree-idle:" + token, "refs/heads/" + idle, base)
    git("worktree", "add", root / "preview idle", idle)
    run(["dotnet", cli, "clean-lanes", "--base", "origin/dev", "--lanes-only"])
    print(json.dumps(dict(mode=mode, ambient=ambient, restored=True, scopes_reacquired=True,
                          policies=policies, preview_exit=0)))


if __name__ == "__main__":
    exercise(*sys.argv[1:])
