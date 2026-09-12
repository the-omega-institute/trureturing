using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class InspectorSourceModeTests
{
    [Theory]
    [InlineData("push")]
    [InlineData("initial")]
    [InlineData("pr")]
    [InlineData("base-environment")]
    public void ColdPairPreparesDemandedContextAndCacheHitVerifiesIt(string mode)
    {
        using var temporary = new TemporaryDirectory();
        var result = TestProcessRunner.Run("python3", ["-c", Fixture,
            TestRepositoryLayout.FindRoot(), temporary.Path,
            Path.Combine(AppContext.BaseDirectory, "StrataLint.dll"), mode], temporary.Path,
            BoundedProcessRunner.HangDetectionBudget, 4 * 1024 * 1024);
        Console.WriteLine(Encoding.UTF8.GetString(result.StandardOutput));
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput)
            + Encoding.UTF8.GetString(result.StandardError));
    }

    // Pair, inspector, input selection, material compaction, source-context entry,
    // parser and native demand/bundle validation are copied without modification.
    // Adapters below that boundary reuse the canonically built candidate CLI and
    // supply only the declaration spool/utility metadata. Lake really builds this
    // small synthetic project and runs the current SourceContext/SourceOptions.
    private const string Fixture = """"
        import hashlib, json, os, shutil, subprocess, sys
        from pathlib import Path

        candidate, scratch, cli, mode = sys.argv[1:]
        candidate, scratch = Path(candidate), Path(scratch)
        root = scratch / "repository"
        root.mkdir()
        def write(relative, text, executable=False):
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
            if executable: path.chmod(0o755)
            return path
        paths = [
            "tools/scripts/lean-report-pair.sh",
            "tools/scripts/report/report-supervisor.sh",
            "tools/scripts/report/lean-report-input.sh",
            "tools/scripts/lib/resource-observation-lib.sh",
            "tools/scripts/worktree/lean-cache-input.sh",
            "tools/scripts/workflow/checked-ci-identity.py",
            "tools/lean-inspector/inspect.sh",
            "tools/lean-inspector/Inspector.lean",
            "tools/lean-inspector/materials.py",
            "tools/lean-inspector/source-context.sh",
            "tools/lean-inspector/source-context.py",
            "tools/lean-inspector/SourceContext.lean",
            "tools/lean-inspector/SourceOptions.lean",
            "tools/StrataLint.Cli/Commands/LeanSourceInputCommand.cs",
            "tools/StrataLint.Engine/Ledger/Admission/LeanSourceHeader.cs",
        ]
        for relative in paths:
            target = root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(candidate / relative, target)
            assert target.read_bytes() == (candidate / relative).read_bytes()
        write("lean-toolchain", (candidate / "lean-toolchain").read_text())
        write("lakefile.toml", 'name = "sourceModeFixture"\ndefaultTargets = ["D5"]\n[[lean_lib]]\nname = "D5"\nroots = ["D5.Probe"]\n')
        write("lake-manifest.json", '{"version":"1.1.0","packages":[],"name":"sourceModeFixture","lakeDir":".lake"}\n')
        write(".gitignore", ".lake/\n")
        write("Trureturing.lean", "import D5.Probe\n")
        source = "import Init\nexample : ')' =')' := by decide\n"
        write("D5/Probe.lean", source if mode == "initial" else "import Init\nexample : True := by trivial\n")
        write("tools/StrataLint.Cli/StrataLint.Cli.csproj", '<Project Sdk="Microsoft.NET.Sdk" />\n')
        write("tools/scripts/worktree/lean-cache-ensure.sh", "#!/bin/bash\nset -euo pipefail\n", True)
        write("tools/scripts/worktree/lean-cache-run.sh", '#!/bin/bash\nset -euo pipefail\nexec "$@"\n', True)
        write("Meta/FILEMAP.toml", '''schema_version = 2
        [residence_policy]
        case_id = "RESIDENCE-EPOCH"
        desired = "data-must-live-outside-tools"
        known_violation_count = 0
        status = "closed"
        [[files]]
        pattern = "Meta/LeanInputs.json"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["LeanInputManifest"]
        verified_by = ["LeanInputManifest"]
        artifact_id = "LeanInputManifest"
        runtime_disposition = "committed-source"
        ''')
        def scope(name, includes, patterns):
            return dict(name=name, includes=includes, inputs=[dict(patterns=[p], exclude=[], optional_root=None,
                min_matches=1) for p in patterns])
        write("Meta/LeanInputs.json", json.dumps(dict(schema_version=1, scopes=[
            scope("managed-modules", [], ["Trureturing.lean", "D5/**/*.lean"]),
            scope("lean-sources", ["managed-modules"], ["tools/lean-inspector/*.lean"]),
            scope("lean-config", [], ["lean-toolchain", "lakefile.toml", "lake-manifest.json"]),
            scope("producer", [], paths + ["Meta/FILEMAP.toml", "Meta/LeanInputs.json",
                "tools/scripts/worktree/lean-cache-ensure.sh", "tools/scripts/worktree/lean-cache-run.sh"]),
        ])))
        def git(*args):
            return subprocess.run(["git", *args], cwd=root, text=True, capture_output=True, check=True).stdout.strip()
        def commit(message):
            git("add", ".")
            git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                "commit", "--quiet", "--no-gpg-sign", "-m", message)
            return git("rev-parse", "HEAD")
        git("init", "--quiet")
        before = commit("P")
        if mode != "initial":
            write("D5/Probe.lean", source)
            head = commit("changed source")
            write("README.md", "later unrelated push input\n")
            head = commit("H")
        else:
            before, head = "0" * 40, before
        if mode == "pr":
            head = git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                "commit-tree", git("rev-parse", "HEAD^{tree}"), "-p", before, "-p", head, "-m", "M")
            git("update-ref", "HEAD", head)
            assert git("rev-parse", "HEAD^1") == before

        # Keep adapters outside the checked Git tree. Native commands receive the
        # fixture cwd and exact arguments; the demand validator is never stubbed.
        bin_dir = scratch / "bin"
        bin_dir.mkdir()
        calls = scratch / "calls.jsonl"
        real_dotnet, real_lake = shutil.which("dotnet"), shutil.which("lake")
        assert real_dotnet and real_lake
        def adapter(name, body):
            path = bin_dir / name
            path.write_text("#!" + sys.executable + "\n" + body)
            path.chmod(0o755)
            return str(path)
        dotnet = adapter("dotnet", '''import json, os, subprocess, sys
        from pathlib import Path
        args = sys.argv[1:]
        with open(os.environ["FIXTURE_CALLS"], "a") as f: f.write(json.dumps(["dotnet", *args]) + "\\n")
        if args[0] == "build": raise SystemExit(0)
        assert args[0] == "run" and "--" in args, args
        command = args[args.index("--") + 1:]
        if command == ["lean-utility-input"]:
            print("{}")
            raise SystemExit(0)
        assert command[0] in ("filemap-conform", "lean-source-input"), command
        os.execv(os.environ["FIXTURE_DOTNET"], [os.environ["FIXTURE_DOTNET"], os.environ["FIXTURE_CLI"], *command])
        ''')
        lake = adapter("lake", '''import json, os, subprocess, sys
        from pathlib import Path
        args = sys.argv[1:]
        with open(os.environ["FIXTURE_CALLS"], "a") as f: f.write(json.dumps(["lake", *args]) + "\\n")
        if args[:3] == ["env", "lean", "--run"] and args[3].endswith("/Inspector.lean"):
            output = Path(args[args.index("--output") + 1])
            modules = []
            start = args.index("--utility-input") + 2
            for i in range(start, len(args), 3):
                module, path, sha = args[i:i+3]
                modules.append(dict(module=module, source_path=path, source_sha256=sha,
                    imports=["Init"] if path == "D5/Probe.lean" else ["D5.Probe"], declarations=[]))
            output.write_text(json.dumps(dict(schema="stratalint-lean-inspector-spool-v1", modules=sorted(modules, key=lambda m: m["module"]))))
            raise SystemExit(0)
        os.execv(os.environ["FIXTURE_LAKE"], [os.environ["FIXTURE_LAKE"], *args])
        ''')
        env = dict(os.environ, PATH=str(bin_dir) + os.pathsep + os.environ["PATH"],
            FIXTURE_DOTNET=real_dotnet, FIXTURE_LAKE=real_lake, FIXTURE_CLI=cli, FIXTURE_CALLS=str(calls),
            STRATALINT_SOURCE_BASE="", STRATALINT_PUSH_BEFORE="", STRATALINT_PUSH_HEAD="",
            STRATALINT_REPORT_CACHE_ROOT=str(scratch / "cache"), STRATALINT_SUPERVISOR_ROOT=str(scratch / "supervisor"))
        source_args = ["--push-before", before, "--push-head", head] if mode in ("push", "initial") else ["--base", before]
        pair_args = source_args
        if mode == "base-environment":
            env["STRATALINT_SOURCE_BASE"] = before
            pair_args = []
        output = scratch / "report.json"
        command = [str(root / "tools/scripts/lean-report-pair.sh"), *pair_args,
            "--producer", str(root / "tools/lean-inspector/inspect.sh"), "--lake-bin", lake,
            "--candidate-root", str(root), "--candidate-output", str(output)]
        def run(args):
            return subprocess.run(args, cwd=root, env=env, text=True, capture_output=True)
        cold = run(command)
        assert cold.returncode == 0, ("COLD_PAIR_MUST_PUBLISH", mode, cold.returncode, cold.stdout, cold.stderr)
        assert "LEAN_REPORT_PROVENANCE side=candidate mode=produced" in cold.stdout, cold.stdout
        phase = Path(str(output) + ".logs")
        assert (phase / "source-context.exit.log").read_text().strip() == "0"
        metrics = json.loads((phase / "source-context.stdout.log").read_text().split("LEAN_SOURCE_CONTEXT ")[1])
        assert metrics["consumer_requests"] > 0 and metrics["compiler_modules"] > 0, metrics
        context_path = Path(str(output) + ".source-context.json")
        context_bytes = context_path.read_bytes()
        bundle = json.loads(context_bytes)
        assert [row["path"] for row in bundle["files"]] == ["D5/Probe.lean"], bundle
        assert bundle["files"][0]["result"]["error"] is None, bundle
        # Verification must actually reject missing demanded data, even with a
        # valid report. It runs the same production wrapper and native consumer.
        context_path.unlink()
        missing = run(["bash", str(root / "tools/lean-inspector/source-context.sh"), "verify",
            "--repository", str(root), "--report", str(output), *source_args, "--lake", lake])
        assert missing.returncode == 2 and "bundle lacks demanded context" in missing.stderr, (missing.stdout, missing.stderr)
        context_path.write_bytes(context_bytes)
        cached = run(command)
        assert cached.returncode == 0, ("CACHE_HIT_MUST_VERIFY", cached.stdout, cached.stderr)
        assert "LEAN_REPORT_PROVENANCE side=candidate mode=cached" in cached.stdout, cached.stdout
        assert context_path.read_bytes() == context_bytes
        assert not phase.exists(), "cache hit retained producer logs"
        invocations = [json.loads(line) for line in calls.read_text().splitlines()]
        assert sum(row == ["lake", "build"] for row in invocations) == 1, invocations
        assert sum(any(a.endswith("/Inspector.lean") for a in row) for row in invocations) == 1, invocations
        demands = [row[row.index("--") + 1:] for row in invocations if "lean-source-input" in row]
        assert len(demands) >= 4, demands
        assert all(row[1:1+len(source_args)] == source_args for row in demands), demands
        print(json.dumps(dict(mode=mode, before=before, head=head, cold_exit=cold.returncode,
            cache_exit=cached.returncode, missing_context_exit=missing.returncode, inspector_context=metrics,
            context_sha256=hashlib.sha256(context_bytes).hexdigest(), native_demand_calls=len(demands),
            fixture_lean_builds=1, fixture_declaration_spools=1)))
        """";
}
