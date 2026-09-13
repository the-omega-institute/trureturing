using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class InspectorSourceModeTests
{
    [Fact]
    public void LocalConsumersCarryExplicitBaseThroughPublicRoutes() => RunFixture("local-consumers");

    [Fact]
    public void CompatiblePriorReportCannotNarrowDeclaredInspection() => RunFixture("compatible-prior");

    [Theory]
    [InlineData("actions-pr")]
    [InlineData("actions-push")]
    [InlineData("actions-initial")]
    [InlineData("actions-nonancestor")]
    public void DefaultReportCallerPreparesAndTransfersContext(string mode) => RunFixture(mode);

    [Fact]
    public void FourFileTransferCarriesDemandedContext() => RunFixture("transfer");

    [Theory]
    [InlineData("push")]
    [InlineData("initial")]
    [InlineData("pr")]
    [InlineData("base-environment")]
    public void ColdPairPreparesDemandedContextAndCacheHitVerifiesIt(string mode)
        => RunFixture(mode);

    private static void RunFixture(string mode)
    {
        using var temporary = new TemporaryDirectory();
        var result = TestProcessRunner.Run("python3", ["-c", Fixture,
            TestRepositoryLayout.FindRoot(), temporary.Path,
            Path.Combine(AppContext.BaseDirectory, "StrataLint.dll"), mode, LocalConsumers, Selection], temporary.Path,
            BoundedProcessRunner.HangDetectionBudget, 4 * 1024 * 1024);
        Console.WriteLine(Encoding.UTF8.GetString(result.StandardOutput));
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput)
            + Encoding.UTF8.GetString(result.StandardError));
        if (mode.StartsWith("actions-", StringComparison.Ordinal) || mode == "transfer")
        {
            using var resultData = JsonDocument.Parse(result.StandardOutput);
            var data = resultData.RootElement;
            var root = data.GetProperty("repository").GetString()!;
            var delivered = data.GetProperty("delivered_report").GetString()!;
            var gateway = new GitRepositoryGateway(root);
            var current = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(gateway.ReadCurrent())).Snapshot;
            var before = data.GetProperty("before").GetString()!;
            var baseline = before.All(character => character == '0') ? current
                : Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(gateway.ReadRevision(before))).Snapshot;
            using var captured = new PrecomputedLeanReportSource.CapturedBundle(root, delivered);
            var context = captured.LoadSourceContext(current, baseline);
            Assert.Empty(NativeDecideSourceRule.Inspect(current, RepoPath.CreateKnown("D5/Probe.lean"), context));
            Assert.Empty(context.Requests);
            Assert.Empty(context.MalformedRows);
            Assert.Equal(2, captured.Load(current).Files.Count);
            File.Delete(delivered + ".materials.zip");
            Assert.Empty(NativeDecideSourceRule.Inspect(current, RepoPath.CreateKnown("D5/Probe.lean"),
                captured.LoadSourceContext(current, baseline)));
        }
    }

    // Pair, inspector, input selection, material compaction, source-context entry,
    // parser and native demand/bundle validation are copied without modification.
    // Adapters below that boundary reuse the canonically built candidate CLI and
    // supply only the declaration spool/utility metadata. Lake really builds this
    // small synthetic project and runs the current SourceContext/SourceOptions.
    private const string Fixture = """"
        import hashlib, json, os, shutil, subprocess, sys, zipfile
        from pathlib import Path

        candidate, scratch, cli, mode, local_consumers, selection = sys.argv[1:]
        actions = mode.startswith("actions-")
        transfer = actions or mode == "transfer"
        source_mode = mode.removeprefix("actions-")
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
            "Makefile",
            "tools/scripts/scribe.sh",
            "tools/scripts/ingest.sh",
            "tools/scripts/workflow/playbook-workflows.sh",
            "tools/scripts/workflow/math-gate.sh",
            "tools/scripts/workflow/scribe-content-checks.sh",
            "tools/scripts/report/report-consumer.sh",
            "tools/scripts/report/lean-report.sh",
            "tools/scripts/report/echo-residual-summary.sh",
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
        write("D5/Probe.lean", source if source_mode == "initial" else "import Init\nexample : True := by trivial\n")
        if mode == "compatible-prior":
            write("D5/Dependent.lean", "import Init\n")
            write("D5/Unrelated.lean", "import Init\n")
            write("Trureturing.lean", "import D5.Dependent\n")
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
            scope("scribe-projections", [], ["D5/**/*.lean"]),
            scope("scribe-describe", [], ["D5/**/*.lean"]),
            scope("scribe-markdown", [], ["D5/**/*.lean"]),
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
        if source_mode != "initial":
            write("D5/Probe.lean", source)
            head = commit("changed source")
            write("README.md", "later unrelated push input\n")
            head = commit("H")
        else:
            before, head = "0" * 40, before
        if source_mode in ("pr", "transfer"):
            pr_head = head
            head = git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                "commit-tree", git("rev-parse", "HEAD^{tree}"), "-p", before, "-p", head, "-m", "M")
            git("update-ref", "HEAD", head)
            assert git("rev-parse", "HEAD^1") == before
        if source_mode == "nonancestor":
            before = git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                "commit-tree", git("rev-parse", before + "^{tree}"), "-m", "nonancestor P")

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
        if os.environ.get("FIXTURE_PUBLIC_CONSUMERS") == "1" and command[0] in (
                "emit", "emit-values", "filemap", "dag-render", "ingest", "align-digestion-status",
                "ledger-reanchor-mathlib", "deposit-header-check", "ledger-frozen", "cover-atom", "check",
                "projections", "describe-report", "markdown-check", "echo-verify", "digest-status", "ledger-align"):
            with open(os.environ["FIXTURE_PUBLIC_RESULTS"], "a") as f:
                f.write(json.dumps(dict(command=command, source_base=os.environ.get("STRATALINT_SOURCE_BASE"),
                    push_before=os.environ.get("STRATALINT_PUSH_BEFORE"), push_head=os.environ.get("STRATALINT_PUSH_HEAD"))) + "\\n")
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
                if os.environ.get("FIXTURE_SELECTION") == "1":
                    modules[-1]["imports"] = ["D5.Dependent"] if module == "Trureturing" else ["Init"]
                    if module == "D5.Dependent":
                        modules[-1]["utility_refutation"] = dict(claim_source_path="D5/Probe.lean",
                            claim_source_sha256="sha256:" + __import__("hashlib").sha256(Path("D5/Probe.lean").read_bytes()).hexdigest(),
                            claim_gid="D5/Probe.claim", result_gid="D5/Dependent.result", is_closed_negation=True)
            output.write_text(json.dumps(dict(schema="stratalint-lean-inspector-spool-v1", modules=sorted(modules, key=lambda m: m["module"]))))
            raise SystemExit(0)
        os.execv(os.environ["FIXTURE_LAKE"], [os.environ["FIXTURE_LAKE"], *args])
        ''')
        env = dict(os.environ, PATH=str(bin_dir) + os.pathsep + os.environ["PATH"],
            FIXTURE_DOTNET=real_dotnet, FIXTURE_LAKE=real_lake, FIXTURE_CLI=cli, FIXTURE_CALLS=str(calls),
            FIXTURE_SELECTION="1" if mode == "compatible-prior" else "0",
            STRATALINT_SOURCE_BASE="", STRATALINT_PUSH_BEFORE="", STRATALINT_PUSH_HEAD="",
            STRATALINT_REPORT_CACHE_ROOT=str(scratch / "cache"), STRATALINT_SUPERVISOR_ROOT=str(scratch / "supervisor"))
        for name in tuple(env):
            if name.startswith("GITHUB_"): env.pop(name)
        source_args = ["--push-before", before, "--push-head", head] if source_mode in ("push", "initial", "nonancestor") else ["--base", before]
        pair_args = source_args
        if mode == "base-environment":
            env["STRATALINT_SOURCE_BASE"] = before
            pair_args = []
        if actions:
            event = "pull_request_target" if source_mode == "pr" else "push"
            payload = dict(before=before, after=head, created=source_mode == "initial", deleted=False)
            if event == "pull_request_target":
                payload["pull_request"] = dict(head=dict(sha=pr_head), base=dict(sha=pr_head))
                assert payload["pull_request"]["base"]["sha"] != before
            event_file = scratch / "event.json"
            event_file.write_text(json.dumps(payload))
            env.update(GITHUB_ACTIONS="true", GITHUB_EVENT_NAME=event, GITHUB_EVENT_PATH=str(event_file),
                GITHUB_SHA=pr_head if event == "pull_request_target" else head,
                GITHUB_WORKFLOW_SHA=pr_head if event == "pull_request_target" else head,
                GITHUB_WORKFLOW_REF="owner/repo/ci-fixture.yml@refs/heads/dev",
                GITHUB_RUN_ID="29", GITHUB_RUN_ATTEMPT="1", GITHUB_JOB="lean-inspect")
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
        archive_path = Path(str(output) + ".materials.zip")
        archive_bytes = archive_path.read_bytes()
        with zipfile.ZipFile(archive_path) as archive:
            statement_entries = [(info, archive.read(info)) for info in archive.infolist()
                                 if info.filename != "source-context.json"]
        with zipfile.ZipFile(archive_path, "w") as archive:
            for info, data in statement_entries: archive.writestr(info, data)
        missing = run(["bash", str(root / "tools/lean-inspector/source-context.sh"), "verify",
            "--repository", str(root), "--report", str(output), *source_args, "--lake", lake])
        assert missing.returncode == 2 and "bundle lacks demanded context" in missing.stderr, (missing.stdout, missing.stderr)
        archive_path.write_bytes(archive_bytes)
        context_path.write_bytes(context_bytes)
        cached = run(command)
        assert cached.returncode == 0, ("CACHE_HIT_MUST_VERIFY", cached.stdout, cached.stderr)
        assert "LEAN_REPORT_PROVENANCE side=candidate mode=cached" in cached.stdout, cached.stdout
        assert context_path.read_bytes() == context_bytes
        assert not phase.exists(), "cache hit retained producer logs"
        if mode == "local-consumers": exec(local_consumers)
        if mode == "compatible-prior": exec(selection)
        if transfer:
            # Literal public report/cache calls with synthetic fixed Git inputs.
            # No workflow source is read or asserted by this test.
            lake_calls_before_transfer = sum(json.loads(line)[0] == "lake" for line in calls.read_text().splitlines())
            shutil.rmtree(root / ".lake")
            env["LAKE_BIN"] = str(scratch / "unavailable-lake")
            def copy_bundle(source, destination):
                for suffix in ("", ".input.attestation", ".provenance.json", ".materials.zip"):
                    shutil.copyfile(str(source) + suffix, str(destination) + suffix)
                Path(str(destination) + ".sha256").write_text(
                    hashlib.sha256(destination.read_bytes()).hexdigest() + "  " + destination.name + "\n")
                assert not Path(str(destination) + ".source-context.json").exists()
            helper = str(root / "tools/scripts/report/lean-report-input.sh")
            staged = scratch / "staged-report.json"
            copy_bundle(output, staged)
            verified = run([helper, "verify", "--repository", str(root), "--report", str(staged),
                *([] if actions else source_args)])
            assert verified.returncode == 0, ("TRANSFER_MUST_VERIFY", verified.stdout, verified.stderr)
            delivered = scratch / "delivered-report.json"
            copy_bundle(staged, delivered)
            admission = run([real_dotnet, cli, "lean-source-input", *source_args, "--report", str(delivered)])
            assert admission.returncode == 0 and json.loads(admission.stdout)["requests"] == [], (
                "TRANSFER_MUST_SATISFY_NATIVE_CONSUMER", admission.stdout, admission.stderr)
            negative_exits = {}
            for defect in ("missing", "stale", "malformed"):
                damaged = scratch / (defect + "-report.json")
                copy_bundle(delivered, damaged)
                with zipfile.ZipFile(str(damaged) + ".materials.zip") as archive:
                    entries = [(info, archive.read(info)) for info in archive.infolist()
                               if info.filename != "source-context.json"]
                with zipfile.ZipFile(str(damaged) + ".materials.zip", "w") as archive:
                    for info, data in entries: archive.writestr(info, data)
                    if defect != "missing":
                        stale = json.loads(context_bytes)
                        stale["files"][0]["sourceSha256"] = "0" * 64
                        archive.writestr("source-context.json", "{" if defect == "malformed" else json.dumps(stale))
                rejected = run([helper, "verify", "--repository", str(root), "--report", str(damaged),
                    *([] if actions else source_args)])
                assert rejected.returncode == 2 and "LEAN_SOURCE_CONTEXT_FAILED" in rejected.stderr, (
                    "PUBLIC_VERIFY_MUST_REJECT_DEMANDED_CONTEXT", defect, rejected.stdout, rejected.stderr)
                negative_exits[defect] = rejected.returncode
            assert sum(json.loads(line)[0] == "lake" for line in calls.read_text().splitlines()) == lake_calls_before_transfer
            assert not (root / ".lake").exists(), "report transfer required Lean build artifacts"
        invocations = [json.loads(line) for line in calls.read_text().splitlines()]
        expected_builds = 2 if mode in ("local-consumers", "compatible-prior") else 1
        assert sum(row == ["lake", "build"] for row in invocations) == expected_builds, invocations
        expected_inspections = 2 if mode == "compatible-prior" else 1
        assert sum(any(a.endswith("/Inspector.lean") for a in row) for row in invocations) == expected_inspections, invocations
        demands = [row[row.index("--") + 1:] for row in invocations if "lean-source-input" in row]
        assert len(demands) >= 4, demands
        expected_sources = [source_args]
        if mode == "local-consumers": expected_sources.append(["--push-before", before, "--push-head", head])
        assert all(any(row[1:1+len(args)] == args for args in expected_sources) for row in demands), demands
        print(json.dumps(dict(mode=mode, before=before, head=head, cold_exit=cold.returncode,
            repository=str(root), delivered_report=str(scratch / "delivered-report.json"),
            cache_exit=cached.returncode, missing_context_exit=missing.returncode, inspector_context=metrics,
            context_sha256=hashlib.sha256(context_bytes).hexdigest(), native_demand_calls=len(demands),
            transfer_context_rejections=negative_exits if transfer else {},
            fixture_lean_builds=expected_builds, fixture_declaration_spools=expected_inspections)))
        """";
}
