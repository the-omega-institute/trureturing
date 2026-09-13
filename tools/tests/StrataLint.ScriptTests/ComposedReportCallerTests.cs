using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ComposedReportCallerTests
{
    [Fact]
    public void EmptyScribeRangeProducesNoDiagnostics() => Run("scribe-empty");

    [Theory]
    [InlineData("make", "nonancestor")]
    [InlineData("direct", "initial")]
    [InlineData("recursive", "ordinary")]
    public void PreflightPreservesPhaseIdentities(string entry, string range)
        => Run("preflight-" + entry + "-" + range);

    [Theory]
    [InlineData("land")]
    [InlineData("noalign")]
    [InlineData("addendum")]
    [InlineData("new-noalign")]
    public void HelpersForwardResolvedBase(string helper) => Run(helper);

    private static void Run(string mode)
    {
        using var temporary = new TemporaryDirectory();
        var result = TestProcessRunner.Run("python3", ["-c", InspectorSourceModeTests.Fixture,
            TestRepositoryLayout.FindRoot(), temporary.Path,
            Path.Combine(AppContext.BaseDirectory, "StrataLint.dll"), mode, "", "",
            JsonSerializer.Serialize(SourcePaths), Program], temporary.Path,
            BoundedProcessRunner.HangDetectionBudget, 4 * 1024 * 1024);
        Console.WriteLine(Encoding.UTF8.GetString(result.StandardOutput));
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
    }

    // This is fixture material, not CI ownership discovery. All source-mode,
    // Make, preflight, helper and report programs run without source edits.
    private static readonly string[] SourcePaths =
    [
        "tools/Makefile", "tools/scripts/preflight.sh",
        "tools/scripts/dotnet-build.sh", "tools/scripts/stratalint-selftest.sh",
        "tools/scripts/local-harness-gate.sh", "tools/scripts/lib/admission-base-lib.sh",
        ".github/scripts/harness-gate.sh",
        "tools/scripts/agent/land.sh",
        "tools/scripts/agent/openproblem/op-ingest-noalign.sh",
        "tools/scripts/agent/openproblem/op-addendum-ingest-v3.sh",
        "tools/scripts/agent/openproblem/op-ingest-new-noalign.sh",
        "tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs",
    ];

    // External side effects and expensive engineering/admission execution are
    // adapted. Source demand, Lean compilation, bundle production/verification,
    // Scribe impact selection and the complete public caller sequence are real.
    private const string Program = """"
        import shlex
        for name in ("BASE", "BEFORE", "MAKEFLAGS", "MFLAGS", "MAKELEVEL", "MAKEOVERRIDES",
                "STRATALINT_SCRIBE_BASE", "PREFLIGHT_DEADLINE_AT"):
            env.pop(name, None)
        real_git, real_make = shutil.which("git"), shutil.which("make")
        assert real_git and real_make
        git("config", "user.name", "Fixture")
        git("config", "user.email", "fixture@example.invalid")
        git("config", "commit.gpgsign", "false")
        write("docs/develop/theory/fixture.md", "# Fixture\n")
        write("Meta/Digestion/atoms/sha256/fixture-atom", "fixture\n")
        write("Blueprint/D5/Probe.md", "fixture mirror\n")
        write("Generated/truth-graph.v1.json", '{"truth":{"nodes":[]}}\n')
        write(".gitignore", ".lake/\n")
        admission_base = commit("B: prepared caller inputs")
        event_before = before
        write("D5/Probe.lean", source + "example : 2 = 2 := by decide\n")
        commit("changed source after B")
        write("README.md", "final unrelated commit\n")
        head = commit("H")
        if mode.endswith("nonancestor"):
            event_before = git("commit-tree", git("rev-parse", before + "^{tree}"), "-m", "nonancestor P")
            assert subprocess.run([real_git, "merge-base", "--is-ancestor", event_before, head],
                cwd=root).returncode == 1
        if mode.endswith("initial"): event_before = "0" * 40
        assert admission_base != event_before and git("rev-parse", "HEAD^1") != event_before
        git("update-ref", "refs/remotes/origin/dev", admission_base)
        branch = "lane/governance/report-caller-fixture"
        git("checkout", "--quiet", "-b", branch)
        assert not git("remote"), "fixture must not have any remote transport"
        message, addendum, subject = (scratch / name for name in ("delivery.msg", "addendum.md", "subject.txt"))
        message.write_text("synthetic caller\n")
        addendum.write_text("\nAppended fixture.\n")
        subject.write_text("fixture addendum\n")
        canonical = root / ".lake/build/stratalint/raw-lean-report.json"
        observations = scratch / "observations.jsonl"
        native_dotnet_adapter = bin_dir / "report-dotnet"
        Path(dotnet).rename(native_dotnet_adapter)
        # BASH_ENV and functions inject external commands even in scripts that
        # prepend a host toolchain PATH. No HOME/global configuration is changed.
        bootstrap = scratch / "fixture-env.sh"
        bootstrap.write_text('export PATH="$FIXTURE_BIN:$PATH"\n'
            'git() { "$FIXTURE_BIN/git" "$@"; }; export -f git\n'
            'make() { "$FIXTURE_BIN/make" "$@"; }; export -f make\n'
            'dotnet() { "$FIXTURE_BIN/dotnet" "$@"; }; export -f dotnet\n')
        common = '''import json, os, subprocess, sys
        from pathlib import Path
        args = sys.argv[1:]
        os.environ["PATH"] = os.environ["FIXTURE_BIN"] + os.pathsep + os.environ["PATH"]
        def observe(kind, command):
            with open(os.environ["FIXTURE_OBSERVATIONS"], "a") as f:
                f.write(json.dumps(dict(kind=kind, command=command, base=os.environ.get("BASE"),
                    source_base=os.environ.get("STRATALINT_SOURCE_BASE"),
                    push_before=os.environ.get("STRATALINT_PUSH_BEFORE"),
                    push_head=os.environ.get("STRATALINT_PUSH_HEAD"),
                    makeflags=os.environ.get("MAKEFLAGS"))) + "\\n")
        '''
        adapter("git", common + '''
        if args[0] == "fetch":
            observe("fetch-adapter", args)
            raise SystemExit(0)
        if args[0] == "push":
            observe("forbidden-push", args)
            raise SystemExit(99)
        if args[0] == "add" and os.environ["FIXTURE_CALLER_MODE"] == "land":
            observe("land-complete-before-stage", args)
            raise SystemExit(99)
        os.execv(os.environ["FIXTURE_GIT"], [os.environ["FIXTURE_GIT"], *args])
        ''')
        adapter("make", common + '''
        observe("make", args)
        if "pr-open" in args:
            observe("forbidden-pr", args)
            raise SystemExit(99)
        os.execv(os.environ["FIXTURE_MAKE"], [os.environ["FIXTURE_MAKE"], *args])
        ''')
        adapter("gh", common + '''
        observe("forbidden-gh", args)
        raise SystemExit(99)
        ''')
        adapter("dotnet", common + '''
        if args[0] == "--version":
            os.execv(os.environ["FIXTURE_DOTNET"], [os.environ["FIXTURE_DOTNET"], *args])
        if args[0] == "restore":
            observe("restore-adapter", args)
            raise SystemExit(0)
        if args[0] == "build":
            observe("build-adapter", args)
            if any("BannedApiCompileFailProof.csproj" in arg for arg in args):
                path = Path("tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs")
                for line, content in enumerate(path.read_text().splitlines(), 1):
                    if "// banned-api-proof" in content:
                        print(str(path) + "(" + str(line) + ",1): error RS0030: fixture banned API")
                raise SystemExit(1)
            raise SystemExit(1 if any("CompileFailProof.csproj" in arg for arg in args) else 0)
        if args[0] == "msbuild":
            target = Path.cwd() / ".lake/caller-judge.dll"
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(b"fixture dispatch marker; never executed as a binary")
            print(target)
            raise SystemExit(0)
        if args[0].endswith("caller-judge.dll"):
            command = args[1:]
            if command[0] == "check":
                observe("admission", command)
                assert command[command.index("--protected-base") + 1] == os.environ["FIXTURE_BASE"], command
                assert "--push-before" not in command and "--push-head" not in command, command
                report = command[command.index("--candidate-lean-report") + 1]
                verified = subprocess.run([os.environ["FIXTURE_DOTNET"], os.environ["FIXTURE_CLI"],
                    "lean-source-input", "--base", os.environ["FIXTURE_BASE"], "--report", report],
                    text=True, capture_output=True)
                assert verified.returncode == 0, (verified.stdout, verified.stderr)
                assert json.loads(verified.stdout)["requests"] == [], verified.stdout
                print("FIXTURE_ADMISSION_SOURCE_VERIFIED " + os.environ["FIXTURE_BASE"])
                raise SystemExit(0)
            assert command == ["filemap-conform"], command
            observe("gate-conformance-adapter", command)
            raise SystemExit(0)
        if args[0] == "run" and any("StrataLint.EngineeringScope.csproj" in arg for arg in args):
            command = args[args.index("--") + 1:]
            observe("engineering", command)
            assert command[command.index("--event") + 1] == "push", command
            assert command[command.index("--before") + 1] == os.environ["FIXTURE_BEFORE"], command
            assert command[command.index("--head") + 1] == os.environ["FIXTURE_HEAD"], command
            assert "--base" not in command, command
            subprocess.run([sys.executable, "tools/scripts/workflow/checked-ci-identity.py", "--repository", str(Path.cwd()),
                "--paths", "--planning-before", os.environ["FIXTURE_BEFORE"],
                "--planning-head", os.environ["FIXTURE_HEAD"]], check=True, stdout=subprocess.DEVNULL)
            raise SystemExit(0)
        command = args[args.index("--") + 1:] if "--" in args else []
        if command and command[0] == "worktree":
            observe("branch-validation", command)
            os.execv(os.environ["FIXTURE_DOTNET"], [os.environ["FIXTURE_DOTNET"], os.environ["FIXTURE_CLI"], *command])
        if command and command[0] in ("selftest", "projections", "describe-report", "markdown-check", "emit",
                "emit-values", "filemap", "dag-render", "ingest", "align-digestion-status", "ledger-frozen", "cover-atom"):
            observe(command[0], command)
            if command[0] in ("ingest", "align-digestion-status", "cover-atom"):
                assert command[command.index("--base") + 1] == os.environ["FIXTURE_BASE"], command
            if command[0] == "selftest": print("FIXTURE_SELFTEST_ADAPTER")
            raise SystemExit(0)
        if command and command[0] == "lean-source-input": observe("source-demand", command)
        os.execv(os.environ["FIXTURE_NATIVE_DOTNET_ADAPTER"], [os.environ["FIXTURE_NATIVE_DOTNET_ADAPTER"], *args])
        ''')
        env.update(BASH_ENV=str(bootstrap), FIXTURE_BIN=str(bin_dir), FIXTURE_GIT=real_git, FIXTURE_MAKE=real_make,
            FIXTURE_NATIVE_DOTNET_ADAPTER=str(native_dotnet_adapter), FIXTURE_OBSERVATIONS=str(observations),
            FIXTURE_BASE=admission_base, FIXTURE_BEFORE=event_before, FIXTURE_HEAD=head, FIXTURE_CALLER_MODE=mode,
            LAKE_BIN=lake, LAND_LOG_DIR=str(scratch / "land-results"))
        if mode == "scribe-empty":
            canonical.parent.mkdir(parents=True, exist_ok=True)
            canonical.write_text("{}\n")
            env.update(STRATALINT_PUSH_BEFORE=head, STRATALINT_PUSH_HEAD=head)
            command = ["/bin/bash", "tools/scripts/workflow/scribe-content-checks.sh", str(canonical)]
            expected = 0
        elif mode.startswith("preflight-"):
            entry = mode.split("-")[1]
            env.update(BASE=admission_base, BEFORE=event_before)
            command = [real_make, "--no-print-directory", "preflight", "BASE=" + admission_base, "BEFORE=" + event_before]
            if entry == "direct": command = ["/bin/bash", "tools/scripts/preflight.sh"]
            if entry == "recursive":
                outer = scratch / "outer.mk"
                outer.write_text(".PHONY: caller\ncaller:\n\t+$(MAKE) -C " + shlex.quote(str(root)) + " preflight\n")
                command = [real_make, "--no-print-directory", "-f", str(outer), "caller",
                    "BASE=" + admission_base, "BEFORE=" + event_before]
            expected = 0
        else:
            if mode == "land":
                command = ["/bin/bash", "tools/scripts/agent/land.sh", str(root), branch, str(message),
                    "--skip-preflight", "--cover", "fixture-atom", "D5/Probe.probe"]
                expected = 98
            elif mode == "noalign":
                command = ["/bin/bash", "tools/scripts/agent/openproblem/op-ingest-noalign.sh",
                    str(root), branch, str(message), "never-matched"]
                expected = 5
            elif mode == "addendum":
                command = ["/bin/bash", "tools/scripts/agent/openproblem/op-addendum-ingest-v3.sh", str(root),
                    "docs/develop/theory/fixture.md", str(addendum), str(subject), str(message), "never-matched", "1"]
                expected = 5
            else:
                command = ["/bin/bash", "tools/scripts/agent/openproblem/op-ingest-new-noalign.sh", str(root),
                    "lane/governance/new-report-caller", str(addendum), str(subject), str(message), "never-matched",
                    "docs/develop/theory/fixture.md"]
                expected = 0  # This existing wrapper prints, rather than propagates, the callee exit.
        result = subprocess.run(command, cwd=root, env=env, text=True, capture_output=True)
        rows = [json.loads(line) for line in observations.read_text().splitlines()] if observations.exists() else []
        helper_report = scratch / "land-results/flights/delivery-leanreport.log"
        report_output = helper_report.read_text() if helper_report.exists() else result.stdout
        summary = dict(mode=mode, command=command, base=admission_base, before=event_before, head=head,
            exit_code=result.returncode, stdout=result.stdout, stderr=result.stderr, report_output=report_output,
            observations=rows, source_hashes={path:hashlib.sha256((root / path).read_bytes()).hexdigest() for path in paths})
        print(json.dumps(summary), flush=True)
        assert result.returncode == expected, (mode, result.returncode, result.stdout, result.stderr, report_output)
        if mode == "scribe-empty":
            assert result.stdout == "" and result.stderr == "", (result.stdout, result.stderr)
            assert not rows, rows
            raise SystemExit(0)
        assert "LEAN_REPORT_PROVENANCE side=candidate mode=produced" in report_output, report_output
        assert not any(row["kind"].startswith("forbidden-") for row in rows), rows
        assert not git("remote"), "fixture acquired a remote transport"
        demands = [row["command"] for row in rows if row["kind"] == "source-demand"]
        assert demands, rows
        if mode.startswith("preflight-"):
            assert "[preflight] PASS" in result.stdout, result.stdout
            assert "FIXTURE_ADMISSION_SOURCE_VERIFIED " + admission_base in result.stdout
            assert len([row for row in rows if row["kind"] == "engineering"]) == 1, rows
            assert len([row for row in rows if row["kind"] == "admission"]) == 1, rows
            assert any(row["kind"] == "selftest" for row in rows), rows
            for kind in ("projections", "describe-report", "markdown-check"):
                selected = [row for row in rows if row["kind"] == kind]
                assert len(selected) == 1, (kind, rows)
                assert (selected[0]["push_before"], selected[0]["push_head"]) == (event_before, head), selected
                assert not selected[0]["source_base"], selected
            expected_sources = [["--push-before", event_before, "--push-head", head], ["--base", admission_base]]
            assert all(any(row[1:1 + len(source)] == source for source in expected_sources) for row in demands), demands
            assert all(any(row[1:1 + len(source)] == source for row in demands) for source in expected_sources), demands
        else:
            assert all(row[1:3] == ["--base", admission_base] for row in demands), demands
            assert any(row["kind"] == ("cover-atom" if mode == "land" else "ingest") for row in rows), rows
            if mode == "addendum": assert any(row["kind"] == "align-digestion-status" for row in rows), rows
            if mode == "land": assert "HALT_LAND_STAGE" in result.stdout
            else: assert "no-atom-matched" in result.stdout
            if mode == "new-noalign": assert "INGEST_EXIT=5" in result.stdout
        """";
}
