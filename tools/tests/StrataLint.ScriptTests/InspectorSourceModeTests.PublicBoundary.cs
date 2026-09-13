using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class InspectorSourceModeTests
{
    [Fact]
    public void PublicReportEntryValidatesExplicitSourceIdentity()
    {
        using var temporary = new TemporaryDirectory();
        var result = TestProcessRunner.Run("python3", ["-c", PublicBoundary,
            TestRepositoryLayout.FindRoot(), temporary.Path], temporary.Path,
            BoundedProcessRunner.HangDetectionBudget, 4 * 1024 * 1024);
        Console.WriteLine(Encoding.UTF8.GetString(result.StandardOutput));
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput)
            + Encoding.UTF8.GetString(result.StandardError));
    }

    // Actual public Make/script/pair/identity programs. The address adapter is
    // reached only after identity validation and deliberately prevents a build.
    private const string PublicBoundary = """
        import hashlib, json, os, shutil, subprocess, sys
        from pathlib import Path

        candidate, scratch = map(Path, sys.argv[1:])
        root = scratch / "repository"
        root.mkdir()
        paths = ["Makefile", "tools/scripts/report/lean-report.sh",
            "tools/scripts/lean-report-pair.sh", "tools/scripts/report/report-supervisor.sh",
            "tools/scripts/workflow/checked-ci-identity.py", "tools/lean-inspector/inspect.sh",
            "tools/lean-inspector/Inspector.lean"]
        sources = []
        for relative in paths:
            target = root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(candidate / relative, target)
            data = target.read_bytes()
            assert data == (candidate / relative).read_bytes()
            sources.append(dict(path=relative, sha256=hashlib.sha256(data).hexdigest(),
                mode=oct(target.stat().st_mode & 0o777)))
        adapter = root / "tools/scripts/report/lean-report-input.sh"
        adapter.write_text("#!/bin/bash\necho POST_IDENTITY_ADDRESS_REACHED >&2\nexit 91\n")
        adapter.chmod(0o755)
        environment = {k:v for k,v in os.environ.items()
            if not k.startswith(("GITHUB_", "STRATALINT_", "GIT_"))
            and k not in ("BASE", "MAKEFLAGS", "MFLAGS", "MAKELEVEL", "MAKEOVERRIDES")}
        environment.update(CI="true", LAKE_BIN="/usr/bin/true")
        def git(*args):
            return subprocess.run(["git", "-c", "user.name=Public source fixture",
                "-c", "user.email=fixture@example.invalid", "-c", "commit.gpgsign=false", *args],
                cwd=root, env=environment, check=True, text=True, capture_output=True).stdout.strip()
        git("init", "--quiet")
        git("add", ".")
        git("commit", "--quiet", "-m", "P")
        before = git("rev-parse", "HEAD")
        (root / "input.txt").write_text("candidate\n")
        git("add", ".")
        git("commit", "--quiet", "-m", "H")
        head = git("rev-parse", "HEAD")
        # Make's implicit default would resolve here, so absence cannot pass
        # just because a fixture happens to lack origin/dev.
        git("update-ref", "refs/remotes/origin/dev", before)
        nonancestor = git("commit-tree", git("rev-parse", "HEAD^{tree}"), "-m", "independent P")
        assert subprocess.run(["git", "merge-base", "--is-ancestor", nonancestor, head],
            cwd=root, env=environment).returncode == 1
        zero = "0" * 40
        push = dict(STRATALINT_PUSH_BEFORE=before, STRATALINT_PUSH_HEAD=head)
        empty_slots = dict(STRATALINT_SOURCE_BASE="", STRATALINT_PUSH_BEFORE="", STRATALINT_PUSH_HEAD="")
        script = ["bash", "tools/scripts/report/lean-report.sh"]
        make = ["make", "--no-print-directory", "lean-report"]
        cases = []
        def case(name, argv, updates=None, accepted=False):
            cases.append((name, argv, updates or {}, accepted))
        for entry, command in (("script", script), ("make", make)):
            def base(value):
                return [*command, value if entry == "script" else "BASE=" + value]
            case(entry + "-missing" + ("-with-default-ref-present" if entry == "make" else ""), command)
            case(entry + "-empty", base(""))
            case(entry + "-zero", base(zero))
            case(entry + "-base", base(before), accepted=True)
            case(entry + "-head-base", base(head), accepted=True)
            case(entry + "-BASE-environment", command, {"BASE":before}, True)
            case(entry + "-empty-BASE-environment", command, {"BASE":""})
            case(entry + "-source-environment", command, {"STRATALINT_SOURCE_BASE":before}, True)
            case(entry + "-empty-source-environment", command, {"STRATALINT_SOURCE_BASE":""})
            case(entry + "-base-empty-inactive-slots", base(before), empty_slots, True)
            case(entry + "-source-conflict", base(before), {"STRATALINT_SOURCE_BASE":head})
            case(entry + "-source-agrees", base(before), {"STRATALINT_SOURCE_BASE":before}, True)
            case(entry + "-base-with-push", base(before), push)
            case(entry + "-empty-with-push", base(""), push)
            case(entry + "-zero-with-push", base(zero), push)
            case(entry + "-BASE-environment-with-push", command, dict(push, BASE=before))
            case(entry + "-empty-BASE-environment-with-push", command, dict(push, BASE=""))
            case(entry + "-push-environment", command, push, True)
            case(entry + "-initial-environment", command, dict(push, STRATALINT_PUSH_BEFORE=zero), True)
            case(entry + "-nonancestor-environment", command, dict(push, STRATALINT_PUSH_BEFORE=nonancestor), True)
            case(entry + "-partial-before-environment", command, {"STRATALINT_PUSH_BEFORE":before})
            case(entry + "-partial-head-environment", command, {"STRATALINT_PUSH_HEAD":head})
            case(entry + "-empty-before-environment", command, dict(push, STRATALINT_PUSH_BEFORE=""))
            case(entry + "-empty-head-environment", command, dict(push, STRATALINT_PUSH_HEAD=""))
            case(entry + "-wrong-head-environment", command, dict(push, STRATALINT_PUSH_HEAD=before))
            case(entry + "-source-with-push", command, dict(push, STRATALINT_SOURCE_BASE=before))
        case("script-BASE-environment-conflict", [*script, before], {"BASE":head})
        case("make-command-overrides-environment", [*make, "BASE=" + before], {"BASE":head}, True)
        case("script-base-flag", [*script, "--base", before], accepted=True)
        for name, value in (("push", before), ("initial", zero), ("nonancestor", nonancestor)):
            case("script-" + name + "-arguments", [*script, "--push-before", value, "--push-head", head], accepted=True)
        case("script-push-split-argument-environment", [*script, "--push-before", before], {"STRATALINT_PUSH_HEAD":head}, True)
        case("script-push-argument-environment-conflict", [*script, "--push-before", head, "--push-head", head], push)
        for name, args in (
            ("partial-before-argument", ["--push-before", before]),
            ("partial-head-argument", ["--push-head", head]),
            ("empty-before-argument", ["--push-before", "", "--push-head", head]),
            ("empty-head-argument", ["--push-before", before, "--push-head", ""]),
            ("zero-head-argument", ["--push-before", before, "--push-head", zero]),
            ("wrong-head-argument", ["--push-before", before, "--push-head", before]),
            ("missing-object-argument", ["--push-before", "1" * 40, "--push-head", head]),
            ("both-mode-arguments", [before, "--push-before", before, "--push-head", head]),
            ("empty-base-flag", ["--base", ""]),
            ("extra-positional", [before, head]),
            ("extra-option", [before, "--unknown"]),
            ("extra-separator", [before, "--"]),
            ("missing-base-value", ["--base"]),
            ("missing-before-value", ["--push-before"]),
            ("missing-head-value", ["--push-before", before, "--push-head"]),
        ):
            case("script-" + name, [*script, *args])
        rows = []
        for name, argv, updates, accepted in cases:
            result = subprocess.run(argv, cwd=root, env=dict(environment, **updates), capture_output=True, text=True)
            reached = "POST_IDENTITY_ADDRESS_REACHED" in result.stderr
            diagnostic = "CI_REPORT_SOURCE_INVALID" in result.stderr
            rows.append(dict(name=name, argv=argv, environment=updates, expected_accept=accepted,
                exit_code=result.returncode, reached_address=reached, identity_diagnostic=diagnostic,
                stdout=result.stdout, stderr=result.stderr,
                expectation_met=result.returncode == 2 and reached == accepted and (accepted or diagnostic)))
        assert all(hashlib.sha256((root / s["path"]).read_bytes()).hexdigest() == s["sha256"] for s in sources)
        report = dict(sources=sources, before=before, head=head, nonancestor=nonancestor, rows=rows,
            adapter_sha256=hashlib.sha256(adapter.read_bytes()).hexdigest(), adapter_exit=91)
        (scratch / "boundary-results.json").write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps(report))
        assert all(row["expectation_met"] for row in rows), [row["name"] for row in rows if not row["expectation_met"]]
        """;
}
