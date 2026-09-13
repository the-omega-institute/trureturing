using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class InspectorSourceModeTests
{
    [Theory]
    [InlineData("schedule")]
    [InlineData("repository_dispatch")]
    public void PublisherSelectedSourceReportChain(string eventName)
    {
        using var temporary = new TemporaryDirectory();
        var result = TestProcessRunner.Run("python3", ["-c", Fixture,
            TestRepositoryLayout.FindRoot(), temporary.Path,
            Path.Combine(AppContext.BaseDirectory, "StrataLint.dll"), eventName, "", "", "[]", Publisher],
            temporary.Path, BoundedProcessRunner.HangDetectionBudget, 4 * 1024 * 1024);
        Console.WriteLine(Encoding.UTF8.GetString(result.StandardOutput));
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput)
            + Encoding.UTF8.GetString(result.StandardError));
        using var data = JsonDocument.Parse(result.StandardOutput);
        var repository = data.RootElement.GetProperty("repository").GetString()!;
        var gateway = new GitRepositoryGateway(repository);
        var selected = data.RootElement.GetProperty("selected_source").GetString()!;
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(gateway.ReadRevision(selected))).Snapshot;
        // truth-release consumes this same report reader against its immutable source.
        using var bundle = new PrecomputedLeanReportSource.CapturedBundle(repository,
            data.RootElement.GetProperty("served_report").GetString()!);
        Assert.Equal(2, bundle.Load(snapshot).Files.Count);
    }

    // Native report/Lean/context programs and their public composition. GitHub
    // transport is a local bundle copy; no workflow text or remote service is read.
    private const string Publisher = """
        event = mode
        write("lakefile.toml", 'name = "publisherFixture"\ndefaultTargets = ["D5", "Trureturing"]\n'
            '[[lean_lib]]\nname = "D5"\nroots = ["D5.Probe"]\n'
            '[[lean_lib]]\nname = "Trureturing"\nroots = ["Trureturing"]\n')
        write("D5/Probe.lean", source + "theorem release_probe : True := by trivial\n")
        head = commit("selected release source")
        git("checkout", "--detach", head)
        event_sha = git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
            "commit-tree", git("rev-parse", "HEAD^{tree}"), "-p", head, "-m", "later event")
        assert event_sha != head
        # Execute the actual inspector as well as actual SourceContext Lean.
        lake = adapter("lake", '''import json, os, sys
        with open(os.environ["FIXTURE_CALLS"], "a") as f: f.write(json.dumps(["lake", *sys.argv[1:]]) + "\\n")
        os.execv(os.environ["FIXTURE_LAKE"], [os.environ["FIXTURE_LAKE"], *sys.argv[1:]])
        ''')
        env.update(LAKE_BIN=lake)
        dotnet_adapter = Path(dotnet)
        dotnet_adapter.write_text(dotnet_adapter.read_text().replace('print("{}")', 'print("[]")'))
        env.pop("BASE", None)
        event_file = scratch / "event.json"
        event_file.write_text(json.dumps(dict(before=before, after=head, created=False, deleted=False)))
        env.update(GITHUB_ACTIONS="true", GITHUB_EVENT_NAME="push", GITHUB_EVENT_PATH=str(event_file),
            GITHUB_SHA=head, GITHUB_WORKFLOW_SHA=head, GITHUB_WORKFLOW_REF="owner/repo/ci-fixture.yml@refs/heads/dev",
            GITHUB_REPOSITORY="owner/repo", GITHUB_RUN_ID="35", GITHUB_RUN_ATTEMPT="1", GITHUB_JOB="produce")
        rows = []
        def run(label, argv, environment=None, expected=0):
            result = subprocess.run(argv, cwd=root, env=environment or env, text=True, capture_output=True)
            rows.append(dict(label=label, argv=argv, cwd=str(root), exit=result.returncode,
                stdout=result.stdout, stderr=result.stderr))
            (scratch / "publisher-results.json").write_text(json.dumps(rows, indent=2))
            assert result.returncode == expected, rows[-1]
            return result
        gate = run("gate-report", ["make", "--no-print-directory", "lean-report"])
        output = root / ".lake/build/stratalint/raw-lean-report.json"
        context_bytes = Path(str(output) + ".source-context.json").read_bytes()
        assert json.loads(context_bytes)["files"], context_bytes
        with zipfile.ZipFile(str(output) + ".materials.zip") as archive:
            assert len(archive.namelist()) > 1 and archive.read("source-context.json") == context_bytes
        helper = str(root / "tools/scripts/report/lean-report-input.sh")
        def copy_bundle(destination):
            destination.parent.mkdir(parents=True, exist_ok=True)
            for suffix in ("", ".input.attestation", ".provenance.json", ".materials.zip"):
                shutil.copyfile(str(output) + suffix, str(destination) + suffix)
            Path(str(destination) + ".sha256").write_text(hashlib.sha256(destination.read_bytes()).hexdigest()
                + "  " + destination.name + "\n")
        cached = scratch / "cached/raw-lean-report.json"
        artifact = scratch / "artifact/candidate-lean-report.json"
        copy_bundle(cached); copy_bundle(artifact)
        gate_env = env.copy()
        gate_event = scratch / "gate-event.json"
        gate_event.write_bytes(event_file.read_bytes())
        gate_env["GITHUB_EVENT_PATH"] = str(gate_event)
        env.update(GITHUB_EVENT_NAME=event, GITHUB_SHA=event_sha, GITHUB_WORKFLOW_SHA=event_sha,
            GITHUB_WORKFLOW_REF="owner/repo/.github/workflows/truth-release-publish.yml@refs/heads/dev",
            STRATALINT_SOURCE_BASE=head)
        event_file.write_text("{}")
        for label, report in (("cached-address", cached), ("gate-artifact", artifact)):
            run(label, [helper, "verify", "--repository", str(root), "--report", str(report)])
        # Renaming an artifact requires its checksum sidecar to name the served file.
        served = scratch / "served/raw-lean-report.json"
        output_saved = output
        output = artifact; copy_bundle(served); output = output_saved
        run("served-artifact", [helper, "verify", "--repository", str(root), "--report", str(served)])
        native_consumer = [real_dotnet, cli, "lean-source-input", "--base", head, "--report", str(served)]
        consumed = run("native-report-consumer", native_consumer)
        assert json.loads(consumed.stdout)["requests"] == [], consumed.stdout
        # The public consumer revalidates the captured bundle and forwards the same H.
        consumer = [str(root / "tools/scripts/report/report-consumer.sh"), "--role", "publisher-fixture",
            "--report", str(served), "--", sys.executable, "-c",
            'import os; assert os.environ["STRATALINT_SOURCE_BASE"] == "' + head + '"; print("CONSUMER_REACHED")']
        assert "CONSUMER_REACHED" in run("public-report-consumer", consumer).stdout
        verify = [helper, "verify", "--repository", str(root), "--report", str(served)]
        for defect in ("missing-source", "wrong-source", "mixed-push"):
            bad_env = env.copy()
            if defect == "missing-source": bad_env.pop("STRATALINT_SOURCE_BASE")
            if defect == "wrong-source": bad_env["STRATALINT_SOURCE_BASE"] = event_sha
            if defect == "mixed-push": bad_env.update(STRATALINT_PUSH_BEFORE=before, STRATALINT_PUSH_HEAD=head)
            run(defect, verify, bad_env, 2)
            rejected = run(defect + "-consumer", consumer, bad_env, 2)
            assert "CONSUMER_REACHED" not in rejected.stdout
        archive_path = Path(str(served) + ".materials.zip")
        saved_archive = archive_path.read_bytes()
        with zipfile.ZipFile(archive_path) as archive:
            entries = [(info, archive.read(info)) for info in archive.infolist() if info.filename != "source-context.json"]
        for defect in ("missing", "stale", "malformed"):
            with zipfile.ZipFile(archive_path, "w") as archive:
                for info, data in entries: archive.writestr(info, data)
                if defect != "missing":
                    context = json.loads(context_bytes); context["files"][0]["sourceSha256"] = "0"*64
                    archive.writestr("source-context.json", "{" if defect == "malformed" else json.dumps(context))
            rejected = run(defect + "-demanded-gate-context", verify, gate_env, 2)
            assert "LEAN_SOURCE_CONTEXT_FAILED" in rejected.stderr, rejected.stderr
        archive_path.write_bytes(saved_archive)
        # A report cannot outlive the declared material/source content it describes.
        original_source = (root / "D5/Probe.lean").read_bytes()
        (root / "D5/Probe.lean").write_bytes(original_source + b"-- stale input\n")
        run("stale-material-input", verify, expected=2)
        (root / "D5/Probe.lean").write_bytes(original_source)
        # A separate empty private cache forces actual publisher production.
        env["STRATALINT_REPORT_CACHE_ROOT"] = str(scratch / "publisher-cache")
        production = run("publisher-production", ["make", "--no-print-directory", "lean-report"])
        assert "mode=produced" in production.stdout, production.stdout
        assert json.loads(Path(str(output) + ".source-context.json").read_bytes())["files"] == []
        # Selected H was already gated: publication has no H-to-H delta demand.
        run("post-production-verify", [helper, "verify", "--repository", str(root), "--report", str(output)])
        hit = run("publisher-cache-hit", ["make", "--no-print-directory", "lean-report"])
        assert "mode=cached" in hit.stdout, hit.stdout
        print(json.dumps(dict(event=event, selected_source=head, event_sha=event_sha,
            repository=str(root), served_report=str(served),
            context_rows=len(json.loads(context_bytes)["files"]), cases=rows)))
        """;
}
