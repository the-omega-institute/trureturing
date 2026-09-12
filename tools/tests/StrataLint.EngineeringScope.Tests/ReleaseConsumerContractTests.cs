using System.IO.Compression;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed class ReleaseConsumerContractTests
{
    [Fact]
    public void OriginalProducerEnvironmentVerifiesButCannotSupplyLocalReuse()
    {
        using var fixture = new ResourceRouteTests.ResourceFixture(["filemap", "lean-report"]);
        var previous = Environment.GetEnvironmentVariable("DOTNET_PROCESSOR_COUNT");
        CommonStageRecord original;
        try
        {
            // A real native consumer runs with a different registered process count.
            // This injects an environment difference; it is not a cross-OS Actions run.
            Environment.SetEnvironmentVariable("DOTNET_PROCESSOR_COUNT", "1");
            Produce(fixture);
            original = CommonExecutionEvidence.ValidateCurrent(fixture.Root);
            Assert.True(CommonExecutionEvidence.ExportCheckSeed(fixture.Root, "current", TextWriter.Null));
            Pack(fixture, 17);
        }
        finally { Environment.SetEnvironmentVariable("DOTNET_PROCESSOR_COUNT", previous); }
        var before = original.Materials.ToDictionary(m => m.Path, m => CommonExecutionEvidence.Hash(Path.Combine(fixture.Root, m.Path)));
        var result = Native(fixture.Root, ["transport-verify", "--repository", fixture.Root, "--stage", "current",
            "--commit", fixture.Commit, "--run-id", "17", "--run-attempt", "1"], "2");
        Capture(fixture.Root, "producer-environment", result);
        Assert.True(result.Exit == 0, result.Text);
        Assert.Contains("status=verified", result.Text, StringComparison.Ordinal);
        var reuse = Native(fixture.Root, ["check-seed-import", "--repository", fixture.Root, "--stage", "current"], "2");
        Capture(fixture.Root, "local-reuse", reuse);
        Assert.True(reuse.Exit == 0, reuse.Text);
        Assert.Contains("COMMON_CHECK_SEED_MISS id=filemap", reuse.Text, StringComparison.Ordinal);
        Assert.DoesNotContain("COMMON_CHECK_REUSED id=filemap", reuse.Text, StringComparison.Ordinal);
        var compatible = Native(fixture.Root, ["check-seed-import", "--repository", fixture.Root, "--stage", "current"], "1");
        Capture(fixture.Root, "compatible-local-reuse", compatible);
        Assert.True(compatible.Exit == 0, compatible.Text);
        Assert.Contains("COMMON_CHECK_REUSED id=filemap", compatible.Text, StringComparison.Ordinal);
        foreach (var material in before)
            Assert.Equal(material.Value, CommonExecutionEvidence.Hash(Path.Combine(fixture.Root, material.Key)));
    }

    [Theory]
    [InlineData("environment")]
    [InlineData("sdk")]
    [InlineData("candidate")]
    [InlineData("round")]
    [InlineData("material")]
    public void BoundMalformedProducerEvidenceCannotVerify(string damage)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture(["filemap"]);
        Produce(fixture);
        Pack(fixture, 17);
        var checksPath = CommonExecutionEvidence.ChecksPath("current");
        var checks = Read(fixture.Root, checksPath);
        var unit = checks["units"]![0]!;
        if (damage == "environment") unit["execution_environment"] = "not-json";
        if (damage == "sdk") unit["execution_environment"] = CommonExecutionEvidence.ExecutionEnvironment(fixture.Root)
            .Replace("10.0.103", "0.0.0", StringComparison.Ordinal);
        if (damage == "candidate") unit["execution_candidate"] = new string('a', 64);
        if (damage == "round") unit["execution_round"] = "other-round";
        if (damage == "material") File.AppendAllText(Path.Combine(fixture.Root, unit["operations"]![0]!["log"]!.ToString()), "corrupt");
        else File.WriteAllText(Path.Combine(fixture.Root, checksPath), checks.ToJsonString());
        // Rebind the outer material hashes so the original-unit validator is tested.
        Rebind(fixture.Root, CommonExecutionEvidence.CurrentPath, checksPath);
        Rebind(fixture.Root, CiTransport.ManifestPath("current"), checksPath, CommonExecutionEvidence.CurrentPath);
        var result = Native(fixture.Root, ["transport-verify", "--repository", fixture.Root, "--stage", "current",
            "--commit", fixture.Commit, "--run-id", "17", "--run-attempt", "1"]);
        Capture(fixture.Root, "malformed-" + damage, result);
        Assert.Equal(2, result.Exit);
        Assert.DoesNotContain("status=verified", result.Text, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("next-report", 0, true)]
    [InlineData("all-report-free", 0, false)]
    [InlineData("missing-required", 0, false)]
    [InlineData("corrupt-required", 0, false)]
    [InlineData("assembly-failure", 2, false)]
    public void ReleasePrepareConsumesValidatedReportRequirement(string scenario, int exit, bool ready)
    {
        using var first = new ResourceRouteTests.ResourceFixture(["filemap"], "Evidence/D5/Fixture.result.json");
        using var next = new ResourceRouteTests.ResourceFixture(scenario == "all-report-free" ? ["filemap"] : ["filemap", "lean-report"]);
        Produce(first); Produce(next);
        var firstArchive = Pack(first, 18);
        var nextArchive = Pack(next, 17);
        var area = Path.Combine(first.Root, "build/release");
        Directory.CreateDirectory(area);
        // GitHub responses and assembly are external fixtures. The actual selector,
        // clone/checkout/extract, native transport verifier and prepare loop run intact.
        // The assembly fixture refuses an absent report, exposing unconditional assembly.
        var result = SharedBuildContractTests.Process(first.Root, "python3", ["-B", "-c", """
            import json, os, pathlib, shutil, subprocess, sys
            source, first, second, area, archive1, archive2 = map(pathlib.Path, sys.argv[1:7])
            commit1, commit2, native, scenario = sys.argv[7:]
            sys.path.insert(0, str(source / 'tools/scripts/workflow'))
            import truth_release as owner
            workflow = dict(id=7, path='.github/workflows/ci-push.yml')
            commits = [commit1, commit2]
            cases = {commit1: (18, first, archive1), commit2: (17, second, archive2)}
            responses = {'branches/dev': dict(protected=True), 'actions/workflows/ci-push.yml': workflow,
                         'commits?sha=dev&per_page=40': [dict(sha=c) for c in commits]}
            for commit, (runid, root, archive) in cases.items():
                run = dict(id=runid, run_attempt=1, workflow_id=7, path=workflow['path'], event='push',
                           head_branch='dev', head_sha=commit, status='completed', conclusion='success')
                responses['actions/workflows/ci-push.yml/runs?event=push&head_sha='+commit+'&per_page=100'] = [dict(workflow_runs=[run])]
                responses[f'actions/runs/{runid}/attempts/1/jobs?per_page=100'] = [dict(jobs=[dict(name=n,
                    run_id=runid, run_attempt=1, head_sha=commit, status='completed', conclusion='success') for n in ('engineering','current')])]
                responses[f'actions/runs/{runid}/artifacts?per_page=100'] = [dict(artifacts=[dict(id=runid*10,
                    name=f'ci-current-{runid}-1', expired=False, workflow_run=dict(id=runid, head_sha=commit))])]
            real = subprocess.run
            def external(command, **kw):
                command = list(command)
                if command[0] == 'gh':
                    path = command[-1].removeprefix('repos/' + os.environ['GITHUB_REPOSITORY'] + '/')
                    if path.endswith('/zip'):
                        archive = archive1 if '/180/' in path else archive2
                        with archive.open('rb') as stream: shutil.copyfileobj(stream, kw['stdout'])
                        return subprocess.CompletedProcess(command, 0)
                    return subprocess.CompletedProcess(command, 0, json.dumps(responses[path]))
                if command[:2] == ['dotnet', owner.RUNNER]:
                    # Same candidate-source native verifier, only its location is injected.
                    if command[2] == 'transport-verify' and str(kw['cwd']).endswith('candidate-17-1'):
                        report = pathlib.Path(kw['cwd']) / '.lake/build/stratalint/raw-lean-report.json'
                        if scenario == 'missing-required': report.unlink()
                        if scenario == 'corrupt-required': report.write_text('corrupt')
                    return real([native, *command[2:]], **kw)
                if command[:3] == ['git', 'clone', '--quiet']:
                    command = [*command[:-2], str(cases[commit2][1] if command[-1].endswith('candidate-17-1') else first), command[-1]]
                if command[:3] == ['dotnet', owner.CLI, 'truth-release']:
                    report = pathlib.Path(command[command.index('--candidate-lean-report')+1])
                    print('ASSEMBLY_ATTEMPT ' + str(kw['cwd']), flush=True)
                    if not report.is_file() or scenario == 'assembly-failure':
                        raise subprocess.CalledProcessError(23, command)
                    bundle = pathlib.Path(command[command.index('--out')+1])
                    commit = command[command.index('--producer-package-commit')+1]
                    tree = real(['git','rev-parse','HEAD^{tree}'], cwd=kw['cwd'], check=True, capture_output=True, text=True).stdout.strip()
                    digest = 'sha256:' + 'a'*64
                    (bundle/'release-manifest.v1.json').write_text(json.dumps(dict(sha256sums_digest=digest)))
                    (bundle/'truth-release-publication.v1.json').write_text(json.dumps(dict(schema='truth-release-publication.v1',
                        release_digest=digest, bundle_ref=digest, source_commit=commit, source_tree=tree, producer_commit=commit)))
                    return subprocess.CompletedProcess(command, 0)
                return real(command, **kw)
            subprocess.run = external
            sys.argv = ['truth_release.py','prepare','--repository',str(first),'--output',str(area)]
            raise SystemExit(owner.main())
            """, TestRepositoryLayout.FindRoot(), first.Root, next.Root, area, firstArchive, nextArchive,
            first.Commit, next.Commit, NativeRunner, scenario], new Dictionary<string, string> {
                ["GITHUB_REPOSITORY"] = Environment.GetEnvironmentVariable("GITHUB_REPOSITORY") ?? "",
                ["GITHUB_RUN_ID"] = "99", ["GITHUB_RUN_ATTEMPT"] = "1", ["GITHUB_OUTPUT"] = Path.Combine(area, "outputs") },
            TestBudgets.WorkflowProcessHangGuard);
        Capture(first.Root, "release-" + scenario, result);
        Assert.True(result.Exit == exit, result.Text);
        Assert.DoesNotContain("ASSEMBLY_ATTEMPT " + Path.Combine(area, "candidate-18-1"), result.Text, StringComparison.Ordinal);
        if (exit == 0)
            Assert.Contains("publish_ready=" + (ready ? "true" : "false"), File.ReadAllText(Path.Combine(area, "outputs")), StringComparison.Ordinal);
        else Assert.Contains("TRUTH_RELEASE_FAILED", result.Text, StringComparison.Ordinal);
        if (scenario.Contains("required", StringComparison.Ordinal))
        {
            Assert.Contains("TRUTH_RELEASE_INPUT_UNAVAILABLE", result.Text, StringComparison.Ordinal);
            Assert.DoesNotContain("ASSEMBLY_ATTEMPT", result.Text, StringComparison.Ordinal);
        }
        if (ready || scenario == "assembly-failure")
            Assert.Contains("ASSEMBLY_ATTEMPT " + Path.Combine(area, "candidate-17-1"), result.Text, StringComparison.Ordinal);
    }

    private static string NativeRunner => Path.Combine(Path.GetDirectoryName(typeof(Program).Assembly.Location)!, "StrataLint.EngineeringScope");
    private static (int Exit, string Text) Native(string root, string[] args, string? processors = null) =>
        SharedBuildContractTests.Process(root, NativeRunner, args, processors is null ? null : new Dictionary<string, string> { ["DOTNET_PROCESSOR_COUNT"] = processors });
    private static JsonNode Read(string root, string path) => JsonNode.Parse(File.ReadAllText(Path.Combine(root, path)))!;
    private static void Rebind(string root, string record, params string[] paths)
    {
        var data = Read(root, record);
        foreach (var item in data["materials"]!.AsArray().Where(m => paths.Contains(m!["path"]!.ToString())))
            item!["sha256"] = CommonExecutionEvidence.Hash(Path.Combine(root, item["path"]!.ToString()));
        File.WriteAllText(Path.Combine(root, record), data.ToJsonString());
    }
    private static void Produce(ResourceRouteTests.ResourceFixture fixture)
    {
        fixture.Processes();
        using var output = new StringWriter();
        Assert.True(fixture.Run("current", output) == 0, output.ToString());
    }
    private static string Pack(ResourceRouteTests.ResourceFixture fixture, int run)
    {
        var tar = Path.Combine(fixture.Root, "build/ci-current.tar.gz");
        using var output = new StringWriter();
        var exit = Program.Run(["transport-pack", "--repository", fixture.Root, "--stage", "current", "--commit", fixture.Commit,
            "--run-id", run.ToString(System.Globalization.CultureInfo.InvariantCulture), "--run-attempt", "1", "--archive", tar], TestResultEvidence.Load, output, output);
        Assert.True(exit == 0, output.ToString());
        var archive = Path.Combine(fixture.Root, "build/artifact.zip");
        using (var zip = ZipFile.Open(archive, ZipArchiveMode.Create)) zip.CreateEntryFromFile(tar, "ci-current.tar.gz");
        return archive;
    }
    internal static void Capture(string root, string name, (int Exit, string Text) result)
    {
        if (Environment.GetEnvironmentVariable("SOURCE_CONTRACT_EVIDENCE") is not { Length: > 0 } destination) return;
        var target = Path.Combine(destination, name);
        Directory.CreateDirectory(target);
        File.WriteAllText(Path.Combine(target, "process.json"), JsonSerializer.Serialize(new { root, result.Exit, result.Text, native_runner = NativeRunner,
            native_dll_sha256 = CommonExecutionEvidence.Hash(typeof(Program).Assembly.Location) }));
        foreach (var path in new[] { CommonExecutionEvidence.BuildPath, CommonExecutionEvidence.CurrentPath, CommonExecutionEvidence.ChecksPath("current"),
            CiTransport.ManifestPath("current"), "build/ci/plan.json", "build/ci/changes.json", "build/ci/engineering-result.json", "build/ci/current-result.json",
            "build/cold-events", "build/launched" })
            if (File.Exists(Path.Combine(root, path))) File.Copy(Path.Combine(root, path), Path.Combine(target, Path.GetFileName(path)), true);
        foreach (var record in new[] { CommonExecutionEvidence.BuildPath, CommonExecutionEvidence.CurrentPath })
        {
            if (!File.Exists(Path.Combine(root, record))) continue;
            foreach (var material in Read(root, record)["materials"]!.AsArray())
            {
                var path = material!["path"]!.ToString();
                if (!File.Exists(Path.Combine(root, path))) continue;
                var copy = Path.Combine(target, "materials", path);
                Directory.CreateDirectory(Path.GetDirectoryName(copy)!);
                File.Copy(Path.Combine(root, path), copy, true);
            }
        }
        if (File.Exists(Path.Combine(root, "build/artifact.zip")))
            File.Copy(Path.Combine(root, "build/artifact.zip"), Path.Combine(target, "original-artifact.zip"), true);
        foreach (var line in result.Text.Split('\n').Where(s => s.StartsWith("PREFLIGHT_ARTIFACT bundle=", StringComparison.Ordinal)))
            File.Copy(line["PREFLIGHT_ARTIFACT bundle=".Length..], Path.Combine(target, "preflight-candidate.tar.gz"), true);
    }
}
