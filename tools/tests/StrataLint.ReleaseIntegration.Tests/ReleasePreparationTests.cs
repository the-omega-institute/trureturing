using System.Text.Json;
using static StrataLint.TestSupport.NativeReleaseFixture;
using StrataLint.EngineeringScope;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.ReleaseIntegration.Tests;

[Collection("Release process boundary")]
public sealed class ReleasePreparationTests
{


    [Theory]
    [InlineData("next-report", 0, true)]
    [InlineData("all-report-free", 0, false)]
    [InlineData("missing-required", 0, false)]
    [InlineData("corrupt-required", 0, false)]
    [InlineData("assembly-failure", 2, false)]
    [InlineData("verify-exact", 0, false)]
    [InlineData("verify-unprotected", 2, false)]
    [InlineData("verify-diverged", 2, false)]
    [InlineData("verify-wrong-branch", 2, false)]
    [InlineData("verify-wrong-attempt", 2, false)]
    [InlineData("verify-report-free", 2, false)]
    [InlineData("verify-missing-required", 2, false)]
    [InlineData("verify-corrupt-required", 2, false)]
    [InlineData("prepare-exact", 0, true)]
    public void ReleasePrepareConsumesValidatedReportRequirement(string scenario, int exit, bool ready)
    {
        using var first = new ResourceFixture(["filemap"], "Evidence/D5/Fixture.result.json");
        using var next = new ResourceFixture(scenario is "all-report-free" or "verify-report-free" ? ["filemap"] : ["filemap", "lean-report"]);
        Produce(first); Produce(next);
        var firstArchive = Pack(first, 18);
        var nextArchive = Pack(next, 17);
        var area = Path.Combine(first.Root, "build/release");
        Directory.CreateDirectory(area);
        // GitHub responses and assembly are external fixtures. The actual selector,
        // clone/checkout/extract, native transport verifier and prepare loop run intact.
        // The assembly fixture refuses an absent report, exposing unconditional assembly.
        var result = EngineeringProcess.Process(first.Root, "python3", ["-B", "-c", """
            import json, os, pathlib, shutil, subprocess, sys
            source, first, second, area, archive1, archive2 = map(pathlib.Path, sys.argv[1:7])
            commit1, commit2, native, scenario = sys.argv[7:]
            sys.path.insert(0, str(source / 'tools/scripts/workflow'))
            import truth_release as owner
            verification = scenario.startswith('verify-')
            exact = verification or scenario == 'prepare-exact'
            branch = 'integration-truth-source' if verification else 'dev'
            workflow = dict(id=7, path='.github/workflows/ci-push.yml')
            commits = [commit1, commit2]
            cases = {commit1: (18, first, archive1), commit2: (17, second, archive2)}
            responses = {'branches/'+branch: dict(name=branch, protected=scenario != 'verify-unprotected', commit=dict(sha=commit1)),
                         'actions/workflows/ci-push.yml': workflow,
                         'commits?sha=dev&per_page=40': [dict(sha=c) for c in commits]}
            if exact:
                # The explicit commit is outside the history scan. Only API boundary
                # evidence is synthetic; selected material and transport stay real.
                del responses['commits?sha=dev&per_page=40']
                responses[f'compare/{commit2}...{commit1}'] = dict(
                    status='diverged' if scenario == 'verify-diverged' else 'ahead', merge_base_commit=dict(sha=commit2))
            for commit, (runid, root, archive) in cases.items():
                run = dict(id=runid, run_attempt=1, workflow_id=7, path=workflow['path'], event='push',
                           head_branch='dev' if scenario == 'verify-wrong-branch' else branch,
                           head_sha=commit, status='completed', conclusion='success')
                responses['actions/workflows/ci-push.yml/runs?event=push&head_sha='+commit+'&per_page=100'] = [dict(workflow_runs=[run])]
                responses[f'actions/runs/{runid}/attempts/1/jobs?per_page=100'] = [dict(jobs=[dict(name=n,
                    run_id=runid, run_attempt=2 if scenario == 'verify-wrong-attempt' and n == 'current' else 1,
                    head_sha=commit, status='completed', conclusion='success') for n in ('engineering','current')])]
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
                        if scenario.endswith('missing-required'): report.unlink()
                        if scenario.endswith('corrupt-required'): report.write_text('corrupt')
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
            if exact:
                sys.argv.extend(['--source-ref','refs/heads/'+branch,'--source-commit',commit2])
            if verification: sys.argv[1] = 'verify-source'
            raise SystemExit(owner.main())
            """, TestRepositoryLayout.FindRoot(), first.Root, next.Root, area, firstArchive, nextArchive,
            first.Commit, next.Commit, NativeRunner, scenario], new Dictionary<string, string> {
                ["GITHUB_REPOSITORY"] = Environment.GetEnvironmentVariable("GITHUB_REPOSITORY") ?? "",
                ["GITHUB_RUN_ID"] = "99", ["GITHUB_RUN_ATTEMPT"] = "1", ["GITHUB_OUTPUT"] = Path.Combine(area, "outputs") },
            TestBudgets.WorkflowProcessHangGuard);
        TransportFixture.Capture(first.Root, "release-" + scenario, result);
        Assert.True(result.Exit == exit, result.Text);
        Assert.DoesNotContain("ASSEMBLY_ATTEMPT " + Path.Combine(area, "candidate-18-1"), result.Text, StringComparison.Ordinal);
        if (exit == 0)
            Assert.Contains("publish_ready=" + (ready ? "true" : "false"), File.ReadAllText(Path.Combine(area, "outputs")), StringComparison.Ordinal);
        else Assert.Contains("TRUTH_RELEASE_FAILED", result.Text, StringComparison.Ordinal);
        if (scenario.StartsWith("verify-", StringComparison.Ordinal))
        {
            Assert.DoesNotContain("ASSEMBLY_ATTEMPT", result.Text, StringComparison.Ordinal);
            if (scenario == "verify-exact")
            {
                var outputs = File.ReadAllText(Path.Combine(area, "outputs"));
                Assert.Contains("source_verified=true", outputs, StringComparison.Ordinal);
                Assert.Contains("source_ref=refs/heads/integration-truth-source", outputs, StringComparison.Ordinal);
                Assert.Contains("source_commit=" + next.Commit, outputs, StringComparison.Ordinal);
                Assert.Contains("run_id=17", outputs, StringComparison.Ordinal);
                Assert.Contains("run_attempt=1", outputs, StringComparison.Ordinal);
                Assert.Contains("artifact_id=170", outputs, StringComparison.Ordinal);
            }
        }
        if (scenario.Contains("required", StringComparison.Ordinal))
        {
            Assert.Contains("TRUTH_RELEASE_INPUT_UNAVAILABLE", result.Text, StringComparison.Ordinal);
            Assert.DoesNotContain("ASSEMBLY_ATTEMPT", result.Text, StringComparison.Ordinal);
        }
        if (ready || scenario == "assembly-failure")
            Assert.Contains("ASSEMBLY_ATTEMPT " + Path.Combine(area, "candidate-17-1"), result.Text, StringComparison.Ordinal);
    }
}
