using System.Formats.Tar;
using System.IO.Compression;
using static StrataLint.TestSupport.TransportFixture;
using StrataLint.EngineeringScope;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.ReleaseIntegration.Tests;

[Collection("Release process boundary")]
public sealed class ReleaseArtifactTests
{


    [Theory]
    [InlineData("valid")]
    [InlineData("undeclared")]
    [InlineData("corrupt")]
    public void TruthReleaseRestoresOnlyVerifiedCurrentArtifacts(string defect)
    {
        using var fixture = new ExecutionFixture();
        PrepareCurrentRuntime(fixture);
        var root = fixture.Root;
        var commit = Git(root, "rev-parse", "HEAD");
        var archive = Path.Combine(root, "build/current.tgz");
        Assert.Equal(0, Run("transport-pack", root, "current", commit, "17", "2", archive));
        var transfer = Path.Combine(root, "build/ci-current.tar.gz");
        using (var input = new GZipStream(File.OpenRead(archive), CompressionMode.Decompress))
        using (var reader = new TarReader(input))
        using (var output = new GZipStream(File.Create(transfer), CompressionLevel.Fastest))
        using (var writer = new TarWriter(output))
        {
            while (reader.GetNextEntry(copyData: true) is { } entry)
            {
                if (defect == "corrupt" && entry.Name == Log)
                    entry = new PaxTarEntry(TarEntryType.RegularFile, entry.Name) { Mode = entry.Mode,
                        ModificationTime = entry.ModificationTime, DataStream = new MemoryStream("corrupt"u8.ToArray()) };
                writer.WriteEntry(entry);
            }
            if (defect == "undeclared")
                writer.WriteEntry(new PaxTarEntry(TarEntryType.RegularFile, "build/ci/undeclared")
                {
                    DataStream = new MemoryStream("extra"u8.ToArray()),
                });
        }
        var artifact = Path.Combine(root, "build/artifact.zip");
        using (var zip = ZipFile.Open(artifact, ZipArchiveMode.Create))
            zip.CreateEntryFromFile(transfer, "ci-current.tar.gz");
        var area = Path.Combine(root, "build/release");
        Directory.CreateDirectory(area);
        var result = EngineeringProcess.Process(root, "python3", ["-B", "-c", """
            import json, os, pathlib, shutil, subprocess, sys
            repository, root, area, artifact = map(pathlib.Path, sys.argv[1:5])
            commit, defect = sys.argv[5:]
            sys.path.insert(0, str(repository / 'tools/scripts/workflow'))
            import truth_release as owner
            repository_name = os.environ['GITHUB_REPOSITORY']
            workflow = dict(id=7, path='.github/workflows/ci-push.yml')
            run = dict(id=17, run_attempt=2, workflow_id=7, path=workflow['path'],
                       event='push', head_branch='dev', head_sha=commit, status='completed', conclusion='success')
            jobs = [dict(name=name, run_id=17, run_attempt=2, head_sha=commit,
                         status='completed', conclusion='success') for name in ('engineering', 'current')]
            responses = {
                'branches/dev': dict(protected=True),
                'actions/workflows/ci-push.yml': workflow,
                'commits?sha=dev&per_page=40': [dict(sha=commit)],
                'actions/workflows/ci-push.yml/runs?event=push&head_sha=' + commit + '&per_page=100':
                    [dict(workflow_runs=[run])],
                'actions/runs/17/attempts/2/jobs?per_page=100': [dict(jobs=jobs)],
                'actions/runs/17/artifacts?per_page=100': [dict(artifacts=[dict(id=170,
                    name='ci-current-17-2', expired=False, workflow_run=dict(id=17, head_sha=commit))])],
            }
            real_run = subprocess.run
            def github(command, **options):
                if command[0] != 'gh':
                    return real_run(command, **options)
                path = command[-1].removeprefix('repos/' + repository_name + '/')
                if path == 'actions/artifacts/170/zip':
                    with artifact.open('rb') as source:
                        shutil.copyfileobj(source, options['stdout'])
                    return subprocess.CompletedProcess(command, 0)
                return subprocess.CompletedProcess(command, 0, json.dumps(responses[path]))
            # Only GitHub is replaced. Selection, clone/checkout, extraction and
            # the transported native verifier all execute their production code.
            subprocess.run = github
            if defect == 'valid':
                selected = owner.select(root, area, owner.collect(repository_name, commit, workflow))
                candidate = owner.restore_candidate(root, area, selected)
                print('TRUTH_RELEASE_RESTORED ' + str(candidate))
            else:
                sys.argv = ['truth_release.py', 'prepare', '--repository', str(root), '--output', str(area)]
                raise SystemExit(owner.main())
            """, TestRepositoryLayout.FindRoot(), root, area, artifact, commit, defect],
            new Dictionary<string, string> {
                ["GITHUB_REPOSITORY"] = Environment.GetEnvironmentVariable("GITHUB_REPOSITORY") ?? "",
                ["CI_WORKFLOW_INPUTS"] = "null", ["GITHUB_OUTPUT"] = Path.Combine(area, "outputs") },
            hangGuard: TestBudgets.WorkflowProcessHangGuard);
        Assert.True(result.Exit == 0, result.Text);
        var target = Path.Combine(area, "candidate-17-2");
        if (defect == "valid")
        {
            Assert.Contains("run_id=17 run_attempt=2 status=verified", result.Text);
            Assert.Contains("TRUTH_RELEASE_RESTORED " + target, result.Text);
            var expected = CommonExecutionEvidence.ValidateCurrent(root);
            var restored = CommonExecutionEvidence.ValidateCurrent(target);
            Assert.Equal(expected.Candidate, restored.Candidate);
            Assert.Equal(expected.Round, restored.Round);
            Assert.Equal(expected.Materials, restored.Materials);
            Assert.Equal(File.ReadAllBytes(Path.Combine(root, "Meta/ci-checks.json")),
                File.ReadAllBytes(Path.Combine(target, "Meta/ci-checks.json")));
        }
        else
        {
            Assert.Contains(defect == "undeclared" ? "stage archive differs from declared transport materials"
                : "artifact integrity mismatch: " + Log, result.Text);
            Assert.Contains("TRUTH_RELEASE_INPUT_UNAVAILABLE", result.Text);
            Assert.Contains("publish_ready=false", File.ReadAllText(Path.Combine(area, "outputs")));
            Assert.DoesNotContain("status=verified", result.Text);
            Assert.False(File.Exists(Path.Combine(target, "build/ci/undeclared")));
            Assert.False(Directory.Exists(Path.Combine(area, "truth-release-assets")));
        }
    }
}
