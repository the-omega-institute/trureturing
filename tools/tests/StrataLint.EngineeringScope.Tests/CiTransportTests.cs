using System.Diagnostics;
using System.Formats.Tar;
using System.IO.Compression;
using System.Security.Cryptography;
using System.Text.Json;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed class CiTransportTests
{
    [Fact]
    public void CurrentTransportFeedsOnlyTheDeclaredReportSnapshot()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        var root = fixture.Root;
        var repository = TestRepositoryLayout.FindRoot();
        var evidence = Environment.GetEnvironmentVariable("CI_REPORT_SNAPSHOT_EVIDENCE");
        // Reuse the nonempty synthetic statement producer, not its manually
        // authored current/transport records. C# owns the actual handoff below.
        var inputs = SharedBuildContractTests.Process(root, "python3", ["-B", "-c", """
            import pathlib, shutil, sys
            repository, root, relative = map(pathlib.Path, sys.argv[1:])
            sys.path.insert(0, str(repository / 'tools/tests/StrataLint.ScriptTests/Fixtures'))
            from report_snapshot_contract import SnapshotContracts
            case = SnapshotContracts()
            case.setUp()
            try:
                fixture = case.prepare_report()
                result = fixture.pair()
                print(result.stdout + result.stderr)
                assert result.returncode == 0
                sys.path.insert(0, str(repository / 'tools/lean-inspector'))
                from report_cache import copy_bundle, seed_valid
                from lean_cache import partition_path
                for name in ('D5', 'Trureturing.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'):
                    source, target = fixture.root / name, root / name
                    if source.is_dir(): shutil.copytree(source, target)
                    else: shutil.copyfile(source, target)
                copy_bundle(fixture.output, root / relative)
                assert seed_valid(root / relative, partition_path(root))
            finally:
                case.doCleanups()
            """, repository, root, CommonExecutionEvidence.ReportPath],
            hangGuard: TestBudgets.WorkflowProcessHangGuard);
        Capture("inputs.log", inputs.Text);
        Assert.True(inputs.Exit == 0, inputs.Text);
        Git(root, "add", "D5", "Trureturing.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain");
        Git(root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "report inputs");
        Prepare(fixture, current: false);
        var build = CommonExecutionEvidence.ValidateBuild(root);
        CheckEvidenceFixture.Seal(root, "current", build);
        CommonExecutionEvidence.SealCurrent(root, build, Steps(CommonExecutionEvidence.CurrentSteps));
        CommonExecutionEvidence.Write(root, "build/ci/current-result.json", new Dictionary<string, object> {
            ["stage"] = "current", ["exit"] = 0, ["candidate"] = build.Candidate,
            ["current_evidence"] = CommonExecutionEvidence.CurrentPath, ["report"] = CommonExecutionEvidence.ReportPath });
        var commit = Git(root, "rev-parse", "HEAD");
        Assert.Equal(0, Run("transport-pack", root, "current", commit, "17", "2", Path.Combine(root, "build/current.tgz")));
        var transportPath = Path.Combine(root, "build/ci/current-transport.json");
        Assert.True(File.Exists(transportPath));
        Assert.False(File.Exists(Path.Combine(root, "build/ci/transport.json")));
        var transportBytes = File.ReadAllBytes(transportPath);
        var currentBytes = File.ReadAllBytes(Path.Combine(root, CommonExecutionEvidence.CurrentPath));
        var summaryBytes = File.ReadAllBytes(Path.Combine(root, "build/ci/current-result.json"));
        foreach (var name in new[] { "current-transport.json", "current.json", "current-result.json", "current-paths.nul", "build.json" })
            Capture(name, File.ReadAllText(Path.Combine(root, "build/ci", name)));
        var report = Path.Combine(root, CommonExecutionEvidence.ReportPath);
        using var seed = JsonDocument.Parse(TemporaryFileSystem.File.ReadAllBytes(report + ".seed.json"));
        var partition = seed.RootElement.GetProperty("partition").GetString()!;
        var identity = Convert.ToHexStringLower(SHA256.HashData(TemporaryFileSystem.File.ReadAllBytes(report + ".seed.json")
            .Concat(TemporaryFileSystem.File.ReadAllBytes(report + ".provenance.json")).ToArray()));
        var suffixes = new[] { "", ".sha256", ".input.attestation", ".provenance.json", ".materials.zip", ".seed.json" };
        if (!string.IsNullOrEmpty(evidence))
            foreach (var suffix in suffixes) File.Copy(report + suffix, Path.Combine(evidence, "producer-report.json" + suffix));
        // Complete historical and foreign bundles exist locally but must not
        // be used to choose or populate this execution's remote snapshot.
        foreach (var history in new[] { partition + "/" + new string('0', 64), new string('b', 40) + "/foreign/old" })
            foreach (var suffix in suffixes)
            {
                var target = Path.Combine(root, ".lake/report-cache", history, "raw-lean-report.json" + suffix);
                Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                File.Copy(report + suffix, target);
            }
        var environment = new Dictionary<string, string> {
            ["GITHUB_EVENT_NAME"] = "push", ["GITHUB_REF"] = "refs/heads/dev",
            ["GITHUB_RUN_ID"] = "17", ["GITHUB_RUN_ATTEMPT"] = "2", ["CANDIDATE_SHA"] = commit,
            ["GITHUB_REPOSITORY"] = Environment.GetEnvironmentVariable("GITHUB_REPOSITORY") ?? "",
            ["STRATALINT_CACHE_WRITES"] = "true", ["STRATALINT_CHECK_SUCCEEDED"] = "true",
            ["GITHUB_OUTPUT"] = Path.Combine(root, "build/snapshot-output") };
        Snapshot("accepted", ready: true);
        var cached = Path.Combine(root, "build/lean-cache/report");
        var manifestBytes = File.ReadAllBytes(Path.Combine(cached, "manifest.json"));
        Capture("snapshot-manifest.json", System.Text.Encoding.UTF8.GetString(manifestBytes));
        using var manifest = JsonDocument.Parse(manifestBytes);
        Assert.Equal("lean-actions-seed-v1", manifest.RootElement.GetProperty("schema").GetString());
        Assert.Equal("report", manifest.RootElement.GetProperty("layer").GetString());
        Assert.Equal(partition, manifest.RootElement.GetProperty("partition").GetString());
        var expected = suffixes.Select(suffix => (Path: partition + "/" + identity + "/raw-lean-report.json" + suffix,
            Sha: Convert.ToHexStringLower(SHA256.HashData(TemporaryFileSystem.File.ReadAllBytes(report + suffix))),
            Mode: OperatingSystem.IsWindows() ? 0 : (int)File.GetUnixFileMode(report + suffix)))
            .OrderBy(item => item.Path, StringComparer.Ordinal).ToArray();
        var actual = manifest.RootElement.GetProperty("files").EnumerateArray().Select(item => (
            Path: item.GetProperty("path").GetString()!, Sha: item.GetProperty("sha256").GetString()!, Mode: item.GetProperty("mode").GetInt32())).ToArray();
        Assert.Equal(expected, actual);
        Assert.Equal(expected.Select(item => item.Path), Directory.GetFiles(Path.Combine(cached, "data"), "*", SearchOption.AllDirectories)
            .Select(path => Path.GetRelativePath(Path.Combine(cached, "data"), path)).Order(StringComparer.Ordinal));
        foreach (var item in expected)
        {
            var path = Path.Combine(cached, "data", item.Path);
            Assert.Equal(item.Sha, Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(path))));
            Assert.Equal(item.Mode, (int)File.GetUnixFileMode(path));
            if (!string.IsNullOrEmpty(evidence))
            {
                var copy = Path.Combine(evidence, "snapshot", item.Path);
                Directory.CreateDirectory(Path.GetDirectoryName(copy)!);
                File.Copy(path, copy);
                File.SetUnixFileMode(copy, File.GetUnixFileMode(path));
            }
        }
        var saved = Directory.GetFiles(cached, "*", SearchOption.AllDirectories).ToDictionary(path => path, File.ReadAllBytes);
        foreach (var defect in new[] { "missing-manifest", "wrong-run", "wrong-commit" })
        {
            if (defect == "missing-manifest") File.Delete(transportPath);
            if (defect == "wrong-run") environment["GITHUB_RUN_ID"] = "18";
            if (defect == "wrong-commit") environment["CANDIDATE_SHA"] = new string('0', 40);
            Snapshot(defect, ready: false);
            Assert.Equal(saved.Keys.Order(StringComparer.Ordinal), Directory.GetFiles(cached, "*", SearchOption.AllDirectories).Order(StringComparer.Ordinal));
            foreach (var item in saved) Assert.Equal(item.Value, TemporaryFileSystem.File.ReadAllBytes(item.Key));
            foreach (var item in expected) Assert.Equal(item.Mode, (int)File.GetUnixFileMode(Path.Combine(cached, "data", item.Path)));
            Assert.Equal(currentBytes, File.ReadAllBytes(Path.Combine(root, CommonExecutionEvidence.CurrentPath)));
            Assert.Equal(summaryBytes, File.ReadAllBytes(Path.Combine(root, "build/ci/current-result.json")));
            CommonExecutionEvidence.ValidateCurrent(root);
            File.WriteAllBytes(transportPath, transportBytes);
            environment["GITHUB_RUN_ID"] = "17";
            environment["CANDIDATE_SHA"] = commit;
        }

        // Bind each malformed current record into the transport so these cases
        // exercise the consumer contract beyond the outer file hash check.
        foreach (var defect in new[] { "version-one", "version-three", "candidate", "round" })
        {
            var current = CommonExecutionEvidence.Read<CommonStageRecord>(root, CommonExecutionEvidence.CurrentPath);
            var changed = defect switch
            {
                "version-one" => current with { Version = 1 },
                "version-three" => current with { Version = 3 },
                "candidate" => current with { Candidate = new string('a', 64) },
                _ => current with { Round = current.Round + "-stale" },
            };
            CommonExecutionEvidence.Write(root, CommonExecutionEvidence.CurrentPath, changed);
            var transport = CommonExecutionEvidence.Read<CiTransportRecord>(root, "build/ci/current-transport.json");
            CommonExecutionEvidence.Write(root, "build/ci/current-transport.json", transport with
            {
                Materials = transport.Materials.Select(material => material.Path == CommonExecutionEvidence.CurrentPath
                    ? material with { Sha256 = CommonExecutionEvidence.Hash(Path.Combine(root, material.Path)) } : material).ToArray(),
            });
            Snapshot(defect, ready: false);
            foreach (var item in saved) Assert.Equal(item.Value, File.ReadAllBytes(item.Key));
            File.WriteAllBytes(Path.Combine(root, CommonExecutionEvidence.CurrentPath), currentBytes);
            File.WriteAllBytes(transportPath, transportBytes);
            CommonExecutionEvidence.ValidateCurrent(root);
        }

        void Snapshot(string label, bool ready)
        {
            File.Delete(environment["GITHUB_OUTPUT"]);
            var result = SharedBuildContractTests.Process(root, "python3", ["-B", Path.Combine(repository, "tools/scripts/worktree/lean_actions.py"),
                "snapshot", "--repository", root], environment);
            Capture(label + ".log", result.Text);
            Assert.True(result.Exit == 0, result.Text);
            Assert.True(TemporaryFileSystem.File.ReadAllText(environment["GITHUB_OUTPUT"]).Contains("report_ready=" + (ready ? "true" : "false"), StringComparison.Ordinal), result.Text);
            Assert.Contains(ready ? "\"status\": \"snapshot\"" : "\"status\": \"save-failed\"", result.Text, StringComparison.Ordinal);
            Assert.False(File.Exists(Path.Combine(root, "build/ci/transport.json")));
            Assert.Empty(Directory.GetDirectories(Path.Combine(root, "build/lean-cache"), ".snapshot-*"));
        }

        void Capture(string name, string text)
        {
            if (string.IsNullOrEmpty(evidence)) return;
            Directory.CreateDirectory(evidence);
            File.WriteAllText(Path.Combine(evidence, name), text);
        }
    }

    [Fact]
    public void CurrentCliTransportRoundTripRetainsRegistrationAndRejectsInvalidBundles()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        PrepareCurrentRuntime(fixture);
        var root = fixture.Root;
        var repository = TestRepositoryLayout.FindRoot();
        var commit = Git(root, "rev-parse", "HEAD");
        var archive = Path.Combine(root, "build/current.tgz");
        var packed = Cli("pack", root, archive);
        Assert.True(packed.Exit == 0, packed.Text);
        Assert.Contains("status=packed", packed.Text);

        var target = Path.Combine(root, "build/destination");
        Git(root, "clone", "--quiet", "--no-hardlinks", root, target);
        var restored = Cli("restore", target, archive);
        Assert.True(restored.Exit == 0, restored.Text);
        Assert.Contains("status=verified", restored.Text);
        Assert.Equal(File.ReadAllBytes(Path.Combine(root, "Meta/ci-checks.json")),
            File.ReadAllBytes(Path.Combine(target, "Meta/ci-checks.json")));
        Assert.Contains(CommonExecutionEvidence.ValidateCurrent(target).Materials, material => material.Path == "Meta/ci-checks.json");
        Assert.Equal(File.GetUnixFileMode(Path.Combine(root, Log)), File.GetUnixFileMode(Path.Combine(target, Log)));

        foreach (var defect in new[] { "extra", "extra-meta", "escape", "absolute", "symlink", "hardlink", "mode", "hash", "candidate", "round", "missing-registration" })
        {
            var damaged = Path.Combine(root, "build/" + defect + ".tgz");
            using (var input = new GZipStream(File.OpenRead(archive), CompressionMode.Decompress))
            using (var reader = new TarReader(input))
            using (var output = new GZipStream(File.Create(damaged), CompressionLevel.Fastest))
            using (var writer = new TarWriter(output))
            {
                while (reader.GetNextEntry(copyData: true) is { } entry)
                {
                    if (defect == "missing-registration" && entry.Name == "Meta/ci-checks.json") continue;
                    if (entry.Name == Log && defect == "mode") entry.Mode ^= UnixFileMode.UserExecute;
                    if (entry.Name == Log && defect == "hash") entry.DataStream = new MemoryStream("corrupt"u8.ToArray());
                    if (entry.Name == CommonExecutionEvidence.CurrentPath && defect is "candidate" or "round")
                    {
                        var record = CommonExecutionEvidence.Read<CommonStageRecord>(root, CommonExecutionEvidence.CurrentPath);
                        var node = System.Text.Json.Nodes.JsonNode.Parse(File.ReadAllText(Path.Combine(root, entry.Name)))!;
                        node[defect] = defect == "candidate" ? new string('a', 64) : record.Round + "-stale";
                        entry.DataStream = new MemoryStream(System.Text.Encoding.UTF8.GetBytes(node.ToJsonString()));
                    }
                    writer.WriteEntry(entry);
                }
                var extra = defect switch { "extra" => "build/ci/undeclared", "extra-meta" => "Meta/undeclared.json",
                    "escape" => "../escaped", "absolute" => "/escaped", "symlink" or "hardlink" => "build/ci/link", _ => null };
                if (extra is not null)
                {
                    var type = defect == "symlink" ? TarEntryType.SymbolicLink : defect == "hardlink" ? TarEntryType.HardLink : TarEntryType.RegularFile;
                    var entry = new PaxTarEntry(type, extra);
                    if (type == TarEntryType.RegularFile) entry.DataStream = new MemoryStream("extra"u8.ToArray());
                    else entry.LinkName = Log;
                    writer.WriteEntry(entry);
                }
            }
            var rejected = Cli("restore", target, damaged);
            Assert.True(rejected.Exit == 2, defect + ": " + rejected.Text);
            Assert.DoesNotContain("status=verified", rejected.Text);
            Assert.False(File.Exists(Path.Combine(target, "build/ci/undeclared")));
            var recovered = Cli("restore", target, archive);
            Assert.True(recovered.Exit == 0, recovered.Text);
        }
        foreach (var (wrongCommit, run, attempt) in new[] { (commit, "18", "2"), (commit, "17", "3"), (new string('a', 40), "17", "2") })
        {
            var rejected = Cli("verify", target, archive, wrongCommit, run, attempt);
            Assert.True(rejected.Exit == 2, rejected.Text);
        }

        (int Exit, string Text) Cli(string command, string destination, string bundle, string? candidate = null, string run = "17", string attempt = "2") =>
            SharedBuildContractTests.Process(destination, "python3", ["-B", Path.Combine(repository, "tools/scripts/workflow/ci.py"),
                command, "--repository", destination, "--stage", "current", "--commit", candidate ?? commit,
                "--run-id", run, "--run-attempt", attempt, "--archive", bundle], hangGuard: TestBudgets.WorkflowProcessHangGuard);
    }

    [Theory]
    [InlineData("valid")]
    [InlineData("undeclared")]
    [InlineData("corrupt")]
    public void TruthReleaseRestoresOnlyVerifiedCurrentArtifacts(string defect)
    {
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
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
                    entry.DataStream = new MemoryStream("corrupt"u8.ToArray());
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
        var result = SharedBuildContractTests.Process(root, "python3", ["-B", "-c", """
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

    [Fact]
    public void CurrentSealRequiresTheIncrementalSeedCompanion()
    {
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        Prepare(fixture, current: false);
        Report(fixture.Root);
        TemporaryFileSystem.File.Delete(Path.Combine(fixture.Root, CommonExecutionEvidence.ReportPath + ".seed.json"));
        Assert.ThrowsAny<IOException>(() => CommonExecutionEvidence.SealCurrent(fixture.Root, CommonExecutionEvidence.ValidateBuild(fixture.Root), Steps(CommonExecutionEvidence.CurrentSteps)));
    }

    [Theory]
    [InlineData("build")]
    [InlineData("engineering")]
    [InlineData("current")]
    public void CompleteNulListedBundleMovesAcrossRootsAndPreservesExecutableModes(string stage)
    {
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        Prepare(fixture, stage == "current");
        var commit = Git(fixture.Root, "rev-parse", "HEAD");
        var archive = Path.Combine(fixture.Root, "build", "transfer.tgz");
        Assert.Equal(0, Run("transport-pack", fixture.Root, stage, commit, "17", "2", archive));
        var target = Path.Combine(fixture.Root, "build", "destination");
        Git(fixture.Root, "clone", "--quiet", "--no-hardlinks", fixture.Root, target);
        if (stage == "engineering")
        {
            var buildArchive = Path.Combine(fixture.Root, "build", "build.tgz");
            Assert.Equal(0, Run("transport-pack", fixture.Root, "build", commit, "17", "2", buildArchive));
            using var shared = new GZipStream(File.OpenRead(buildArchive), CompressionMode.Decompress);
            TarFile.ExtractToDirectory(shared, target, overwriteFiles: true);
        }
        using (var input = new GZipStream(File.OpenRead(archive), CompressionMode.Decompress))
            TarFile.ExtractToDirectory(input, target, overwriteFiles: true);
        Assert.Equal(0, Run("transport-verify", target, stage, commit, "17", "2"));
        Assert.Equal(stage == "engineering", TemporaryFileSystem.File.Exists(Path.Combine(target, CommonExecutionEvidence.EngineeringPath)));
        Assert.Equal(stage == "engineering", TemporaryFileSystem.File.Exists(Path.Combine(target, CommonExecutionEvidence.TestsPath)));
        Assert.Equal(stage == "current", TemporaryFileSystem.File.Exists(Path.Combine(target, CommonExecutionEvidence.CurrentPath)));
        if (!OperatingSystem.IsWindows())
            Assert.NotEqual(0, (int)(File.GetUnixFileMode(Path.Combine(target, Log)) & UnixFileMode.UserExecute));
        if (stage == "current")
            foreach (var suffix in new[] { "", ".sha256", ".input.attestation", ".provenance.json", ".materials.zip", ".seed.json" })
                Assert.Equal(TemporaryFileSystem.File.ReadAllBytes(Path.Combine(fixture.Root, CommonExecutionEvidence.ReportPath + suffix)),
                    TemporaryFileSystem.File.ReadAllBytes(Path.Combine(target, CommonExecutionEvidence.ReportPath + suffix)));
        Assert.Equal(2, Run("transport-verify", target, stage, commit, "18", "2"));
        Assert.Equal(2, Run("transport-verify", target, stage, commit, "17", "3"));
        Assert.Equal(2, Run("transport-verify", target, stage, new string('a', 40), "17", "2"));
        TemporaryFileSystem.File.AppendAllText(Path.Combine(target, Log), "corrupt");
        Assert.Equal(2, Run("transport-verify", target, stage, commit, "17", "2"));
    }

    [Theory]
    [InlineData("candidate")]
    [InlineData("failed-evidence")]
    [InlineData("missing-report")]
    [InlineData("missing-seed")]
    public void RequiredTransportCannotSealStaleOrIncompleteProduction(string defect)
    {
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        Prepare(fixture, current: true);
        switch (defect)
        {
            case "candidate": TemporaryFileSystem.File.AppendAllText(Path.Combine(fixture.Root, CurrentExecutionContractTests.CandidateFixture.First), "\n"); break;
            case "failed-evidence":
                var record = CommonExecutionEvidence.Read<CommonStageRecord>(fixture.Root, CommonExecutionEvidence.CurrentPath);
                CommonExecutionEvidence.Write(fixture.Root, CommonExecutionEvidence.CurrentPath,
                    record with { Steps = record.Steps.Select(step => step with { Exit = 1 }).ToArray() });
                break;
            case "missing-report": TemporaryFileSystem.File.Delete(Path.Combine(fixture.Root, CommonExecutionEvidence.ReportPath)); break;
            case "missing-seed": TemporaryFileSystem.File.Delete(Path.Combine(fixture.Root, CommonExecutionEvidence.ReportPath + ".seed.json")); break;
        }
        Assert.Equal(2, Run("transport-pack", fixture.Root, "current", Git(fixture.Root, "rev-parse", "HEAD"), "17", "2", Path.Combine(fixture.Root, "build", "bad.tgz")));
    }

    private const string Log = "build/ci/fixture-executable";
    private static StageStep[] Steps(string[] names) => names.Select(name => new StageStep(name, name.EndsWith("proof", StringComparison.Ordinal) ? 1 : 0, 0, "executed", Log)).ToArray();

    private static void PrepareCurrentRuntime(CurrentExecutionContractTests.CandidateFixture fixture)
    {
        Prepare(fixture, current: false);
        var root = fixture.Root;
        var runtime = Path.GetDirectoryName(CommonExecutionEvidence.RunnerPath)!;
        Directory.CreateDirectory(Path.Combine(root, runtime));
        var binaries = Directory.GetFiles(Path.Combine(TestRepositoryLayout.FindRoot(), runtime)).Select(file =>
        {
            var relative = runtime + "/" + Path.GetFileName(file);
            File.Copy(file, Path.Combine(root, relative));
            return relative;
        }).ToArray();
        SealEngineering(root, CommonExecutionEvidence.Candidate(root), binaries, Steps(CommonExecutionEvidence.EngineeringSteps));
        Report(root);
        CheckEvidenceFixture.Seal(root, "current", CommonExecutionEvidence.ValidateBuild(root));
        CommonExecutionEvidence.SealCurrent(root, CommonExecutionEvidence.ValidateBuild(root), Steps(CommonExecutionEvidence.CurrentSteps));
    }

    private static void Prepare(CurrentExecutionContractTests.CandidateFixture fixture, bool current)
    {
        fixture.Build();
        Assert.Equal(0, Program.RunCurrentTests(fixture.Root, (_, results) => { fixture.WriteTrx(results, "Passed"); return 0; }, TextWriter.Null));
        TemporaryFileSystem.File.WriteAllText(Path.Combine(fixture.Root, Log), "#!/bin/sh\nexit 0\n");
        if (!OperatingSystem.IsWindows())
            File.SetUnixFileMode(Path.Combine(fixture.Root, Log), UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var candidate = CommonExecutionEvidence.Read<TestExecutionRecord>(fixture.Root, CommonExecutionEvidence.TestsPath).Candidate;
        CiTransportTests.SealEngineering(fixture.Root, candidate, [Log], Steps(CommonExecutionEvidence.EngineeringSteps));
        if (!current) return;
        Report(fixture.Root);
        CheckEvidenceFixture.Seal(fixture.Root, "current", CommonExecutionEvidence.ValidateBuild(fixture.Root));
        CommonExecutionEvidence.SealCurrent(fixture.Root, CommonExecutionEvidence.ValidateBuild(fixture.Root), Steps(CommonExecutionEvidence.CurrentSteps));
    }

    internal static void SealEngineering(string root, string candidate, IEnumerable<string> binaries, StageStep[] steps)
    {
        var build = CommonExecutionEvidence.ValidateBuild(root);
        Assert.Equal(candidate, build.Candidate);
        build = build with { Materials = CommonExecutionEvidence.Materials(root,
            build.Materials.Select(material => material.Path).Concat(binaries)) };
        CommonExecutionEvidence.Write(root, CommonExecutionEvidence.BuildPath, build);
        var list = CommonExecutionEvidence.BundleListPath("build");
        TemporaryFileSystem.File.WriteAllText(Path.Combine(root, list), string.Join('\0',
            build.Materials.Select(material => material.Path).Append(CommonExecutionEvidence.BuildPath).Append(list)
                .Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal)) + "\0");
        CheckEvidenceFixture.Seal(root, "engineering", build);
        CommonExecutionEvidence.SealEngineering(root, build, steps);
    }

    internal static void Report(string root)
    {
        var report = Path.Combine(root, CommonExecutionEvidence.ReportPath);
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(report)!);
        TemporaryFileSystem.File.WriteAllText(report, "{\"modules\": [], \"schema\": \"stratalint-raw-lean-report-v2\"}\n");
        using (var stream = File.Create(report + ".materials.zip"))
        using (new ZipArchive(stream, ZipArchiveMode.Create)) { }
        foreach (var suffix in new[] { ".sha256", ".input.attestation", ".provenance.json", ".seed.json" })
            TemporaryFileSystem.File.WriteAllText(report + suffix, "fixture companion\n");
    }

    private static int Run(string command, string root, string stage, string commit, string run, string attempt, string? archive = null) =>
        Program.Run(new[] { command, "--repository", root, "--stage", stage, "--commit", commit, "--run-id", run, "--run-attempt", attempt }
            .Concat(archive is null ? [] : new[] { "--archive", archive }).ToArray(), TestResultEvidence.Load, TextWriter.Null, TextWriter.Null);

    private static string Git(string root, params string[] args)
    {
        var start = new ProcessStartInfo("git") { WorkingDirectory = root, RedirectStandardOutput = true, RedirectStandardError = true };
        foreach (var arg in args) start.ArgumentList.Add(arg);
        using var process = Process.Start(start)!;
        var output = process.StandardOutput.ReadToEnd();
        var error = process.StandardError.ReadToEnd();
        process.WaitForExit();
        Assert.True(process.ExitCode == 0, error);
        return output.Trim();
    }
}
