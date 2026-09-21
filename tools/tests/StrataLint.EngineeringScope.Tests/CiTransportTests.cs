using System.Diagnostics;
using System.Formats.Tar;
using System.IO.Compression;
using System.Security.Cryptography;
using System.Text.Json;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed partial class CiTransportTests
{

    [Fact]
    public void CurrentCliTransportRoundTripRetainsRegistrationAndRejectsInvalidBundles()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        Prepare(fixture, current: false);
        var root = fixture.Root;
        var repository = TestRepositoryLayout.FindRoot();
        var runtime = Path.GetDirectoryName(CommonExecutionEvidence.RunnerPath)!;
        Directory.CreateDirectory(Path.Combine(root, runtime));
        var binaries = Directory.GetFiles(Path.Combine(repository, runtime)).Select(file =>
        {
            var relative = runtime + "/" + Path.GetFileName(file);
            File.Copy(file, Path.Combine(root, relative));
            return relative;
        }).ToArray();
        SealEngineering(root, CommonExecutionEvidence.Candidate(root), binaries, Steps(CommonExecutionEvidence.EngineeringSteps));
        Report(root);
        CheckEvidenceFixture.Seal(root, "current", CommonExecutionEvidence.ValidateBuild(root));
        CommonExecutionEvidence.SealCurrent(root, CommonExecutionEvidence.ValidateBuild(root), Steps(CommonExecutionEvidence.CurrentSteps));
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
                    if (entry.Name == Log && defect == "hash")
                        entry = new PaxTarEntry(TarEntryType.RegularFile, entry.Name) { Mode = entry.Mode,
                            ModificationTime = entry.ModificationTime, DataStream = new MemoryStream("corrupt"u8.ToArray()) };
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
    [InlineData("build")]
    [InlineData("engineering")]
    [InlineData("current")]
    [InlineData("engineering-seed")]
    [InlineData("current-seed")]
    public void NativeTransportSharesRequiredPayloadsAndRestoresIndependentFiles(string stage)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        var root = fixture.Root;
        Prepare(fixture, stage.StartsWith("current", StringComparison.Ordinal));
        var owner = stage.Replace("-seed", "", StringComparison.Ordinal);
        var original = CommonExecutionEvidence.Read<CommonStageRecord>(root, "build/ci/" + owner + ".json");
        var equal = original.Materials.GroupBy(material => material.Sha256)
            .First(group => group.Count() > 1).Take(2).ToArray();
        File.SetLastWriteTimeUtc(Path.Combine(root, equal[0].Path), new DateTime(2020, 1, 2, 3, 4, 5, DateTimeKind.Utc));
        File.SetLastWriteTimeUtc(Path.Combine(root, equal[1].Path), new DateTime(2021, 2, 3, 4, 5, 6, DateTimeKind.Utc));
        if (owner == "current")
            File.SetUnixFileMode(Path.Combine(root, CommonExecutionEvidence.ReportPath + ".input.attestation"),
                UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var commit = Git(root, "rev-parse", "HEAD");
        var archive = Path.Combine(root, "build/alias.tgz");
        Assert.Equal(0, Run("transport-pack", root, stage, commit, "17", "2", archive));
        var manifest = CommonExecutionEvidence.Read<CiTransportRecord>(root, CiTransport.ManifestPath(stage));
        var entries = new Dictionary<string, (TarEntryType Type, string Link, UnixFileMode Mode, DateTimeOffset Modified, long Length)>(StringComparer.Ordinal);
        using (var input = new GZipStream(File.OpenRead(archive), CompressionMode.Decompress))
        using (var reader = new TarReader(input))
            while (reader.GetNextEntry() is { } entry)
                entries.Add(entry.Name, (entry.EntryType, entry.LinkName, entry.Mode, entry.ModificationTime, entry.Length));
        var seed = stage.EndsWith("-seed", StringComparison.Ordinal);
        var groups = manifest.Materials.GroupBy(material => (material.Sha256, material.Mode)).ToArray();
        Assert.Contains(groups, group => group.Count() > 1);
        foreach (var group in groups)
        {
            var paths = group.Select(material => material.Path).Order(StringComparer.Ordinal).ToArray();
            var regular = paths.Where(path => entries[path].Type is TarEntryType.RegularFile or TarEntryType.V7RegularFile).ToArray();
            Assert.True(regular.Length == (seed ? paths.Length : 1),
                $"{stage}: expected {(seed ? paths.Length : 1)} regular payloads for {group.Key}, actual {regular.Length}");
            foreach (var path in paths)
            {
                Assert.Equal((UnixFileMode)group.Key.Mode, entries[path].Mode);
                Assert.Equal(new DateTimeOffset(File.GetLastWriteTimeUtc(Path.Combine(root, path))).ToUnixTimeSeconds(),
                    entries[path].Modified.ToUnixTimeSeconds());
                if (seed || path == regular[0]) continue;
                Assert.Equal(TarEntryType.HardLink, entries[path].Type);
                Assert.Equal(regular[0], entries[path].Link);
                Assert.Equal(0, entries[path].Length);
            }
        }
        Assert.Equal(TarEntryType.RegularFile, entries[CiTransport.ManifestPath(stage)].Type);
        if (seed) return; // Optional seed consumers retain the existing regular-file format.
        if (owner == "current") Assert.Contains(manifest.Materials.GroupBy(material => material.Sha256),
            group => group.Select(material => material.Mode).Distinct().Count() > 1);
        var target = Path.Combine(root, "build/destination");
        Git(root, "clone", "--quiet", "--no-hardlinks", root, target);
        if (stage == "engineering")
        {
            var buildArchive = Path.Combine(root, "build/shared.tgz");
            Assert.Equal(0, Run("transport-pack", root, "build", commit, "17", "2", buildArchive));
            var shared = Extract(target, buildArchive, "build");
            Assert.True(shared.Exit == 0, shared.Text);
        }
        var restored = Extract(target, archive, stage);
        Assert.True(restored.Exit == 0, restored.Text);
        Assert.Equal(0, Run("transport-verify", target, stage, commit, "17", "2"));
        foreach (var material in manifest.Materials)
        {
            var source = Path.Combine(root, material.Path);
            var destination = Path.Combine(target, material.Path);
            Assert.Equal(File.ReadAllBytes(source), File.ReadAllBytes(destination));
            Assert.Equal(File.GetUnixFileMode(source), File.GetUnixFileMode(destination));
            Assert.Equal(entries[material.Path].Modified.ToUnixTimeSeconds(),
                new DateTimeOffset(File.GetLastWriteTimeUtc(destination)).ToUnixTimeSeconds());
            if (equal.Any(original => original.Path == material.Path))
                Assert.Equal(File.GetLastWriteTimeUtc(source), File.GetLastWriteTimeUtc(destination));
            Assert.Null(new FileInfo(destination).LinkTarget);
        }
        var pair = groups.First(group => group.Count() > 1).Take(2).Select(material => Path.Combine(target, material.Path)).ToArray();
        var untouched = File.ReadAllBytes(pair[1]);
        File.WriteAllText(pair[0], "independent mutation\n");
        Assert.Equal(untouched, File.ReadAllBytes(pair[1]));
    }

    [Theory]
    [InlineData("valid")]
    [InlineData("missing")]
    [InlineData("escape")]
    [InlineData("absolute")]
    [InlineData("self")]
    [InlineData("chain")]
    [InlineData("directory")]
    [InlineData("symlink")]
    [InlineData("manifest-target")]
    [InlineData("manifest-alias")]
    [InlineData("hash-association")]
    [InlineData("mode-association")]
    [InlineData("header-mode")]
    [InlineData("target-content")]
    public void DeclaredArchiveAliasesAreValidatedBeforeAnyMaterialIsWritten(string defect)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        var root = fixture.Root;
        Prepare(fixture, current: false);
        var commit = Git(root, "rev-parse", "HEAD");
        var archive = Path.Combine(root, "build/original.tgz");
        Assert.Equal(0, Run("transport-pack", root, "build", commit, "17", "2", archive));
        var manifestPath = CiTransport.ManifestPath("build");
        var manifest = CommonExecutionEvidence.Read<CiTransportRecord>(root, manifestPath);
        var pair = manifest.Materials.GroupBy(material => (material.Sha256, material.Mode))
            .First(group => group.Count() > 1).OrderBy(material => material.Path, StringComparer.Ordinal).Take(2).ToArray();
        var first = pair[0].Path;
        var alias = pair[1].Path;
        if (defect is "hash-association" or "mode-association")
            manifest = manifest with { Materials = manifest.Materials.Select(material => material.Path != alias ? material
                : defect == "hash-association" ? material with { Sha256 = new string('0', 64) }
                : material with { Mode = material.Mode ^ (int)UnixFileMode.UserExecute }).ToArray() };
        CommonExecutionEvidence.Write(root, manifestPath, manifest);
        var crafted = Path.Combine(root, "build/crafted.tgz");
        using (var output = new GZipStream(File.Create(crafted), CompressionLevel.Fastest))
        using (var writer = new TarWriter(output))
            foreach (var path in manifest.Materials.Select(material => material.Path).Append(manifestPath))
            {
                var type = path == alias || path == first && defect == "chain" || path == manifestPath && defect == "manifest-alias"
                    ? TarEntryType.HardLink : path == first && defect == "directory" ? TarEntryType.Directory
                    : path == first && defect == "symlink" ? TarEntryType.SymbolicLink : TarEntryType.RegularFile;
                var entry = new PaxTarEntry(type, path) { Mode = File.GetUnixFileMode(Path.Combine(root, path)),
                    ModificationTime = File.GetLastWriteTimeUtc(Path.Combine(root, path)) };
                if (type is TarEntryType.HardLink or TarEntryType.SymbolicLink)
                    entry.LinkName = path != alias ? alias : defect switch { "missing" => "build/ci/absent",
                        "escape" => "../escaped", "absolute" => "/escaped", "self" => alias,
                        "manifest-target" => manifestPath, _ => first };
                else if (type == TarEntryType.RegularFile)
                    entry.DataStream = new MemoryStream(path == first && defect == "target-content" ? "corrupt target"u8.ToArray()
                        : File.ReadAllBytes(Path.Combine(root, path)));
                if (path == alias && defect == "header-mode") entry.Mode ^= UnixFileMode.UserExecute;
                writer.WriteEntry(entry);
            }
        var target = Path.Combine(root, "build/empty-destination");
        Directory.CreateDirectory(target);
        if (defect == "target-content") Git(root, "clone", "--quiet", "--no-hardlinks", root, target);
        var extracted = Extract(target, crafted, "build");
        if (defect is not ("valid" or "target-content"))
        {
            Assert.True(extracted.Exit != 0, defect + ": " + extracted.Text);
            Assert.Empty(Directory.GetFileSystemEntries(target));
            return;
        }
        Assert.True(extracted.Exit == 0, extracted.Text);
        if (defect == "target-content")
        {
            Assert.Equal(commit, Git(target, "rev-parse", "HEAD"));
            Assert.Equal(2, Run("transport-verify", target, "build", commit, "17", "2"));
            Assert.Contains("artifact integrity mismatch: " + first,
                Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidateBuild(target)).Message, StringComparison.Ordinal);
            return;
        }
        foreach (var material in manifest.Materials)
            Assert.Equal(File.ReadAllBytes(Path.Combine(root, material.Path)), File.ReadAllBytes(Path.Combine(target, material.Path)));
        var original = File.ReadAllBytes(Path.Combine(target, first));
        File.WriteAllText(Path.Combine(target, alias), "independent alias\n");
        Assert.Equal(original, File.ReadAllBytes(Path.Combine(target, first)));
    }

    private static (int Exit, string Text) Extract(string root, string archive, string stage) =>
        SharedBuildContractTests.Process(root, "python3", ["-B", "-c",
            "import pathlib,sys; sys.path.insert(0,sys.argv[1]); import ci; ci.extract(pathlib.Path(sys.argv[2]),pathlib.Path(sys.argv[3]),sys.argv[4])",
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/workflow"), root, archive, stage],
            hangGuard: TestBudgets.WorkflowProcessHangGuard);

    [Fact]
    public void CurrentSealRequiresThePublishedProvenanceCompanion()
    {
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        Prepare(fixture, current: false);
        Report(fixture.Root);
        TemporaryFileSystem.File.Delete(Path.Combine(fixture.Root, CommonExecutionEvidence.ReportPath + ".provenance.json"));
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
            foreach (var suffix in new[] { "", ".sha256", ".input.attestation", ".provenance.json", ".materials.zip" })
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
    [InlineData("missing-provenance")]
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
            case "missing-provenance": TemporaryFileSystem.File.Delete(Path.Combine(fixture.Root, CommonExecutionEvidence.ReportPath + ".provenance.json")); break;
        }
        Assert.Equal(2, Run("transport-pack", fixture.Root, "current", Git(fixture.Root, "rev-parse", "HEAD"), "17", "2", Path.Combine(fixture.Root, "build", "bad.tgz")));
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

    internal static (int Exit, string Text) ProduceReport(string root)
    {
        var repository = TestRepositoryLayout.FindRoot();
        return SharedBuildContractTests.Process(root, "python3", ["-B", "-c", """
            import json, pathlib, shutil, sys, time
            repository, root, relative = map(pathlib.Path, sys.argv[1:])
            sys.path.insert(0, str(repository / 'tools/lean-inspector/tests'))
            from test_native import NativeTests
            import publication
            NativeTests.setUpClass()
            fixture = NativeTests('test_native_invalidation')
            fixture.setUp()
            phases = fixture.root / 'native-phases.jsonl'
            fixture.env['STRATALINT_INSPECTOR_PHASES'] = str(phases)
            observation = {'processes': None, 'phase_lines': 0}
            owned_processes = fixture.owned_processes
            def observed_processes(command, **options):
                rows = owned_processes(command, **options)
                identity = sorted((row['pid'], row['identity'], row['command']) for row in rows)
                if identity != observation['processes']:
                    print('NATIVE_HANDOFF_PROCESSES ' + json.dumps(dict(
                        monotonic_ms=time.monotonic_ns() // 1_000_000, processes=rows)),
                        file=sys.stderr, flush=True)
                    observation['processes'] = identity
                if phases.exists():
                    lines = phases.read_text().splitlines()
                    for line in lines[observation['phase_lines']:]:
                        print('NATIVE_HANDOFF_PHASE ' + line, file=sys.stderr, flush=True)
                    observation['phase_lines'] = len(lines)
                return rows
            fixture.owned_processes = observed_processes
            run_command = fixture.guarded_command
            def observed_output(stream, text):
                print('NATIVE_HANDOFF_OUTPUT ' + json.dumps(dict(stream=stream, text=text)),
                    file=sys.stderr, flush=True)
            def observed_command(args, **options):
                if pathlib.Path(args[0]).name == 'lake' and 'build' in args:
                    args = [args[0], '--verbose', *args[1:]]
                print('NATIVE_HANDOFF_COMMAND ' + json.dumps(list(args)), file=sys.stderr, flush=True)
                result = run_command(args, observe_output=observed_output, **options)
                print('NATIVE_HANDOFF_COMMAND_EXIT ' + str(result.returncode), file=sys.stderr, flush=True)
                return result
            fixture.guarded_command = observed_command
            try:
                # Native fixtures supply real Lake facets; this shape uses the
                # managed module names consumed by the C# report reader.
                source = fixture.root / 'Fixture.lean'
                source.rename(fixture.root / 'Trureturing.lean')
                for name in ('lakefile.toml', 'lean-report-inputs.json', 'utility.json'):
                    path = fixture.root / name
                    path.write_text(path.read_text().replace('Fixture', 'Trureturing'))
                fixture.write('utility.json', '[]\n')
                fixture.build()
                print('NATIVE_HANDOFF_PUBLISH', file=sys.stderr, flush=True)
                fixture.publish()
                for name in ('D5', 'Trureturing.lean', 'External.lean', 'ClaimSupport.lean',
                        'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'):
                    source, target = fixture.root / name, root / name
                    if source.is_dir(): shutil.copytree(source, target, dirs_exist_ok=True)
                    else: shutil.copyfile(source, target)
                destination = root / relative
                destination.parent.mkdir(parents=True, exist_ok=True)
                for suffix in publication.SUFFIXES:
                    shutil.copyfile(publication.member(fixture.root / 'public.json', suffix),
                                    publication.member(destination, suffix))
                publication.member(destination, '.sha256').write_text(publication.digest(destination)
                    + '  ' + destination.name + '\n')
                print('NATIVE_CURRENT_HANDOFF files=' + str(len(publication.SUFFIXES)))
            finally:
                fixture.doCleanups()
            """, repository, root, CommonExecutionEvidence.ReportPath],
            hangGuard: TestBudgets.WorkflowProcessHangGuard);
    }

    internal static void Report(string root)
    {
        var report = Path.Combine(root, CommonExecutionEvidence.ReportPath);
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(report)!);
        TemporaryFileSystem.File.WriteAllText(report, "{\"modules\": [], \"schema\": \"stratalint-raw-lean-report-v2\"}\n");
        using (var stream = File.Create(report + ".materials.zip"))
        using (new ZipArchive(stream, ZipArchiveMode.Create)) { }
        TemporaryFileSystem.File.WriteAllText(report + ".sha256", CommonExecutionEvidence.Hash(report) + "  " + Path.GetFileName(report) + "\n");
        foreach (var suffix in new[] { ".input.attestation", ".provenance.json" })
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
