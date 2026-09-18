using System.Formats.Tar;
using System.IO.Compression;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed partial class ExecutionSeedTransportBehaviorTests
{
    [Theory]
    [InlineData("engineering")]
    [InlineData("current")]
    public void OrdinaryPackProducesOptionalSeedWithOneCandidateRead(string stage)
    {
        using var fixture = Prepare(stage);
        var root = fixture.Root;
        var commit = SharedBuildContractTests.Git(root, "rev-parse", "HEAD");
        var environment = Environment(commit, root, "43", "2");
        var trace = Path.Combine(root, "build/git-trace.jsonl");
        environment["GIT_TRACE2_EVENT"] = trace;
        var archive = Path.Combine(root, "build", stage + ".tgz");
        var seedArchive = Path.Combine(root, "build", stage + "-seed.tgz");
        Directory.Delete(Path.Combine(root, CommonExecutionEvidence.CheckSeedPath(stage)), recursive: true);
        if (stage == "engineering") Directory.Delete(Path.Combine(root, CommonExecutionEvidence.TestSeedPath), recursive: true);
        var packed = NativeTransport(root, "transport-pack", stage, commit, environment,
            "--archive", archive, "--seed-archive", seedArchive);
        Assert.True(packed.Exit == 0, packed.Text);
        Assert.True(File.Exists(archive));
        Assert.True(File.Exists(seedArchive));
        var commands = File.ReadLines(trace).Select(line => JsonNode.Parse(line)!)
            .Where(row => row["event"]?.ToString() == "start")
            .Select(row => row["argv"]!.AsArray().Select(value => value!.ToString()).ToArray())
            .Where(arguments => arguments.Contains("ls-files", StringComparer.Ordinal)).ToArray();
        Assert.Single(commands, arguments => arguments.Contains("--stage", StringComparer.Ordinal));
        Assert.Single(commands, arguments => arguments.Contains("--others", StringComparer.Ordinal));
        var outputs = File.ReadAllLines(environment["GITHUB_OUTPUT"]);
        Assert.Contains("artifact_name=ci-" + stage + "-43-2", outputs);
        Assert.Contains("seed_artifact_name=ci-" + stage + "-seed-43-2", outputs);
        Assert.Contains("seed_archive=" + seedArchive, outputs);
        var original = NativeTransport(root, "transport-verify", stage, commit, environment);
        Assert.True(original.Exit == 0, original.Text);
        var wrongCommit = NativeTransport(root, "transport-verify", stage, new string('a', 40), environment);
        Assert.Equal(2, wrongCommit.Exit);
        Assert.Contains("exact clean candidate commit", wrongCommit.Text, StringComparison.Ordinal);
        environment.Remove("GIT_TRACE2_EVENT");
        var target = Destination(fixture, "paired-" + stage);
        var restored = Workflow(target, "restore", stage + "-seed", commit, seedArchive, environment);
        Assert.True(restored.Exit == 0, restored.Text);
        AssertAccepted(root, target, stage, "paired-" + stage);
        if (stage == "engineering")
        {
            var manifest = CommonExecutionEvidence.Read<CiTransportRecord>(root, CiTransport.ManifestPath("engineering-seed"));
            Assert.Contains(manifest.Materials, material => material.Path == CommonExecutionEvidence.TestSeedPath + "/tests.json");
            Assert.Contains(manifest.Materials, material => material.Path.EndsWith(".trx", StringComparison.Ordinal));
        }
    }

    [Theory]
    [InlineData("engineering", "material")]
    [InlineData("engineering", "round")]
    [InlineData("current", "material")]
    [InlineData("current", "round")]
    public void OrdinaryPackRejectsDamagedAcceptanceBeforePublishingEitherArchive(string stage, string damage)
    {
        using var fixture = Prepare(stage);
        var root = fixture.Root;
        var commit = SharedBuildContractTests.Git(root, "rev-parse", "HEAD");
        var path = stage == "current" ? CommonExecutionEvidence.CurrentPath : CommonExecutionEvidence.EngineeringPath;
        var record = CommonExecutionEvidence.Read<CommonStageRecord>(root, path);
        if (damage == "material") File.AppendAllText(Path.Combine(root, record.Steps[0].Log), "corrupt");
        else CommonExecutionEvidence.Write(root, path, record with { Round = new string('0', 32) });
        var archive = Path.Combine(root, "build/required.tgz");
        var seedArchive = Path.Combine(root, "build/optional.tgz");
        var packed = NativeTransport(root, "transport-pack", stage, commit, Environment(commit, root, "44", "1"),
            "--archive", archive, "--seed-archive", seedArchive);
        Assert.Equal(2, packed.Exit);
        Assert.Contains(damage == "material" ? "artifact integrity mismatch" : "candidate identity or round mismatch",
            packed.Text, StringComparison.Ordinal);
        Assert.False(File.Exists(archive));
        Assert.False(File.Exists(seedArchive));
    }

    [Theory]
    [InlineData("engineering", "blocked-parent")]
    [InlineData("current", "blocked-parent")]
    [InlineData("engineering", "evidence-directory")]
    [InlineData("current", "evidence-directory")]
    public void OptionalSeedArchiveFailurePreservesRequiredTransport(string stage, string destination)
    {
        using var fixture = Prepare(stage);
        var root = fixture.Root;
        var commit = SharedBuildContractTests.Git(root, "rev-parse", "HEAD");
        var environment = Environment(commit, root, "45", "1");
        fixture.Write("build/blocked-seed-parent", "a file cannot contain an archive");
        var archive = Path.Combine(root, "build/required.tgz");
        var seedArchive = Path.Combine(root, destination == "blocked-parent"
            ? "build/blocked-seed-parent/optional.tgz" : "build/ci/optional.tgz");
        var packed = NativeTransport(root, "transport-pack", stage, commit, environment,
            "--archive", archive, "--seed-archive", seedArchive);
        Assert.True(packed.Exit == 0, packed.Text);
        Assert.Contains("COMMON_CHECK_SEED_NOT_SAVED stage=" + stage, packed.Text, StringComparison.Ordinal);
        Assert.True(File.Exists(archive));
        Assert.False(File.Exists(seedArchive));
        Assert.DoesNotContain(File.ReadAllLines(environment["GITHUB_OUTPUT"]), line => line.StartsWith("seed_", StringComparison.Ordinal));
        var verified = NativeTransport(root, "transport-verify", stage, commit, environment);
        Assert.True(verified.Exit == 0, verified.Text);
    }

    [Theory]
    [InlineData("engineering", false)]
    [InlineData("engineering", true)]
    [InlineData("current", false)]
    [InlineData("current", true)]
    public void PrepackedSnapshotReusesOnlyVerifiedSameExecutionSeed(string stage, bool bounded)
    {
        if (OperatingSystem.IsWindows()) throw Xunit.Sdk.SkipException.ForSkip("native tar transport fixture is unsupported on Windows");
        using var fixture = Prepare(stage);
        var root = fixture.Root;
        var repository = TestRepositoryLayout.FindRoot();
        var commit = SharedBuildContractTests.Git(root, "rev-parse", "HEAD");
        var environment = Environment(commit, root, "46", "2");
        var seedArchive = Path.Combine(root, "build/prepared-seed.tgz");
        var packed = NativeTransport(root, "transport-pack", stage, commit, environment,
            "--archive", Path.Combine(root, "build/required.tgz"), "--seed-archive", seedArchive);
        Assert.True(packed.Exit == 0, packed.Text);
        var before = File.ReadAllBytes(seedArchive);
        var dotnet = SharedBuildContractTests.Process(root, "which", ["dotnet"]).Text.Trim();
        fixture.Write("build/verify-only/dotnet", """
            #!/bin/sh
            set -eu
            printf '%s\n' "$*" >> "$CONTRACT_CALLS"
            test "$2" = transport-verify
            exec "$CONTRACT_DOTNET" "$@"
            """);
        File.SetUnixFileMode(Path.Combine(root, "build/verify-only/dotnet"),
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        environment["PATH"] = Path.Combine(root, "build/verify-only") + Path.PathSeparator + System.Environment.GetEnvironmentVariable("PATH");
        environment["CONTRACT_DOTNET"] = dotnet;
        environment["CONTRACT_CALLS"] = Path.Combine(root, "build/verification-calls");
        var snapshot = bounded
            ? SharedBuildContractTests.Process(root, "python3", ["-B", "-c", """
                import pathlib, sys
                sys.path.insert(0, sys.argv[1])
                from cache_deadline import CacheDeadline
                from lean_actions import actions_keys, snapshot
                root, archive = map(pathlib.Path, sys.argv[2:4])
                snapshot(root, actions_keys(root), [sys.argv[4]], seed_archive=archive,
                         deadline=CacheDeadline(400, monotonic=lambda: 100))
                """, Path.Combine(repository, "tools/scripts/worktree"), root, seedArchive, stage], environment,
                TestBudgets.LongWorkflowProcessHangGuard)
            : Python(root, repository, ["snapshot", "--repository", root, "--layers", stage, "--seed-archive", seedArchive], environment);
        AssertReceipt(snapshot, "snapshot");
        Assert.Equal("true", Key(snapshot.Text, stage + "_ready"));
        Assert.Equal(before, File.ReadAllBytes(seedArchive));
        var calls = File.ReadAllLines(environment["CONTRACT_CALLS"]);
        Assert.Equal(2, calls.Length);
        Assert.All(calls, command => Assert.Contains("transport-verify", command, StringComparison.Ordinal));
        Assert.Contains("--repository " + root + " --stage " + stage + "-seed", calls[0], StringComparison.Ordinal);
        Assert.Contains("/.snapshot-", calls[1], StringComparison.Ordinal);
        var cache = Path.Combine(root, "build/lean-cache", stage);
        var key = JsonNode.Parse(File.ReadAllText(Path.Combine(cache, "manifest.json")))!["key"]!.ToString();
        var target = Destination(fixture, "prepacked-" + stage);
        CopyDirectory(cache, Path.Combine(target, "build/lean-cache", stage));
        environment["CONTRACT_CALLS"] = Path.Combine(root, "build/restore-calls");
        AssertReceipt(Python(target, repository, ["restore", "--repository", target, "--layers", stage,
            "--" + stage + "-key", key], environment), "restored");
        AssertAccepted(root, target, stage, "prepacked-" + stage);
    }

    [Theory]
    [InlineData("current", "commit")]
    [InlineData("current", "run_id")]
    [InlineData("current", "run_attempt")]
    [InlineData("current", "material")]
    [InlineData("current", "producer-material")]
    [InlineData("current", "truncated")]
    [InlineData("current", "extra")]
    [InlineData("current", "duplicate")]
    [InlineData("engineering", "material")]
    public void PrepackedSnapshotRejectsForeignOrDamagedSeedWithoutPublishing(string stage, string damage)
    {
        using var fixture = Prepare(stage);
        var root = fixture.Root;
        var repository = TestRepositoryLayout.FindRoot();
        var commit = SharedBuildContractTests.Git(root, "rev-parse", "HEAD");
        var environment = Environment(commit, root, "47", "2");
        AssertReceipt(Python(root, repository, ["snapshot", "--repository", root, "--layers", stage], environment), "snapshot");
        var cache = Path.Combine(root, "build/lean-cache", stage);
        var before = Inventory(cache);
        var archive = Path.Combine(root, "build/prepared-seed.tgz");
        var packed = NativeTransport(root, "transport-pack", stage, commit, environment,
            "--archive", Path.Combine(root, "build/required.tgz"), "--seed-archive", archive);
        Assert.True(packed.Exit == 0, packed.Text);
        var manifest = CommonExecutionEvidence.Read<CiTransportRecord>(root, CiTransport.ManifestPath(stage + "-seed"));
        var material = manifest.Materials.First(item => stage == "engineering"
            ? item.Path.EndsWith(".trx", StringComparison.Ordinal) : item.Path.EndsWith(".log", StringComparison.Ordinal)).Path;
        if (damage == "producer-material") File.AppendAllText(Path.Combine(root, material), "damaged producer material");
        else if (damage == "truncated") File.WriteAllBytes(archive, File.ReadAllBytes(archive)[..16]);
        else RewriteSeedArchive(archive, CiTransport.ManifestPath(stage + "-seed"), material, damage);
        var result = Python(root, repository, ["snapshot", "--repository", root, "--layers", stage, "--seed-archive", archive], environment);
        AssertReceipt(result, "save-failed");
        Assert.Equal("false", Key(result.Text, stage + "_ready"));
        Assert.Equal(before, Inventory(cache));
        Assert.Empty(Directory.GetDirectories(Path.GetDirectoryName(cache)!, ".snapshot-*"));
    }

    [Theory]
    [InlineData("candidate")]
    [InlineData("round")]
    public void PrepackedSnapshotRejectsAnotherSelfConsistentAcceptance(string identity)
    {
        using var fixture = Prepare("current");
        var root = fixture.Root;
        var commit = SharedBuildContractTests.Git(root, "rev-parse", "HEAD");
        var environment = Environment(commit, root, "49", "1");
        var archive = Path.Combine(root, "build/prepared-seed.tgz");
        var packed = NativeTransport(root, "transport-pack", "current", commit, environment,
            "--archive", Path.Combine(root, "build/required.tgz"), "--seed-archive", archive);
        Assert.True(packed.Exit == 0, packed.Text);
        var other = Path.Combine(root, "build/other-acceptance");
        Directory.CreateDirectory(other);
        using (var gzip = new GZipStream(File.OpenRead(archive), CompressionMode.Decompress))
            TarFile.ExtractToDirectory(gzip, other, overwriteFiles: false);
        var checkPath = CommonExecutionEvidence.CheckSeedPath("current") + "/checks.json";
        var checks = CommonExecutionEvidence.Read<CommonCheckRecord>(other, checkPath);
        checks = checks with
        {
            Candidate = identity == "candidate" ? new string('b', 64) : checks.Candidate,
            Round = identity == "round" ? new string('c', 32) : checks.Round,
            Units = checks.Units.Select(unit => unit with { Status = "reused" }).ToArray(),
        };
        CommonExecutionEvidence.Write(other, checkPath, checks);
        var transportPath = CiTransport.ManifestPath("current-seed");
        var transport = CommonExecutionEvidence.Read<CiTransportRecord>(other, transportPath);
        transport = transport with
        {
            Candidate = checks.Candidate, Round = checks.Round,
            Materials = transport.Materials.Select(material => material.Path == checkPath
                ? material with { Sha256 = CommonExecutionEvidence.Hash(Path.Combine(other, checkPath)) } : material).ToArray(),
        };
        CommonExecutionEvidence.Write(other, transportPath, transport);
        foreach (var source in new[] { root, other })
        {
            var verified = NativeTransport(source, "transport-verify", "current-seed", commit, environment);
            Assert.True(verified.Exit == 0, verified.Text);
        }
        using (var writer = new TarWriter(new GZipStream(File.Create(archive), CompressionLevel.Fastest)))
            foreach (var path in transport.Materials.Select(material => material.Path).Append(transportPath))
                writer.WriteEntry(Path.Combine(other, path), path);
        fixture.Write("build/lean-cache/current/manifest.json", "previous accepted cache");
        var before = Inventory(Path.Combine(root, "build/lean-cache/current"));
        var result = Python(root, TestRepositoryLayout.FindRoot(), ["snapshot", "--repository", root,
            "--layers", "current", "--seed-archive", archive], environment);
        AssertReceipt(result, "save-failed");
        Assert.Contains("prepared seed differs from producer transport", result.Text, StringComparison.Ordinal);
        Assert.Equal("false", Key(result.Text, "current_ready"));
        Assert.Equal(before, Inventory(Path.Combine(root, "build/lean-cache/current")));
    }

    [Theory]
    [InlineData("engineering")]
    [InlineData("current")]
    public void EmptyPrepackedArchiveUsesOrdinarySnapshot(string stage)
    {
        using var fixture = Prepare(stage);
        var root = fixture.Root;
        var commit = SharedBuildContractTests.Git(root, "rev-parse", "HEAD");
        var result = Python(root, TestRepositoryLayout.FindRoot(), ["snapshot", "--repository", root,
            "--layers", stage, "--seed-archive", ""], Environment(commit, root, "48", "1"));
        AssertReceipt(result, "snapshot");
        Assert.Equal("true", Key(result.Text, stage + "_ready"));
        var transport = CommonExecutionEvidence.Read<CiTransportRecord>(root, CiTransport.ManifestPath(stage + "-seed"));
        Assert.Equal(commit, transport.Commit);
        Assert.Equal(48, transport.RunId);
        Assert.Equal(1, transport.RunAttempt);
    }

    private static void RewriteSeedArchive(string archive, string transportPath, string materialPath, string damage)
    {
        using (var input = new TarReader(new GZipStream(File.OpenRead(archive), CompressionMode.Decompress)))
        using (var output = new TarWriter(new GZipStream(File.Create(archive + ".changed"), CompressionLevel.Fastest)))
        {
            while (input.GetNextEntry() is { } entry)
            {
                using var data = new MemoryStream();
                entry.DataStream!.CopyTo(data);
                var bytes = data.ToArray();
                if (entry.Name == materialPath && damage == "material") bytes = "damaged archive material"u8.ToArray();
                if (entry.Name == transportPath && damage is "commit" or "run_id" or "run_attempt")
                {
                    var transport = JsonNode.Parse(bytes)!;
                    transport[damage] = damage == "commit" ? JsonValue.Create(new string('a', 40)) : JsonValue.Create(99);
                    bytes = JsonSerializer.SerializeToUtf8Bytes(transport);
                }
                Write(entry.Name, bytes, entry.Mode);
                if (damage == "duplicate" && entry.Name == transportPath) Write(entry.Name, bytes, entry.Mode);
            }
            if (damage == "extra") Write("build/ci/undeclared", "undeclared"u8.ToArray(), UnixFileMode.UserRead);
            void Write(string name, byte[] bytes, UnixFileMode mode)
            {
                using var data = new MemoryStream(bytes);
                output.WriteEntry(new PaxTarEntry(TarEntryType.RegularFile, name) { DataStream = data, Mode = mode });
            }
        }
        File.Move(archive + ".changed", archive, overwrite: true);
    }

    private static (int Exit, string Text) NativeTransport(string root, string command, string stage, string commit,
        Dictionary<string, string> environment, params string[] extra) =>
        SharedBuildContractTests.Process(root, "dotnet", [Path.Combine(TestRepositoryLayout.FindRoot(), CommonExecutionEvidence.RunnerPath),
            command, "--repository", root, "--stage", stage, "--commit", commit,
            "--run-id", environment["GITHUB_RUN_ID"], "--run-attempt", environment["GITHUB_RUN_ATTEMPT"], .. extra], environment,
            TestBudgets.LongWorkflowProcessHangGuard);

}
