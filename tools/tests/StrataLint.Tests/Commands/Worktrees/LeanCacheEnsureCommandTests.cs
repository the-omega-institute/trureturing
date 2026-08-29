using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Collection("Lean cache environment")]
public sealed partial class LeanCacheEnsureCommandTests
{
    [Fact]
    public void MatchingPinStampReportsUnknownMathlibOleanCompletenessWithoutBlocking()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "already warm\n", mathlibComplete: false);
        var runner = new RecordingWorktreeProcessRunner();

        Assert.False(LeanCacheFixtureFile.MathlibProjectionExists(repository.Path));

        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache"], runner);

        Assert.True(result.Success, result.Error);
        Assert.Empty(result.Error);
        using var receipt = ParseReceipt(result.Output);
        foreach (var field in new[] { "status", "worktree", "donor", "method", "reason", "pin_sha256" })
        {
            Assert.True(receipt.RootElement.TryGetProperty(field, out _), $"receipt is missing {field}");
        }
        Assert.Equal(ReadPins(repository.Path).Sha256, receipt.RootElement.GetProperty("pin_sha256").GetString());
        Assert.False(receipt.RootElement.TryGetProperty("shared_cache_scope", out _));
        Assert.False(receipt.RootElement.TryGetProperty("mathlib_cache_pruned_files", out _));
        Assert.False(receipt.RootElement.TryGetProperty("mathlib_cache_clean_status", out _));
        Assert.Equal(JsonValueKind.Null, receipt.RootElement.GetProperty("mathlib_missing_olean_files").ValueKind);
        Assert.Equal(JsonValueKind.Null, receipt.RootElement.GetProperty("reason").ValueKind);
        Assert.Empty(runner.Invocations);
        Assert.Equal("already warm\n", LeanCacheFixtureFile.ReadCacheText(repository.Path));
    }

    [Fact]
    public void UnstampedMainCheckoutRunsCurrentProducerInPlaceAndPublishesMissingReceipt()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "unstamped cache\n", stamp: false);
        var repositoryOlean = Path.Combine(
            repository.Path,
            ".lake",
            "build",
            "lib",
            "lean",
            "Trureturing",
            "Hot.olean");
        Directory.CreateDirectory(Path.GetDirectoryName(repositoryOlean)!);
        File.WriteAllText(repositoryOlean, "expensive repository build\n");
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache"], runner);

        Assert.True(result.Success, result.Error);
        Assert.True(File.Exists(Path.Combine(repository.Path, ".lake", "build", "cache.bin")));
        Assert.True(File.Exists(repositoryOlean));
        Assert.True(File.Exists(Path.Combine(repository.Path, ".lake", "cache-get.marker")));
        Assert.True(runner.CacheGetSawExistingProjection);
        Assert.Equal([true], runner.CacheGetExistingProjectionObservations);
        Assert.True(LeanCacheStamp.Matches(Path.Combine(repository.Path, ".lake"), ReadPins(repository.Path), out _));
        Assert.Equal(
            ["get"],
            runner.Invocations
                .Where(static call => Path.GetFileName(call.FileName) == "lake")
                .Select(static call => call.Arguments[2])
                .ToArray());
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal("fetched", receipt.RootElement.GetProperty("status").GetString());
        Assert.Equal("missing", receipt.RootElement.GetProperty("stamp_miss").GetString());
        Assert.DoesNotContain(
            "do not match",
            receipt.RootElement.GetProperty("reason").GetString()!,
            StringComparison.OrdinalIgnoreCase);
        Assert.Equal(0, receipt.RootElement.GetProperty("mathlib_missing_olean_files").GetInt32());
        Assert.False(receipt.RootElement.TryGetProperty("mathlib_cache_pruned_files", out _));
        Assert.False(receipt.RootElement.TryGetProperty("mathlib_cache_clean_status", out _));
    }

    [Fact]
    public void StampCarriesTheExactPinBytesAndLeavesNoPublicationTemporary()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "stamped\n");
        var lake = Path.Combine(repository.Path, ".lake");
        var pins = ReadPins(repository.Path);

        using var stamp = LeanCacheFixtureFile.ParseJson(LeanCacheStamp.PathFor(lake));

        Assert.Equal(pins.LeanToolchain, Convert.FromBase64String(
            stamp.RootElement.GetProperty("lean_toolchain_base64").GetString()!));
        Assert.Equal(pins.LakeManifest, Convert.FromBase64String(
            stamp.RootElement.GetProperty("lake_manifest_base64").GetString()!));
        Assert.Empty(Directory.GetFiles(lake, ".stratalint-lean-cache-stamp.*.tmp"));
    }

    [Theory]
    [InlineData("not json\n")]
    [InlineData("{\"schema\":\"unknown\"}\n")]
    [InlineData("{\"schema\":\"stratalint-lean-cache-v1\",\"pin_sha256\":42}\n")]
    public void CorruptStampRunsCurrentProducerInPlaceWithoutDeletingTheProjection(string stamp)
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "untrusted cache\n");
        File.WriteAllText(LeanCacheStamp.PathFor(Path.Combine(repository.Path, ".lake")), stamp);
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache"], runner);

        Assert.True(result.Success, result.Error);
        Assert.True(File.Exists(Path.Combine(repository.Path, ".lake", "build", "cache.bin")));
        Assert.True(runner.CacheGetSawExistingProjection);
        Assert.Equal([true], runner.CacheGetExistingProjectionObservations);
        Assert.True(LeanCacheStamp.Matches(Path.Combine(repository.Path, ".lake"), ReadPins(repository.Path), out _));
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal("corrupt", receipt.RootElement.GetProperty("stamp_miss").GetString());
    }

    [Fact]
    public void InternallyInconsistentStampAndProducerFailurePreserveExistingProjection()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "must survive inconsistent stamp\n");
        var lake = Path.Combine(repository.Path, ".lake");
        var ownedOlean = Path.Combine(lake, "build", "lib", "lean", "Trureturing", "Owned.olean");
        Directory.CreateDirectory(Path.GetDirectoryName(ownedOlean)!);
        File.WriteAllText(ownedOlean, "must survive\n");
        var pins = ReadPins(repository.Path);
        File.WriteAllText(
            LeanCacheStamp.PathFor(lake),
            JsonSerializer.Serialize(new
            {
                schema = "stratalint-lean-cache-v1",
                pin_sha256 = "sha256:" + new string('0', 64),
                lean_toolchain_base64 = Convert.ToBase64String(pins.LeanToolchain),
                lake_manifest_base64 = Convert.ToBase64String(pins.LakeManifest),
            }) + "\n");
        var runner = new RecordingWorktreeProcessRunner { FailLake = true };

        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache"], runner);

        Assert.False(result.Success);
        Assert.True(File.Exists(Path.Combine(lake, "build", "cache.bin")));
        Assert.True(File.Exists(ownedOlean));
        Assert.Equal([true], runner.CacheGetExistingProjectionObservations);
        using var receipt = ParseReceipt(result.Error);
        Assert.Equal("corrupt", receipt.RootElement.GetProperty("stamp_miss").GetString());
    }

    [Fact]
    public void StampForPreviousPinsDeletesOldLakeBeforeProvisioning()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "old pin cache\n");
        File.WriteAllText(Path.Combine(repository.Path, "lean-toolchain"), "leanprover/lean4:v4.33.0\n");
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache"], runner);

        Assert.True(result.Success, result.Error);
        Assert.False(File.Exists(Path.Combine(repository.Path, ".lake", "build", "cache.bin")));
        Assert.False(runner.CacheGetSawExistingProjection);
        Assert.Equal([false], runner.CacheGetExistingProjectionObservations);
        Assert.True(LeanCacheStamp.Matches(Path.Combine(repository.Path, ".lake"), ReadPins(repository.Path), out _));
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal("mismatch", receipt.RootElement.GetProperty("stamp_miss").GetString());
    }

    [Fact]
    public void PresentLakeSymlinkIsRefusedLoudly()
    {
        if (OperatingSystem.IsWindows()) return;

        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var sharedCache = Path.Combine(repository.Path, "shared-cache");
        Directory.CreateDirectory(sharedCache);
        Directory.CreateSymbolicLink(Path.Combine(repository.Path, ".lake"), sharedCache);
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache"], runner);

        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.Contains("refused", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.Contains("symlink", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.Empty(runner.Invocations);
    }

    [Fact]
    public void ExistingLakeFileIsPreservedAndFailsClosedAsCorrupt()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var lake = Path.Combine(repository.Path, ".lake");
        File.WriteAllText(lake, "repository-owned bytes\n");
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache"], runner);

        Assert.False(result.Success);
        Assert.Equal("repository-owned bytes\n", LeanCacheFixtureFile.ReadText(lake));
        Assert.Empty(runner.Invocations);
        using var receipt = ParseReceipt(result.Error);
        Assert.Equal("corrupt", receipt.RootElement.GetProperty("stamp_miss").GetString());
        Assert.Contains("not a directory", result.Error, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void ClonefileRetryReceiptSerializesErrnoHistoryAttemptsAndCleanup()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "main repository cache\n");
        var target = AddWorktree(repository.Path, "matching-target");
        var scripted = new Queue<DirectoryCloneResult>(
            [new(false, true, 5, 1, "clonefile(2) failed: EIO"), new(true, false, null, 1, null)]);
        var cloner = new RecordingDirectoryCloner
        {
            Results = scripted,
            AfterClone = (_, path) => { if (scripted.Count > 0) Directory.CreateDirectory(path); },
        };
        var runner = new RecordingWorktreeProcessRunner();
        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache", "--path", target], runner, cloner);
        Assert.True(result.Success, result.Error);
        Assert.Empty(result.Error);
        Assert.Equal(2, cloner.Invocations.Count);
        using var receipt = ParseReceipt(result.Output);
        var root = receipt.RootElement;
        Assert.Equal("seeded", root.GetProperty("status").GetString());
        Assert.Equal(LeanCacheGuard.PhysicalPath(repository.Path), root.GetProperty("donor").GetString());
        Assert.Equal("clonefile", root.GetProperty("method").GetString());
        Assert.Equal(5, root.GetProperty("clonefile_errno").GetInt32());
        Assert.Equal([5], root.GetProperty("clonefile_errnos").EnumerateArray().Select(item => item.GetInt32()).ToArray());
        Assert.Equal(2, root.GetProperty("clonefile_attempts").GetInt32());
        Assert.Equal(JsonValueKind.Null, root.GetProperty("clonefile_cleanup_error").ValueKind);
        Assert.Equal("main repository cache\n", LeanCacheFixtureFile.ReadText(Path.Combine(target, ".lake", "build", "cache.bin")));
        Assert.DoesNotContain(runner.Invocations, static call => Path.GetFileName(call.FileName) == "lake");
        Assert.True(LeanCacheStamp.Matches(Path.Combine(target, ".lake"), ReadPins(target), out _));
    }

    [Fact]
    public void IncompleteDonorStagingIsPublishedWithMissingCountReceipt()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "incomplete donor\n");
        MathlibProjectionFixture.RemoveAllOleans(Path.Combine(repository.Path, ".lake"));
        var target = AddWorktree(repository.Path, "incomplete-donor-target");
        var runner = new RecordingWorktreeProcessRunner();
        var cloner = new RecordingDirectoryCloner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            runner,
            cloner);

        Assert.True(result.Success, result.Error);
        Assert.Empty(result.Error);
        Assert.True(Directory.Exists(Path.Combine(target, ".lake")));
        Assert.True(File.Exists(LeanCacheStamp.PathFor(Path.Combine(target, ".lake"))));
        Assert.Empty(Directory.EnumerateFileSystemEntries(target, ".lake.stage-*"));
        var clone = Assert.Single(cloner.Invocations);
        Assert.StartsWith(
            Path.Combine(target, ".lake.stage-"),
            clone.Target,
            StringComparison.Ordinal);
        Assert.DoesNotContain(runner.Invocations, static call => call.FileName == "cp");
        Assert.DoesNotContain(runner.Invocations, static call => Path.GetFileName(call.FileName) == "lake");
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal(
            MathlibProjectionFixture.ModuleCount,
            receipt.RootElement.GetProperty("mathlib_missing_olean_files").GetInt32());
        Assert.Contains(
            receipt.RootElement.GetProperty("mathlib_missing_olean_samples").EnumerateArray(),
            sample => sample.GetString() == MathlibProjectionFixture.FirstModule);
    }

    [Fact]
    public void DonorWithoutMatchingStampIsRejected()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "unstamped donor\n", stamp: false);
        var target = AddWorktree(repository.Path, "unstamped-donor-target");
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            runner);

        Assert.True(result.Success, result.Error);
        Assert.False(File.Exists(Path.Combine(target, ".lake", "build", "cache.bin")));
        Assert.True(File.Exists(Path.Combine(target, ".lake", "cache-get.marker")));
        Assert.Contains("stamp", result.Output, StringComparison.OrdinalIgnoreCase);
        Assert.DoesNotContain(runner.Invocations, static call => call.FileName == "cp");
    }

    [Fact]
    public void DonorStampForDifferentPinBytesIsRejectedEvenWhenWorktreePinsMatch()
    {
        using var repository = new TemporaryDirectory();
        using var otherPins = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        File.WriteAllText(Path.Combine(otherPins.Path, "lean-toolchain"), "leanprover/lean4:v4.30.0\n");
        File.WriteAllText(Path.Combine(otherPins.Path, "lake-manifest.json"), "{\"version\":\"old\"}\n");
        WriteCache(repository.Path, "wrongly stamped donor\n", stamp: false);
        LeanCacheStamp.Write(Path.Combine(repository.Path, ".lake"), ReadPins(otherPins.Path));
        var target = AddWorktree(repository.Path, "wrong-stamp-donor-target");
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            runner);

        Assert.True(result.Success, result.Error);
        Assert.True(File.Exists(Path.Combine(target, ".lake", "cache-get.marker")));
        Assert.False(File.Exists(Path.Combine(target, ".lake", "build", "cache.bin")));
        Assert.Contains("stamp", result.Output, StringComparison.OrdinalIgnoreCase);
        Assert.DoesNotContain(runner.Invocations, static call => call.FileName == "cp");
    }

    [Fact]
    public void ByteMismatchedPinsNeverCopyCandidateCache()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var target = AddWorktree(repository.Path, "mismatched-target");
        var targetManifest = File.ReadAllBytes(Path.Combine(target, "lake-manifest.json"));
        File.WriteAllText(Path.Combine(repository.Path, "lake-manifest.json"), "{\"version\": \"1.1.0\"}\n");
        Git(repository.Path, "add", "lake-manifest.json");
        Git(repository.Path, "commit", "-m", "change pin bytes only");
        var donorManifest = File.ReadAllBytes(Path.Combine(repository.Path, "lake-manifest.json"));
        WriteCache(repository.Path, "poisoned for target pins\n");
        var runner = new RecordingWorktreeProcessRunner();

        using (var targetJson = JsonDocument.Parse(targetManifest))
        using (var donorJson = JsonDocument.Parse(donorManifest))
        {
            Assert.Equal(
                targetJson.RootElement.GetProperty("version").GetString(),
                donorJson.RootElement.GetProperty("version").GetString());
        }
        Assert.False(targetManifest.AsSpan().SequenceEqual(donorManifest));

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            runner);

        Assert.True(result.Success);
        Assert.Empty(result.Error);
        Assert.Contains("pin bytes do not match", result.Output, StringComparison.OrdinalIgnoreCase);
        Assert.False(File.Exists(Path.Combine(target, ".lake", "build", "cache.bin")));
        Assert.True(File.Exists(Path.Combine(target, ".lake", "cache-get.marker")));
        Assert.DoesNotContain(
            runner.Invocations,
            static call => call.FileName == "cp");
    }

    [Theory]
    [InlineData("cache-get", "missing")]
    [InlineData("stamp", "corrupt")]
    public void InPlaceProducerFailurePreservesExistingLakeAndNeverFallsThrough(
        string failure,
        string expectedStampMiss)
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "expensive unstamped cache\n", stamp: false);
        var repositoryOlean = Path.Combine(
            repository.Path,
            ".lake",
            "build",
            "lib",
            "lean",
            "Trureturing",
            "Expensive.olean");
        Directory.CreateDirectory(Path.GetDirectoryName(repositoryOlean)!);
        File.WriteAllText(repositoryOlean, "must survive\n");
        if (failure == "stamp")
        {
            Directory.CreateDirectory(LeanCacheStamp.PathFor(Path.Combine(repository.Path, ".lake")));
        }
        var runner = new RecordingWorktreeProcessRunner
        {
            FailLake = failure == "cache-get",
        };

        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache"], runner);

        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.True(Directory.Exists(Path.Combine(repository.Path, ".lake")));
        Assert.True(File.Exists(Path.Combine(repository.Path, ".lake", "build", "cache.bin")));
        Assert.True(File.Exists(repositoryOlean));
        Assert.False(File.Exists(LeanCacheStamp.PathFor(Path.Combine(repository.Path, ".lake"))));
        Assert.Equal([true], runner.CacheGetExistingProjectionObservations);
        using var receipt = ParseReceipt(result.Error);
        Assert.Equal(expectedStampMiss, receipt.RootElement.GetProperty("stamp_miss").GetString());
        Assert.False(receipt.RootElement.TryGetProperty("mathlib_cache_pruned_files", out _));
        Assert.False(receipt.RootElement.TryGetProperty("mathlib_cache_clean_status", out _));
        if (failure == "cache-get")
        {
            Assert.Contains(
                "cache get failed",
                receipt.RootElement.GetProperty("reason").GetString()!,
                StringComparison.OrdinalIgnoreCase);
        }
    }

    [Fact]
    public void InPlaceProducerReportsMissingMathlibOleansAndPublishesStamp()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "expensive unstamped cache\n", stamp: false);
        MathlibProjectionFixture.RemoveAllOleans(Path.Combine(repository.Path, ".lake"));
        var runner = new RecordingWorktreeProcessRunner { OmitMathlibOleans = true };

        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache"], runner);

        Assert.True(result.Success, result.Error);
        Assert.True(File.Exists(LeanCacheStamp.PathFor(Path.Combine(repository.Path, ".lake"))));
        Assert.DoesNotContain(
            runner.Invocations,
            static call => Path.GetFileName(call.FileName) == "lake"
                && call.Arguments.SequenceEqual(["exe", "cache", "clean"]));
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal(
            MathlibProjectionFixture.ModuleCount,
            receipt.RootElement.GetProperty("mathlib_missing_olean_files").GetInt32());
    }

    [Fact]
    public void ExhaustedCopyFallbacksFailClosedAndNameEveryFailure()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm donor\n");
        var target = AddWorktree(repository.Path, "copy-failure-target");
        var runner = new RecordingWorktreeProcessRunner
        {
            FailCopy = true,
            FailLake = true,
        };

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            runner,
            new RecordingDirectoryCloner { FailureReason = "clonefile unavailable" });

        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.Contains("clonefile failed", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.Contains("ordinary copy failed", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.Contains("cache get failed", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.False(Directory.Exists(Path.Combine(target, ".lake")));
    }

    [Fact]
    public void CacheGetNeverInvokesMachineCacheCleanOrPublishesPruneAccounting()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var runner = new RecordingWorktreeProcessRunner { FailClean = true };

        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache"], runner);

        Assert.True(result.Success, result.Error);
        Assert.True(File.Exists(LeanCacheStamp.PathFor(Path.Combine(repository.Path, ".lake"))));
        Assert.DoesNotContain(
            runner.Invocations,
            static call => Path.GetFileName(call.FileName) == "lake"
                && call.Arguments.SequenceEqual(["exe", "cache", "clean"]));
        using var receipt = ParseReceipt(result.Output);
        Assert.False(receipt.RootElement.TryGetProperty("shared_cache_scope", out _));
        Assert.False(receipt.RootElement.TryGetProperty("mathlib_cache_pruned_files", out _));
        Assert.False(receipt.RootElement.TryGetProperty("mathlib_cache_clean_status", out _));
    }

    private static string AddWorktree(string repositoryRoot, string name)
    {
        var target = Path.Combine(repositoryRoot, name);
        Git(repositoryRoot, "worktree", "add", "-b", $"harness/{name}", target, "HEAD");
        return target;
    }

    private static void InitializeRepository(string root)
    {
        Git(root, "init", "--initial-branch=dev");
        Git(root, "config", "user.email", "stratalint@example.invalid");
        Git(root, "config", "user.name", "StrataLint Tests");
        File.WriteAllText(Path.Combine(root, "README.md"), "# lean cache fixture\n");
        File.WriteAllText(Path.Combine(root, "lean-toolchain"), "leanprover/lean4:v4.31.0\n");
        File.WriteAllText(Path.Combine(root, "lake-manifest.json"), "{\"version\":\"1.1.0\"}\n");
        Git(root, "add", "README.md", "lean-toolchain", "lake-manifest.json");
        Git(root, "commit", "-m", "fixture baseline");
    }

    private static void WriteCache(
        string root,
        string contents,
        bool stamp = true,
        bool mathlibComplete = true)
    {
        var lake = Path.Combine(root, ".lake");
        var cache = Path.Combine(lake, "build", "cache.bin");
        Directory.CreateDirectory(Path.GetDirectoryName(cache)!);
        File.WriteAllText(cache, contents);
        if (mathlibComplete) MathlibProjectionFixture.Write(lake);
        if (stamp) LeanCacheStamp.Write(lake, ReadPins(root));
    }

    private static LeanPinSet ReadPins(string root) =>
        LeanPinSet.TryReadWorktree(root, out var reason)
        ?? throw new InvalidOperationException(reason);

    private static JsonDocument ParseReceipt(string output) =>
        JsonDocument.Parse(output["LEAN_CACHE ".Length..]);

    private static string Git(string root, params string[] arguments) =>
        ReviewRegressionTests.RunGit(root, arguments);
}

internal static class LeanCacheFixtureFile
{
    internal static bool MathlibProjectionExists(string repositoryRoot) =>
        Directory.Exists(Path.Combine(
            repositoryRoot,
            ".lake",
            "packages",
            "mathlib",
            "Mathlib"));

    internal static string ReadCacheText(string repositoryRoot) =>
        File.ReadAllText(Path.Combine(repositoryRoot, ".lake", "build", "cache.bin"));

    internal static JsonDocument ParseJson(string path) =>
        JsonDocument.Parse(File.ReadAllText(path));

    internal static string ReadText(string path) => File.ReadAllText(path);
}
