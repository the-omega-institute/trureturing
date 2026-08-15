using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Collection("Lean cache environment")]
public sealed class LeanCacheEnsureCommandTests
{
    [Fact]
    public void PresentPrivateLakeRequiresAMatchingProducerStamp()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "already warm\n", mathlibComplete: false);
        var runner = new RecordingWorktreeProcessRunner();

        Assert.False(Directory.Exists(Path.Combine(
            repository.Path,
            ".lake",
            "packages",
            "mathlib",
            "Mathlib")));

        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache"], runner);

        Assert.True(result.Success);
        Assert.Contains("present", result.Output, StringComparison.Ordinal);
        using var receipt = ParseReceipt(result.Output);
        foreach (var field in new[] { "status", "worktree", "donor", "method", "reason", "pin_sha256" })
        {
            Assert.True(receipt.RootElement.TryGetProperty(field, out _), $"receipt is missing {field}");
        }
        Assert.Equal(ReadPins(repository.Path).Sha256, receipt.RootElement.GetProperty("pin_sha256").GetString());
        Assert.Equal("machine", receipt.RootElement.GetProperty("shared_cache_scope").GetString());
        Assert.Equal(JsonValueKind.Null, receipt.RootElement.GetProperty("mathlib_cache_pruned_files").ValueKind);
        Assert.Equal(JsonValueKind.Null, receipt.RootElement.GetProperty("mathlib_missing_olean_files").ValueKind);
        Assert.Equal(JsonValueKind.Null, receipt.RootElement.GetProperty("mathlib_missing_olean_samples").ValueKind);
        Assert.Empty(result.Error);
        Assert.Empty(runner.Invocations);
        Assert.Equal(
            "already warm\n",
            File.ReadAllText(Path.Combine(repository.Path, ".lake", "build", "cache.bin")));
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
            ["get", "clean"],
            runner.Invocations
                .Where(static call => call.FileName == "lake")
                .Select(static call => call.Arguments[2])
                .ToArray());
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal("fetched", receipt.RootElement.GetProperty("status").GetString());
        Assert.Equal("missing", receipt.RootElement.GetProperty("stamp_miss").GetString());
        Assert.DoesNotContain(
            "do not match",
            receipt.RootElement.GetProperty("reason").GetString()!,
            StringComparison.OrdinalIgnoreCase);
        Assert.Equal(1, receipt.RootElement.GetProperty("mathlib_cache_pruned_files").GetInt32());
    }

    [Fact]
    public void StampCarriesTheExactPinBytesAndLeavesNoPublicationTemporary()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "stamped\n");
        var lake = Path.Combine(repository.Path, ".lake");
        var pins = ReadPins(repository.Path);

        using var stamp = JsonDocument.Parse(File.ReadAllText(LeanCacheStamp.PathFor(lake)));

        Assert.Equal(pins.LeanToolchain, Convert.FromBase64String(
            stamp.RootElement.GetProperty("lean_toolchain_base64").GetString()!));
        Assert.Equal(pins.LakeManifest, Convert.FromBase64String(
            stamp.RootElement.GetProperty("lake_manifest_base64").GetString()!));
        Assert.Empty(Directory.EnumerateFiles(lake, ".stratalint-lean-cache-stamp.*.tmp"));
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
    public void MissingLakeIsSeededFromMatchingMainRepository()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "main repository cache\n");
        var target = AddWorktree(repository.Path, "matching-target");
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            runner);

        Assert.True(result.Success);
        Assert.Empty(result.Error);
        Assert.Contains("seeded", result.Output, StringComparison.Ordinal);
        Assert.Contains(repository.Path, result.Output, StringComparison.Ordinal);
        Assert.Contains("method", result.Output, StringComparison.Ordinal);
        Assert.Equal(
            "main repository cache\n",
            File.ReadAllText(Path.Combine(target, ".lake", "build", "cache.bin")));
        Assert.DoesNotContain(
            runner.Invocations,
            static call => call.FileName == "lake");
    }

    [Fact]
    public void IncompleteDonorStagingIsDiscardedWithoutPublishingAStamp()
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

        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.False(Directory.Exists(Path.Combine(target, ".lake")));
        Assert.False(File.Exists(LeanCacheStamp.PathFor(Path.Combine(target, ".lake"))));
        Assert.Empty(Directory.EnumerateFileSystemEntries(target, ".lake.stage-*"));
        var clone = Assert.Single(cloner.Invocations);
        Assert.StartsWith(
            Path.Combine(target, ".lake.stage-"),
            clone.Target,
            StringComparison.Ordinal);
        Assert.DoesNotContain(runner.Invocations, static call => call.FileName == "cp");
        Assert.DoesNotContain(runner.Invocations, static call => call.FileName == "lake");
        using var receipt = ParseReceipt(result.Error);
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
    [InlineData(false)]
    [InlineData(true)]
    public void UnstampedExistingLakeFailureDeletesOnlyAfterTheAttemptAndFailsClosed(
        bool failCompleteness)
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(
            repository.Path,
            "expensive unstamped cache\n",
            stamp: false,
            mathlibComplete: !failCompleteness);
        var runner = new RecordingWorktreeProcessRunner
        {
            FailLake = !failCompleteness,
            OmitMathlibOleans = failCompleteness,
        };

        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache"], runner);

        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.False(Directory.Exists(Path.Combine(repository.Path, ".lake")));
        Assert.False(File.Exists(LeanCacheStamp.PathFor(Path.Combine(repository.Path, ".lake"))));
        Assert.Equal([true, false], runner.CacheGetExistingProjectionObservations);
        Assert.DoesNotContain(
            runner.Invocations,
            static call => call.FileName == "lake" && call.Arguments.SequenceEqual(["exe", "cache", "clean"]));
        using var receipt = ParseReceipt(result.Error);
        Assert.Equal("missing", receipt.RootElement.GetProperty("stamp_miss").GetString());
        if (failCompleteness)
        {
            Assert.Equal(
                MathlibProjectionFixture.ModuleCount,
                receipt.RootElement.GetProperty("mathlib_missing_olean_files").GetInt32());
        }
        else
        {
            Assert.Contains(
                "cache get failed",
                receipt.RootElement.GetProperty("reason").GetString()!,
                StringComparison.OrdinalIgnoreCase);
        }
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
    public void CacheCleanFailureLeavesTheProjectionUnstamped()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var runner = new RecordingWorktreeProcessRunner { FailClean = true };

        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache"], runner);

        Assert.False(result.Success);
        Assert.Contains("cache clean failed", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.False(File.Exists(LeanCacheStamp.PathFor(Path.Combine(repository.Path, ".lake"))));
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

[Collection("Lean cache environment")]
public sealed class LeanCacheEnsureScriptTests
{
    [Fact]
    public void MissingLakeDelegatesToCanonicalWorktreeEnsureCacheCommand()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new TemporaryDirectory();
        var installed = InstallScript(fixture.Path);
        var bin = Path.Combine(fixture.Path, "bin");
        var arguments = Path.Combine(fixture.Path, "dotnet-arguments");
        var dotnetCwd = Path.Combine(fixture.Path, "dotnet-cwd");
        Directory.CreateDirectory(bin);
        var dotnet = Path.Combine(bin, "dotnet");
        File.WriteAllText(
            dotnet,
            "#!/usr/bin/env bash\nprintf '%s\\n' \"$@\" > \"$DOTNET_ARGUMENTS\"\nprintf '%s\\n' \"$PWD\" > \"$DOTNET_CWD\"\nprintf 'delegated\\n'\n");
        File.SetUnixFileMode(
            dotnet,
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);

        var result = BoundedProcessRunner.Run(
            "/bin/bash",
            [
                "-c",
                "PATH=\"$1:$PATH\" DOTNET_ARGUMENTS=\"$2\" DOTNET_CWD=\"$3\" exec /bin/bash \"$4\"",
                "lean-cache-test",
                bin,
                arguments,
                dotnetCwd,
                installed.Script,
            ],
            installed.Caller,
            TimeSpan.FromSeconds(10),
            64 * 1024);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal("delegated\n", Encoding.UTF8.GetString(result.StandardOutput));
        Assert.Empty(result.StandardError);
        var canonicalRoot = BoundedProcessRunner.Run(
            "/bin/pwd",
            ["-P"],
            installed.Repository,
            TimeSpan.FromSeconds(10),
            4096);
        Assert.Equal(0, canonicalRoot.ExitCode);
        var canonicalRepository = Encoding.UTF8.GetString(canonicalRoot.StandardOutput).TrimEnd('\n');
        var project = Path.Combine(
            canonicalRepository,
            "tools",
            "StrataLint.Cli",
            "StrataLint.Cli.csproj");
        Assert.Equal(
            string.Join('\n',
                "run",
                "--project",
                project,
                "--configuration",
                "Release",
                "--",
                "worktree",
                "ensure-cache") + "\n",
            File.ReadAllText(arguments));
        Assert.Equal(canonicalRepository + "\n", File.ReadAllText(dotnetCwd));
    }

    [Fact]
    public void PrivateDirectoryDelegatesToTheCanonicalJudge()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new TemporaryDirectory();
        var installed = InstallScript(fixture.Path);
        Directory.CreateDirectory(Path.Combine(installed.Repository, ".lake"));
        var marker = Path.Combine(fixture.Path, "dotnet-started");

        var result = RunWithFailingDotnet(installed.Script, installed.Caller, marker);

        Assert.Equal(97, result.ExitCode);
        Assert.Empty(result.StandardOutput);
        Assert.Empty(result.StandardError);
        Assert.True(File.Exists(marker));
    }

    [Fact]
    public void SymlinkDelegatesToTheCanonicalJudge()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new TemporaryDirectory();
        var installed = InstallScript(fixture.Path);
        var shared = Path.Combine(installed.Repository, "shared");
        Directory.CreateDirectory(shared);
        Directory.CreateSymbolicLink(Path.Combine(installed.Repository, ".lake"), shared);
        var marker = Path.Combine(fixture.Path, "dotnet-started");

        var result = RunWithFailingDotnet(installed.Script, installed.Caller, marker);

        Assert.Equal(97, result.ExitCode);
        Assert.Empty(result.StandardOutput);
        Assert.Empty(result.StandardError);
        Assert.True(File.Exists(marker));
    }

    private const string LeanCacheEnsureScriptPath =
        "tools/scripts/worktree/lean-cache-ensure.sh";

    private static InstalledScript InstallScript(string fixtureRoot)
    {
        var repository = Path.Combine(fixtureRoot, "repository");
        var caller = Path.Combine(fixtureRoot, "caller");
        var script = Path.Combine(
            repository,
            LeanCacheEnsureScriptPath.Replace('/', Path.DirectorySeparatorChar));
        Directory.CreateDirectory(Path.GetDirectoryName(script)!);
        Directory.CreateDirectory(caller);
        File.Copy(
            Path.Combine(TestRepositoryLayout.FindRoot(), LeanCacheEnsureScriptPath),
            script);
        return new InstalledScript(repository, caller, script);
    }

    private static ProcessOutput RunWithFailingDotnet(
        string script,
        string workingDirectory,
        string marker)
    {
        if (OperatingSystem.IsWindows())
        {
            throw new PlatformNotSupportedException("the shell fast-path fixture requires Unix");
        }

        var bin = Path.Combine(workingDirectory, "bin");
        Directory.CreateDirectory(bin);
        var dotnet = Path.Combine(bin, "dotnet");
        File.WriteAllText(dotnet, "#!/usr/bin/env bash\ntouch \"$DOTNET_MARKER\"\nexit 97\n");
        File.SetUnixFileMode(
            dotnet,
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        return BoundedProcessRunner.Run(
            "/bin/bash",
            ["-c", "PATH=\"$1:$PATH\" DOTNET_MARKER=\"$2\" exec /bin/bash \"$3\"", "lean-cache-test", bin, marker, script],
            workingDirectory,
            TimeSpan.FromSeconds(10),
            64 * 1024);
    }

    private sealed record InstalledScript(string Repository, string Caller, string Script);

}
