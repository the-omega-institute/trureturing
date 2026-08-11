using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class LeanCacheEnsureCommandTests
{
    [Fact]
    public void PresentPrivateLakeIsANoOp()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "already warm\n");
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache"], runner);

        Assert.True(result.Success);
        Assert.Contains("present", result.Output, StringComparison.Ordinal);
        Assert.Empty(result.Error);
        Assert.Empty(runner.Invocations);
        Assert.Equal(
            "already warm\n",
            File.ReadAllText(Path.Combine(repository.Path, ".lake", "build", "cache.bin")));
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
    public void ByteMismatchedPinsNeverCopyCandidateCache()
    {
        using var repository = new TemporaryDirectory();
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

    [Fact]
    public void NoDonorAndFailedCacheGetProceedColdWithAReceipt()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var target = AddWorktree(repository.Path, "cold-target");
        var runner = new RecordingWorktreeProcessRunner { FailLake = true };

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            runner);

        Assert.True(result.Success);
        Assert.Empty(result.Error);
        Assert.Contains("cold", result.Output, StringComparison.Ordinal);
        Assert.Contains("no existing worktree contains .lake", result.Output, StringComparison.Ordinal);
        Assert.Contains("cache get failed", result.Output, StringComparison.OrdinalIgnoreCase);
        Assert.False(Directory.Exists(Path.Combine(target, ".lake")));
    }

    [Fact]
    public void ExhaustedCopyFallbacksProceedColdAndNameEveryFailure()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm donor\n");
        var target = AddWorktree(repository.Path, "copy-failure-target");
        var runner = new RecordingWorktreeProcessRunner
        {
            FailClonefile = true,
            FailCopy = true,
            FailLake = true,
        };

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            runner);

        Assert.True(result.Success);
        Assert.Empty(result.Error);
        Assert.Contains("cold", result.Output, StringComparison.Ordinal);
        Assert.Contains("clonefile failed", result.Output, StringComparison.OrdinalIgnoreCase);
        Assert.Contains("ordinary copy failed", result.Output, StringComparison.OrdinalIgnoreCase);
        Assert.Contains("cache get failed", result.Output, StringComparison.OrdinalIgnoreCase);
        Assert.False(Directory.Exists(Path.Combine(target, ".lake")));
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

    private static void WriteCache(string root, string contents)
    {
        var cache = Path.Combine(root, ".lake", "build", "cache.bin");
        Directory.CreateDirectory(Path.GetDirectoryName(cache)!);
        File.WriteAllText(cache, contents);
    }

    private static string Git(string root, params string[] arguments) =>
        ReviewRegressionTests.RunGit(root, arguments);
}

[Trait("Category", "Script")] public sealed class LeanCacheEnsureScriptTests
{
    [Fact]
    public void MissingLakeDelegatesToCanonicalWorktreeEnsureCacheCommand()
    {
        if (OperatingSystem.IsWindows()) return;

        var script = Path.Combine(FindRepositoryRoot(), LeanCacheEnsureScriptPath);
        using var fixture = new TemporaryDirectory();
        var bin = Path.Combine(fixture.Path, "bin");
        var arguments = Path.Combine(fixture.Path, "dotnet-arguments");
        Directory.CreateDirectory(bin);
        var dotnet = Path.Combine(bin, "dotnet");
        File.WriteAllText(
            dotnet,
            "#!/usr/bin/env bash\nprintf '%s\\n' \"$@\" > \"$DOTNET_ARGUMENTS\"\nprintf 'delegated\\n'\n");
        File.SetUnixFileMode(
            dotnet,
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);

        var result = BoundedProcessRunner.Run(
            "/bin/bash",
            [
                "-c",
                "PATH=\"$1:$PATH\" DOTNET_ARGUMENTS=\"$2\" exec /bin/bash \"$3\"",
                "lean-cache-test",
                bin,
                arguments,
                script,
            ],
            fixture.Path,
            TimeSpan.FromSeconds(10),
            64 * 1024);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal("delegated\n", Encoding.UTF8.GetString(result.StandardOutput));
        Assert.Empty(result.StandardError);
        Assert.Equal(
            """
            run
            --project
            Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj
            --configuration
            Release
            --
            worktree
            ensure-cache
            """ + "\n",
            File.ReadAllText(arguments));
    }

    [Fact]
    public void PrivateDirectoryFastPathDoesNotStartDotnet()
    {
        if (OperatingSystem.IsWindows()) return;

        var script = Path.Combine(FindRepositoryRoot(), LeanCacheEnsureScriptPath);
        using var fixture = new TemporaryDirectory();
        Directory.CreateDirectory(Path.Combine(fixture.Path, ".lake"));
        var marker = Path.Combine(fixture.Path, "dotnet-started");

        var result = RunWithFailingDotnet(script, fixture.Path, marker);

        Assert.Equal(0, result.ExitCode);
        Assert.Contains(
            "present",
            Encoding.UTF8.GetString(result.StandardOutput),
            StringComparison.Ordinal);
        Assert.Empty(result.StandardError);
        Assert.False(File.Exists(marker));
    }

    [Fact]
    public void SymlinkFastPathRefusesWithoutStartingDotnet()
    {
        if (OperatingSystem.IsWindows()) return;

        var script = Path.Combine(FindRepositoryRoot(), LeanCacheEnsureScriptPath);
        using var fixture = new TemporaryDirectory();
        var shared = Path.Combine(fixture.Path, "shared");
        Directory.CreateDirectory(shared);
        Directory.CreateSymbolicLink(Path.Combine(fixture.Path, ".lake"), shared);
        var marker = Path.Combine(fixture.Path, "dotnet-started");

        var result = RunWithFailingDotnet(script, fixture.Path, marker);

        Assert.Equal(1, result.ExitCode);
        Assert.Empty(result.StandardOutput);
        Assert.Contains(
            "symlink",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.OrdinalIgnoreCase);
        Assert.False(File.Exists(marker));
    }

    private const string LeanCacheEnsureScriptPath =
        "Meta/StrataLint/scripts/worktree/lean-cache-ensure.sh";

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

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "CLAUDE.md"))) return current.FullName;
        }

        throw new DirectoryNotFoundException("Could not locate repository root.");
    }
}
