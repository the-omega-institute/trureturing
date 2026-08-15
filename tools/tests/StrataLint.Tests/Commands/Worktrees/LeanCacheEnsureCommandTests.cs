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
            FailCopy = true,
            FailLake = true,
        };

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            runner,
            new RecordingDirectoryCloner { FailureReason = "clonefile unavailable" });

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
    public void PrivateDirectoryFastPathDoesNotStartDotnet()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new TemporaryDirectory();
        var installed = InstallScript(fixture.Path);
        Directory.CreateDirectory(Path.Combine(installed.Repository, ".lake"));
        var marker = Path.Combine(fixture.Path, "dotnet-started");

        var result = RunWithFailingDotnet(installed.Script, installed.Caller, marker);

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

        using var fixture = new TemporaryDirectory();
        var installed = InstallScript(fixture.Path);
        var shared = Path.Combine(installed.Repository, "shared");
        Directory.CreateDirectory(shared);
        Directory.CreateSymbolicLink(Path.Combine(installed.Repository, ".lake"), shared);
        var marker = Path.Combine(fixture.Path, "dotnet-started");

        var result = RunWithFailingDotnet(installed.Script, installed.Caller, marker);

        Assert.Equal(1, result.ExitCode);
        Assert.Empty(result.StandardOutput);
        Assert.Contains(
            "symlink",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.OrdinalIgnoreCase);
        Assert.False(File.Exists(marker));
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
