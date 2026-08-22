using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

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
