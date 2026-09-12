using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Collection("Lean cache environment")]
public sealed class LeanCacheEnsureScriptTests
{
    [Theory]
    [InlineData("tools/scripts/worktree/lean-cache-ensure.sh", "ensure-cache")]
    [InlineData("tools/scripts/worktree/lean-cache-run.sh", "lean-cache-writer")]
    public void MissingLakeDelegatesToCandidateBuiltDllWithoutRestoreOrBuild(string scriptPath, string command)
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new TemporaryDirectory();
        var scriptText = scriptPath switch
        {
            "tools/scripts/worktree/lean-cache-ensure.sh" => File.ReadAllText(
                Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree/lean-cache-ensure.sh")),
            "tools/scripts/worktree/lean-cache-run.sh" => File.ReadAllText(
                Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree/lean-cache-run.sh")),
            _ => throw new ArgumentOutOfRangeException(nameof(scriptPath)),
        };
        var installed = InstallScript(fixture.Path, scriptText, scriptPath);
        Directory.CreateDirectory(installed.Bin);
        var dotnet = Path.Combine(installed.Bin, "dotnet");
        File.WriteAllText(
            dotnet,
            "#!/usr/bin/env bash\nprintf '%s\\n' \"$@\" > \"$DOTNET_ARGUMENTS\"\nprintf '%s\\n' \"$PWD\" > \"$DOTNET_CWD\"\nprintf 'delegated\\n'\n");
        File.SetUnixFileMode(
            dotnet,
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);

        var result = TestProcessRunner.Run(
            "/bin/bash",
            [
                "-c",
                "PATH=\"$1:$PATH\" DOTNET_ARGUMENTS=\"$2\" DOTNET_CWD=\"$3\" STRATALINT_LEAN_CLI_DLL=\"$(cd \"$5\" && pwd -P)/tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll\" STRATALINT_LEAN_PRODUCER_DLL=\"$(cd \"$5\" && pwd -P)/tools/StrataLint.Lean/bin/Release/net10.0/StrataLint.Lean.dll\" exec /bin/bash \"$4\"",
                "lean-cache-test",
                installed.Bin,
                installed.ArgumentsPath,
                installed.DotnetCwdPath,
                installed.Script,
                installed.Repository,
            ],
            installed.Caller,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal("delegated\n", Encoding.UTF8.GetString(result.StandardOutput));
        Assert.Empty(result.StandardError);
        var canonicalRoot = TestProcessRunner.Run(
            "/bin/pwd",
            ["-P"],
            installed.Repository,
            TestBudgets.ScriptProcessHangGuard,
            4096);
        Assert.Equal(0, canonicalRoot.ExitCode);
        var canonicalRepository = Encoding.UTF8.GetString(canonicalRoot.StandardOutput).TrimEnd('\n');
        var expected = command == "lean-cache-writer"
            ? Path.Combine(canonicalRepository, "tools/StrataLint.Lean/bin/Release/net10.0/StrataLint.Lean.dll") + "\nlean-cache-writer\n--\n"
            : Path.Combine(canonicalRepository, "tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll") + "\nworktree\nensure-cache\n";
        Assert.Equal(expected, installed.ArgumentsText);
        Assert.Equal(canonicalRepository + "\n", installed.DotnetCwdText);
    }

    [Fact]
    public void PrivateDirectoryDelegatesToTheCanonicalJudge()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new TemporaryDirectory();
        var installed = InstallScript(fixture.Path, File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree/lean-cache-ensure.sh")));
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
        var installed = InstallScript(fixture.Path, File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree/lean-cache-ensure.sh")));
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

    private static InstalledScript InstallScript(string fixtureRoot, string scriptText, string scriptPath = LeanCacheEnsureScriptPath)
    {
        var repository = Path.Combine(fixtureRoot, "repository");
        var caller = Path.Combine(fixtureRoot, "caller");
        var script = Path.Combine(
            repository,
            scriptPath.Replace('/', Path.DirectorySeparatorChar));
        Directory.CreateDirectory(Path.GetDirectoryName(script)!);
        Directory.CreateDirectory(caller);
        ScriptHarnessScratch.WriteScratchText(script, scriptText);
        return new InstalledScript(fixtureRoot, repository, caller, script);
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
        return TestProcessRunner.Run(
            "/bin/bash",
            ["-c", "PATH=\"$1:$PATH\" DOTNET_MARKER=\"$2\" exec /bin/bash \"$3\"", "lean-cache-test", bin, marker, script],
            workingDirectory,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);
    }

    private sealed record InstalledScript(
        string FixtureRoot,
        string Repository,
        string Caller,
        string Script)
    {
        internal string Bin => Path.Combine(FixtureRoot, "bin");

        internal string ArgumentsPath => Path.Combine(FixtureRoot, "dotnet-arguments");

        internal string DotnetCwdPath => Path.Combine(FixtureRoot, "dotnet-cwd");

        internal string ArgumentsText => TemporaryFileSystem.File.ReadAllText(ArgumentsPath);

        internal string DotnetCwdText => TemporaryFileSystem.File.ReadAllText(DotnetCwdPath);
    }
}
