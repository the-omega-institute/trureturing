using System.Diagnostics;
using System.Text;
using StrataLint.Cli;
using StrataLint.Runtime;

namespace StrataLint.Tests;

public sealed class WorktreeAdapterTransportTests
{
    private const int LaunchStringBound = 8192;
    private const int LinuxArgumentLimit = 131072;

    [Theory]
    [InlineData("run")]
    [InlineData("lines")]
    [InlineData("environment")]
    public void OversizedEmbeddedProgramKeepsEveryLaunchStringBounded(string entry)
    {
        using var directory = new TemporaryDirectory();
        // These checkout-local modules must never supply executable code.
        foreach (var module in new[] { "worktree_protocol", "worktree_publication",
                     "worktree_preservation", "worktree_pool" })
            File.WriteAllText(Path.Combine(directory.Path, module + ".py"), "raise RuntimeError('checkout import')\n");
        var launches = 0;
        string? programPath = null;
        var previous = BoundedProcessRunner.StartProcess.Value;
        try
        {
            BoundedProcessRunner.StartProcess.Value = process =>
            {
                launches++;
                var arguments = process.StartInfo.ArgumentList;
                // Replaying the embedded module definitions grows the executable
                // image without changing its final command or policy query.
                if (arguments[1] == "-c")
                    arguments[2] = EnlargeEmbeddedProgram(arguments[2]);
                else
                {
                    programPath = arguments[2];
                    File.WriteAllText(programPath, EnlargeEmbeddedProgram(File.ReadAllText(programPath)));
                }
                AssertBoundedLaunch(process.StartInfo);
                return process.Start();
            };
            var production = new ProductionWorktreeProcessRunner();
            if (entry == "environment")
            {
                var policy = WorktreeProtocolCommand.InitializationEnvironment(directory.Path);
                Assert.Equal("1", policy["MSBUILDDISABLENODEREUSE"]);
                Assert.Equal("0", policy["DOTNET_CLI_USE_MSBUILD_SERVER"]);
            }
            else
            {
                var lines = new List<string>();
                var result = entry == "run"
                    ? WorktreeProtocolCommand.Run(directory.Path, ["--help"], production)
                    : WorktreeProtocolCommand.RunLines(directory.Path, ["--help"], production,
                        TestBudgets.ScriptProcessHangGuard, lines.Add);
                Assert.True(result.Success, result.Error);
                Assert.Equal(0, result.ExitCode);
                Assert.Empty(result.Error);
                Assert.Contains("checkpoint", entry == "run" ? result.Output : string.Join('\n', lines));
                if (entry == "lines") Assert.Empty(result.Output);
            }
        }
        finally { BoundedProcessRunner.StartProcess.Value = previous; }
        Assert.Equal(1, launches);
        Assert.NotNull(programPath);
        Assert.False(File.Exists(programPath));
        Assert.False(Directory.Exists(Path.GetDirectoryName(programPath)));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void NonzeroVerdictAndDiagnosticsSurviveTransport(bool streaming)
    {
        using var directory = new TemporaryDirectory();
        var lines = new List<string>();
        var runner = new ProductionWorktreeProcessRunner();
        var result = streaming
            ? WorktreeProtocolCommand.RunLines(directory.Path, ["unknown-action"], runner,
                TestBudgets.ScriptProcessHangGuard, lines.Add)
            : WorktreeProtocolCommand.Run(directory.Path, ["unknown-action"], runner);
        Assert.False(result.Success);
        Assert.Equal(2, result.ExitCode);
        Assert.Empty(result.Output);
        Assert.Empty(lines);
        Assert.Contains("invalid choice", result.Error);
    }

    [Theory]
    [InlineData("result")]
    [InlineData("start_failure")]
    [InlineData("consumer_failure")]
    public void PrivateProgramContainsBuildResourcesAndIsRemovedOnEveryExit(string outcome)
    {
        using var directory = new TemporaryDirectory();
        string? programPath = null;
        var runner = new ScriptedWorktreeProcessRunner(new ProductionWorktreeProcessRunner(), (_, args, _) =>
        {
            Assert.Equal(new[] { "-I", "-B" }, args.Take(2));
            programPath = args[2];
            Assert.True(Path.IsPathFullyQualified(programPath));
            Assert.False(programPath.StartsWith(directory.Path + Path.DirectorySeparatorChar, StringComparison.Ordinal));
            Assert.True(File.Exists(programPath));
            if (!OperatingSystem.IsWindows())
            {
                Assert.Equal(UnixFileMode.UserRead | UnixFileMode.UserWrite, File.GetUnixFileMode(programPath));
                Assert.Equal(UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute,
                    File.GetUnixFileMode(Path.GetDirectoryName(programPath)!));
            }
            var program = File.ReadAllText(programPath);
            var assembly = typeof(WorktreeCommand).Assembly;
            foreach (var name in new[] { "worktree_protocol", "worktree_publication",
                         "worktree_preservation", "worktree_pool" })
            {
                using var resource = assembly.GetManifestResourceStream($"WorktreeProtocol.{name}.py");
                Assert.NotNull(resource);
                using var bytes = new MemoryStream();
                resource.CopyTo(bytes);
                Assert.Contains(Convert.ToBase64String(bytes.ToArray()), program);
            }
            if (outcome == "start_failure") throw new IOException("fixture start failure");
            return new ProcessOutput(19, Encoding.UTF8.GetBytes("row\n"), Encoding.UTF8.GetBytes("diagnostic"));
        });
        if (outcome == "consumer_failure")
            Assert.Throws<InvalidOperationException>(() => WorktreeProtocolCommand.RunLines(directory.Path,
                ["--help"], runner, TestBudgets.ScriptProcessHangGuard, _ => throw new InvalidOperationException("consumer")));
        else if (outcome == "start_failure")
            Assert.Throws<IOException>(() => WorktreeProtocolCommand.Run(directory.Path, ["--help"], runner));
        else
        {
            var result = WorktreeProtocolCommand.Run(directory.Path, ["--help"], runner);
            Assert.Equal(19, result.ExitCode);
            Assert.Equal("row\n", result.Output);
            Assert.Equal("diagnostic", result.Error);
        }
        Assert.NotNull(programPath);
        Assert.False(File.Exists(programPath));
        Assert.False(Directory.Exists(Path.GetDirectoryName(programPath)));
    }

    private static string EnlargeEmbeddedProgram(string source)
    {
        var lastDefinition = source.LastIndexOf("exec(compile(", StringComparison.Ordinal);
        Assert.True(lastDefinition >= 0);
        var definitionsEnd = source.IndexOf('\n', lastDefinition) + 1;
        Assert.True(definitionsEnd > 0);
        var definitions = source[..definitionsEnd];
        var enlarged = definitions + definitions + source;
        Assert.True(Encoding.UTF8.GetByteCount(enlarged) > LinuxArgumentLimit);
        return enlarged;
    }

    private static void AssertBoundedLaunch(ProcessStartInfo start)
    {
        Assert.All(start.ArgumentList, argument => Assert.True(
            Encoding.UTF8.GetByteCount(argument) < LaunchStringBound, "oversized argv string"));
        Assert.All(start.Environment, item => Assert.True(
            Encoding.UTF8.GetByteCount(item.Key + "=" + item.Value) < LaunchStringBound, "oversized environment string"));
    }
}
