using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ScribeWrapperModeTests
{
    private const string ScriptPath = "Meta/StrataLint/scripts/scribe.sh";

    [Fact]
    public void ScribeWrapperExposesEmitAndCheckWithOneGeneratorDispatch()
    {
        var script = File.ReadAllText(Path.Combine(FindRepositoryRoot(), ScriptPath));

        Assert.Contains("usage: scribe.sh emit|check", script, StringComparison.Ordinal);
        Assert.Contains("emit|check)", script, StringComparison.Ordinal);
        Assert.Equal(1, Count(script, "generators=(emit emit-values filemap dag)"));
        Assert.Equal(1, Count(script, "run_generator()"));
        Assert.Contains("--check", script, StringComparison.Ordinal);
        Assert.Contains("generator\" == \"emit\"", script, StringComparison.Ordinal);
    }

    [Fact]
    public void CheckModePassesCheckToAllCanonicalProducersWithoutReportConsumer()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new TemporaryDirectory();
        var root = FindRepositoryRoot();
        var script = Path.Combine(fixture.Path, ScriptPath);
        var binDirectory = Path.Combine(fixture.Path, "bin");
        var reportDirectory = Path.Combine(fixture.Path, "Meta", "StrataLint", "scripts", "report");
        Directory.CreateDirectory(binDirectory);
        Directory.CreateDirectory(reportDirectory);
        Directory.CreateDirectory(Path.Combine(fixture.Path, ".lake", "build", "stratalint"));
        File.Copy(Path.Combine(root, ScriptPath), script);
        File.WriteAllText(
            Path.Combine(reportDirectory, "report-consumer.sh"),
            "#!/usr/bin/env bash\nprintf 'consumer-called\\n' >> \"$TRACE\"\nwhile [[ \"${1:-}\" != -- && $# -gt 0 ]]; do shift; done\nshift\nexec \"$@\"\n");
        File.SetUnixFileMode(
            Path.Combine(reportDirectory, "report-consumer.sh"),
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        File.WriteAllText(
            Path.Combine(binDirectory, "dotnet"),
            "#!/usr/bin/env bash\nprintf 'dotnet:%s\\n' \"$*\" >> \"$TRACE\"\nexit 0\n");
        File.SetUnixFileMode(
            Path.Combine(binDirectory, "dotnet"),
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);

        var result = BoundedProcessRunner.Run(
            "/bin/bash",
            ["-c", "PATH=\"$1:$PATH\" TRACE=\"$2\" exec \"$3\" check", "scribe-check", binDirectory, Path.Combine(fixture.Path, "trace.log"), script],
            fixture.Path,
            TimeSpan.FromSeconds(30),
            64 * 1024);

        var trace = File.Exists(Path.Combine(fixture.Path, "trace.log"))
            ? File.ReadAllText(Path.Combine(fixture.Path, "trace.log"))
            : string.Empty;
        Assert.Equal(0, result.ExitCode);
        Assert.Equal(1, trace.Split("consumer-called", StringSplitOptions.None).Length - 1);
        Assert.Equal(5, trace.Split('\n', StringSplitOptions.RemoveEmptyEntries).Length);
        Assert.All(
            trace.Split('\n', StringSplitOptions.RemoveEmptyEntries).Where(static line => line.StartsWith("dotnet:", StringComparison.Ordinal)),
            line => Assert.Contains("--check", line, StringComparison.Ordinal));
    }

    private static int Count(string value, string needle) =>
        value.Split(needle, StringSplitOptions.None).Length - 1;

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
