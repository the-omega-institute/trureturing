using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class LeanReportPairScriptTests
{
    [Fact]
    public void CandidateInterfaceForwardsArgumentsAndProducerFailure()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var producer = Path.Combine(temporary.Path, "producer");
        File.WriteAllText(producer, "#!/bin/sh\nprintf '%s\\n' \"$LAKE_BIN\" \"$@\"\nexit 71\n");
        File.SetUnixFileMode(producer, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var output = Path.Combine(temporary.Path, "candidate report.json");
        var result = TestProcessRunner.Run("bash", [Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/lean-report-pair.sh"),
            "--producer", producer, "--lake-bin", "/usr/bin/true", "--candidate-root", temporary.Path,
            "--candidate-output", output], temporary.Path, BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
        Assert.Equal(71, result.ExitCode);
        Assert.Equal($"/usr/bin/true\n--repository\n{temporary.Path}\n--output\n{output}\n", Encoding.UTF8.GetString(result.StandardOutput));
    }

    [Theory]
    [InlineData("--base-root")]
    [InlineData("--producer")]
    public void IncompleteOrUnknownInterfacesFail(string argument)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("bash", [Path.Combine(root, "tools/scripts/lean-report-pair.sh"), argument], root,
            BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
        Assert.Equal(2, result.ExitCode);
    }
}
