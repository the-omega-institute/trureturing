using System.Text;
using System.Text.Json;

namespace StrataLint.Tests;

public sealed class SegmentEventTimingScriptTests
{
    [Fact]
    public void EngineeringSegmentValidPushMissingRepositoryKeepsEvent()
    {
        if (OperatingSystem.IsWindows()) return;
        AssertValidPushMissingRepository("engineering");
    }

    [Fact]
    public void LeanInspectSegmentValidPushMissingRepositoryKeepsEvent()
    {
        if (OperatingSystem.IsWindows()) return;
        AssertValidPushMissingRepository("lean-inspect");
    }

    [Fact]
    public void AdmissionSegmentValidPushMissingRepositoryKeepsEvent()
    {
        if (OperatingSystem.IsWindows()) return;
        AssertValidPushMissingRepository("admission");
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static void AssertValidPushMissingRepository(string segment)
    {
        using var temporary = new TemporaryDirectory();
        var script = Path.Combine(
            TestRepositoryLayout.FindRoot(), "tools", "scripts", "workflow", $"segment-{segment}.sh");
        var result = TestProcessRunner.Run(
            "/usr/bin/env",
            [
                "-u", "REPOSITORY",
                "EVENT=push",
                "/bin/bash", script,
            ],
            temporary.Path,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);

        Assert.Equal(2, result.ExitCode);
        var line = Assert.Single(Encoding.UTF8.GetString(result.StandardOutput)
            .Split('\n', StringSplitOptions.RemoveEmptyEntries));
        using var sentinel = JsonDocument.Parse(line);
        var root = sentinel.RootElement;
        Assert.Equal(segment, root.GetProperty("segment").GetString());
        Assert.Equal("\"push\"", root.GetProperty("event").GetRawText());
        Assert.Equal(2, root.GetProperty("raw_rc").GetInt32());
        Assert.Equal("missing-required-input", root.GetProperty("outcome").GetString());
        Assert.Contains("field=REPOSITORY reason=missing", Encoding.UTF8.GetString(result.StandardError));
    }
}
