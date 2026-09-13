using StrataLint.Cli;

namespace StrataLint.Tests;

[Collection("Lean cache environment")]
public sealed class ArchiveInEnsureChainTests
{
    [Theory]
    [InlineData("miss", 1, "miss")]
    [InlineData("rejected", 1, "rejected")]
    [InlineData("unpacked", 1, "failed")]
    [InlineData("unpacked", 0, "unpacked")]
    public void PrivateReleaseFallbackRunsUnderReaderPolicyAndChecksItsExit(string status, int exit, string expected)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new SharedLakeFixture();
        var script = LeanArchiveFetch.ScriptPath(fixture.Reader);
        Directory.CreateDirectory(Path.GetDirectoryName(script)!);
        File.WriteAllText(script, "#!/bin/sh\n"
            + "printf '%s\\n' \"$MATHLIB_CACHE_DIR\" > downloads-path\n"
            + "echo 'LEAN_CACHE_FETCH {\"status\":\"" + status + "\",\"reason\":\"fixture\"}'\nexit " + exit + "\n");
        var result = fixture.Command(fixture.Reader, "ensure-cache");
        Assert.True(result.Success, result.Error);
        Assert.Contains("\"archive_status\":\"" + expected + "\"", result.Output);
        Assert.Equal(fixture.Reader + "/.lake/mathlib-cache\n",
            File.ReadAllText(Path.Combine(fixture.Reader, "downloads-path")));
    }

    [Fact]
    public void OccupiedPrivateBuildRootIsNotOverwrittenByReleaseFetch()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new SharedLakeFixture();
        var script = LeanArchiveFetch.ScriptPath(fixture.Reader);
        Directory.CreateDirectory(Path.GetDirectoryName(script)!);
        File.WriteAllText(script, "#!/bin/sh\necho invoked > unexpected\nexit 1\n");
        var build = Path.Combine(fixture.Reader, ".lake", "build");
        Directory.CreateDirectory(build);
        File.WriteAllText(Path.Combine(build, "occupied"), "preserve");
        var result = fixture.Command(fixture.Reader, "ensure-cache");
        Assert.True(result.Success, result.Error);
        Assert.False(File.Exists(Path.Combine(fixture.Reader, "unexpected")));
        Assert.Equal("preserve", File.ReadAllText(Path.Combine(build, "occupied")));
    }
}
