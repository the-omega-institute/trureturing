namespace StrataLint.Tests;

public sealed partial class PrShepherdRecalculationTests
{
    private sealed partial class ShepherdFixture
    {
        internal string ProjectionObservation =>
            File.ReadAllText(calls + ".projection");
    }

    [Fact]
    public void DerivedLaneKeepsTemporaryProjectionOutsideWorkspaceScanSurface()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.Equal("outside-workspace\n", fixture.ProjectionObservation);
        Assert.DoesNotContain(
            Directory.EnumerateFiles(fixture.CacheWorktree, "*", SearchOption.AllDirectories),
            path => Path.GetFileName(path).Contains(
                ".pr-shepherd.",
                StringComparison.Ordinal));

        var script = ReadShepherdScripts();
        Assert.Contains(
            "projection=\"$(mktemp \"${TMPDIR:-/tmp}/pr-shepherd-projection.XXXXXXXX\")\"",
            script,
            StringComparison.Ordinal);
        Assert.DoesNotContain(
            "projection=\"$workspace/",
            script,
            StringComparison.Ordinal);
    }
}
