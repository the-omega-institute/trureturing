using StrataLint.Cli;

namespace StrataLint.Tests;

[Collection("Lean cache environment")]
public sealed class ArchiveInEnsureChainTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void EnsureNeverFetchesArchivesOrOverwritesExistingBuilds(bool occupied)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new SharedLakeFixture();
        var script = Path.Combine(fixture.Reader, "tools/scripts/worktree/lean-cache-publish.sh");
        Directory.CreateDirectory(Path.GetDirectoryName(script)!);
        File.WriteAllText(script, "#!/bin/sh\necho invoked > unexpected\nexit 1\n");
        var build = Path.Combine(fixture.Reader, ".lake", "build");
        if (occupied)
        {
            Directory.CreateDirectory(build);
            File.WriteAllText(Path.Combine(build, "occupied"), "preserve");
        }
        var result = fixture.Command(fixture.Reader, "ensure-cache");
        Assert.True(result.Success, result.Error);
        Assert.False(File.Exists(Path.Combine(fixture.Reader, "unexpected")));
        if (occupied) Assert.Equal("preserve", File.ReadAllText(Path.Combine(build, "occupied")));
        else Assert.False(Directory.Exists(build));
    }
}
