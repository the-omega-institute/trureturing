namespace StrataLint.Tests;

public sealed partial class IngestRobustTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void Ingest_MissingGitWorktreeFailsClosedWithoutWrites(bool sourceScoped)
    {
        var fixture = ConcurrentClaimFixture();
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        Directory.Delete(Path.Combine(temporary.Path, ".git"));
        var before = DirectoryLedgerTestSupport.ReadRepository(temporary);

        var result = Environment(fixture, temporary).Ingest(sourceScoped ? Arguments("alpha") : Arguments());

        Assert.False(result.Success);
        Assert.Equal("INGEST_INVALID repository root has no .git; report-free ingest requires a git worktree\n",
            result.Error);
        AssertSameRepository(before, DirectoryLedgerTestSupport.ReadRepository(temporary));
    }

    [Theory]
    [InlineData("")]
    [InlineData("not a git pointer\n")]
    [InlineData("gitdir: \n")]
    [InlineData("gitdir: missing-metadata\n")]
    public void Ingest_InvalidGitDirectoryPointerFailsClosedWithoutWrites(string pointer)
    {
        var fixture = ConcurrentClaimFixture();
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var dotGit = Path.Combine(temporary.Path, ".git");
        Directory.Delete(dotGit);
        File.WriteAllText(dotGit, pointer);
        var before = DirectoryLedgerTestSupport.ReadRepository(temporary);

        var result = Environment(fixture, temporary).Ingest(Arguments());

        Assert.False(result.Success);
        Assert.StartsWith("INGEST_INVALID ", result.Error, StringComparison.Ordinal);
        AssertSameRepository(before, DirectoryLedgerTestSupport.ReadRepository(temporary));
        Assert.Equal(pointer, File.ReadAllText(dotGit));
    }
}
