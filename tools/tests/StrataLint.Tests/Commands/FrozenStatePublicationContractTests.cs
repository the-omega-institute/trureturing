using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class FrozenStatePublicationContractTests
{
    [Fact]
    public void TruthReleaseRejectsIssuanceWhenEventFieldsHaveNoSource()
    {
        using var output = new TemporaryDirectory();
        var repository = new FakeRepositoryGateway(RawChangeSet.Create([]), RawRepositorySnapshot.Create([]), null);
        var result = TruthReleaseCommand.Run(repository, null,
        [
            "--out", output.Path, "--candidate-lean-report", "not-read.json",
            "--producer-package-commit", new string('e', 40), "--produced-at", "2026-10-11T00:00:00Z",
            "--scribe-pack", "not-read.zip", "--scribe-pack-digest", new string('a', 64),
            "--commit-on-protected-dev", "true", "--required-check", "current=success",
        ]);
        Assert.Equal(2, result.ExitCode);
        Assert.Contains("TRUTH_RELEASE_EVENT_FIELDS_UNAVAILABLE", result.Error, StringComparison.Ordinal);
        Assert.Empty(Directory.EnumerateFileSystemEntries(output.Path));
        Assert.Equal(0, repository.ReadCount);
    }
}
