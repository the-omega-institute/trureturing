using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.TruthRelease.Tests;

public sealed class TruthReleaseCommandTests
{
    [Fact]
    public void IssuanceRejectsUnavailableEventFieldsWithoutReadingOrWriting()
    {
        using var temporary = new TemporaryDirectory();
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), RawRepositorySnapshot.Create([]), null);
        var result = global::StrataLint.Cli.TruthReleaseCommand.Run(gateway, null, ["--out", temporary.Path, "--candidate-lean-report", "unused", "--producer-package-commit", new string('e', 40), "--produced-at", "2026-10-11T00:00:00Z", "--scribe-pack", "unused.zip", "--scribe-pack-digest", new string('a', 64), "--commit-on-protected-dev", "true", "--required-check", "current=success"]);
        Assert.Equal(2, result.ExitCode);
        Assert.Contains("TRUTH_RELEASE_EVENT_FIELDS_UNAVAILABLE", result.Error, StringComparison.Ordinal);
        Assert.Equal(0, gateway.ReadCount);
        Assert.Empty(Directory.EnumerateFileSystemEntries(temporary.Path));
    }

    [Fact]
    public void IssuanceRejectsMalformedArguments()
    {
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), RawRepositorySnapshot.Create([]), null);
        Assert.Equal(1, global::StrataLint.Cli.TruthReleaseCommand.Run(gateway, null, []).ExitCode);
        Assert.Equal(0, gateway.ReadCount);
    }
}
