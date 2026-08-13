using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class FrozenLedgerRejectFixtureTests
{
    [Fact]
    public void MissingObjectIsATypedSemanticRejectionWithGitExitDetails()
    {
        using var repository = new TemporaryDirectory();
        ReviewRegressionTests.RunGit(repository.Path, "init", "--object-format=sha1");
        var missing = "git-sha1:" + new string('f', 40);

        var exception = Assert.Throws<FrozenReferenceRejectionException>(() =>
            new GitRepositoryGateway(repository.Path).ValidateFrozenReferences(
                OnlyCommit(missing)));

        Assert.Equal(FrozenReferenceRejectionKind.MissingObject, exception.Kind);
        var failure = Assert.IsType<GitCommandFailure>(exception.GitFailure);
        Assert.Equal(GitCommandFailureKind.NonzeroExit, failure.Kind);
        Assert.Equal(128, failure.ExitCode);
        Assert.Contains("cat-file", failure.Arguments);
        Assert.NotEmpty(failure.StandardError);
    }

    [Fact]
    public void WrongObjectTypeIsATypedSemanticRejectionDistinctFromMissingObject()
    {
        using var repository = new TemporaryDirectory();
        ReviewRegressionTests.RunGit(repository.Path, "init", "--object-format=sha1");
        var source = Path.Combine(repository.Path, "evidence.txt");
        File.WriteAllText(source, "evidence\n", new UTF8Encoding(false));
        var blob = ReviewRegressionTests.RunGit(
            repository.Path,
            "hash-object",
            "-w",
            source).Trim();

        var exception = Assert.Throws<FrozenReferenceRejectionException>(() =>
            new GitRepositoryGateway(repository.Path).ValidateFrozenReferences(
                OnlyCommit("git-sha1:" + blob)));

        Assert.Equal(FrozenReferenceRejectionKind.WrongObjectType, exception.Kind);
        Assert.Null(exception.GitFailure);
        Assert.Contains("has type blob; expected commit", exception.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("not a reachable", exception.Message, StringComparison.Ordinal);
    }

    private static FrozenLedgerReferenceSet OnlyCommit(string oid) =>
        FrozenLedgerReferenceSet.Create(
            ImmutableArray<FrozenLedgerInput>.Empty,
            ImmutableArray<string>.Empty,
            [oid],
            Array.Empty<string>(),
            Array.Empty<string>());
}
