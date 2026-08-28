using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class FrozenLedgerRejectFixtureTests
{
    [Fact]
    public void MissingObjectIsATypedSemanticRejectionDistinctFromWrongType()
    {
        using var repository = new TemporaryDirectory();
        ReviewRegressionTests.RunGit(repository.Path, "init", "--object-format=sha1");
        var missing = "git-sha1:" + new string('f', 40);

        var exception = Assert.Throws<FrozenReferenceRejectionException>(() =>
            new GitRepositoryGateway(repository.Path).ValidateFrozenReferences(
                OnlyCommit(missing)));

        // `git cat-file --batch-check` reports an absent object as a `<oid> missing`
        // line and exits zero, so a legitimately-missing anchor is a pure semantic
        // rejection carrying no Git command failure (parity with WrongObjectType).
        // A genuine Git infrastructure fault still surfaces as GitInfrastructureException.
        Assert.Equal(FrozenReferenceRejectionKind.MissingObject, exception.Kind);
        Assert.Null(exception.GitFailure);
        Assert.Contains("is not a reachable commit", exception.Message, StringComparison.Ordinal);
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
