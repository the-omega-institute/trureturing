using System.Collections.Immutable;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class RefactorQuotientTests
{
    private static readonly ImmutableArray<QuotientObligation> Obligations =
        [new("root/a", "successor/a")];

    [Fact]
    public void ProjectionStalenessRequiresForwardAdmission()
    {
        var result = RefactorQuotient.Classify(
            "reject", "admit", "admit", ["Generated/x.json"],
            new HashSet<string>(["Generated/x.json"], StringComparer.Ordinal),
            ["OBL-PROJECTION-FRESHNESS", "OBL-X"], ["OBL-X"], ["OBL-X"],
            Obligations, Obligations);

        Assert.Equal("projection-staleness-only", result.Classification);
        Assert.True(result.Pass);

        var mutation = RefactorQuotient.Classify(
            "reject", "admit", "reject", ["Generated/x.json"],
            new HashSet<string>(["Generated/x.json"], StringComparer.Ordinal),
            ["OBL-PROJECTION-FRESHNESS", "OBL-X"], ["OBL-X"], ["OBL-X"],
            Obligations, Obligations);
        Assert.False(mutation.Pass);
        Assert.Contains("QUOTIENT_PROJECTION_NEW_REJECT", mutation.Diagnostics);
    }

    [Fact]
    public void SemanticDifferenceCannotBeClassifiedOut()
    {
        var result = RefactorQuotient.Classify(
            "admit", "admit", "reject", ["D5/source.lean"],
            new HashSet<string>(["Generated/x.json"], StringComparer.Ordinal),
            ["OBL-X"], ["OBL-X"], ["OBL-X"], Obligations, Obligations);

        Assert.Equal("semantic-domain", result.Classification);
        Assert.False(result.Pass);
        Assert.Contains("QUOTIENT_SEMANTIC_DISPOSITION_MISMATCH", result.Diagnostics);
    }

    [Fact]
    public void AuthorityObligationsFailClosedOnMissingOrDuplicateSuccessor()
    {
        var missing = RefactorQuotient.Classify(
            "admit", "admit", "admit", [], new HashSet<string>(StringComparer.Ordinal),
            [], [], [], [], Obligations);
        Assert.False(missing.Pass);
        Assert.Contains("QUOTIENT_AUTHORITY_ROOT_MISMATCH", missing.Diagnostics);

        var duplicate = RefactorQuotient.Classify(
            "admit", "admit", "admit", [], new HashSet<string>(StringComparer.Ordinal),
            [], [], [], [new("root/a", "successor/a"), new("root/a", "successor/b")], Obligations);
        Assert.False(duplicate.Pass);
        Assert.Contains("QUOTIENT_AUTHORITY_SUCCESSOR_CARDINALITY", duplicate.Diagnostics);
    }
}
