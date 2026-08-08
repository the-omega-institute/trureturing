using System.Collections.Immutable;

namespace StrataLint.Cli;

internal sealed record QuotientObligation(string RootId, string SuccessorVerifierId);
internal sealed record QuotientClassification(string Classification, bool Pass, ImmutableArray<string> Diagnostics);

internal static class RefactorQuotient
{
    internal const string ProjectionFreshness = "OBL-PROJECTION-FRESHNESS";

    internal static QuotientClassification Classify(
        string oldRaw,
        string oldCanonical,
        string successor,
        IReadOnlyList<string> diffPaths,
        IReadOnlySet<string> runLocalPaths,
        IReadOnlyList<string> oldRawObligations,
        IReadOnlyList<string> oldCanonicalObligations,
        IReadOnlyList<string> successorObligations,
        IReadOnlyList<QuotientObligation> obligations,
        IReadOnlyList<QuotientObligation> expectedObligations)
    {
        var diagnostics = ImmutableArray.CreateBuilder<string>();
        var expectedRoots = expectedObligations.Select(static item => item.RootId).ToHashSet(StringComparer.Ordinal);
        var actualRoots = obligations.Select(static item => item.RootId).ToArray();
        if (actualRoots.Distinct(StringComparer.Ordinal).Count() != actualRoots.Length)
            diagnostics.Add("QUOTIENT_AUTHORITY_SUCCESSOR_CARDINALITY");
        if (!actualRoots.ToHashSet(StringComparer.Ordinal).SetEquals(expectedRoots))
            diagnostics.Add("QUOTIENT_AUTHORITY_ROOT_MISMATCH");
        if (obligations.Any(static item => string.IsNullOrWhiteSpace(item.SuccessorVerifierId)))
            diagnostics.Add("QUOTIENT_AUTHORITY_SUCCESSOR_CARDINALITY");

        var rawWithoutFreshness = oldRawObligations
            .Where(static value => value != ProjectionFreshness).ToHashSet(StringComparer.Ordinal);
        var canonicalSet = oldCanonicalObligations.ToHashSet(StringComparer.Ordinal);
        var successorSet = successorObligations.ToHashSet(StringComparer.Ordinal);
        var stalenessOnly = oldRaw == "reject"
            && oldCanonical == "admit"
            && diffPaths.Count > 0
            && diffPaths.All(runLocalPaths.Contains)
            && oldRawObligations.Contains(ProjectionFreshness, StringComparer.Ordinal)
            && rawWithoutFreshness.SetEquals(canonicalSet)
            && canonicalSet.SetEquals(successorSet);
        var classification = stalenessOnly ? "projection-staleness-only" : "semantic-domain";
        if (stalenessOnly && successor != "admit") diagnostics.Add("QUOTIENT_PROJECTION_NEW_REJECT");
        if (!stalenessOnly && oldRaw != successor) diagnostics.Add("QUOTIENT_SEMANTIC_DISPOSITION_MISMATCH");
        return new(classification, diagnostics.Count == 0, diagnostics.ToImmutable());
    }
}
