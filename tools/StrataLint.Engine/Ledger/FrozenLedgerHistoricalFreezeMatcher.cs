using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static class FrozenLedgerHistoricalFreezeMatcher
{
    internal static bool HistoricalActiveFreezeMatches(
        FrozenFreezePayload payload,
        FrozenNodeMaterial material,
        IReadOnlyDictionary<FrozenNodeId, RepoPath> recordedPathsByIdentity,
        IReadOnlyDictionary<FrozenNodeId, RepoPath> currentPathsByIdentity,
        out ImmutableArray<string> differences)
    {
        var result = ImmutableArray.CreateBuilder<string>();
        if (!payload.DeclarationStatementIds.SequenceEqual(material.DeclarationStatementIds))
        {
            result.Add(SequenceDifference(
                "DeclarationStatementIds",
                material.DeclarationStatementIds,
                payload.DeclarationStatementIds,
                static item =>
                    $"{item.DeclarationNameKey}|{item.Kind}|{item.StatementId.Value}"));
        }

        if (payload.StatementId != material.StatementId)
        {
            result.Add(ScalarDifference(
                "StatementId",
                material.StatementId.Value,
                payload.StatementId.Value));
        }

        if (!material.AxiomClosure.All(LeanAxiomFacts.IsStandard))
        {
            result.Add(
                $"AxiomClosure current={FormatSequence(material.AxiomClosure, static item => item)} exceeds the standard axiom allowlist");
        }

        var hasExpectedPrerequisitePaths = TryResolvePrerequisitePaths(
            material.PrerequisiteFrozenNodeIds,
            currentPathsByIdentity,
            out var expectedPrerequisitePaths,
            out var unresolvedExpectedIdentity);
        var hasActualPrerequisitePaths = TryResolvePrerequisitePaths(
            payload.PrerequisiteFrozenNodeIds,
            recordedPathsByIdentity,
            out var actualPrerequisitePaths,
            out var unresolvedActualIdentity);
        if (!hasExpectedPrerequisitePaths)
        {
            result.Add(
                $"PrerequisitePaths expected=<unresolved:{unresolvedExpectedIdentity!.Value}>, "
                + (hasActualPrerequisitePaths
                    ? $"actual={FormatSequence(actualPrerequisitePaths, static item => item.Value)}"
                    : $"actual=<unresolved:{unresolvedActualIdentity!.Value}>"));
        }
        else if (hasActualPrerequisitePaths
            && !actualPrerequisitePaths.SequenceEqual(expectedPrerequisitePaths))
        {
            result.Add(SequenceDifference(
                "PrerequisitePaths",
                expectedPrerequisitePaths,
                actualPrerequisitePaths,
                static item => item.Value));
        }

        if (payload.Input.DescriptorSelector != material.RepoPath.Value)
        {
            result.Add(ScalarDifference(
                "Input.DescriptorSelector",
                material.RepoPath.Value,
                payload.Input.DescriptorSelector));
        }

        differences = result.ToImmutable();
        return differences.IsEmpty;
    }

    private static bool TryResolvePrerequisitePaths(
        ImmutableArray<FrozenNodeId> identities,
        IReadOnlyDictionary<FrozenNodeId, RepoPath> pathsByIdentity,
        out ImmutableArray<RepoPath> paths,
        out FrozenNodeId? unresolvedIdentity)
    {
        var resolved = ImmutableArray.CreateBuilder<RepoPath>(identities.Length);
        foreach (var identity in identities)
        {
            if (!pathsByIdentity.TryGetValue(identity, out var path))
            {
                paths = [];
                unresolvedIdentity = identity;
                return false;
            }

            resolved.Add(path);
        }

        paths = resolved
            .Distinct()
            .OrderBy(static path => path.Value, StringComparer.Ordinal)
            .ToImmutableArray();
        unresolvedIdentity = null;
        return true;
    }

    private static string ScalarDifference(string field, string expected, string actual) =>
        $"{field} expected={expected}, actual={actual}";

    private static string SequenceDifference<T>(
        string field,
        ImmutableArray<T> expected,
        ImmutableArray<T> actual,
        Func<T, string> format)
    {
        var missing = MissingItems(expected, actual);
        var extra = MissingItems(actual, expected);
        var shape = missing.IsEmpty && extra.IsEmpty
            ? "order differs"
            : $"missing={FormatSequence(missing, format)}, extra={FormatSequence(extra, format)}";
        return $"{field} expected={FormatSequence(expected, format)}, "
            + $"actual={FormatSequence(actual, format)}, {shape}";
    }

    private static ImmutableArray<T> MissingItems<T>(
        ImmutableArray<T> expected,
        ImmutableArray<T> actual)
    {
        var remaining = actual.ToList();
        var missing = ImmutableArray.CreateBuilder<T>();
        foreach (var item in expected)
        {
            var index = remaining.FindIndex(candidate =>
                EqualityComparer<T>.Default.Equals(candidate, item));
            if (index < 0)
            {
                missing.Add(item);
            }
            else
            {
                remaining.RemoveAt(index);
            }
        }

        return missing.ToImmutable();
    }

    private static string FormatSequence<T>(
        ImmutableArray<T> items,
        Func<T, string> format) =>
        "[" + string.Join(", ", items.Select(format)) + "]";
}
