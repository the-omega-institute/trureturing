using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static class FrozenLedgerHistoricalFreezeMatcher
{
    internal static bool HistoricalActiveFreezeMatches(
        FrozenFreezePayload payload,
        FrozenNodeMaterial material,
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

        differences = result.ToImmutable();
        return differences.IsEmpty;
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
