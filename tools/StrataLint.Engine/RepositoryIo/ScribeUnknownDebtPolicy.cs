using System.Collections.Immutable;

namespace StrataLint.Engine;

internal sealed record ScribeUnknownDebtPartitionV1(
    string Key,
    ImmutableSortedDictionary<string, ScribeTestMethod> UnknownMethods);

internal sealed record ScribeUnknownDebtBaselineV1(
    int SchemaVersion,
    ImmutableSortedDictionary<string, ScribeUnknownDebtPartitionV1> Partitions)
{
    internal const int CurrentSchemaVersion = 1;

    internal int UnknownCount => Partitions.Values.Sum(static partition => partition.UnknownMethods.Count);

    internal static ScribeUnknownDebtBaselineV1 Create(ScribeTestMap map)
    {
        var partitions = map.Methods
            .Where(static method => method.IsUnknown)
            .GroupBy(static method => method.PartitionKey, StringComparer.Ordinal)
            .ToImmutableSortedDictionary(
                static group => group.Key,
                static group => new ScribeUnknownDebtPartitionV1(
                    group.Key,
                    group.GroupBy(static method => method.Identity, StringComparer.Ordinal)
                        .ToImmutableSortedDictionary(
                            static methods => methods.Key,
                            static methods => methods.Single(),
                            StringComparer.Ordinal)),
                StringComparer.Ordinal);
        return new ScribeUnknownDebtBaselineV1(CurrentSchemaVersion, partitions);
    }

    internal IEnumerable<ScribeTestMethod> UnknownMethods() =>
        Partitions.Values.SelectMany(static partition => partition.UnknownMethods.Values);

    internal bool Contains(ScribeTestMethod method) =>
        Partitions.TryGetValue(method.PartitionKey, out var partition)
        && partition.UnknownMethods.ContainsKey(method.Identity);
}

internal sealed record ScribeUnknownDebtFinding(
    string Path,
    string Message,
    AdmissionEffect Effect);

internal static class ScribeUnknownDebtPolicy
{
    // The admission debt line remains the phase-4a value. New unknown identities block even
    // below this line; the number describes inherited debt, not spendable capacity.
    internal const int UnknownDebtLimit = 280;

    // policy-override #2204, 2026-08-17. Domain: repository-read test methods that the
    // conservative parser cannot resolve. Positive reading: both merge parents had 280 and
    // their union had 281. Negative boundary: 282 was not observed and remains a repository-wide
    // block. Owner: repository tau=0 owner. Exit: remove this reserve after every branch forked
    // before the v1 partitioned-delta rule landed is merged or closed and dev is back at <= 280.
    internal const int ConcurrentMergeReserve = 1;

    internal const int UnknownDebtToleranceLimit = UnknownDebtLimit + ConcurrentMergeReserve;

    internal static ImmutableArray<ScribeUnknownDebtFinding> Evaluate(
        ScribeTestMap currentMap,
        ScribeTestMap forkPointMap)
    {
        var current = ScribeUnknownDebtBaselineV1.Create(currentMap);
        var forkPoint = ScribeUnknownDebtBaselineV1.Create(forkPointMap);
        var findings = ImmutableArray.CreateBuilder<ScribeUnknownDebtFinding>();
        var introduced = current.UnknownMethods()
            .Where(method => !forkPoint.Contains(method))
            .OrderBy(static method => method.PartitionKey, StringComparer.Ordinal)
            .ThenBy(static method => method.SourcePath, StringComparer.Ordinal)
            .ThenBy(static method => method.Id, StringComparer.Ordinal)
            .ToArray();

        if (current.UnknownCount > UnknownDebtToleranceLimit)
        {
            findings.Add(new ScribeUnknownDebtFinding(
                "tools/tests",
                $"repository contains {current.UnknownCount} conservative unknown test methods "
                    + $"(admission limit {UnknownDebtLimit}, repository tolerance "
                    + $"{UnknownDebtToleranceLimit}; reduce parser debt)",
                AdmissionEffect.Block));
        }
        else if (current.UnknownCount > UnknownDebtLimit && introduced.Length == 0)
        {
            findings.Add(new ScribeUnknownDebtFinding(
                "tools/tests",
                $"repository contains {current.UnknownCount} conservative unknown test methods "
                    + $"(admission limit {UnknownDebtLimit}, repository tolerance "
                    + $"{UnknownDebtToleranceLimit}), but this change introduced none",
                AdmissionEffect.Observe));
        }

        foreach (var method in introduced)
        {
            findings.Add(new ScribeUnknownDebtFinding(
                method.SourcePath,
                $"conservative unknown test method introduced after fork point: "
                    + method.DisplayIdentity,
                AdmissionEffect.Block));
        }

        return findings.ToImmutable();
    }

    internal static ImmutableArray<ScribeUnknownDebtFinding> InspectCurrent(ScribeTestMap currentMap)
    {
        var current = ScribeUnknownDebtBaselineV1.Create(currentMap);
        return current.UnknownCount <= UnknownDebtToleranceLimit
            ? []
            :
            [
                new ScribeUnknownDebtFinding(
                    "tools/tests",
                    $"repository contains {current.UnknownCount} conservative unknown test methods "
                        + $"(admission limit {UnknownDebtLimit}, repository tolerance "
                        + $"{UnknownDebtToleranceLimit}; reduce parser debt)",
                    AdmissionEffect.Block),
            ];
    }
}
