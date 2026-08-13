namespace StrataLint.ArchitectureTests;

internal static class StratumAlphabetPolicy
{
    internal static IReadOnlyList<string> FindDrift(
        IEnumerable<string> expected,
        IReadOnlyDictionary<string, IEnumerable<string>> touchpoints)
    {
        var canonical = expected
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();
        var findings = new List<string>();
        foreach (var touchpoint in touchpoints.OrderBy(static item => item.Key, StringComparer.Ordinal))
        {
            var actual = touchpoint.Value
                .Distinct(StringComparer.Ordinal)
                .Order(StringComparer.Ordinal)
                .ToArray();
            if (!canonical.SequenceEqual(actual, StringComparer.Ordinal))
            {
                findings.Add(
                    $"{touchpoint.Key}: expected [{string.Join(',', canonical)}], "
                    + $"actual [{string.Join(',', actual)}]");
            }
        }

        return findings;
    }
}
