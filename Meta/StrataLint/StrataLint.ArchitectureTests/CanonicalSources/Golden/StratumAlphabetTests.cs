using System.Reflection;
using StrataLint.Definitions;
using StrataLint.Engine;

namespace StrataLint.ArchitectureTests;

public sealed class StratumAlphabetTests
{
    private static readonly string[] Expected = ["S0", "S1", "S2", "S3", "S4"];

    [Fact]
    public void EveryClosedStratumTouchpointMatchesTheFiveMemberAlphabet()
    {
        var goldenStratum = typeof(Anchor).Assembly.GetType(
            "StrataLint.Definitions.GoldenStratum",
            throwOnError: true)!;
        var candidates = Expected.Concat(["", "S5", "S10", "s0", "X_Assumptions"]);
        var sets = new Dictionary<string, IEnumerable<string>>(StringComparer.Ordinal)
        {
            ["GoldenStratum"] = Enum.GetNames(goldenStratum),
            ["Engine.Stratum"] = Enum.GetNames<Stratum>(),
            ["RepositoryRules.IsStratum"] = AcceptedBy(
                typeof(RepositoryRules),
                candidates),
            ["Gid.IsStratum"] = AcceptedBy(typeof(Gid), candidates),
        };

        Assert.Empty(StratumAlphabetPolicy.FindDrift(Expected, sets));
    }

    [Fact]
    public void ExtraStratumIsRejectedByTheRedFixture()
    {
        var sets = new Dictionary<string, IEnumerable<string>>(StringComparer.Ordinal)
        {
            ["synthetic"] = [.. Expected, "S5"],
        };

        var finding = Assert.Single(StratumAlphabetPolicy.FindDrift(Expected, sets));

        Assert.Contains("S5", finding, StringComparison.Ordinal);
    }

    private static string[] AcceptedBy(Type owner, IEnumerable<string> candidates)
    {
        var method = owner.GetMethod(
            "IsStratum",
            BindingFlags.Static | BindingFlags.NonPublic)
            ?? throw new InvalidOperationException($"{owner.FullName}.IsStratum is absent");
        return candidates
            .Where(value => (bool)method.Invoke(null, [value])!)
            .Order(StringComparer.Ordinal)
            .ToArray();
    }
}
