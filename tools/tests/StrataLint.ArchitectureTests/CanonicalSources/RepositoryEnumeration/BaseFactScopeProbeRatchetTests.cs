using System.Reflection;
using StrataLint.Engine;
using StrataLint.Tests;
using Xunit;

namespace StrataLint.ArchitectureTests.CanonicalSources.RepositoryEnumeration;

public sealed class BaseFactScopeProbeRatchetTests
{
    private static readonly ScopeProbeExemption[] Exemptions =
    [
        new(
            "SL-003",
            "Capacity pressure is a repository-wide aggregate; its finding is the global bucket size, not a historical object fact."),
    ];

    [Fact]
    public void EveryActiveRuleHasANamedDifferentialBaseFactScopeProbeOrPinnedExemption()
    {
        var active = RuleCatalog.Default.Descriptors
            .Where(static descriptor => descriptor.Lifecycle == RuleLifecycle.Active)
            .Select(static descriptor => descriptor.Id.Value)
            .ToHashSet(StringComparer.Ordinal);
        var exempt = Exemptions
            .Select(static exemption => exemption.Rule)
            .ToHashSet(StringComparer.Ordinal);
        Assert.Equal(Exemptions.Length, exempt.Count);
        Assert.All(Exemptions, static exemption =>
            Assert.False(string.IsNullOrWhiteSpace(exemption.Reason)));
        var probes = ProbeMethods()
            .SelectMany(method => method.GetCustomAttributes<BaseFactScopeProbeAttribute>()
                .Select(attribute => new
                {
                    Rule = $"SL-{attribute.RuleNumber:000}",
                    Method = method,
                }))
            .ToArray();

        var unknown = probes.Select(static probe => probe.Rule)
            .Concat(exempt)
            .Where(rule => !active.Contains(rule))
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();
        Assert.True(
            unknown.Length == 0,
            "scope probes/exemptions name non-active rules: " + string.Join(", ", unknown));

        foreach (var probe in probes)
        {
            Assert.True(
                probe.Method.Name.StartsWith(
                    probe.Rule.Replace("-", string.Empty, StringComparison.Ordinal),
                    StringComparison.OrdinalIgnoreCase),
                $"{probe.Rule} probe {probe.Method.DeclaringType?.FullName}.{probe.Method.Name} is not named for its rule");
            Assert.True(
                probe.Method.GetCustomAttributes()
                    .Any(attribute => attribute.GetType().FullName is "Xunit.FactAttribute" or "Xunit.TheoryAttribute"),
                $"{probe.Rule} probe {probe.Method.DeclaringType?.FullName}.{probe.Method.Name} is not an executable xUnit test");
        }

        var duplicate = probes.GroupBy(static probe => probe.Rule, StringComparer.Ordinal)
            .Where(static group => group.Count() != 1)
            .Select(static group => group.Key)
            .Order(StringComparer.Ordinal)
            .ToArray();
        Assert.True(
            duplicate.Length == 0,
            "active rules must have exactly one canonical scope probe: " + string.Join(", ", duplicate));

        var probeAndExemption = probes.Select(static probe => probe.Rule)
            .Where(exempt.Contains)
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();
        Assert.True(
            probeAndExemption.Length == 0,
            "active rules cannot have both a scope probe and an exemption: "
                + string.Join(", ", probeAndExemption));

        var covered = probes.Select(static probe => probe.Rule)
            .Concat(exempt)
            .ToHashSet(StringComparer.Ordinal);
        var missing = active.Except(covered, StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray();
        Assert.True(
            missing.Length == 0,
            "active rules missing a named differential base-fact scope probe: "
                + string.Join(", ", missing));
    }

    [Fact]
    public void GlobalScopeExemptionListMatchesTheApprovedClosedSet()
    {
        Assert.Equal(
            [
                new ScopeProbeExemption(
                    "SL-003",
                    "Capacity pressure is a repository-wide aggregate; its finding is the global bucket size, not a historical object fact."),
            ],
            Exemptions);
    }

    private static IEnumerable<MethodInfo> ProbeMethods() =>
        typeof(R15ScopeNarrowingTests).Assembly.GetTypes()
            .OrderBy(static type => type.FullName, StringComparer.Ordinal)
            .SelectMany(static type => type.GetMethods(
                BindingFlags.Instance | BindingFlags.Static | BindingFlags.Public | BindingFlags.NonPublic))
            .Where(static method => method.IsDefined(typeof(BaseFactScopeProbeAttribute), inherit: false));

    public sealed record ScopeProbeExemption(string Rule, string Reason);
}
