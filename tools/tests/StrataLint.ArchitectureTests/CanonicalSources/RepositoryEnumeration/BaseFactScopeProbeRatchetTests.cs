using System.Reflection;
using StrataLint.Engine;
using StrataLint.Tests;
using Xunit;

namespace StrataLint.ArchitectureTests;

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
                    Attribute = attribute,
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
                    .Any(attribute => IsXunitTestAttribute(attribute.GetType())),
                $"{probe.Rule} probe {probe.Method.DeclaringType?.FullName}.{probe.Method.Name} is not an executable xUnit test");
        }

        var registeredEdges = RuleCatalog.Default.FindingEdges
            .Where(edge => active.Contains(edge.RuleId.Value))
            .Where(edge => !exempt.Contains(edge.RuleId.Value))
            .ToArray();

        var resolved = probes
            .Select(probe =>
            {
                var candidates = registeredEdges
                    .Where(edge => edge.RuleId.Value == probe.Rule)
                    .ToArray();
                if (probe.Attribute.EdgeOwnerType is null)
                {
                    return new
                    {
                        Probe = probe,
                        Edge = candidates.Length == 1 ? candidates[0] : null,
                        Error = candidates.Length == 1
                            ? null
                            : $"{probe.Rule} has {candidates.Length} registered finding edges; the probe must bind one explicitly",
                    };
                }

                var expected = FindingEdgeId.For(
                    probe.Attribute.EdgeOwnerType,
                    probe.Attribute.EdgeMemberName!);
                var match = candidates.SingleOrDefault(edge => edge.Edge.Id == expected);
                return new
                {
                    Probe = probe,
                    Edge = match,
                    Error = match is null
                        ? $"{probe.Rule} probe binds unregistered finding edge {expected}"
                        : null,
                };
            })
            .ToArray();

        var unnamed = resolved
            .Where(static item => item.Edge is not null
                && item.Probe.Attribute.EdgeOwnerType is not null
                && !item.Probe.Method.Name.Contains(
                    item.Edge!.Edge.MemberName,
                    StringComparison.OrdinalIgnoreCase))
            .Select(static item =>
                $"{item.Probe.Rule} probe {item.Probe.Method.Name} does not name edge {item.Edge!.Edge.MemberName}")
            .Order(StringComparer.Ordinal)
            .ToArray();
        Assert.True(
            unnamed.Length == 0,
            "explicit edge probes must name their bound finding edge: "
                + string.Join("; ", unnamed));

        var bindingErrors = resolved
            .Where(static item => item.Error is not null)
            .Select(static item => item.Error!)
            .Order(StringComparer.Ordinal)
            .ToArray();
        Assert.True(
            bindingErrors.Length == 0,
            "scope probes have invalid finding-edge bindings: " + string.Join("; ", bindingErrors));

        var duplicate = resolved
            .Where(static item => item.Edge is not null)
            .GroupBy(static item => item.Edge!, EqualityComparer<RegisteredFindingEdge>.Default)
            .Where(static group => group.Count() != 1)
            .Select(static group => group.Key.DisplayName)
            .Order(StringComparer.Ordinal)
            .ToArray();
        Assert.True(
            duplicate.Length == 0,
            "registered finding edges must have exactly one canonical scope probe: "
                + string.Join(", ", duplicate));

        var probeAndExemption = probes.Select(static probe => probe.Rule)
            .Where(exempt.Contains)
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();
        Assert.True(
            probeAndExemption.Length == 0,
            "active rules cannot have both a scope probe and an exemption: "
                + string.Join(", ", probeAndExemption));

        var coveredEdges = resolved
            .Where(static item => item.Edge is not null)
            .Select(static item => item.Edge!)
            .ToHashSet();
        var missing = registeredEdges
            .Where(edge => !coveredEdges.Contains(edge))
            .Select(static edge => edge.DisplayName)
            .Order(StringComparer.Ordinal)
            .ToArray();
        Assert.True(
            missing.Length == 0,
            "registered finding edges missing a named differential base-fact scope probe: "
                + string.Join(", ", missing));
    }

    private static bool IsXunitTestAttribute(Type attributeType)
    {
        for (var current = attributeType; current is not null; current = current.BaseType)
        {
            if (current.FullName is "Xunit.FactAttribute" or "Xunit.TheoryAttribute") return true;
        }

        return false;
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

    [Fact]
    public void RegisteredFindingEdgeIdsAreDerivedFromTheirDeclaringSink()
    {
        var edges = RuleCatalog.Default.FindingEdges;
        Assert.Equal(
            edges.Length,
            edges.Select(edge => $"{edge.RuleId.Value}:{edge.Edge.Id}")
                .Distinct(StringComparer.Ordinal)
                .Count());
        Assert.All(edges, edge =>
            Assert.Equal(
                FindingEdgeId.For(edge.Edge.OwnerType, edge.Edge.MemberName),
                edge.Edge.Id));
    }

    private static IEnumerable<MethodInfo> ProbeMethods() =>
        typeof(R15ScopeNarrowingTests).Assembly.GetTypes()
            .OrderBy(static type => type.FullName, StringComparer.Ordinal)
            .SelectMany(static type => type.GetMethods(
                BindingFlags.Instance | BindingFlags.Static | BindingFlags.Public | BindingFlags.NonPublic))
            .Where(static method => method.IsDefined(typeof(BaseFactScopeProbeAttribute), inherit: false));

    public sealed record ScopeProbeExemption(string Rule, string Reason);
}
