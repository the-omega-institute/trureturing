using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static class EngineeringTestPlanPolicy
{
    internal static ImmutableArray<string> Evaluate(TestProjectTopologySnapshot candidate) =>
        candidate.Projects.Where(project => project.Registration.Ci)
            .Select(project => project.Path)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
}
