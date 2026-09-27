using StrataLint.TestSupport;
using TestProjectTopologyPolicy = StrataLint.Engine.RepositoryRules;

namespace StrataLint.ArchitectureTests;

public sealed class TestProjectTopologyPolicyTests
{

    [Fact]
    public void CurrentRepositoryTopologyContainsKnownDebtAndOwnedPairs()
    {
        var root = RepositoryLayout.FindRoot();
        var candidate = TestProjectTopologyPolicy.ReadTrackedProjects(root);
        var debt = TestProjectTopologyPolicy.CalculateDebt(candidate);
        Assert.All(
            debt,
            static debt => Assert.Contains(
                debt.Kind,
                new[]
                {
                    "duplicate-production-identity",
                    "extra-production-reference",
                    "missing-expected-production-reference",
                    "missing-owned-project",
                    "orphan-owned-project",
                    "owned-test-to-owned-test-reference",
                }));
        AssertHasDebtFreePair(candidate, debt);
    }

    [Fact]
    public void CanonicalSolutionIncludesTruthOwnedTestProjectExactlyOnce()
    {
        var solutionLines = File.ReadAllLines(Path.Combine(
            RepositoryLayout.FindRoot(),
            "tools",
            "StrataLint.sln"));
        var matchingProjects = solutionLines.Where(static line => line.StartsWith(
                "Project(",
                StringComparison.Ordinal)
            && line.Contains(
                "\"Trureturing.Truth.Tests\", \"tests\\Trureturing.Truth.Tests\\Trureturing.Truth.Tests.csproj\",",
                StringComparison.Ordinal));

        Assert.Single(matchingProjects);
    }

    private static void AssertHasDebtFreePair(
        TestProjectTopologySnapshot snapshot,
        IReadOnlyList<TestProjectTopologyDebt> debt)
    {
        var pairs = snapshot.Projects.Where(project => project.Registration.Role == "owned-test")
            .Select(project => (Test: project.Registration.Assembly, Owner: project.Registration.Owner!.Assembly));
        Assert.Contains(pairs, pair => !debt.Any(item =>
            StringComparer.OrdinalIgnoreCase.Equals(item.Subject, pair.Test)
            || StringComparer.OrdinalIgnoreCase.Equals(item.Subject, pair.Owner)
            || StringComparer.OrdinalIgnoreCase.Equals(item.Related, pair.Test)
            || StringComparer.OrdinalIgnoreCase.Equals(item.Related, pair.Owner)));
    }
}
