using System.Reflection;
using StrataLint.Scribe.Documents;

namespace StrataLint.ArchitectureTests;

public sealed class ScribeTestMethodOwnershipTests
{
    private const string DocumentsAnchor =
        "StrataLint.Scribe.Tests.DocumentDiscoveryTests.ReflectionDiscoveryIsDeterministic";
    private const string ScribeAnchor =
        "StrataLint.Scribe.Tests.DocumentDiscoveryTests.EmptyProjectionAssertionPreservesTheCompleteRepairMessage";

    [Fact]
    public void EveryScribeTestMethodBelongsToItsSymbolLevelProductionOwner()
    {
        var documentsAssembly = typeof(DocumentAssembly).Assembly;
        var readings = new[]
        {
            ScribeTestMethodOwnershipPolicy.Inspect(
                Assembly.Load("StrataLint.Scribe.Documents.Tests"),
                documentsAssembly,
                mustTouchDocuments: true),
            ScribeTestMethodOwnershipPolicy.Inspect(
                Assembly.Load("StrataLint.Scribe.Tests"),
                documentsAssembly,
                mustTouchDocuments: false),
        };

        var documentsReading = readings.Single(static reading =>
            reading.TestAssembly == "StrataLint.Scribe.Documents.Tests");
        var scribeReading = readings.Single(static reading =>
            reading.TestAssembly == "StrataLint.Scribe.Tests");
        Assert.NotEmpty(documentsReading.DiscoveredTestMethods);
        Assert.Contains(DocumentsAnchor, documentsReading.DiscoveredTestMethods);
        Assert.NotEmpty(scribeReading.DiscoveredTestMethods);
        Assert.Contains(ScribeAnchor, scribeReading.DiscoveredTestMethods);

        var violations = readings.SelectMany(static reading => reading.Violations).ToArray();
        Assert.True(violations.Length == 0, Format(readings, violations));
    }

    [Fact]
    public void PolicySensitivityOracleClassifiesBothSidesAndProjectsBothViolations()
    {
        var fixtureAssembly = typeof(OwnershipPolicyFixture).Assembly;
        var documentsAssembly = typeof(DocumentAssembly).Assembly;
        var touching = GetFixtureMethod(nameof(OwnershipPolicyFixture.TouchesDocuments));
        var notTouching = GetFixtureMethod(nameof(OwnershipPolicyFixture.DoesNotTouchDocuments));

        Assert.True(ScribeTestMethodOwnershipPolicy.TouchesAssemblyThroughSameAssemblyCallClosure(
            touching,
            fixtureAssembly,
            documentsAssembly));
        Assert.False(ScribeTestMethodOwnershipPolicy.TouchesAssemblyThroughSameAssemblyCallClosure(
            notTouching,
            fixtureAssembly,
            documentsAssembly));

        var knownClassifications = new Dictionary<MethodInfo, bool>
        {
            [touching] = true,
            [notTouching] = false,
        };

        var mustTouchViolations = ScribeTestMethodOwnershipPolicy.ProjectViolations(
            fixtureAssembly,
            knownClassifications,
            mustTouchDocuments: true);
        var mustNotTouchViolations = ScribeTestMethodOwnershipPolicy.ProjectViolations(
            fixtureAssembly,
            knownClassifications,
            mustTouchDocuments: false);

        Assert.Equal(nameof(OwnershipPolicyFixture.DoesNotTouchDocuments), Assert.Single(mustTouchViolations).TestMethod);
        Assert.Equal(nameof(OwnershipPolicyFixture.TouchesDocuments), Assert.Single(mustNotTouchViolations).TestMethod);
    }

    private static MethodInfo GetFixtureMethod(string name) => typeof(OwnershipPolicyFixture).GetMethod(
        name,
        BindingFlags.Public | BindingFlags.Static)
        ?? throw new InvalidOperationException($"Missing ownership policy fixture method {name}.");

    private static string Format(
        IEnumerable<ScribeTestMethodOwnershipReading> readings,
        IReadOnlyCollection<ScribeTestMethodOwnershipViolation> violations)
    {
        var lines = readings.Select(reading =>
                $"{reading.TestAssembly}: declared={reading.DeclaredTestMethods}, "
                + $"touches Documents={reading.TouchesDocuments}, "
                + $"does not touch Documents={reading.DoesNotTouchDocuments}")
            .ToList();

        lines.Add($"violations={violations.Count}; classes={violations.Select(static item => item.TestClass).Distinct(StringComparer.Ordinal).Count()}");
        lines.AddRange(violations.Select(violation =>
            $"{violation.TestClass}.{violation.TestMethod}: "
            + (violation.TouchesDocuments
                ? "touches StrataLint.Scribe.Documents but must not"
                : "does not touch StrataLint.Scribe.Documents but must")));
        return string.Join(Environment.NewLine, lines);
    }

    private static class OwnershipPolicyFixture
    {
        public static Type TouchesDocuments() => typeof(DocumentAssembly);

        public static int DoesNotTouchDocuments() => 0;
    }
}
