using System.Xml.Linq;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal sealed record TestResultEvidence(
    int Executed,
    IReadOnlySet<(string Assembly, string Id)> ExecutedTests)
{
    internal static TestResultEvidence Load(string resultsDirectory)
    {
        var files = Directory.GetFiles(resultsDirectory, "*.trx", SearchOption.TopDirectoryOnly);
        if (files.Length == 0) throw new InvalidDataException("dotnet test produced no TRX evidence");

        var executed = 0;
        var actual = new HashSet<(string Assembly, string Id)>(EngineeringTestIdentityComparer.Instance);
        var unresolved = new List<string>();
        foreach (var file in files)
        {
            var document = XDocument.Load(file, LoadOptions.None);
            var counters = document.Descendants().Single(element => element.Name.LocalName == "Counters");
            if (!int.TryParse((string?)counters.Attribute("executed"), out var fileExecuted))
                throw new InvalidDataException($"TRX has no executed count: {file}");
            executed += fileExecuted;

            var results = document.Descendants()
                .Where(element => element.Name.LocalName == "UnitTestResult")
                .ToDictionary(
                    element => (string?)element.Attribute("testId")
                        ?? throw new InvalidDataException("TRX result has no test identity"),
                    StringComparer.Ordinal);
            foreach (var result in results.Values)
            {
                var message = result.Descendants()
                    .SingleOrDefault(element => element.Name.LocalName == "Message")?.Value;
                if ((string?)result.Attribute("outcome") == "NotExecuted"
                    && message?.StartsWith(InfrastructureHangGuard.SkipReasonPrefix, StringComparison.Ordinal) == true)
                {
                    unresolved.Add($"{(string?)result.Attribute("testName")}: {message}");
                }
            }

            foreach (var test in document.Descendants().Where(element => element.Name.LocalName == "UnitTest"))
            {
                var id = (string?)test.Attribute("id");
                if (id is null
                    || !results.TryGetValue(id, out var result)
                    || (string?)result.Attribute("outcome") == "NotExecuted")
                {
                    continue;
                }

                var method = test.Elements().Single(element => element.Name.LocalName == "TestMethod");
                var className = (string?)method.Attribute("className")
                    ?? throw new InvalidDataException("TRX test has no class identity");
                var methodName = (string?)method.Attribute("name")
                    ?? throw new InvalidDataException("TRX test has no method identity");
                var storage = (string?)test.Attribute("storage")
                    ?? throw new InvalidDataException("TRX test has no assembly identity");
                actual.Add((Path.GetFileNameWithoutExtension(storage), $"{className.Split('.').Last()}.{methodName}"));
            }
        }

        if (unresolved.Count != 0)
        {
            throw new InfrastructureUnresolvedException(unresolved);
        }

        if (executed == 0) throw new InvalidDataException("dotnet test executed zero tests");
        return new TestResultEvidence(executed, actual);
    }

    internal int CountAssembly(string expectedAssembly) =>
        ExecutedTests.Count(test =>
            StringComparer.OrdinalIgnoreCase.Equals(test.Assembly, expectedAssembly));

    internal ExpectedTestEvidence CompareExpectedTests(
        IEnumerable<(string Assembly, string Id)> expectedTests,
        IEnumerable<(string Assembly, string Id)> candidateSourceTests)
    {
        var actual = ExecutedTests.ToHashSet(EngineeringTestIdentityComparer.Instance);
        var candidate = candidateSourceTests.ToHashSet(EngineeringTestIdentityComparer.Instance);
        var missing = expectedTests
            .Distinct(EngineeringTestIdentityComparer.Instance)
            .Where(test => !actual.Contains(test))
            .OrderBy(static test => test.Assembly, StringComparer.OrdinalIgnoreCase)
            .ThenBy(static test => test.Id, StringComparer.Ordinal)
            .ToArray();
        return new ExpectedTestEvidence(
            missing.Where(candidate.Contains).ToArray(),
            missing.Where(test => !candidate.Contains(test)).ToArray());
    }
}

internal sealed record ExpectedTestEvidence(
    IReadOnlyList<(string Assembly, string Id)> Blocking,
    IReadOnlyList<(string Assembly, string Id)> Exemptions);

internal sealed class InfrastructureUnresolvedException(IReadOnlyList<string> tests)
    : Exception(
        $"INFRASTRUCTURE_UNRESOLVED count={tests.Count} tests={string.Join(" | ", tests)}");

internal sealed class EngineeringTestIdentityComparer : IEqualityComparer<(string Assembly, string Id)>
{
    internal static readonly EngineeringTestIdentityComparer Instance = new();

    public bool Equals((string Assembly, string Id) x, (string Assembly, string Id) y) =>
        StringComparer.OrdinalIgnoreCase.Equals(x.Assembly, y.Assembly)
        && StringComparer.Ordinal.Equals(x.Id, y.Id);

    public int GetHashCode((string Assembly, string Id) value) =>
        HashCode.Combine(
            StringComparer.OrdinalIgnoreCase.GetHashCode(value.Assembly),
            StringComparer.Ordinal.GetHashCode(value.Id));
}
