using System.Xml.Linq;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal sealed record TestResultEvidence(
    int Executed,
    IReadOnlySet<(string Assembly, string Id)> ExecutedTests,
    IReadOnlyDictionary<(string Assembly, string Id), string> NotExecutedTests)
{
    internal TestResultEvidence(
        int executed,
        IReadOnlySet<(string Assembly, string Id)> executedTests)
        : this(
            executed,
            executedTests,
            new Dictionary<(string Assembly, string Id), string>(
                EngineeringTestIdentityComparer.Instance))
    {
    }

    internal static TestResultEvidence Load(string resultsDirectory)
    {
        var files = Directory.GetFiles(resultsDirectory, "*.trx", SearchOption.TopDirectoryOnly);
        if (files.Length == 0) throw new InvalidDataException("dotnet test produced no TRX evidence");

        var executed = 0;
        var actual = new HashSet<(string Assembly, string Id)>(EngineeringTestIdentityComparer.Instance);
        var notExecuted = new Dictionary<(string Assembly, string Id), string>(
            EngineeringTestIdentityComparer.Instance);
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
                if (id is null || !results.TryGetValue(id, out var result))
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
                var identity = (
                    Path.GetFileNameWithoutExtension(storage),
                    $"{className.Split('.').Last()}.{methodName}");
                if ((string?)result.Attribute("outcome") == "NotExecuted")
                {
                    var message = result.Descendants()
                        .SingleOrDefault(element => element.Name.LocalName == "Message")?.Value;
                    if (message is not null)
                    {
                        notExecuted[identity] = message;
                    }
                    continue;
                }

                actual.Add(identity);
            }
        }

        if (unresolved.Count != 0)
        {
            throw new InfrastructureUnresolvedException(unresolved);
        }

        if (executed == 0) throw new InvalidDataException("dotnet test executed zero tests");
        return new TestResultEvidence(executed, actual, notExecuted);
    }

    internal int CountAssembly(string expectedAssembly) =>
        ExecutedTests.Count(test =>
            StringComparer.OrdinalIgnoreCase.Equals(test.Assembly, expectedAssembly));

    internal ExpectedTestEvidence CompareExpectedTests(
        IEnumerable<(string Assembly, string Id)> expectedTests,
        IEnumerable<(string Assembly, string Id)> candidateSourceTests) =>
        CompareExpectedTests(
            expectedTests.Select(static test => new ExpectedTestIdentity(test.Assembly, test.Id, [], [])),
            candidateSourceTests.Select(static test => new CandidateTestIdentity(test.Assembly, test.Id, [], [])));

    internal ExpectedTestEvidence CompareExpectedTests(
        IEnumerable<ExpectedTestIdentity> expectedTests,
        IEnumerable<CandidateTestIdentity> candidateSourceTests)
    {
        var actual = ExecutedTests.ToHashSet(EngineeringTestIdentityComparer.Instance);
        var skipped = NotExecutedTests.ToDictionary(
            static item => item.Key,
            static item => item.Value,
            EngineeringTestIdentityComparer.Instance);
        var candidate = candidateSourceTests.ToDictionary(
            static test => (test.Assembly, test.Id),
            EngineeringTestIdentityComparer.Instance);
        var missing = expectedTests
            .DistinctBy(
                static test => (test.Assembly, test.Id),
                EngineeringTestIdentityComparer.Instance)
            .Where(test => !actual.Contains((test.Assembly, test.Id)))
            .OrderBy(static test => test.Assembly, StringComparer.OrdinalIgnoreCase)
            .ThenBy(static test => test.Id, StringComparer.Ordinal)
            .ToArray();
        var blocking = new List<ExpectedTestIdentity>();
        var sourceAbsent = new List<ExpectedTestIdentity>();
        var runtimeConditionalSkips = new List<ExpectedTestIdentity>();
        foreach (var test in missing)
        {
            var identity = (test.Assembly, test.Id);
            candidate.TryGetValue(identity, out var candidateIdentity);
            var candidateRuntimeConditionalSkipReasons =
                candidateIdentity?.RuntimeConditionalSkipReasons ?? [];
            var candidateRuntimeConditionalSkipContracts =
                candidateIdentity?.RuntimeConditionalSkipContracts ?? [];
            if (candidateIdentity is null)
            {
                sourceAbsent.Add(test);
                continue;
            }

            if (test.RuntimeConditionalSkipReasons.Count != 0
                && test.RuntimeConditionalSkipContracts.Count != 0
                && test.RuntimeConditionalSkipReasons.SequenceEqual(
                    candidateRuntimeConditionalSkipReasons,
                    StringComparer.Ordinal)
                && test.RuntimeConditionalSkipContracts.SequenceEqual(
                    candidateRuntimeConditionalSkipContracts,
                    StringComparer.Ordinal)
                && skipped.TryGetValue(identity, out var message)
                && test.RuntimeConditionalSkipReasons.Contains(message, StringComparer.Ordinal))
            {
                runtimeConditionalSkips.Add(test);
                continue;
            }

            blocking.Add(test);
        }

        return new ExpectedTestEvidence(blocking, sourceAbsent, runtimeConditionalSkips);
    }
}

internal sealed record ExpectedTestEvidence(
    IReadOnlyList<ExpectedTestIdentity> Blocking,
    IReadOnlyList<ExpectedTestIdentity> SourceAbsentExemptions,
    IReadOnlyList<ExpectedTestIdentity> RuntimeConditionalSkipExemptions);

internal sealed record ExpectedTestIdentity(
    string Assembly,
    string Id,
    IReadOnlyList<string> RuntimeConditionalSkipReasons,
    IReadOnlyList<string> RuntimeConditionalSkipContracts);

internal sealed record CandidateTestIdentity(
    string Assembly,
    string Id,
    IReadOnlyList<string> RuntimeConditionalSkipReasons,
    IReadOnlyList<string> RuntimeConditionalSkipContracts);

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
