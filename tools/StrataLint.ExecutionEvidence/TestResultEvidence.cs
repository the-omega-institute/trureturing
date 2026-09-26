using StrataLint.Engine;
using System.Xml.Linq;

namespace StrataLint.EngineeringScope;

internal sealed record TestResultEvidence(
    int Executed,
    IReadOnlySet<(string Assembly, string Id)> ExecutedTests)
{
    internal static TestResultEvidence Load(string resultsDirectory)
    {
        var files = Directory.GetFiles(resultsDirectory, "*.trx", SearchOption.TopDirectoryOnly);
        if (files.Length == 0) throw new InvalidDataException("dotnet test produced no TRX evidence");

        var runs = files.Select(file => (File: file, Document: XDocument.Load(file, LoadOptions.None))).ToArray();
        var results = runs.SelectMany(run => run.Document.Descendants()
            .Where(element => element.Name.LocalName == "UnitTestResult")).ToArray();
        foreach (var result in results) _ = Message(result);
        var unresolved = results.Where(result => (string?)result.Attribute("outcome") == "NotExecuted")
            .Where(result => Message(result)?.StartsWith(InfrastructureHangGuard.SkipReasonPrefix, StringComparison.Ordinal) == true)
            .Select(Describe).ToArray();
        try
        {
            var evidence = LoadSuccessfulRuns(runs);
            if (unresolved.Length != 0) throw new InfrastructureUnresolvedException(unresolved);
            return evidence;
        }
        catch (Exception failure) when (unresolved.Length != 0
            && failure is InvalidDataException or InvalidOperationException or ArgumentException)
        {
            // Guard expiration and a business failure can coexist, even in different
            // TRX files. Keep the validation failure and named outcomes alongside the guard.
            var failed = results.Where(result => (string?)result.Attribute("outcome") is not ("Passed" or "NotExecuted"))
                .Select(Describe).ToArray();
            var detail = failure.Message + (failed.Length == 0 ? ""
                : $"; test outcomes={string.Join(" | ", failed)}");
            throw new InfrastructureUnresolvedException(unresolved, detail);
        }

        static string? Message(XElement result) => result.Descendants()
            .SingleOrDefault(element => element.Name.LocalName == "Message")?.Value;
        static string Describe(XElement result) =>
            $"{(string?)result.Attribute("testName")} [{(string?)result.Attribute("outcome")}]: {Message(result)}";
    }

    private static TestResultEvidence LoadSuccessfulRuns((string File, XDocument Document)[] runs)
    {
        var executed = 0;
        var actual = new HashSet<(string Assembly, string Id)>();
        foreach (var (file, document) in runs)
        {
            if (document.Root?.Name.LocalName != "TestRun") throw new InvalidDataException("invalid TRX root");
            var summary = document.Descendants().Single(element => element.Name.LocalName == "ResultSummary");
            if ((string?)summary.Attribute("outcome") is not ("Completed" or "Passed"))
                throw new InvalidDataException($"TRX run summary did not succeed: {file}");
            var counters = document.Descendants().Single(element => element.Name.LocalName == "Counters");
            if (!int.TryParse((string?)counters.Attribute("executed"), System.Globalization.CultureInfo.InvariantCulture, out var fileExecuted))
                throw new InvalidDataException($"TRX has no executed count: {file}");
            executed += fileExecuted;

            var results = document.Descendants()
                .Where(element => element.Name.LocalName == "UnitTestResult")
                .ToDictionary(
                    element => (string?)element.Attribute("testId")
                        ?? throw new InvalidDataException("TRX result has no test identity"),
                    StringComparer.Ordinal);
            var passed = results.Values.Count(static result => (string?)result.Attribute("outcome") == "Passed");
            if (results.Values.Any(static result => (string?)result.Attribute("outcome") is not ("Passed" or "NotExecuted")))
                throw new InvalidDataException($"TRX contains a failed or unknown test outcome: {file}");
            if (fileExecuted < 0 || fileExecuted != passed)
                throw new InvalidDataException($"TRX executed count disagrees with successful results: {file}");
            foreach (var name in new[] { "passed", "failed", "error", "timeout", "aborted" })
            {
                if (counters.Attribute(name) is not { } counter) continue;
                if (!int.TryParse(counter.Value, System.Globalization.CultureInfo.InvariantCulture, out var value)
                    || value != (name == "passed" ? passed : 0))
                    throw new InvalidDataException($"TRX {name} counter disagrees with successful results: {file}");
            }
            var definitions = document.Descendants().Where(element => element.Name.LocalName == "UnitTest")
                .Select(element => (string?)element.Attribute("id")).ToHashSet(StringComparer.Ordinal);
            if (results.Keys.Any(id => !definitions.Contains(id))) throw new InvalidDataException("TRX result has no matching definition");
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

        if (executed == 0) throw new InvalidDataException("dotnet test executed zero tests");
        return new TestResultEvidence(executed, actual);
    }

    internal int CountAssembly(string expectedAssembly) =>
        ExecutedTests.Count(test =>
            StringComparer.OrdinalIgnoreCase.Equals(test.Assembly, expectedAssembly));
}

internal sealed class InfrastructureUnresolvedException(IReadOnlyList<string> tests, string? validationFailure = null)
    : Exception(
        $"INFRASTRUCTURE_UNRESOLVED count={tests.Count} tests={string.Join(" | ", tests)}"
        + (validationFailure is null ? "" : $"; TRX_VALIDATION_FAILED {validationFailure}"));
