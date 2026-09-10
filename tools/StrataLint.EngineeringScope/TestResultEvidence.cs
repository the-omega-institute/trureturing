using System.Text.Json;
using System.Text.RegularExpressions;
using System.Xml;
using System.Xml.Linq;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal sealed record TestResultEvidence(
    int Executed,
    IReadOnlySet<(string Assembly, string Id)> ExecutedTests)
{
    // Disposable startup diagnostic: delivery is independent of evidence validation,
    // including failed runs and infrastructure skips, before the owner deletes TRX.
    internal static void ForwardDefaultCliStartupProbe(string resultsDirectory, Action<string> emit)
    {
        try
        {
            foreach (var file in Directory.EnumerateFiles(resultsDirectory, "*.trx"))
            {
                try
                {
                    var document = XDocument.Load(file, LoadOptions.None);
                    var outputs = document.Descendants()
                        .Where(element => element.Name.LocalName is "UnitTestResult" or "ResultSummary")
                        .Elements().Where(element => element.Name.LocalName == "Output")
                        .Elements().Where(element => element.Name.LocalName is "StdOut" or "StdErr");
                    foreach (var output in outputs)
                    {
                        using var lines = new StringReader(output.Value);
                        while (lines.ReadLine() is { } captured)
                        {
                            // xUnit puts skip output in the run summary with this adapter prefix.
                            var line = Regex.Replace(captured, @"^\[xUnit\.net [0-9]{2}:[0-9]{2}:[0-9]{2}\.[0-9]{2}\] +", "");
                            if (!line.StartsWith(DefaultCliStartupProbe.Prefix, StringComparison.Ordinal)) continue;
                            try
                            {
                                using var record = JsonDocument.Parse(line[DefaultCliStartupProbe.Prefix.Length..]);
                                if (record.RootElement.ValueKind == JsonValueKind.Object)
                                    DefaultCliStartupProbe.Emit(emit, line);
                            }
                            catch (JsonException) { }
                        }
                    }
                }
                catch (Exception error) when (DeliveryUnavailable(error)) { }
            }
        }
        catch (Exception error) when (DeliveryUnavailable(error)) { }
    }

    private static bool DeliveryUnavailable(Exception error) => error is IOException
        or UnauthorizedAccessException or System.Security.SecurityException or XmlException;

    internal static TestResultEvidence Load(string resultsDirectory)
    {
        var files = Directory.GetFiles(resultsDirectory, "*.trx", SearchOption.TopDirectoryOnly);
        if (files.Length == 0) throw new InvalidDataException("dotnet test produced no TRX evidence");

        var executed = 0;
        var actual = new HashSet<(string Assembly, string Id)>();
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
}

internal sealed class InfrastructureUnresolvedException(IReadOnlyList<string> tests)
    : Exception(
        $"INFRASTRUCTURE_UNRESOLVED count={tests.Count} tests={string.Join(" | ", tests)}");
