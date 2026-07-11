using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class FullPythonCorpusCompatibilityTests
{
    private static readonly string GoldenRoot = Path.Combine(AppContext.BaseDirectory, "Golden");

    public static TheoryData<string> Cases
    {
        get
        {
            using var document = JsonDocument.Parse(
                File.ReadAllBytes(Path.Combine(GoldenRoot, "python-cases.json")));
            var data = new TheoryData<string>();
            foreach (var item in document.RootElement.EnumerateArray())
            {
                data.Add(item.GetProperty("name").GetString() ?? throw new JsonException("case name is null"));
            }

            return data;
        }
    }

    [Theory]
    [MemberData(nameof(Cases))]
    public void EveryLanguageNeutralCaseMatchesPythonDiagnosticBytes(string caseName)
    {
        using var cases = JsonDocument.Parse(File.ReadAllBytes(Path.Combine(GoldenRoot, "python-cases.json")));
        using var diagnostics = JsonDocument.Parse(
            File.ReadAllBytes(Path.Combine(GoldenRoot, "python-diagnostics.json")));
        var testCase = cases.RootElement.EnumerateArray().Single(
            item => item.GetProperty("name").GetString() == caseName);
        var fixture = new RuleFixture();
        NormalizeBackfillTargets(fixture);

        if (testCase.TryGetProperty("head_mutations", out var headMutations))
        {
            ApplyMutations(caseName, fixture, headMutations, baseline: true);
            ApplyMutations(caseName, fixture, headMutations, baseline: false);
        }

        ApplyMutations(caseName, fixture, testCase.GetProperty("mutations"), baseline: false);
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(BuildContext(fixture)));
        var actual = completed.Capability.Diagnostics
            .Select(static item => item.Render())
            .Order(StringComparer.Ordinal)
            .ToArray();
        var pythonExpected = diagnostics.RootElement.TryGetProperty(caseName, out var expectedDiagnostics)
            ? expectedDiagnostics.EnumerateArray()
                .Select(static item => $"{item[0].GetString()} {item[1].GetString()}: {item[2].GetString()}")
                .Order(StringComparer.Ordinal)
                .ToArray()
            : Array.Empty<string>();
        var expected = ApprovedCSharpExpectation(caseName, pythonExpected);

        var expectedText = string.Join('\n', expected) + (expected.Length == 0 ? string.Empty : "\n");
        var actualText = string.Join('\n', actual) + (actual.Length == 0 ? string.Empty : "\n");
        Assert.Equal(expectedText, actualText);
        Assert.Equal(Encoding.UTF8.GetBytes(expectedText), Encoding.UTF8.GetBytes(actualText));
    }

    private static string[] ApprovedCSharpExpectation(string caseName, string[] pythonExpected)
    {
        using var document = JsonDocument.Parse(File.ReadAllBytes(Path.Combine(GoldenRoot, "differences.json")));
        var registryDifference = document.RootElement.GetProperty("differences")
            .EnumerateArray()
            .Single(static item => item.GetProperty("item").GetString() == "registry-externalization");
        var caseDifference = registryDifference.GetProperty("case_diffs")
            .EnumerateArray()
            .SingleOrDefault(item => item.GetProperty("case").GetString() == caseName);
        if (caseDifference.ValueKind is JsonValueKind.Undefined)
        {
            return pythonExpected;
        }

        var declaredPython = caseDifference.GetProperty("python")
            .EnumerateArray()
            .Select(static item => item.GetString() ?? throw new JsonException("null Python difference"))
            .Order(StringComparer.Ordinal)
            .ToArray();
        Assert.Equal(pythonExpected, declaredPython);
        return caseDifference.GetProperty("csharp")
            .EnumerateArray()
            .Select(static item => item.GetString() ?? throw new JsonException("null C# difference"))
            .Order(StringComparer.Ordinal)
            .ToArray();
    }

    private static void ApplyMutations(
        string caseName,
        RuleFixture fixture,
        JsonElement mutations,
        bool baseline)
    {
        foreach (var mutation in mutations.EnumerateArray())
        {
            var operation = mutation.GetProperty("op").GetString();
            var files = baseline ? fixture.Baseline : fixture.Files;
            var reports = baseline ? fixture.BaselineReports : fixture.Reports;
            switch (operation)
            {
                case "write":
                    Write(
                        caseName,
                        files,
                        reports,
                        mutation.GetProperty("path").GetString() ?? string.Empty,
                        mutation.GetProperty("content").GetString() ?? string.Empty);
                    break;
                case "write_parts":
                    Write(
                        caseName,
                        files,
                        reports,
                        mutation.GetProperty("path").GetString() ?? string.Empty,
                        string.Concat(mutation.GetProperty("parts").EnumerateArray()
                            .Select(static item => item.GetString())));
                    break;
                case "lean":
                    {
                        var path = mutation.GetProperty("path").GetString() ?? string.Empty;
                        var body = mutation.GetProperty("body").GetString() ?? string.Empty;
                        Write(
                            caseName,
                            files,
                            reports,
                            path,
                            Header(
                                mutation.GetProperty("gid").GetString() ?? string.Empty,
                                mutation.GetProperty("generality").GetString() ?? string.Empty)
                            + body);
                        break;
                    }
                case "delete":
                    {
                        var path = mutation.GetProperty("path").GetString() ?? string.Empty;
                        files.Remove(path);
                        reports.Remove(path);
                        break;
                    }
                case "append_lines":
                    {
                        var path = mutation.GetProperty("path").GetString() ?? string.Empty;
                        files[path] += string.Concat(Enumerable.Repeat(
                            (mutation.GetProperty("line").GetString() ?? string.Empty) + "\n",
                            mutation.GetProperty("count").GetInt32()));
                        break;
                    }
                case "domain":
                    {
                        var path = "Meta/domains.yaml";
                        files[path] += $"  {mutation.GetProperty("name").GetString()}:\n"
                            + $"    stratum: {mutation.GetProperty("stratum").GetString()}\n"
                            + "    definition: Fixture.\n";
                        break;
                    }
                case "task":
                    {
                        var path = mutation.GetProperty("path").GetString() ?? string.Empty;
                        var gid = mutation.GetProperty("gid").GetString() ?? string.Empty;
                        var code = mutation.GetProperty("code").GetString() ?? string.Empty;
                        Write(
                            caseName,
                            files,
                            reports,
                            path,
                            Header(gid, "E")
                            + $"/-- TASK {code} | 难度:3 | 依赖:就绪 | 尝试:0\n"
                            + "    提示:Fixture task.\n"
                            + "    尸检:none -/\n"
                            + "def fixtureTask : Unit := ()\n");
                        if (code.StartsWith("D5-T", StringComparison.Ordinal)
                            && caseName is not ("frontier-task-missing-ticket-index" or "retired-task-code")
                            && !files["Meta/BACKFILL.yaml"].Contains($"case_id: {code}\n", StringComparison.Ordinal))
                        {
                            files["Meta/BACKFILL.yaml"] += $"  - case_id: {code}\n    gid: {gid}\n";
                        }
                        break;
                    }
                case "directory_capacity":
                    for (var index = 0; index < 12; index++)
                    {
                        files[$"Blueprint/D5/S0/Carrier/Extra{index:00}.md"] = "fixture\n";
                    }

                    break;
                case "empty_waiver":
                    Write(
                        caseName,
                        files,
                        reports,
                        RuleFixture.RingPath,
                        Header(
                            "D5/S0/Carrier/Ring",
                            "G",
                            "none(waiver:)",
                            "none(waiver:test)")
                        + "def goldenRing : Nat := 0\n");
                    break;
                case "e_collision":
                    EvidenceMirror(caseName, files, reports, includeJson: true, includeYaml: true);
                    break;
                case "e_exact":
                    EvidenceMirror(caseName, files, reports, includeJson: true, includeYaml: false);
                    break;
                case "e_missing":
                    EvidenceMirror(caseName, files, reports, includeJson: false, includeYaml: false);
                    break;
                case "backfill_replace":
                    ReplaceOnce(
                        files,
                        mutation.GetProperty("old").GetString() ?? string.Empty,
                        mutation.GetProperty("new").GetString() ?? string.Empty);
                    break;
                case "backfill_replace_first_disposition":
                    ReplaceFirstDisposition(
                        files,
                        mutation.GetProperty("disposition").GetString() ?? string.Empty);
                    break;
                case "backfill_drop_anchor":
                    MutateAnchor(files, mutation.GetProperty("anchor").GetString() ?? string.Empty, duplicate: false);
                    break;
                case "backfill_duplicate_anchor":
                    MutateAnchor(files, mutation.GetProperty("anchor").GetString() ?? string.Empty, duplicate: true);
                    break;
                default:
                    throw new InvalidOperationException($"unsupported Python corpus operation: {operation}");
            }
        }
    }

}
