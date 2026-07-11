using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class FullPythonCorpusCompatibilityTests
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

    private static void Write(
        string caseName,
        IDictionary<string, string> files,
        IDictionary<string, LeanFileReport> reports,
        string path,
        string content)
    {
        files[path] = content;
        if (LeanClosureValidator.IsManagedLean(path))
        {
            reports[path] = SemanticReport(caseName, path, content);
        }
    }

    private static LeanFileReport SemanticReport(string caseName, string path, string content)
    {
        if (caseName == "managed-early-exit-hides-axiom")
        {
            return new LeanFileReport(
                ImmutableArray<string>.Empty,
                ImmutableArray<LeanDeclaration>.Empty,
                "compiler exited successfully without complete module artifacts");
        }

        if (caseName == "hearts-baseline-inspection-fails" && content.Contains(": :=", StringComparison.Ordinal))
        {
            return new LeanFileReport(
                ImmutableArray<string>.Empty,
                ImmutableArray<LeanDeclaration>.Empty,
                "compiler rejected malformed Hearts fixture");
        }

        var semantic = Regex.Replace(content, "/-.*?-/", string.Empty, RegexOptions.Singleline);
        var imports = Regex.Matches(semantic, "^\\s*import\\s+(?<module>\\S+)", RegexOptions.Multiline)
            .Select(static match => match.Groups["module"].Value.Replace("«D5»", "D5", StringComparison.Ordinal))
            .ToImmutableArray();
        var declarations = ImmutableArray.CreateBuilder<LeanDeclaration>();
        foreach (Match match in Regex.Matches(
            semantic,
            "(?:(?<modifier>protected|private)\\s+)?axiom\\s+(?<name>[A-Za-z_][A-Za-z0-9_]*)\\s*:\\s*(?<type>[^\\n]+)",
            RegexOptions.CultureInvariant))
        {
            var name = match.Groups["name"].Value;
            if (match.Groups["modifier"].Value == "private")
            {
                name = $"_private.{path[..^5].Replace('/', '.')}.0.{name}";
            }
            else
            {
                var namespaceMatch = Regex.Match(semantic, "^namespace\\s+(?<name>\\S+)", RegexOptions.Multiline);
                if (namespaceMatch.Success)
                {
                    name = namespaceMatch.Groups["name"].Value + "." + name;
                }
            }

            declarations.Add(new LeanDeclaration(
                name,
                "axiom",
                match.Groups["type"].Value.Trim(),
                ImmutableArray.Create(name)));
        }

        foreach (Match match in Regex.Matches(
            semantic,
            "theorem\\s+(?<name>[A-Za-z_][A-Za-z0-9_]*)\\s*:\\s*(?<type>.*?)\\s*:=",
            RegexOptions.Singleline | RegexOptions.CultureInvariant))
        {
            var axioms = semantic.Contains("registeredDebt", StringComparison.Ordinal)
                ? ImmutableArray.Create("registeredDebt")
                : match.Value.Contains("sorry", StringComparison.Ordinal)
                    || semantic[(match.Index + match.Length)..].Contains("sorry", StringComparison.Ordinal)
                        ? ImmutableArray.Create("sorryAx")
                        : ImmutableArray<string>.Empty;
            declarations.Add(new LeanDeclaration(
                match.Groups["name"].Value,
                "theorem",
                match.Groups["type"].Value.Trim(),
                axioms));
        }

        return new LeanFileReport(imports, declarations.ToImmutable());
    }

    private static RuleEvaluationContext BuildContext(RuleFixture fixture)
    {
        var current = Decode(fixture.Files);
        var baseline = Decode(fixture.Baseline);
        var registry = Assert.IsType<RegistryLoadOutcome.Accepted>(
            RegistryLoader.Load(
                Encoding.UTF8.GetBytes(TestRegistry.Canonical),
                Encoding.UTF8.GetBytes(fixture.Files["Meta/domains.yaml"])));
        var meta = Assert.IsType<BootstrapOutcome.Clear>(
            BootstrapGate.Evaluate(RawChangeSet.Create(new[] { RuleFixture.BlueprintPath })));
        return RuleEvaluationContext.Create(
            current,
            baseline,
            registry.Policy,
            AcceptedLeanClosure.Create(LeanAxiomReport.Create(fixture.Reports)),
            AcceptedLeanClosure.Create(LeanAxiomReport.Create(fixture.BaselineReports)),
            RawChangeSet.Create(new[] { RuleFixture.BlueprintPath }),
            meta.Capability);
    }

    private static RepositorySnapshot Decode(IReadOnlyDictionary<string, string> files)
    {
        var raw = RawRepositorySnapshot.Create(files.Select(
            static pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
    }

    private static void EvidenceMirror(
        string caseName,
        IDictionary<string, string> files,
        IDictionary<string, LeanFileReport> reports,
        bool includeJson,
        bool includeYaml)
    {
        Write(
            caseName,
            files,
            reports,
            RuleFixture.RingPath,
            Header(
                "D5/S0/Carrier/Ring",
                "G",
                "D5/B/S0/Carrier/Ring",
                "D5/E/S0/Carrier/Ring.result--json")
            + "def goldenRing : Nat := 0\n");
        if (includeJson) files["Evidence/D5/S0/Carrier/Ring.result.json"] = "{}\n";
        if (includeYaml) files["Evidence/D5/S0/Carrier/Ring.result.yaml"] = "result: duplicate\n";
    }

    private static string Header(
        string gid,
        string generality,
        string mirrorB = "none(waiver:test-fixture)",
        string mirrorE = "none(waiver:test-fixture)") => $"""
        /- GID: {gid}
           generality: {generality}
           mirror-B: {mirrorB}
           mirror-E: {mirrorE}
           anchors: []
           digest: StrataLint fixture. -/
        """;

    private static void NormalizeBackfillTargets(RuleFixture fixture)
    {
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            var lines = files["Meta/BACKFILL.yaml"].Split('\n');
            for (var index = 0; index < lines.Length; index++)
            {
                var trimmed = lines[index].TrimStart();
                var indentation = lines[index][..(lines[index].Length - trimmed.Length)];
                if (trimmed.StartsWith("disposition: ", StringComparison.Ordinal))
                {
                    lines[index] = indentation + "disposition: D5/S0/Carrier/Ring";
                }
                else if (trimmed.StartsWith("gid: ", StringComparison.Ordinal))
                {
                    lines[index] = indentation + "gid: D5/S0/Carrier/Ring";
                }
            }

            files["Meta/BACKFILL.yaml"] = string.Join('\n', lines);
        }
    }

    private static void ReplaceOnce(IDictionary<string, string> files, string oldValue, string newValue)
    {
        var text = files["Meta/BACKFILL.yaml"];
        var index = text.IndexOf(oldValue, StringComparison.Ordinal);
        if (index < 0) throw new InvalidOperationException($"unknown protected fixture text '{oldValue}'");
        files["Meta/BACKFILL.yaml"] = string.Concat(
            text.AsSpan(0, index),
            newValue,
            text.AsSpan(index + oldValue.Length));
    }

    private static void ReplaceFirstDisposition(IDictionary<string, string> files, string disposition)
    {
        var lines = files["Meta/BACKFILL.yaml"].Split('\n').ToList();
        var index = lines.FindIndex(static line => line.TrimStart().StartsWith("disposition: ", StringComparison.Ordinal));
        if (index < 0) throw new InvalidOperationException("BACKFILL fixture has no disposition");
        var indentation = lines[index][..(lines[index].Length - lines[index].TrimStart().Length)];
        lines[index] = indentation + "disposition: " + disposition;
        files["Meta/BACKFILL.yaml"] = string.Join('\n', lines);
    }

    private static void MutateAnchor(IDictionary<string, string> files, string anchor, bool duplicate)
    {
        var lines = files["Meta/BACKFILL.yaml"].Split('\n').ToList();
        var index = lines.FindIndex(line => string.Equals(line.Trim(), $"- anchor: {anchor}", StringComparison.Ordinal));
        if (index < 0 || index + 4 > lines.Count) throw new InvalidOperationException("unknown protected anchor");
        var block = lines.GetRange(index, 4);
        if (duplicate) lines.InsertRange(index + 4, block);
        else lines.RemoveRange(index, 4);
        files["Meta/BACKFILL.yaml"] = string.Join('\n', lines);
    }
}
