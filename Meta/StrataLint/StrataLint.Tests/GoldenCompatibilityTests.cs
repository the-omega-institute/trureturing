using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class GoldenCompatibilityTests
{
    private static readonly string GoldenRoot = Path.Combine(AppContext.BaseDirectory, "Golden");

    [Fact]
    public void ExtractedPythonOracleBytesArePinned()
    {
        Assert.Equal(
            "afe3b55ddebb59434de8361009a9bc7455ac1cf39af8756caf951f70a77d8ec1",
            Hash("python-cases.json"));
        Assert.Equal(
            "26b91fc60e526ac35e1d3cd92f4cc2b94fc373ead034bfdf9668c216352ca616",
            Hash("python-diagnostics.json"));
    }

    public static TheoryData<string> Sl019RedCases => new()
    {
        "floating-anomaly",
        "typed-record-anomaly-without-case",
        "typed-numeric-anomaly-without-case",
        "unknown-anomaly-bearing-schema",
        "yaml-block-scalar-cannot-hide-typed-anomaly",
        "unknown-anomaly-discriminator-with-case",
        "encoded-unresolved-anomaly-without-case",
        "prefixed-serialized-anomaly-without-case",
        "bom-prefixed-serialized-anomaly-without-case",
        "mid-string-serialized-anomaly-without-case",
        "malformed-anomaly-bearing-encoding",
        "unicode-escaped-malformed-anomaly-encoding",
        "noncanonical-json-object-key-order",
        "noncanonical-yaml-object-key-order",
        "structured-artifact-file-bom",
        "structured-artifact-trailing-whitespace",
        "structured-prose-ledger-anomaly-without-case",
    };

    public static TheoryData<string> Sl019GreenCases => new()
    {
        "valid-ledgered-anomaly",
        "valid-typed-ledgered-anomaly",
        "valid-typed-numeric-anomaly-with-case",
        "opaque-serialized-looking-string",
        "valid-serialized-anomaly-with-case",
        "canonical-json-object-key-order",
        "canonical-yaml-object-key-order",
        "valid-structured-prose-ledger",
    };

    public static TheoryData<string> Sl016RedCases => new()
    {
        "empty-protected-backfill-inventory",
        "deleted-protected-backfill-entry",
        "duplicate-protected-backfill-entry",
        "dangling-backfill-entry",
        "invalid-protected-backfill-schema",
        "changed-protected-source-path",
        "protected-source-digest-mismatch",
        "protected-line-anchor-mismatch",
        "missing-protected-ticket-index-case",
    };

    [Theory]
    [MemberData(nameof(Sl016RedCases))]
    public void Sl016MatchesPythonDiagnosticBytes(string caseName)
    {
        using var cases = JsonDocument.Parse(File.ReadAllBytes(Path.Combine(GoldenRoot, "python-cases.json")));
        using var diagnostics = JsonDocument.Parse(File.ReadAllBytes(Path.Combine(GoldenRoot, "python-diagnostics.json")));
        var testCase = cases.RootElement.EnumerateArray().Single(
            item => item.GetProperty("name").GetString() == caseName);
        var fixture = new RuleFixture();
        NormalizeBackfillTargetsToPythonFixture(fixture);
        ApplyLanguageNeutralMutations(fixture, testCase.GetProperty("mutations"));

        var actual = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(16), fixture.Build())
            .Diagnostics
            .OrderBy(static item => item.Path, StringComparer.Ordinal)
            .ThenBy(static item => item.Message, StringComparer.Ordinal)
            .Select(static item => item.Render())
            .ToArray();
        var expected = diagnostics.RootElement.GetProperty(caseName)
            .EnumerateArray()
            .Select(static item => $"{item[0].GetString()} {item[1].GetString()}: {item[2].GetString()}")
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.Equal(
            Encoding.UTF8.GetBytes(string.Join('\n', expected) + "\n"),
            Encoding.UTF8.GetBytes(string.Join('\n', actual) + "\n"));
    }

    [Fact]
    public void Sl016MatchesPythonAcceptanceCase()
    {
        var fixture = new RuleFixture();
        NormalizeBackfillTargetsToPythonFixture(fixture);
        var actual = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(16),
            fixture.Build());

        Assert.Empty(actual.Diagnostics);
    }

    [Theory]
    [MemberData(nameof(Sl019RedCases))]
    public void Sl019MatchesPythonDiagnosticBytes(string caseName)
    {
        using var cases = JsonDocument.Parse(File.ReadAllBytes(Path.Combine(GoldenRoot, "python-cases.json")));
        using var diagnostics = JsonDocument.Parse(File.ReadAllBytes(Path.Combine(GoldenRoot, "python-diagnostics.json")));
        var testCase = cases.RootElement.EnumerateArray().Single(
            item => item.GetProperty("name").GetString() == caseName);
        var fixture = new RuleFixture();
        ApplyLanguageNeutralMutations(fixture, testCase.GetProperty("mutations"));

        var actual = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(19), fixture.Build())
            .Diagnostics
            .OrderBy(static item => item.Path, StringComparer.Ordinal)
            .ThenBy(static item => item.Message, StringComparer.Ordinal)
            .Select(static item => item.Render())
            .ToArray();
        var expected = diagnostics.RootElement.GetProperty(caseName)
            .EnumerateArray()
            .Select(static item => $"{item[0].GetString()} {item[1].GetString()}: {item[2].GetString()}")
            .Order(StringComparer.Ordinal)
            .ToArray();

        var expectedText = string.Join('\n', expected) + "\n";
        var actualText = string.Join('\n', actual) + "\n";
        Assert.Equal(expectedText, actualText);
        Assert.Equal(Encoding.UTF8.GetBytes(expectedText), Encoding.UTF8.GetBytes(actualText));
    }

    [Theory]
    [MemberData(nameof(Sl019GreenCases))]
    public void Sl019MatchesPythonAcceptanceCases(string caseName)
    {
        using var cases = JsonDocument.Parse(File.ReadAllBytes(Path.Combine(GoldenRoot, "python-cases.json")));
        var testCase = cases.RootElement.EnumerateArray().Single(
            item => item.GetProperty("name").GetString() == caseName);
        var fixture = new RuleFixture();
        ApplyLanguageNeutralMutations(fixture, testCase.GetProperty("mutations"));

        var actual = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(19), fixture.Build());

        Assert.Empty(actual.Diagnostics);
    }

    public static TheoryData<string, int, string> OtherRuleCases => new()
    {
        { "wrong-layer-import", 1, "upward-import" },
        { "stray-sorry", 2, "sorry" },
        { "capacity-over-400-lines", 3, "file-capacity" },
        { "missing-blueprint-mirror", 4, "mirror" },
        { "chronicle-rewrite", 5, "chronicle" },
        { "manual-status-badge", 6, "badge" },
        { "hearts-signature-frozen", 8, "heart" },
        { "general-imports-instance-fact", 10, "generality" },
        { "unknown-domain", 11, "domain" },
        { "missing-six-line-header", 12, "header" },
        { "malformed-task-block", 13, "task" },
        { "illegal-formula-character", 15, "formula" },
        { "unresolvable-query-anchor", 17, "query" },
        { "legacy-value-masquerades-as-verified", 18, "values" },
        { "unregistered-axiom", 20, "axiom" },
        { "future-theory-is-uninstantiated", 21, "future" },
    };

    [Theory]
    [MemberData(nameof(OtherRuleCases))]
    public void OtherRulesMatchPythonDiagnosticBytes(string caseName, int ruleNumber, string mutation)
    {
        using var diagnostics = JsonDocument.Parse(File.ReadAllBytes(Path.Combine(GoldenRoot, "python-diagnostics.json")));
        var fixture = new RuleFixture();
        fixture.Apply(mutation);
        var context = ruleNumber == 20 ? fixture.BuildForRuleCompatibility() : fixture.Build();
        var actual = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(ruleNumber), context)
            .Diagnostics
            .OrderBy(static item => item.Path, StringComparer.Ordinal)
            .ThenBy(static item => item.Message, StringComparer.Ordinal)
            .Select(static item => item.Render())
            .ToArray();
        var expected = diagnostics.RootElement.GetProperty(caseName)
            .EnumerateArray()
            .Select(static item => $"{item[0].GetString()} {item[1].GetString()}: {item[2].GetString()}")
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.Equal(
            Encoding.UTF8.GetBytes(string.Join('\n', expected) + "\n"),
            Encoding.UTF8.GetBytes(string.Join('\n', actual) + "\n"));
    }

    [Fact]
    public void EveryDeclaredDifferenceIsApprovedAndCaseBacked()
    {
        using var document = JsonDocument.Parse(File.ReadAllBytes(Path.Combine(GoldenRoot, "differences.json")));
        var differences = document.RootElement.GetProperty("differences").EnumerateArray().ToArray();
        Assert.Equal(
            new[] { "SL-022-baseline-meta-gate", "canonical-uniqueness-name", "registry-externalization" },
            differences.Select(static item => item.GetProperty("item").GetString()).Order(StringComparer.Ordinal));
        Assert.All(differences, static item =>
        {
            Assert.True(CaseId.TryCreate(item.GetProperty("case_id").GetString(), out _));
            Assert.False(string.IsNullOrWhiteSpace(item.GetProperty("python").GetString()));
            Assert.False(string.IsNullOrWhiteSpace(item.GetProperty("csharp").GetString()));
        });
        var registry = differences.Single(
            static item => item.GetProperty("item").GetString() == "registry-externalization");
        var cases = registry.GetProperty("case_diffs").EnumerateArray().ToArray();
        Assert.Empty(cases);
    }

    private static void ApplyLanguageNeutralMutations(RuleFixture fixture, JsonElement mutations)
    {
        foreach (var mutation in mutations.EnumerateArray())
        {
            var operation = mutation.GetProperty("op").GetString();
            if (operation == "write")
            {
                fixture.Files[mutation.GetProperty("path").GetString() ?? string.Empty] =
                    mutation.GetProperty("content").GetString() ?? string.Empty;
            }
            else if (operation == "write_parts")
            {
                fixture.Files[mutation.GetProperty("path").GetString() ?? string.Empty] = string.Concat(
                    mutation.GetProperty("parts").EnumerateArray().Select(static item => item.GetString()));
            }
            else if (operation == "task")
            {
                fixture.AddTask(
                    mutation.GetProperty("path").GetString() ?? string.Empty,
                    mutation.GetProperty("gid").GetString() ?? string.Empty,
                    mutation.GetProperty("code").GetString() ?? string.Empty);
            }
            else if (operation == "backfill_replace")
            {
                ReplaceBackfill(
                    fixture,
                    mutation.GetProperty("old").GetString() ?? string.Empty,
                    mutation.GetProperty("new").GetString() ?? string.Empty);
            }
            else if (operation == "backfill_replace_first_disposition")
            {
                var lines = fixture.Files["Meta/BACKFILL.yaml"].Split('\n').ToList();
                var index = lines.FindIndex(static line => line.TrimStart().StartsWith("disposition: ", StringComparison.Ordinal));
                if (index < 0)
                {
                    throw new InvalidOperationException("BACKFILL fixture has no disposition");
                }

                var indentation = lines[index][..(lines[index].Length - lines[index].TrimStart().Length)];
                lines[index] = indentation + "disposition: "
                    + (mutation.GetProperty("disposition").GetString() ?? string.Empty);
                fixture.Files["Meta/BACKFILL.yaml"] = string.Join('\n', lines);
            }
            else if (operation is "backfill_drop_anchor" or "backfill_duplicate_anchor")
            {
                MutateBackfillAnchor(
                    fixture,
                    mutation.GetProperty("anchor").GetString() ?? string.Empty,
                    duplicate: operation == "backfill_duplicate_anchor");
            }
            else
            {
                throw new InvalidOperationException($"unsupported language-neutral mutation: {operation}");
            }
        }
    }

    private static void ReplaceBackfill(RuleFixture fixture, string oldValue, string newValue)
    {
        var text = fixture.Files["Meta/BACKFILL.yaml"];
        if (!text.Contains(oldValue, StringComparison.Ordinal))
        {
            throw new InvalidOperationException($"unknown protected fixture text '{oldValue}'");
        }

        var index = text.IndexOf(oldValue, StringComparison.Ordinal);
        fixture.Files["Meta/BACKFILL.yaml"] = string.Concat(
            text.AsSpan(0, index),
            newValue,
            text.AsSpan(index + oldValue.Length));
    }

    private static void NormalizeBackfillTargetsToPythonFixture(RuleFixture fixture)
    {
        var lines = fixture.Files["Meta/BACKFILL.yaml"].Split('\n');
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

        fixture.Files["Meta/BACKFILL.yaml"] = string.Join('\n', lines);
    }

    private static void MutateBackfillAnchor(RuleFixture fixture, string anchor, bool duplicate)
    {
        var lines = fixture.Files["Meta/BACKFILL.yaml"].Split('\n').ToList();
        var marker = $"- anchor: {anchor}";
        var index = lines.FindIndex(line => string.Equals(line.Trim(), marker, StringComparison.Ordinal));
        if (index < 0 || index + 4 > lines.Count)
        {
            throw new InvalidOperationException($"unknown protected fixture anchor '{anchor}'");
        }

        var block = lines.GetRange(index, 4);
        if (duplicate)
        {
            lines.InsertRange(index + 4, block);
        }
        else
        {
            lines.RemoveRange(index, 4);
        }

        fixture.Files["Meta/BACKFILL.yaml"] = string.Join('\n', lines);
    }

    private static string Hash(string file) => Convert.ToHexStringLower(
        SHA256.HashData(File.ReadAllBytes(Path.Combine(GoldenRoot, file))));
}
