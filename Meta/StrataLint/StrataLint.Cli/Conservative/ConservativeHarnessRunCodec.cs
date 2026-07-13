using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Text.Json.Serialization;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class ConservativeHarnessRunCodec
{
    private const string Schema = "stratalint-conservative-harness-result-v1";

    private static readonly JsonSerializerOptions JsonOptions = new()
    {
        PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
        PropertyNameCaseInsensitive = false,
        UnmappedMemberHandling = JsonUnmappedMemberHandling.Disallow,
    };

    internal static ImmutableArray<byte> Write(ConservativeHarnessRun run)
    {
        ArgumentNullException.ThrowIfNull(run);
        var material = JsonSerializer.SerializeToElement(new
        {
            active_rules = run.ActiveRules.Order(StringComparer.Ordinal),
            cases = run.Cases.OrderBy(static item => item.CaseId, StringComparer.Ordinal).Select(item => new
            {
                blocking_rules = item.BlockingRules.Order(StringComparer.Ordinal),
                case_id = item.CaseId,
                case_root = item.CaseRoot,
                disposition = item.Disposition.ToString().ToLowerInvariant(),
                sl022_diagnostics = item.Sl022Diagnostics
                    .OrderBy(static diagnostic => diagnostic.Path, StringComparer.Ordinal)
                    .ThenBy(static diagnostic => diagnostic.Message, StringComparer.Ordinal)
                    .Select(static diagnostic => new
                    {
                        message = diagnostic.Message,
                        path = diagnostic.Path,
                        rule_id = diagnostic.RuleId,
                    }),
            }),
            harness_root = run.HarnessRoot,
            schema = Schema,
        });
        return StructuredCanonicalWriter.WriteJson(material);
    }

    internal static ConservativeHarnessRun Read(ReadOnlySpan<byte> bytes)
    {
        string text;
        try
        {
            text = new UTF8Encoding(false, true).GetString(bytes);
        }
        catch (DecoderFallbackException exception)
        {
            throw new FormatException("harness result must be strict UTF-8", exception);
        }

        ImmutableArray<byte> canonical;
        try
        {
            canonical = StructuredCanonicalWriter.WriteJson(text);
        }
        catch (JsonException exception)
        {
            throw new FormatException("harness result is not valid JSON", exception);
        }

        if (!canonical.AsSpan().SequenceEqual(bytes))
        {
            throw new FormatException("harness result bytes are not canonical JSON");
        }

        HarnessDocument document;
        try
        {
            document = JsonSerializer.Deserialize<HarnessDocument>(text, JsonOptions)
                ?? throw new FormatException("harness result document is null");
        }
        catch (JsonException exception)
        {
            throw new FormatException("harness result schema is invalid", exception);
        }

        if (!string.Equals(document.Schema, Schema, StringComparison.Ordinal)
            || string.IsNullOrWhiteSpace(document.HarnessRoot)
            || document.ActiveRules.IsDefaultOrEmpty
            || document.Cases.IsDefaultOrEmpty)
        {
            throw new FormatException("harness result required fields are missing");
        }

        RequireSortedUnique(document.ActiveRules, "active rules");
        RequireSortedUnique(document.Cases.Select(static item => item.CaseId), "case ids");
        var cases = document.Cases.Select(item =>
        {
            if (string.IsNullOrWhiteSpace(item.CaseRoot)
                || item.BlockingRules.IsDefault
                || item.Sl022Diagnostics.IsDefault
                || !Enum.TryParse<ConservativeDisposition>(
                    item.Disposition,
                    ignoreCase: true,
                    out var disposition))
            {
                throw new FormatException($"harness result case is malformed: {item.CaseId}");
            }

            RequireSortedUnique(item.BlockingRules, $"{item.CaseId} blocking rules");
            if (item.CaseId.StartsWith("golden:", StringComparison.Ordinal)
                && disposition is ConservativeDisposition.Admit
                && !item.BlockingRules.IsEmpty)
            {
                throw new FormatException(
                    $"harness result golden admit carries blocking rules: {item.CaseId}");
            }

            ValidateSl022Diagnostics(item.CaseId, item.BlockingRules, item.Sl022Diagnostics);
            return new ConservativeCaseResult(
                item.CaseId,
                item.CaseRoot,
                disposition,
                item.BlockingRules,
                item.Sl022Diagnostics.Select(static diagnostic => new ConservativeDiagnostic(
                    diagnostic.RuleId,
                    diagnostic.Path,
                    diagnostic.Message)).ToImmutableArray());
        }).ToImmutableArray();
        return new ConservativeHarnessRun(document.HarnessRoot, document.ActiveRules, cases);
    }

    private static void ValidateSl022Diagnostics(
        string caseId,
        ImmutableArray<string> blockingRules,
        ImmutableArray<HarnessDiagnostic> diagnostics)
    {
        string? previous = null;
        foreach (var diagnostic in diagnostics)
        {
            if (!string.Equals(diagnostic.RuleId, "SL-022", StringComparison.Ordinal)
                || string.IsNullOrWhiteSpace(diagnostic.Message)
                || !RepoPath.TryCreate(diagnostic.Path, out var path)
                || !BootstrapGate.IsProtected(path))
            {
                throw new FormatException(
                    $"harness result {caseId} has a malformed SL-022 diagnostic");
            }

            var key = diagnostic.Path + "\n" + diagnostic.Message;
            if (previous is not null && string.CompareOrdinal(previous, key) >= 0)
            {
                throw new FormatException(
                    $"harness result {caseId} SL-022 diagnostics must be sorted and unique");
            }

            previous = key;
        }

        if (!diagnostics.IsEmpty
            && !blockingRules.Contains("SL-022", StringComparer.Ordinal))
        {
            throw new FormatException(
                $"harness result {caseId} has SL-022 diagnostics without its blocking rule");
        }
    }

    private static void RequireSortedUnique(IEnumerable<string> values, string context)
    {
        string? previous = null;
        foreach (var value in values)
        {
            if (string.IsNullOrWhiteSpace(value)
                || previous is not null && string.CompareOrdinal(previous, value) >= 0)
            {
                throw new FormatException($"harness result {context} must be sorted and unique");
            }

            previous = value;
        }
    }

    private sealed record HarnessDocument(
        string Schema,
        string HarnessRoot,
        ImmutableArray<string> ActiveRules,
        ImmutableArray<HarnessCase> Cases);

    private sealed record HarnessCase(
        string CaseId,
        string CaseRoot,
        string Disposition,
        ImmutableArray<string> BlockingRules,
        ImmutableArray<HarnessDiagnostic> Sl022Diagnostics);

    private sealed record HarnessDiagnostic(string RuleId, string Path, string Message);
}
