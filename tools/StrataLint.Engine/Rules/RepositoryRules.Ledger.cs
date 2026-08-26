using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    internal const string TowerManifestPath = "tools/TOWER.yaml";

    private static ImmutableArray<RuleFinding> Ledger(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        var tasks = CollectTaskCodes(context.Current);
        foreach (var (path, file) in context.Current.Files)
        {
            var governed = IsGovernedStructured(path, context.Policy);
            var pathAffected = context.IsBaseFactAffected(path.Value);
            var anomalyAffected = pathAffected || context.Changes.Paths.Any(change =>
                IsManagedLeanPath(change.Value));
            if (governed && pathAffected)
            {
                if (file.HasBom)
                {
                    findings.Add(new RuleFinding(path.Value, "structured artifact must not start with a BOM"));
                    continue;
                }

                if (file.HasTrailingWhitespace || file.HasCarriageReturn)
                {
                    var lines = file.Text.Split('\n');
                    var lineNumber = Array.FindIndex(
                        lines,
                        static line => line.EndsWith(' ') || line.EndsWith('\t') || line.EndsWith('\r')) + 1;
                    findings.Add(new RuleFinding(
                        path.Value,
                        $"structured artifact has trailing whitespace on line {lineNumber}"));
                    continue;
                }

                if (!file.Text.EndsWith('\n') || file.Text.EndsWith("\n\n", StringComparison.Ordinal))
                {
                    findings.Add(new RuleFinding(path.Value, "structured artifact must end with exactly one LF"));
                    continue;
                }
            }

            if (path.Value == TowerManifestPath)
            {
                if (pathAffected
                    && TowerManifestParser.Parse(file.RawBytes.AsSpan())
                    is TowerManifestParseOutcome.Invalid invalid)
                {
                    findings.Add(new RuleFinding(path.Value, $"invalid TOWER schema: {invalid.Message}"));
                }

                continue;
            }

            if (path.Value.EndsWith(".json", StringComparison.Ordinal))
            {
                try
                {
                    using var document = JsonDocument.Parse(file.Text.TrimStart('\uFEFF'));
                    ScanJson(
                        path.Value,
                        document.RootElement,
                        "$",
                        AddressSlot.Entry,
                        tasks,
                        findings,
                        scanAnomalies: anomalyAffected,
                        scanStrings: governed && anomalyAffected,
                        enforceKeyOrder: governed && pathAffected);
                }
                catch (JsonException)
                {
                    if (governed && pathAffected)
                    {
                        findings.Add(new RuleFinding(path.Value, "structured anomaly scan cannot parse JSON"));
                    }
                }
            }
            else if (path.Value.EndsWith((".yaml"), StringComparison.Ordinal)
                || path.Value.EndsWith((".yml"), StringComparison.Ordinal))
            {
                ScanYaml(
                    path.Value,
                    file.Text,
                    tasks,
                    findings,
                    scanAnomalies: anomalyAffected,
                    enforceKeyOrder: governed && pathAffected,
                    reportParseErrors: pathAffected);
            }
            else if (path.Value.StartsWith("Chronicle/", StringComparison.Ordinal))
            {
                ScanLedgerBlocks(
                    path.Value,
                    file.Text,
                    tasks,
                    findings,
                    scanAnomalies: anomalyAffected,
                    reportParseErrors: pathAffected);
            }
        }

        ValidateCandidateRevocationReceipts(context, findings);

        return findings.ToImmutable();
    }

    private static void ValidateCandidateRevocationReceipts(
        RuleEvaluationContext context,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        FrozenLedgerConsistent? baseline = null;
        foreach (var path in context.Current.Files.Keys
                     .Where(path => context.IsBaseFactAffected(path.Value))
                     .Where(static path => path.Value.StartsWith("Evidence/D5/", StringComparison.Ordinal))
                     .OrderBy(static path => path.Value, StringComparer.Ordinal))
        {
            if (!context.Current.Files.TryGetValue(path, out var file)
                || !path.Value.EndsWith(".json", StringComparison.Ordinal))
            {
                continue;
            }

            try
            {
                using var document = JsonDocument.Parse(file.RawBytes.AsMemory());
                if (!document.RootElement.TryGetProperty("kind", out var kind)
                    || kind.ValueKind != JsonValueKind.String
                    || kind.GetString() != "revocation-receipt")
                {
                    continue;
                }

                baseline ??= FrozenLedgerBaseViewReader.Read(context.Baseline).ToWriterBaseline();
                TrustedRevocationReceiptStore.ValidateCandidateReceipt(baseline, file.RawBytes);
            }
            catch (Exception exception) when (
                exception is FormatException or InvalidOperationException or JsonException)
            {
                findings.Add(new RuleFinding(
                    path.Value,
                    "revocation receipt write gate rejected candidate: " + exception.Message));
            }
        }
    }
}
