using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    internal const string TowerManifestPath = "tools/TOWER.yaml";
    internal const string RegistryPolicyPath = "Meta/registry.yaml";
    internal const string DomainsPolicyPath = "Meta/domains.yaml";
    internal const string FileMapPolicyPath = "Meta/FILEMAP.toml";

    // Registry and domain bytes compile ValidatedPolicy. FILEMAP is a conservative wake path:
    // SL-019 does not read FileMapManifest, but replaying on its change is intentionally harmless.
    // This bounded schema-owned inventory is unlike the structurally defined judge-code closure.
    private static readonly ImmutableHashSet<string> LedgerPolicyDataPaths =
        ImmutableHashSet.Create(
            StringComparer.Ordinal,
            RegistryPolicyPath,
            DomainsPolicyPath,
            FileMapPolicyPath);

    private static ImmutableArray<RuleFinding> Ledger(CurrentRuleContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        HashSet<string>? tasks = null;
        foreach (var (path, file) in context.Current.Files)
        {
            var governed = IsGovernedStructured(path, context.Policy);
            if (governed)
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
                if (TowerManifestParser.Parse(file.RawBytes.AsSpan())
                    is TowerManifestParseOutcome.Invalid invalid)
                {
                    findings.Add(new RuleFinding(path.Value, $"invalid TOWER schema: {invalid.Message}"));
                }

                continue;
            }

            tasks ??= CollectTaskCodes(context.Current);

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
                        scanAnomalies: true,
                        scanStrings: governed,
                        enforceKeyOrder: governed);
                }
                catch (JsonException)
                {
                    if (governed)
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
                    scanAnomalies: true,
                    enforceKeyOrder: governed,
                    reportParseErrors: true);
            }
            else if (path.Value.StartsWith("Chronicle/", StringComparison.Ordinal))
            {
                ScanLedgerBlocks(
                    path.Value,
                    file.Text,
                    tasks,
                    findings,
                    scanAnomalies: true,
                    reportParseErrors: true);
            }
        }

        return findings.ToImmutable();
    }

    internal static bool IsLedgerPolicyDataPath(string path) =>
        LedgerPolicyDataPaths.Contains(path);
}
