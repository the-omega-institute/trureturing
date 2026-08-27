using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    internal const string TowerManifestPath = "tools/TOWER.yaml";
    internal const string RegistryPolicyPath = "Meta/registry.yaml";
    internal const string DomainsPolicyPath = "Meta/domains.yaml";
    internal const string FileMapPolicyPath = "Meta/FILEMAP.toml";

    // Registry and domain bytes compile ValidatedPolicy; FILEMAP declares repository path
    // classifications. This policy data has a bounded schema-owned inventory, unlike judge code.
    private static readonly ImmutableHashSet<string> LedgerPolicyDataPaths =
        ImmutableHashSet.Create(
            StringComparer.Ordinal,
            RegistryPolicyPath,
            DomainsPolicyPath,
            FileMapPolicyPath);

    private static ImmutableArray<RuleFinding> Ledger(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        var judgeSourceChanged = JudgeSourceChanged(context);
        var taskSetChanged = ChangedLeanTaskSet(context);
        var policyDataChanged = PolicyDataChanged(context);
        HashSet<string>? tasks = null;
        foreach (var (path, file) in context.Current.Files)
        {
            var governed = IsGovernedStructured(path, context.Policy);
            var pathAffected = context.IsBaseFactAffected(path.Value);
            var replay = ShouldReplayLedgerArtifact(
                context,
                path.Value,
                judgeSourceChanged,
                taskSetChanged,
                policyDataChanged);
            var anomalyAffected = pathAffected || replay;
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

            if (!anomalyAffected)
            {
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

        ValidateAcceptedEventFilesAfterJudgeSourceChange(
            context,
            findings,
            judgeSourceChanged);
        ValidateCandidateRevocationReceipts(context, findings);

        return findings.ToImmutable();
    }

    private static bool ChangedLeanTaskSet(RuleEvaluationContext context)
    {
        var changedPaths = context.Changes.Paths
            .Where(static path => IsManagedLeanPath(path.Value))
            .ToHashSet();
        if (changedPaths.Count == 0)
        {
            return false;
        }

        var currentTasks = CollectTaskCodes(context.Current.Files
            .Where(item => changedPaths.Contains(item.Key))
            .Select(static item => item.Value));
        var forkPointTasks = CollectTaskCodes(context.ForkPoint.Files
            .Where(item => changedPaths.Contains(item.Key))
            .Select(static item => item.Value));
        return !currentTasks.SetEquals(forkPointTasks);
    }

    private static bool PolicyDataChanged(RuleEvaluationContext context) =>
        context.Changes.Paths.Any(path => IsLedgerPolicyDataPath(path.Value));

    private static bool JudgeSourceChanged(RuleEvaluationContext context) =>
        context.RuleImplementationChanged
        || context.Changes.Paths.Any(path =>
            StrataLintEngineBuildInputs.ContainsJudgeSource(path.Value));

    /// <summary>
    /// SL-019 may skip a stored artifact only when all four replay-contract conditions hold:
    /// (a) the complete judge source closure is unchanged (<c>tools/</c>, excluding
    /// <c>tools/tests/</c>, plus inherited build inputs); (b) none of the closed policy-data inputs
    /// changed; (c) the managed-Lean TASK-code set is unchanged; and (d) this artifact is not an
    /// affected JSON, YAML, or Chronicle ledger path. Conditions (a)-(c) replay the full corpus;
    /// condition (d) preserves the per-artifact scan for affected paths.
    /// </summary>
    private static bool ShouldReplayLedgerArtifact(
        RuleEvaluationContext context,
        string path,
        bool judgeSourceChanged,
        bool taskSetChanged,
        bool policyDataChanged) =>
        judgeSourceChanged
        || policyDataChanged
        || taskSetChanged
        || LedgerArtifactChanged(context, path);

    private static bool LedgerArtifactChanged(RuleEvaluationContext context, string path) =>
        context.IsBaseFactAffected(path) && IsStructuredLedgerArtifactPath(path);

    private static bool IsStructuredLedgerArtifactPath(string path) =>
        path.EndsWith(".json", StringComparison.Ordinal)
        || path.EndsWith(".yaml", StringComparison.Ordinal)
        || path.EndsWith(".yml", StringComparison.Ordinal)
        || path.StartsWith("Chronicle/", StringComparison.Ordinal);

    internal static bool IsLedgerPolicyDataPath(string path) =>
        LedgerPolicyDataPaths.Contains(path);

    private static void ValidateAcceptedEventFilesAfterJudgeSourceChange(
        RuleEvaluationContext context,
        ImmutableArray<RuleFinding>.Builder findings,
        bool judgeSourceChanged)
    {
        if (!judgeSourceChanged)
        {
            return;
        }

        var files = context.Current.Files.Values
            .Where(file => FrozenLedgerChangeClassifier.IsAcceptedEventPath(file.Path.Value))
            .OrderBy(static file => file.Path.Value, StringComparer.Ordinal)
            .ToArray();
        if (files.Length == 0
            || FrozenAcceptedEventLoader.LoadFiles(files) is not DagLedgerFilesLoadOutcome.Invalid invalid)
        {
            return;
        }

        findings.Add(new RuleFinding(
            files.Length == 1 ? files[0].Path.Value : FrozenLedgerChangeClassifier.AcceptedRoot,
            "accepted-event write gate rejected stored candidate after implementation change: "
                + invalid.Message));
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
