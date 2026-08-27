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
    internal const string TaskBlockReferenceSyntaxPath =
        "tools/StrataLint.Engine/TaskBlockReferenceSyntax.cs";
    internal const string YamlSubsetParserPath =
        "tools/Trureturing.Truth/YamlSubsetParser.cs";

    // These are the non-snapshot inputs that can change how SL-019 classifies or parses
    // every structured artifact. Keep the list beside the replay predicate so a new input
    // cannot be added to the rule without also being added to its wake-up closure.
    private static readonly ImmutableHashSet<string> LedgerPolicySourcePaths =
        ImmutableHashSet.Create(
            StringComparer.Ordinal,
            RegistryPolicyPath,
            DomainsPolicyPath);

    private static readonly ImmutableHashSet<string> LedgerRuleDependencyPaths =
        ImmutableHashSet.Create(
            StringComparer.Ordinal,
            TaskBlockReferenceSyntaxPath,
            YamlSubsetParserPath);

    private static ImmutableArray<RuleFinding> Ledger(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        var replay = ChangedLeanTaskSet(context)
            || PolicyChanged(context)
            || RuleDependencyChanged(context)
            || LedgerArtifactChanged(context);
        HashSet<string>? tasks = null;
        foreach (var (path, file) in context.Current.Files)
        {
            var governed = IsGovernedStructured(path, context.Policy);
            var pathAffected = context.IsBaseFactAffected(path.Value);
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

        ValidateAcceptedEventFilesAfterImplementationChange(context, findings);
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

    private static bool PolicyChanged(RuleEvaluationContext context) =>
        context.Changes.Paths.Any(path => LedgerPolicySourcePaths.Contains(path.Value));

    private static bool RuleDependencyChanged(RuleEvaluationContext context) =>
        context.RuleImplementationChanged
        || context.Changes.Paths.Any(path => LedgerRuleDependencyPaths.Contains(path.Value));

    private static bool LedgerArtifactChanged(RuleEvaluationContext context) =>
        context.Changes.Paths.Any(path => IsStructuredLedgerArtifactPath(path.Value));

    private static bool IsStructuredLedgerArtifactPath(string path) =>
        path.EndsWith(".json", StringComparison.Ordinal)
        || path.EndsWith(".yaml", StringComparison.Ordinal)
        || path.EndsWith(".yml", StringComparison.Ordinal)
        || path.StartsWith("Chronicle/", StringComparison.Ordinal);

    internal static bool HasExternalLedgerDependencyChange(RawChangeSet changes) =>
        changes.Paths.Any(path => LedgerRuleDependencyPaths.Contains(path.Value));

    internal static bool IsLedgerRuleDependencyPath(string path) =>
        LedgerRuleDependencyPaths.Contains(path);


    private static void ValidateAcceptedEventFilesAfterImplementationChange(
        RuleEvaluationContext context,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        if (!context.RuleImplementationChanged)
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
