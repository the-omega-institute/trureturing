using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

internal static partial class TheoristFrontierContractValidator
{
    private static readonly ImmutableHashSet<string> RevisionKinds =
        ImmutableHashSet.Create(
            StringComparer.Ordinal,
            "equivalent-restatement",
            "strengthening",
            "weakening");

    internal static ImmutableArray<RuleFinding> EvaluateDeliveryIdentity(
        RuleEvaluationContext context)
    {
        ArgumentNullException.ThrowIfNull(context);
        var retiredPaths = context.Baseline.Files.Keys
            .Where(path => IsFrontier(path)
                && !context.Current.TryGetFile(path.Value, out _))
            .OrderBy(static path => path.Value, StringComparer.Ordinal)
            .ToArray();
        var revisedPaths = context.Changes.Paths
            .Where(path => IsFrontier(path)
                && TryReadStatementSha(context.Baseline, path, out var baselineStatement)
                && TryReadStatementSha(context.Current, path, out var currentStatement)
                && !string.Equals(
                    baselineStatement,
                    currentStatement,
                    StringComparison.Ordinal))
            .OrderBy(static path => path.Value, StringComparer.Ordinal)
            .ToArray();
        if (retiredPaths.Length == 0 && revisedPaths.Length == 0)
        {
            return [];
        }

        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var revisedPath in revisedPaths)
        {
            if (!TryReadContractRoot(context.Current, revisedPath, out var root)
                || !root.TryGetProperty("revision", out _))
            {
                findings.Add(new RuleFinding(
                    revisedPath.Value,
                    "changed exact_statement.statement_sha256 requires a revision declaration"));
                continue;
            }

            _ = TryReadStatementSha(
                context.Baseline,
                revisedPath,
                out var baselineStatement);
            var revision = root.GetProperty("revision");
            if (revision.ValueKind is not JsonValueKind.Object
                || !TryString(revision, "predecessor_sha256", out var predecessor)
                || !string.Equals(predecessor, baselineStatement, StringComparison.Ordinal))
            {
                findings.Add(new RuleFinding(
                    revisedPath.Value,
                    "revision.predecessor_sha256 must equal the baseline exact_statement.statement_sha256"));
            }

            if (revision.ValueKind is JsonValueKind.Object
                && (!TryString(revision, "kind", out var kind)
                    || !RevisionKinds.Contains(kind)))
            {
                findings.Add(new RuleFinding(
                    revisedPath.Value,
                    "revision.kind must be one of equivalent-restatement, strengthening, weakening"));
            }

            if (revision.ValueKind is JsonValueKind.Object
                && TryString(revision, "kind", out var declaredKind)
                && declaredKind == "weakening"
                && (!TryString(revision, "case_id", out var caseId)
                    || !CaseId.TryCreate(caseId, out _)))
            {
                findings.Add(new RuleFinding(
                    revisedPath.Value,
                    "weakening revision.case_id must be a canonical case id"));
            }
        }

        if (retiredPaths.Length == 0)
        {
            return findings.ToImmutable();
        }

        var baselineMission = LoadMission(context.Baseline);
        if (baselineMission.UnreadableReason is { } baselineReason)
        {
            foreach (var retiredPath in retiredPaths)
            {
                findings.Add(new RuleFinding(
                    retiredPath.Value,
                    Undecidable("baseline Frontier ownership", baselineReason)));
            }

            return findings.ToImmutable();
        }

        var currentMission = LoadMission(context.Current);
        FrozenLedgerBaseView? frozen = null;
        foreach (var retiredPath in retiredPaths)
        {
            if (baselineMission.Entries.TryGetValue(retiredPath, out var baselineOwner)
                && baselineOwner is FrontierEligibilityKind.Governance)
            {
                continue;
            }

            if (!currentMission.Retirements.TryGetValue(retiredPath, out var deliveryGids))
            {
                continue;
            }

            frozen ??= FrozenLedgerBaseViewReader.Read(context.Current);
            findings.AddRange(ValidateDeliveryIdentity(
                retiredPath,
                deliveryGids,
                context.Lean.Report,
                context.Baseline,
                frozen));
        }

        return findings.ToImmutable();
    }

    internal static bool IsDeliveryIdentityAffected(RuleEvaluationContext context)
    {
        ArgumentNullException.ThrowIfNull(context);
        return context.Changes.Paths.Any(path =>
            IsFrontier(path)
            && context.Baseline.TryGetFile(path.Value, out _)
            && (!context.Current.TryGetFile(path.Value, out _)
                || TryReadStatementSha(context.Baseline, path, out var baselineStatement)
                    && TryReadStatementSha(context.Current, path, out var currentStatement)
                    && !string.Equals(
                        baselineStatement,
                        currentStatement,
                        StringComparison.Ordinal)));
    }

    private static void ValidateRevision(
        RepoPath path,
        JsonElement revision,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        var isWeakening = revision.ValueKind is JsonValueKind.Object
            && TryString(revision, "kind", out var kind)
            && kind == "weakening";
        var hasCanonicalKeys = isWeakening
            ? HasExactKeys(revision, "predecessor_sha256", "kind", "note", "case_id")
            : HasExactKeys(revision, "predecessor_sha256", "kind", "note");
        if (!hasCanonicalKeys)
        {
            findings.Add(new RuleFinding(path.Value, "revision keys are not canonical"));
        }

        if (revision.ValueKind is not JsonValueKind.Object
            || !TryString(revision, "predecessor_sha256", out var predecessor)
            || !FrozenHashSyntax.IsSha256(predecessor))
        {
            findings.Add(new RuleFinding(
                path.Value,
                "revision.predecessor_sha256 must be a canonical sha256 address"));
        }

        if (revision.ValueKind is not JsonValueKind.Object
            || !TryString(revision, "kind", out var declaredKind)
            || !RevisionKinds.Contains(declaredKind))
        {
            findings.Add(new RuleFinding(
                path.Value,
                "revision.kind must be one of equivalent-restatement, strengthening, weakening"));
        }

        if (revision.ValueKind is not JsonValueKind.Object
            || !TryString(revision, "note", out var note)
            || string.IsNullOrWhiteSpace(note))
        {
            findings.Add(new RuleFinding(path.Value, "revision.note must be non-empty"));
        }

        if (isWeakening
            && (!TryString(revision, "case_id", out var caseId)
                || !CaseId.TryCreate(caseId, out _)))
        {
            findings.Add(new RuleFinding(
                path.Value,
                "weakening revision.case_id must be a canonical case id"));
        }
    }

    private static bool TryReadStatementSha(
        RepositorySnapshot snapshot,
        RepoPath path,
        out string statement)
    {
        statement = string.Empty;
        return TryReadContractRoot(snapshot, path, out var root)
            && root.TryGetProperty("exact_statement", out var exact)
            && TryString(exact, "statement_sha256", out statement);
    }

    private static bool TryReadContractRoot(
        RepositorySnapshot snapshot,
        RepoPath path,
        out JsonElement root)
    {
        root = default;
        if (!snapshot.TryGetFile(path.Value, out var file)
            || CountOccurrences(file.Text, Marker) != 1)
        {
            return false;
        }

        var start = file.Text.IndexOf(Marker, StringComparison.Ordinal) + Marker.Length;
        var end = file.Text.IndexOf(EndMarker, start, StringComparison.Ordinal);
        if (end < 0)
        {
            return false;
        }

        try
        {
            using var document = JsonDocument.Parse(file.Text[start..end]);
            root = document.RootElement.Clone();
            return root.ValueKind is JsonValueKind.Object
                && TryString(root, "schema", out var schema)
                && schema == Schema;
        }
        catch (JsonException)
        {
            return false;
        }
    }

    private static bool HasCanonicalContractKeys(JsonElement root) =>
        HasExactKeys(
            root,
            "schema",
            "exact_statement",
            "motivation_gids",
            "falsifier",
            "search_receipt_gids",
            "computation_receipt_gids",
            "triage_class")
        || HasExactKeys(
            root,
            "schema",
            "exact_statement",
            "motivation_gids",
            "falsifier",
            "search_receipt_gids",
            "computation_receipt_gids",
            "triage_class",
            "revision");
}
