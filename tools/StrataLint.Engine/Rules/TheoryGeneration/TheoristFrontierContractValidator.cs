using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

internal static partial class TheoristFrontierContractValidator
{
    internal const string Marker = "/- THEORIST_FRONTIER_CONTRACT_V2\n";

    private const string LegacyMarker = "/- THEORIST_FRONTIER_CONTRACT_V1\n";
    private const string Schema = "trureturing-theorist-frontier-v2";
    private const string EndMarker = "\n-/";
    private const string FrontierPrefix = "D5/X_Frontier/";
    private static readonly ImmutableHashSet<string> TriageClasses =
        ImmutableHashSet.Create(StringComparer.Ordinal, "theorem", "window", "wall");

    internal static ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context)
    {
        ArgumentNullException.ThrowIfNull(context);
        var currentMission = LoadMission(context.Current);
        var targets = context.Lean.Report.Files.Keys
            .Where(IsFrontier)
            .Concat(context.Baseline.Files
                .Where(item => IsFrontier(item.Key)
                    && (CountOccurrences(item.Value.Text, Marker) > 0
                        || currentMission.Retirements.ContainsKey(item.Key)
                        || !context.Current.TryGetFile(item.Key.Value, out _)))
                .Select(static item => item.Key))
            .Distinct()
            .OrderBy(static path => path.Value, StringComparer.Ordinal)
            .ToArray();
        if (targets.Length == 0)
        {
            return [];
        }
        // Baseline ownership is read through the typed frontier projection only. The protected
        // baseline may still carry the retired worth-vector case_id payload.
        var baselineMission = LoadBaselineMission(context.Baseline);
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        FrozenLedgerBaseView? frozen = null;
        foreach (var path in targets)
        {
            var hasCurrentReport = context.Lean.Report.Files.TryGetValue(path, out var report);
            var isNew = !context.Baseline.TryGetFile(path.Value, out var baselineFile);
            var hasCurrentSource = context.Current.TryGetFile(path.Value, out var currentFile);
            var currentHasContract = currentFile is not null
                && CountOccurrences(currentFile.Text, Marker) > 0;
            var currentHasLegacyContract = currentFile is not null
                && CountOccurrences(currentFile.Text, LegacyMarker) > 0;
            var baselineHadContract = baselineFile is not null
                && CountOccurrences(baselineFile.Text, Marker) > 0;
            var baselineHadLegacyContract = baselineFile is not null
                && CountOccurrences(baselineFile.Text, LegacyMarker) > 0;
            FrontierEligibilityKind? currentOwner = currentMission.Entries.TryGetValue(
                path,
                out var typedCurrentOwner)
                ? typedCurrentOwner
                : null;
            FrontierEligibilityKind? baselineOwner = baselineMission.Entries.TryGetValue(
                path,
                out var typedBaselineOwner)
                ? typedBaselineOwner
                : null;
            var transitionedToDeclarationReady = currentOwner
                    is FrontierEligibilityKind.DeclarationReadyMathematicalOpen
                && baselineOwner is not null
                && baselineOwner is not FrontierEligibilityKind.DeclarationReadyMathematicalOpen;

            var isDeletedBaselineSource = baselineFile is not null && !hasCurrentSource;
            var isGovernanceDeletionExempt = isDeletedBaselineSource
                && baselineOwner is FrontierEligibilityKind.Governance
                && !baselineHadContract
                && !baselineHadLegacyContract
                && currentMission.UnreadableReason is null
                && currentOwner is null;
            if (isDeletedBaselineSource
                && !isGovernanceDeletionExempt
                && currentOwner is not FrontierEligibilityKind.Retired)
            {
                findings.Add(new RuleFinding(
                    path.Value,
                    currentMission.UnreadableReason is { } retirementOwnerReason
                        ? Undecidable("deleted Frontier source retirement ownership", retirementOwnerReason)
                        : "deleted Frontier source requires a retired owner with delivery evidence"));
                continue;
            }

            if (isGovernanceDeletionExempt)
            {
                continue;
            }

            var isRetiredBaselineSource = baselineFile is not null
                && currentOwner is FrontierEligibilityKind.Retired;
            if (isRetiredBaselineSource)
            {
                frozen ??= FrozenLedgerBaseViewReader.Read(context.Current);
                if (!currentMission.Retirements.TryGetValue(path, out var deliveryGids))
                {
                    findings.Add(new RuleFinding(
                        path.Value,
                        "retired Frontier owner has no delivery evidence"));
                }
                else
                {
                    findings.AddRange(ValidateRetirement(
                        path,
                        deliveryGids,
                        context.Lean.Report,
                        frozen));
                }

                if (!hasCurrentSource || currentFile is null)
                {
                    continue;
                }
            }

            if (isNew && currentOwner is null or FrontierEligibilityKind.Unknown)
            {
                findings.Add(new RuleFinding(
                    path.Value,
                    currentMission.UnreadableReason is { } missingOwnerReason
                        ? Undecidable("Frontier owner", missingOwnerReason)
                        : "Frontier owner is unknown; docs/MISSION.md.frontier_eligibility must classify the new module"));
                continue;
            }

            if (currentOwner is FrontierEligibilityKind.MathematicalNotYetStated
                && report is not null
                && report.Declarations.Any(UsesSorry))
            {
                findings.Add(new RuleFinding(
                    path.Value,
                    "mathematical-not-yet-stated owner cannot carry an elaborated sorryAx declaration"));
                continue;
            }

            var requiresContract = currentHasContract
                || currentHasLegacyContract
                || baselineHadContract
                || baselineHadLegacyContract
                || transitionedToDeclarationReady
                || isNew && currentOwner
                    is FrontierEligibilityKind.DeclarationReadyMathematicalOpen;
            if (!requiresContract)
            {
                continue;
            }

            if (!hasCurrentSource || currentFile is null)
            {
                findings.Add(new RuleFinding(path.Value, "theorist contract source is unavailable"));
                continue;
            }

            if (!hasCurrentReport || report is null)
            {
                findings.Add(new RuleFinding(
                    path.Value,
                    "theorist contract compiled report is unavailable"));
                continue;
            }

            if (currentOwner is not FrontierEligibilityKind.DeclarationReadyMathematicalOpen)
            {
                findings.Add(new RuleFinding(
                    path.Value,
                    currentMission.UnreadableReason is { } ownershipReason
                        ? Undecidable("theorist contract ownership", ownershipReason)
                        : "theorist contract requires declaration-ready-mathematical-open ownership"));
                continue;
            }

            frozen ??= FrozenLedgerBaseViewReader.Read(context.Current);
            findings.AddRange(Validate(path, currentFile.Text, report, context.Current, frozen));
        }

        return findings.ToImmutable();
    }

    private static ImmutableArray<RuleFinding> Validate(
        RepoPath path,
        string source,
        LeanFileReport report,
        RepositorySnapshot snapshot,
        FrozenLedgerBaseView frozen)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        if (CountOccurrences(source, LegacyMarker) > 0)
        {
            return [new RuleFinding(
                path.Value,
                "THEORIST_FRONTIER_CONTRACT_V1 is legacy; V2 type-address contract is required")];
        }

        var count = CountOccurrences(source, Marker);
        if (count == 0)
        {
            return [new RuleFinding(path.Value, "theorist contract is required")];
        }

        if (count != 1)
        {
            return [new RuleFinding(path.Value, "duplicate theorist contracts are forbidden")];
        }

        var start = source.IndexOf(Marker, StringComparison.Ordinal) + Marker.Length;
        var end = source.IndexOf(EndMarker, start, StringComparison.Ordinal);
        if (end < 0)
        {
            return [new RuleFinding(path.Value, "theorist contract closing marker is missing")];
        }

        JsonElement root;
        try
        {
            using var document = JsonDocument.Parse(source[start..end]);
            root = document.RootElement.Clone();
        }
        catch (JsonException exception)
        {
            return [new RuleFinding(path.Value, $"theorist contract is not valid JSON: {exception.Message}")];
        }

        if (!HasCanonicalContractKeys(root))
        {
            return [new RuleFinding(path.Value, "theorist contract keys are not canonical")];
        }

        if (!TryString(root, "schema", out var schema) || schema != Schema)
        {
            findings.Add(new RuleFinding(path.Value, $"theorist contract schema must be {Schema}"));
        }

        if (!TryString(root, "falsifier", out var falsifier)
            || string.IsNullOrWhiteSpace(falsifier))
        {
            findings.Add(new RuleFinding(path.Value, "falsifier must be non-empty"));
        }

        if (!TryString(root, "triage_class", out var triage)
            || !TriageClasses.Contains(triage))
        {
            findings.Add(new RuleFinding(
                path.Value,
                "triage_class must be one of theorem, window, wall"));
        }

        if (root.TryGetProperty("revision", out var revision))
        {
            ValidateRevision(path, revision, findings);
        }

        ValidateExactStatement(path, root.GetProperty("exact_statement"), report, findings);
        ValidateMotivations(path, root.GetProperty("motivation_gids"), frozen, findings);
        ValidateReceipts(
            path,
            root.GetProperty("search_receipt_gids"),
            "search_receipt_gids",
            snapshot,
            static target => target is Target.Library,
            "Library",
            findings);
        ValidateReceipts(
            path,
            root.GetProperty("computation_receipt_gids"),
            "computation_receipt_gids",
            snapshot,
            static target => target is Target.Evidence,
            "Evidence",
            findings);
        return findings.ToImmutable();
    }

    private static void ValidateExactStatement(
        RepoPath path,
        JsonElement exact,
        LeanFileReport report,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        if (!HasExactKeys(exact, "gid", "statement_sha256"))
        {
            findings.Add(new RuleFinding(path.Value, "exact_statement keys are not canonical"));
            return;
        }

        if (!TryString(exact, "gid", out var gidText)
            || !Gid.TryParse(gidText, out var gid)
            || gid.ToTarget() is not Target.Formal { Declaration: not null } formal
            || formal.Path != path)
        {
            findings.Add(new RuleFinding(
                path.Value,
                "exact_statement.gid must select the open declaration"));
            return;
        }

        var expectedName = gidText.Replace('/', '.');
        var declarations = report.Declarations
            .Where(declaration => string.Equals(
                declaration.Name,
                expectedName,
                StringComparison.Ordinal))
            .ToArray();
        if (declarations.Length != 1)
        {
            findings.Add(new RuleFinding(
                path.Value,
                "exact_statement.gid must select the open declaration"));
            return;
        }

        var declaration = declarations[0];
        if (!declaration.IncludeInStatement || !UsesSorry(declaration))
        {
            findings.Add(new RuleFinding(
                path.Value,
                "exact statement must be open via sorryAx"));
            return;
        }

        var openDeclarations = report.Declarations.Where(UsesSorry).ToArray();
        if (openDeclarations.Length != 1 || !ReferenceEquals(openDeclarations[0], declaration))
        {
            findings.Add(new RuleFinding(
                path.Value,
                "theorist contract must bind the module's only open declaration"));
            return;
        }

        if (!TryString(exact, "statement_sha256", out var statementSha256)
            || !string.Equals(
                CanonicalStatementWriter.StatementTypeAddress(declaration),
                statementSha256,
                StringComparison.Ordinal))
        {
            findings.Add(new RuleFinding(
                path.Value,
                "exact_statement.statement_sha256 does not match CanonicalStatementWriter"));
        }

    }

    private static void ValidateMotivations(
        RepoPath path,
        JsonElement value,
        FrozenLedgerBaseView frozen,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        if (!TryCanonicalNonEmptyStrings(value, out var gids))
        {
            findings.Add(new RuleFinding(
                path.Value,
                "motivation_gids must be a non-empty sorted unique string array"));
            return;
        }

        for (var index = 0; index < gids.Length; index++)
        {
            var gidText = gids[index];
            if (!Gid.TryParse(gidText, out var gid)
                || gid.ToTarget() is not Target.Formal)
            {
                findings.Add(new RuleFinding(
                    path.Value,
                    $"motivation_gids[{index}] is not a canonical formal GID"));
                continue;
            }

            if (!frozen.ActiveByPath.ContainsKey(gid.Path))
            {
                findings.Add(new RuleFinding(
                    path.Value,
                    $"motivation_gids[{index}] is not an active frozen member"));
            }
        }
    }

    private static void ValidateReceipts(
        RepoPath path,
        JsonElement value,
        string field,
        RepositorySnapshot snapshot,
        Func<Target, bool> isExpectedPlane,
        string plane,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        if (!TryCanonicalNonEmptyStrings(value, out var gids))
        {
            findings.Add(new RuleFinding(
                path.Value,
                $"{field} must be a non-empty sorted unique string array"));
            return;
        }

        for (var index = 0; index < gids.Length; index++)
        {
            var gidText = gids[index];
            if (!Gid.TryParse(gidText, out var gid) || !isExpectedPlane(gid.ToTarget()))
            {
                findings.Add(new RuleFinding(
                    path.Value,
                    $"{field}[{index}] must be {(plane == "Evidence" ? "an" : "a")} {plane} GID"));
                continue;
            }

            if (!snapshot.TryGetFile(gid.Path.Value, out _))
            {
                findings.Add(new RuleFinding(
                    path.Value,
                    $"{field}[{index}] does not resolve: {gidText}"));
            }
        }
    }

    private static ImmutableArray<RuleFinding> ValidateRetirement(
        RepoPath retiredPath,
        ImmutableArray<string> deliveryGids,
        LeanAxiomReport report,
        FrozenLedgerBaseView frozen)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var deliveryGid in deliveryGids)
        {
            if (!TryResolveActiveFrozenDelivery(deliveryGid, report, frozen, out _))
            {
                findings.Add(new RuleFinding(
                    retiredPath.Value,
                    $"retired delivery GID does not resolve to an active frozen declaration: {deliveryGid}"));
            }
        }

        return findings.ToImmutable();
    }

    private static ImmutableArray<RuleFinding> ValidateDeliveryIdentity(
        RepoPath retiredPath,
        ImmutableArray<string> deliveryGids,
        LeanAxiomReport report,
        RepositorySnapshot baseline,
        FrozenLedgerBaseView frozen)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        var baselineStatement = ReadRetiredBaselineStatement(retiredPath, baseline, findings);
        if (baselineStatement is null)
        {
            return findings.ToImmutable();
        }

        var hasMatchingStatement = deliveryGids.Any(deliveryGid =>
            TryResolveActiveFrozenDelivery(deliveryGid, report, frozen, out var signature)
            && string.Equals(
                CanonicalStatementWriter.StatementTypeAddress(signature.Type),
                baselineStatement,
                StringComparison.Ordinal));
        if (!hasMatchingStatement)
        {
            findings.Add(new RuleFinding(
                retiredPath.Value,
                "no delivery declaration has the baseline Frontier contract statement"));
        }

        return findings.ToImmutable();
    }

    private static bool TryResolveActiveFrozenDelivery(
        string deliveryGid,
        LeanAxiomReport report,
        FrozenLedgerBaseView frozen,
        out DigestionFormalizationSignature signature)
    {
        signature = null!;
        if (!Gid.TryParse(deliveryGid, out var gid)
            || gid.ToTarget() is not Target.Formal { Declaration: not null } formal
            || !frozen.ActiveByPath.TryGetValue(formal.Path, out var active))
        {
            return false;
        }

        try
        {
            signature = DigestionFormalizationReceipt.ResolveSignature(gid, report);
        }
        catch (FormatException)
        {
            return false;
        }

        var resolved = signature;
        return active.Material.DeclarationStatementIds.Any(item =>
            string.Equals(item.DeclarationNameKey, resolved.NameKey, StringComparison.Ordinal)
            && string.Equals(item.Kind, resolved.Kind, StringComparison.Ordinal));
    }

    internal static string? ReadRetiredBaselineStatement(
        RepoPath retiredPath,
        RepositorySnapshot baseline,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        if (!baseline.TryGetFile(retiredPath.Value, out var baselineFile))
        {
            findings.Add(new RuleFinding(
                retiredPath.Value,
                "baseline Frontier source is unavailable"));
            return null;
        }

        var source = baselineFile.Text;
        if (CountOccurrences(source, LegacyMarker) > 0)
        {
            findings.Add(new RuleFinding(
                retiredPath.Value,
                "baseline Frontier contract uses legacy V1 statement identity; V2 type-address contract is required"));
            return null;
        }

        if (CountOccurrences(source, Marker) == 0)
        {
            findings.Add(new RuleFinding(
                retiredPath.Value,
                "baseline Frontier contract block is missing"));
            return null;
        }

        if (CountOccurrences(source, Marker) != 1)
        {
            findings.Add(new RuleFinding(
                retiredPath.Value,
                "baseline Frontier contract block is duplicated"));
            return null;
        }

        var start = source.IndexOf(Marker, StringComparison.Ordinal) + Marker.Length;
        var end = source.IndexOf(EndMarker, start, StringComparison.Ordinal);
        if (end < 0)
        {
            findings.Add(new RuleFinding(
                retiredPath.Value,
                "baseline Frontier contract closing marker is missing"));
            return null;
        }

        JsonElement root;
        try
        {
            using var document = JsonDocument.Parse(source[start..end]);
            root = document.RootElement.Clone();
        }
        catch (JsonException exception)
        {
            findings.Add(new RuleFinding(
                retiredPath.Value,
                $"baseline Frontier contract is not valid JSON: {exception.Message}"));
            return null;
        }

        if (!HasCanonicalContractKeys(root)
            || !TryString(root, "schema", out var schema)
            || schema != Schema
            || !root.TryGetProperty("exact_statement", out var exact)
            || !HasExactKeys(exact, "gid", "statement_sha256")
            || !TryString(exact, "statement_sha256", out var statement)
            || !FrozenHashSyntax.IsSha256(statement))
        {
            findings.Add(new RuleFinding(
                retiredPath.Value,
                "baseline Frontier exact_statement is not canonical"));
            return null;
        }

        if (root.TryGetProperty("revision", out var revision))
        {
            var revisionFindings = ImmutableArray.CreateBuilder<RuleFinding>();
            ValidateRevision(retiredPath, revision, revisionFindings);
            foreach (var revisionFinding in revisionFindings)
            {
                findings.Add(new RuleFinding(
                    retiredPath.Value,
                    $"baseline Frontier {revisionFinding.Message}"));
            }

            if (revisionFindings.Count > 0)
            {
                return null;
            }
        }

        return statement;
    }

    // An unreadable MISSION is absence of authority, not an owner verdict. Carry the reason so the
    // diagnostic names the file to repair instead of telling the author to classify a module.
    private static MissionOwners LoadMission(RepositorySnapshot snapshot) =>
        MissionFileLoader.Load(snapshot) switch
        {
            MissionLoadOutcome.Loaded loaded => BuildMissionOwners(loaded.Policy.FrontierEligibility),
            MissionLoadOutcome.Invalid invalid => new MissionOwners(
                ImmutableDictionary<RepoPath, FrontierEligibilityKind>.Empty,
                ImmutableDictionary<RepoPath, ImmutableArray<string>>.Empty,
                invalid.Error.Message),
            _ => throw new InvalidOperationException("unknown MISSION load outcome"),
        };

    private static MissionOwners LoadBaselineMission(RepositorySnapshot snapshot) =>
        MissionFileLoader.TryLoadFrontierEligibility(snapshot, out var entries, out var error)
            ? BuildMissionOwners(entries)
            : new MissionOwners(
                ImmutableDictionary<RepoPath, FrontierEligibilityKind>.Empty,
                ImmutableDictionary<RepoPath, ImmutableArray<string>>.Empty,
                error ?? "unknown MISSION projection failure");

    private static MissionOwners BuildMissionOwners(
        ImmutableArray<FrontierEligibilityEntry> entries) =>
        new(
            entries.ToImmutableDictionary(
                static entry => Gid.TryParse(entry.SourceRef, out var gid)
                    ? gid.Path
                    : throw new InvalidOperationException(
                        $"MISSION owner has invalid GID {entry.SourceRef}"),
                static entry => entry.Kind),
            entries
                .Where(static entry => entry.Kind is FrontierEligibilityKind.Retired)
                .ToImmutableDictionary(
                    static entry => Gid.TryParse(entry.SourceRef, out var gid)
                        ? gid.Path
                        : throw new InvalidOperationException(
                            $"MISSION retirement has invalid GID {entry.SourceRef}"),
                    static entry => entry.DeliveryGids),
            null);

    private static string Undecidable(string subject, string reason) =>
        $"{subject} is undecidable because {MissionFileLoader.RelativePath} does not load: {reason}";

    private static bool IsFrontier(RepoPath path) =>
        path.Value.StartsWith(FrontierPrefix, StringComparison.Ordinal)
        && path.Value.EndsWith(".lean", StringComparison.Ordinal);

    private static bool UsesSorry(LeanDeclaration declaration) =>
        declaration.Axioms.Contains("sorryAx", StringComparer.Ordinal);

    private static bool HasExactKeys(JsonElement value, params string[] expected)
    {
        if (value.ValueKind != JsonValueKind.Object)
        {
            return false;
        }

        var actual = value.EnumerateObject()
            .Select(static property => property.Name)
            .Order(StringComparer.Ordinal)
            .ToArray();
        return actual.SequenceEqual(expected.Order(StringComparer.Ordinal), StringComparer.Ordinal);
    }

    private static bool TryString(JsonElement value, string property, out string text)
    {
        if (value.TryGetProperty(property, out var element)
            && element.ValueKind == JsonValueKind.String
            && element.GetString() is { } decoded)
        {
            text = decoded;
            return true;
        }

        text = string.Empty;
        return false;
    }

    private static bool TryCanonicalNonEmptyStrings(
        JsonElement value,
        out ImmutableArray<string> strings)
    {
        if (value.ValueKind != JsonValueKind.Array)
        {
            strings = [];
            return false;
        }

        var builder = ImmutableArray.CreateBuilder<string>();
        foreach (var item in value.EnumerateArray())
        {
            if (item.ValueKind != JsonValueKind.String
                || item.GetString() is not { Length: > 0 } text)
            {
                strings = [];
                return false;
            }

            builder.Add(text);
        }

        strings = builder.ToImmutable();
        return strings.Length > 0
            && strings.SequenceEqual(
                strings.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal),
                StringComparer.Ordinal);
    }

    private static int CountOccurrences(string source, string value)
    {
        var count = 0;
        var offset = 0;
        while ((offset = source.IndexOf(value, offset, StringComparison.Ordinal)) >= 0)
        {
            count++;
            offset += value.Length;
        }

        return count;
    }

    private static bool HasContractMarker(RepositorySnapshot snapshot, RepoPath path) =>
        snapshot.TryGetFile(path.Value, out var file)
        && (CountOccurrences(file.Text, Marker) > 0
            || CountOccurrences(file.Text, LegacyMarker) > 0);

    private sealed record MissionOwners(
        ImmutableDictionary<RepoPath, FrontierEligibilityKind> Entries,
        ImmutableDictionary<RepoPath, ImmutableArray<string>> Retirements,
        string? UnreadableReason);
}
