using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

internal static class TheoristFrontierContractValidator
{
    internal const string Marker = "/- THEORIST_FRONTIER_CONTRACT_V1\n";

    private const string Schema = "trureturing-theorist-frontier-v1";
    private const string EndMarker = "\n-/";
    private const string FrontierPrefix = "D5/X_Frontier/";

    private static readonly ImmutableHashSet<string> TriageClasses =
        ImmutableHashSet.Create(StringComparer.Ordinal, "theorem", "window", "wall");

    internal static ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context)
    {
        ArgumentNullException.ThrowIfNull(context);
        var targets = context.Lean.Report.Files
            .Where(static item => IsFrontier(item.Key))
            .OrderBy(static item => item.Key.Value, StringComparer.Ordinal)
            .ToArray();
        if (targets.Length == 0)
        {
            return [];
        }

        var currentMission = LoadMission(context.Current);
        var baselineMission = LoadMission(context.Baseline);
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        FrozenLedgerBaseView? frozen = null;
        foreach (var (path, report) in targets)
        {
            var isNew = !context.Baseline.TryGetFile(path.Value, out var baselineFile);
            var hasCurrentSource = context.Current.TryGetFile(path.Value, out var currentFile);
            var currentHasContract = currentFile is not null
                && CountOccurrences(currentFile.Text, Marker) > 0;
            var baselineHadContract = baselineFile is not null
                && CountOccurrences(baselineFile.Text, Marker) > 0;
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

            if (isNew && currentOwner is null or FrontierEligibilityKind.Unknown)
            {
                findings.Add(new RuleFinding(
                    path.Value,
                    "Frontier owner is unknown; docs/MISSION.md.frontier_eligibility must classify the new module"));
                continue;
            }

            if (currentOwner is FrontierEligibilityKind.MathematicalNotYetStated
                && report.Declarations.Any(UsesSorry))
            {
                findings.Add(new RuleFinding(
                    path.Value,
                    "mathematical-not-yet-stated owner cannot carry an elaborated sorryAx declaration"));
                continue;
            }

            var requiresContract = currentHasContract
                || baselineHadContract
                || transitionedToDeclarationReady
                || isNew && currentOwner
                    is FrontierEligibilityKind.DeclarationReadyMathematicalOpen;
            if (!requiresContract)
            {
                continue;
            }

            if (currentOwner is not FrontierEligibilityKind.DeclarationReadyMathematicalOpen)
            {
                findings.Add(new RuleFinding(
                    path.Value,
                    "theorist contract requires declaration-ready-mathematical-open ownership"));
                continue;
            }

            if (!hasCurrentSource || currentFile is null)
            {
                findings.Add(new RuleFinding(path.Value, "theorist contract source is unavailable"));
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

        if (!HasExactKeys(
                root,
                "schema",
                "exact_statement",
                "motivation_gids",
                "falsifier",
                "search_receipt_gids",
                "computation_receipt_gids",
                "triage_class"))
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

        var statement = CanonicalStatementWriter.DeclarationStatementIds(path, report)
            .SingleOrDefault(item => item.DeclarationNameKey == declaration.NameKey
                && item.Kind == declaration.Kind);
        if (statement is null
            || !TryString(exact, "statement_sha256", out var statementSha256)
            || !string.Equals(statement.StatementId.Value, statementSha256, StringComparison.Ordinal))
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

    private static MissionOwners LoadMission(RepositorySnapshot snapshot) =>
        MissionFileLoader.Load(snapshot) switch
        {
            MissionLoadOutcome.Loaded loaded => new MissionOwners(
                loaded.Policy.FrontierEligibility.ToImmutableDictionary(
                    static entry => Gid.TryParse(entry.SourceRef, out var gid)
                        ? gid.Path
                        : throw new InvalidOperationException(
                            $"MISSION owner has invalid GID {entry.SourceRef}"),
                    static entry => entry.Kind)),
            MissionLoadOutcome.Invalid => new MissionOwners(
                ImmutableDictionary<RepoPath, FrontierEligibilityKind>.Empty),
            _ => throw new InvalidOperationException("unknown MISSION load outcome"),
        };

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

    private sealed record MissionOwners(
        ImmutableDictionary<RepoPath, FrontierEligibilityKind> Entries);
}
