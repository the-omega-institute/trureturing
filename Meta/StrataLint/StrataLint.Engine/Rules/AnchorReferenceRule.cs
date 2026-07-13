using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text.Json;

namespace StrataLint.Engine;

internal static class AnchorReferenceRule
{
    private enum TargetState
    {
        Resolved,
        InvalidTarget,
        Ambiguous,
    }

    private sealed record TargetCheck(TargetState State, string? Reason = null);

    private sealed record AnchorGovernance(
        IReadOnlySet<string> Cases,
        IReadOnlyDictionary<string, string> TheorySources,
        string? Error);

    internal static ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context)
    {
        var catalog = AnchorCatalogLoader.Load(context.Current);
        var baseline = BaselineAnchorsByGid(context.Baseline);
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        var governance = LoadGovernance(context.Current);
        var referencedDefinitions = new HashSet<string>(StringComparer.Ordinal);
        foreach (var (path, file) in RepositoryRules.FormalFiles(context.Current)
            .OrderBy(static item => item.Path.Value, StringComparer.Ordinal))
        {
            if (!RepositoryRules.TryHeader(file.Text, out var header))
            {
                continue;
            }

            var unchangedLegacySet = baseline.TryGetValue(header.Gid, out var baselineSets)
                && baselineSets.Length == 1
                && AnchorMultisetsEqual(header.Anchors, baselineSets[0]);
            foreach (var anchor in header.Anchors)
            {
                if (catalog.Definitions.TryGetValue(anchor, out var definition))
                {
                    referencedDefinitions.Add(definition.Anchor);
                    EvaluateDefinition(
                        path.Value,
                        definition,
                        context.Current,
                        governance,
                        findings);
                    continue;
                }

                if (catalog.Legacy.TryGetValue(anchor, out var legacy))
                {
                    if (unchangedLegacySet)
                    {
                        referencedDefinitions.UnionWith(legacy.CanonicalTargets);
                    }

                    EvaluateLegacy(
                        path.Value,
                        legacy,
                        unchangedLegacySet,
                        catalog,
                        context.Current,
                        governance,
                        findings);
                    continue;
                }

                findings.Add(new RuleFinding(
                    path.Value,
                    $"anchor '{anchor}' is unregistered (Unregistered) in the typed catalog"));
            }
        }

        if (context.Changes.Paths.Any(static path => path.Value == AnchorCatalogLoader.RelativePath))
        {
            foreach (var definition in catalog.Definitions.Values
                .Where(definition => !referencedDefinitions.Contains(definition.Anchor))
                .OrderBy(static definition => definition.Anchor, StringComparer.Ordinal))
            {
                EvaluateDefinition(
                    AnchorCatalogLoader.RelativePath,
                    definition,
                    context.Current,
                    governance,
                    findings,
                    observeRegisteredOpen: false);
            }
        }

        return findings.ToImmutable();
    }

    private static void EvaluateDefinition(
        string path,
        AnchorCatalogDefinition definition,
        RepositorySnapshot snapshot,
        AnchorGovernance governance,
        ImmutableArray<RuleFinding>.Builder findings,
        bool observeRegisteredOpen = true)
    {
        if (definition.Status == "registered-open"
            && !CaseIsRegistered(definition.CaseId!, governance, out var caseReason))
        {
            findings.Add(new RuleFinding(
                path,
                $"anchor '{definition.Anchor}' has invalid target (InvalidTarget): {caseReason}"));
            return;
        }

        var target = ValidateTarget(definition, snapshot, governance);
        if (target.State is TargetState.InvalidTarget)
        {
            findings.Add(new RuleFinding(
                path,
                $"anchor '{definition.Anchor}' has invalid target (InvalidTarget): {target.Reason}"));
            return;
        }

        if (target.State is TargetState.Ambiguous)
        {
            findings.Add(new RuleFinding(
                path,
                $"anchor '{definition.Anchor}' is ambiguous (Ambiguous): {target.Reason}"));
            return;
        }

        if (definition.Status == "registered-open" && observeRegisteredOpen)
        {
            findings.Add(new RuleFinding(
                path,
                $"anchor '{definition.Anchor}' is registered open (RegisteredOpen) under {definition.CaseId}: {definition.OpenReason}",
                AdmissionEffect.Observe));
        }
    }

    private static void EvaluateLegacy(
        string path,
        LegacyAnchorCatalogEntry legacy,
        bool unchangedLegacySet,
        AnchorCatalog catalog,
        RepositorySnapshot snapshot,
        AnchorGovernance governance,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        if (!unchangedLegacySet)
        {
            findings.Add(new RuleFinding(
                path,
                $"legacy anchor '{legacy.Legacy}' cannot be added or changed; write canonical anchors"));
            return;
        }

        if (legacy.CaseId is not null
            && !CaseIsRegistered(legacy.CaseId, governance, out var caseReason))
        {
            findings.Add(new RuleFinding(
                path,
                $"legacy anchor '{legacy.Legacy}' has invalid target (InvalidTarget): {caseReason}"));
            return;
        }

        foreach (var canonical in legacy.CanonicalTargets)
        {
            var definition = catalog.Definitions[canonical];
            if (definition.Status == "registered-open"
                && !CaseIsRegistered(definition.CaseId!, governance, out caseReason))
            {
                findings.Add(new RuleFinding(
                    path,
                    $"legacy anchor '{legacy.Legacy}' has invalid target (InvalidTarget): {caseReason}"));
                return;
            }

            var target = ValidateTarget(definition, snapshot, governance);
            if (target.State is TargetState.InvalidTarget)
            {
                findings.Add(new RuleFinding(
                    path,
                    $"legacy anchor '{legacy.Legacy}' has invalid target (InvalidTarget): {target.Reason}"));
                return;
            }

            if (target.State is TargetState.Ambiguous)
            {
                findings.Add(new RuleFinding(
                    path,
                    $"legacy anchor '{legacy.Legacy}' is ambiguous (Ambiguous): {target.Reason}"));
                return;
            }
        }

        var disposition = legacy.Disposition == "grandfathered-unresolved"
            ? $"grandfathered unresolved under {legacy.CaseId}"
            : $"baseline grandfathered legacy anchor ({legacy.Disposition})";
        findings.Add(new RuleFinding(
            path,
            $"legacy anchor '{legacy.Legacy}' is {disposition}; migrate to canonical anchors",
            AdmissionEffect.Observe));
    }

    private static TargetCheck ValidateTarget(
        AnchorCatalogDefinition definition,
        RepositorySnapshot snapshot,
        AnchorGovernance governance)
    {
        if (definition.TargetKind == "theory-node")
        {
            var binding = ValidateTheorySourceBinding(definition, governance);
            if (binding.State is not TargetState.Resolved)
            {
                return binding;
            }
        }

        return definition.TargetKind == "mathlib-symbol"
            ? ValidateMathlibTarget(definition, snapshot)
            : ValidateLocalTarget(definition, snapshot);
    }

    private static TargetCheck ValidateLocalTarget(
        AnchorCatalogDefinition definition,
        RepositorySnapshot snapshot)
    {
        if (!snapshot.TryGetFile(definition.SourcePath, out var source))
        {
            return new TargetCheck(
                TargetState.InvalidTarget,
                "registered local source is missing: " + definition.SourcePath);
        }

        var actualHash = Convert.ToHexStringLower(SHA256.HashData(source.RawBytes.AsSpan()));
        if (!string.Equals(actualHash, definition.ExpectedSha256, StringComparison.Ordinal))
        {
            return new TargetCheck(
                TargetState.InvalidTarget,
                "source SHA-256 does not match the catalog receipt");
        }

        if (!AnchorCatalogLoader.TryParseStructuralSelector(
                definition.StructuralSelector,
                out var selector))
        {
            return new TargetCheck(TargetState.InvalidTarget, "structural selector is malformed");
        }

        var matches = CountSelectorMatches(source.Text, selector);
        return matches switch
        {
            0 => new TargetCheck(TargetState.InvalidTarget, "structural selector has no target"),
            1 => new TargetCheck(TargetState.Resolved),
            _ => new TargetCheck(TargetState.Ambiguous, "structural selector has multiple targets"),
        };
    }

    private static TargetCheck ValidateMathlibTarget(
        AnchorCatalogDefinition definition,
        RepositorySnapshot snapshot)
    {
        if (!snapshot.TryGetFile(definition.SourcePath, out var manifest))
        {
            return new TargetCheck(TargetState.InvalidTarget, "lake manifest is missing");
        }

        try
        {
            using var document = JsonDocument.Parse(manifest.Text);
            if (document.RootElement.ValueKind != JsonValueKind.Object
                || !document.RootElement.TryGetProperty("packages", out var packages)
                || packages.ValueKind != JsonValueKind.Array)
            {
                return new TargetCheck(TargetState.InvalidTarget, "lake manifest packages are malformed");
            }

            var revisions = packages.EnumerateArray()
                .Where(package =>
                    package.ValueKind == JsonValueKind.Object
                    && package.TryGetProperty("name", out var name)
                    && name.ValueKind == JsonValueKind.String
                    && string.Equals(name.GetString(), definition.SourceId, StringComparison.Ordinal))
                .Select(static package =>
                    package.TryGetProperty("rev", out var revision)
                    && revision.ValueKind == JsonValueKind.String
                        ? revision.GetString()
                        : null)
                .ToArray();
            return revisions.Length switch
            {
                0 => new TargetCheck(TargetState.InvalidTarget, "pinned package is absent"),
                > 1 => new TargetCheck(TargetState.Ambiguous, "pinned package occurs multiple times"),
                _ when !string.Equals(
                    revisions[0],
                    definition.SourceRevision,
                    StringComparison.Ordinal) =>
                    new TargetCheck(TargetState.InvalidTarget, "package revision does not match the catalog"),
                _ => new TargetCheck(TargetState.Resolved),
            };
        }
        catch (JsonException exception)
        {
            return new TargetCheck(
                TargetState.InvalidTarget,
                "lake manifest is malformed: " + exception.Message);
        }
    }

    private static TargetCheck ValidateTheorySourceBinding(
        AnchorCatalogDefinition definition,
        AnchorGovernance governance)
    {
        if (governance.Error is not null)
        {
            return new TargetCheck(TargetState.InvalidTarget, governance.Error);
        }

        if (!governance.TheorySources.TryGetValue(definition.SourceId, out var sourcePath)
            || !string.Equals(sourcePath, definition.SourcePath, StringComparison.Ordinal))
        {
            return new TargetCheck(
                TargetState.InvalidTarget,
                $"BACKFILL source {definition.SourceId} does not bind {definition.SourcePath}");
        }

        return new TargetCheck(TargetState.Resolved);
    }

    private static int CountSelectorMatches(
        string text,
        AnchorCatalogStructuralSelector selector)
    {
        var contextLevel = selector.HeadingPrefix is null
            ? 0
            : AnchorCatalogLoader.AtxHeadingLevel(selector.HeadingPrefix);
        var contextMatches = selector.HeadingPrefix is null;
        var matches = 0;
        foreach (var line in text.Split('\n'))
        {
            if (selector.HeadingPrefix is not null)
            {
                var headingLevel = AnchorCatalogLoader.AtxHeadingLevel(line);
                if (headingLevel is > 0 && headingLevel <= contextLevel)
                {
                    contextMatches = headingLevel == contextLevel
                        && line.StartsWith(selector.HeadingPrefix, StringComparison.Ordinal);
                }
            }

            if (contextMatches
                && line.StartsWith(selector.LinePrefix, StringComparison.Ordinal)
                && (selector.RequiredToken is null
                    || line.Contains(selector.RequiredToken, StringComparison.Ordinal)))
            {
                matches++;
            }
        }

        return matches;
    }

    private static ImmutableDictionary<string, ImmutableArray<string[]>> BaselineAnchorsByGid(
        RepositorySnapshot baseline) =>
        RepositoryRules.FormalFiles(baseline)
            .Select(static item => RepositoryRules.TryHeader(item.File.Text, out var header)
                ? header
                : null)
            .Where(static header => header is not null)
            .GroupBy(static header => header!.Gid, StringComparer.Ordinal)
            .ToImmutableDictionary(
                static group => group.Key,
                static group => group.Select(static header => header!.Anchors).ToImmutableArray(),
                StringComparer.Ordinal);

    private static bool AnchorMultisetsEqual(string[] current, string[] baseline) =>
        current.Order(StringComparer.Ordinal)
            .SequenceEqual(baseline.Order(StringComparer.Ordinal), StringComparer.Ordinal);

    private static AnchorGovernance LoadGovernance(RepositorySnapshot snapshot)
    {
        const string path = "Meta/BACKFILL.yaml";
        if (!snapshot.TryGetFile(path, out var file))
        {
            return new AnchorGovernance(
                new HashSet<string>(StringComparer.Ordinal),
                new Dictionary<string, string>(StringComparer.Ordinal),
                "BACKFILL source registry and ticket_index are missing");
        }

        try
        {
            var document = BackfillInventoryLoader.Load(file.Text);
            var cases = document.RequireTickets()
                .Select(static ticket => ticket.CaseId)
                .ToHashSet(StringComparer.Ordinal);
            if (!document.Root.TryGetValue("sources", out var rawSources)
                || rawSources is not List<object?> sources)
            {
                throw new FormatException("sources must be a list");
            }

            var sourceBindings = new Dictionary<string, string>(StringComparer.Ordinal);
            foreach (var rawSource in sources)
            {
                if (rawSource is not Dictionary<string, object?> source
                    || source.GetValueOrDefault("id") is not string sourceId
                    || source.GetValueOrDefault("path") is not string sourcePath
                    || !sourceBindings.TryAdd(sourceId, sourcePath))
                {
                    throw new FormatException("sources must uniquely bind scalar id and path values");
                }
            }

            return new AnchorGovernance(cases, sourceBindings, Error: null);
        }
        catch (FormatException exception)
        {
            return new AnchorGovernance(
                new HashSet<string>(StringComparer.Ordinal),
                new Dictionary<string, string>(StringComparer.Ordinal),
                "BACKFILL source registry or ticket_index is malformed: " + exception.Message);
        }
    }

    private static bool CaseIsRegistered(
        string caseId,
        AnchorGovernance governance,
        out string reason)
    {
        if (governance.Error is not null)
        {
            reason = governance.Error;
            return false;
        }

        if (!governance.Cases.Contains(caseId))
        {
            reason = $"case {caseId} is not registered in BACKFILL ticket_index";
            return false;
        }

        reason = string.Empty;
        return true;
    }
}
