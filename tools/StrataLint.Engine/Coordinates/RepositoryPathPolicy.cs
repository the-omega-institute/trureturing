using System.Collections.Immutable;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal sealed record RepositoryPathIssue(RuleId RuleId, string Path, string Message);

[FindingEdgeProvider(15)]
internal static partial class RepositoryPathPolicy
{
    internal const string AgentFilesRootPath = "agents/";
    // Spec drafts and agent reports have author-chosen names, so this path layer admits
    // their prefixes without copying a filename registry into the harness. Reports have
    // a stricter, separate FILEMAP gate: FileMapPolicy requires one exact entry per
    // tracked docs/reports file before the file is usable. Path admission alone is not
    // registration and must not be treated as a substitute for filemap-conform.
    internal const string SpecRootPath = "docs/develop/spec/";
    internal const string ReportsRootPath = "docs/reports/";
    internal const string AssumptionRegistryPath = "D5/X_Assumptions/REGISTRY.md";
    internal const string WorkflowPath = ".github/workflows/ci.yml";
    // 缓存发布 workflow（#2542）。`.github` 下是白名单而非通配，新增控制工件必须在此具名登记。
    internal const string CachePublicationWorkflowPath =
        ".github/workflows/lean-cache-publish.yml";
    // Persistent truth-release publisher. `.github` remains an explicit allowlist.
    internal const string TruthReleasePublicationWorkflowPath =
        ".github/workflows/truth-release-publish.yml";
    internal const string AnalysisFixturesWorkflowPath =
        ".github/workflows/lean-analysis-fixtures.yml";
    internal const string HarnessGatePath = ".github/scripts/harness-gate.sh";
    internal const string RepositoryCoordinate = "the-omega-institute/trureturing";

    internal static bool ContainsRepositorySourceMaterializationIndicator(string value) =>
        value.StartsWith("./", StringComparison.Ordinal)
        || value.StartsWith("actions/checkout@", StringComparison.OrdinalIgnoreCase)
        || IsSelfRepositorySourceMaterializationIndicator(value)
        || RepositorySourceMaterializationIndicator().IsMatch(value);

    internal static bool ContainsRepositorySourceExecutionIndicator(string value) =>
        RepositorySourceExecutionIndicator().IsMatch(value);

    private static bool IsSelfRepositorySourceMaterializationIndicator(string value) =>
        value.StartsWith($"{RepositoryCoordinate}/", StringComparison.OrdinalIgnoreCase)
        && RepositorySelfSourceMaterializationIndicator().IsMatch(value[RepositoryCoordinate.Length..]);

    [GeneratedRegex(
        @"^/[^@\s]+@[^@\s]+$",
        RegexOptions.IgnoreCase | RegexOptions.CultureInvariant)]
    private static partial Regex RepositorySelfSourceMaterializationIndicator();

    [GeneratedRegex(
        @"(?:^|[\s;&|])(?:git\s+(?:clone|fetch|checkout|switch|worktree)\b|gh\s+repo\s+clone\b)",
        RegexOptions.IgnoreCase | RegexOptions.CultureInvariant)]
    private static partial Regex RepositorySourceMaterializationIndicator();

    [GeneratedRegex(
        @"(?:^|[\s;&|])(?:dotnet\s+(?:build|run|test)\b|lake(?:\s|$)|make\s+|run\s+--project\b|(?:\./)?(?:tools|scripts)/|(?:bash|sh|source|python\d*|node)\s+\./)",
        RegexOptions.IgnoreCase | RegexOptions.CultureInvariant)]
    private static partial Regex RepositorySourceExecutionIndicator();

    internal static ImmutableArray<Diagnostic> Evaluate(
        RepositorySnapshot snapshot,
        ValidatedPolicy policy,
        RuleDescriptor sl015,
        Func<string, bool>? shouldEvaluatePath = null)
        => EvaluatePathFindings(snapshot, policy, sl015, shouldEvaluatePath)
            .AddRange(EvaluateCompositionFindings(snapshot, sl015, shouldEvaluatePath));

    [FindingEdge(FindingEdgeKind.Local)]
    internal static ImmutableArray<Diagnostic> EvaluatePathFindings(
        RepositorySnapshot snapshot,
        ValidatedPolicy policy,
        RuleDescriptor sl015,
        Func<string, bool>? shouldEvaluatePath = null)
    {
        var diagnostics = snapshot.Files.Keys
            .OrderBy(static path => path.Value, StringComparer.Ordinal)
            .Select(path => shouldEvaluatePath is null || shouldEvaluatePath(path.Value)
                ? Validate(path, policy)
                : null)
            .OfType<RepositoryPathIssue>()
            .Select(issue => issue is { RuleId.Value: "SL-000" }
                ? new Diagnostic(
                    issue.RuleId,
                    "Repository entry shape",
                    DisplaySeverity.Error,
                    AdmissionEffect.Block,
                    issue.Path,
                    issue.Message)
                : new Diagnostic(
                    sl015.Id,
                    sl015.Title,
                    sl015.DisplaySeverity,
                    sl015.AdmissionEffect,
                    issue.Path,
                    issue.Message))
            .ToImmutableArray();

        return diagnostics;
    }

    [FindingEdge(FindingEdgeKind.Interaction)]
    internal static ImmutableArray<Diagnostic> EvaluateCompositionFindings(
        RepositorySnapshot snapshot,
        RuleDescriptor sl015,
        Func<string, bool>? shouldEvaluatePath = null)
    {
        var compositionProjects = snapshot.Files.Keys
            .Where(static path => IsBlueprintContentCompositionBuildFile(path.Value)
                && path.Value.EndsWith(".csproj", StringComparison.Ordinal))
            .OrderBy(static path => path.Value, StringComparer.Ordinal)
            .ToArray();
        if (compositionProjects.Length > 1
            && compositionProjects.Any(path =>
                shouldEvaluatePath is null || shouldEvaluatePath(path.Value)))
        {
            return compositionProjects.Skip(1).Select(path => new Diagnostic(
                    sl015.Id,
                    sl015.Title,
                    sl015.DisplaySeverity,
                    sl015.AdmissionEffect,
                    path.Value,
                    "Blueprint composition root allows at most one direct .csproj"))
                .ToImmutableArray();
        }

        return [];
    }

    internal static RepositoryPathIssue? Validate(RepoPath path, ValidatedPolicy policy)
    {
        var value = path.Value;
        var matches = policy.Manifest.Match(value);
        if (matches is not [var entry])
            return Sl000(value, $"path must match exactly one FILEMAP entry; matches={matches.Length}");
        if (value.StartsWith(ReportsRootPath, StringComparison.Ordinal) && entry.Pattern != value)
            return Sl000(value, "docs/reports files require an exact FILEMAP entry");

        // Non-coordinate files derive membership solely from FILEMAP. Coordinate
        // planes still pass their canonical path, GID and domain checks below.
        if ((!value.Contains('/') || value.StartsWith(AgentFilesRootPath, StringComparison.Ordinal) || entry.Pattern == value)
            && !value.StartsWith("D5/", StringComparison.Ordinal)
            && !value.StartsWith("Blueprint/", StringComparison.Ordinal)
            && !value.StartsWith("Evidence/", StringComparison.Ordinal)
            && !value.StartsWith("Library/", StringComparison.Ordinal)
            && !value.StartsWith("Papers/", StringComparison.Ordinal)
            && !value.StartsWith("Chronicle/", StringComparison.Ordinal)
            && !value.StartsWith("Meta/Digestion/", StringComparison.Ordinal)
            && !value.StartsWith("Golden/", StringComparison.Ordinal))
            return null;

        if (value is "Meta/domains.yaml" or "Meta/BACKFILL.yaml" or "Meta/FILEMAP.toml"
            or "Library/queries.yaml" or AssumptionRegistryPath
            or "D5/X_Frontier/HeartsAuthorizations.md"
            or "Golden/values-kernels.toml" or "Golden/gate-authority-roots.toml"
            or "Meta/Digestion/atomizers.toml"
            or WorkflowPath
            or CachePublicationWorkflowPath
            or TruthReleasePublicationWorkflowPath
            or AnalysisFixturesWorkflowPath
            or ".github/CODEOWNERS"
            or HarnessGatePath
            || value.StartsWith("tools/", StringComparison.Ordinal)
            || DigestionCasStore.IsCanonicalPath(value)
            || BackfillInventoryLoader.IsCanonicalPath(value)
            || IsEchoResidualShardPath(value)
            || ProblemPoolPaths.IsCanonicalPath(value)
            || FrozenLedgerChangeClassifier.IsAcceptedEventPath(value)
            || FrozenStatePath.TryToModulePath(value, out _)
            || value.StartsWith("skills/", StringComparison.Ordinal)
            || value.StartsWith(".codex/skills/", StringComparison.Ordinal)
            || value.StartsWith(ReportsRootPath, StringComparison.Ordinal)
            // Report filenames have explicit FILEMAP membership. Their
            // exact per-file registration is enforced by FILEMAP's content-plane gate.
            || value.StartsWith(DigestionOpaquePathPolicy.TheoryRootPath, StringComparison.Ordinal)
            || value.StartsWith(SpecRootPath, StringComparison.Ordinal)
            || IsGoldenProjectionData(value)
            || IsCanonicalFutureCoordinate(value))
        {
            return null;
        }

        if (IsCanonicalBlueprintDefinitionSource(value))
        {
            return null;
        }

        if (IsBlueprintContentCompositionBuildFile(value))
        {
            return null;
        }

        if (TryDescribeSemanticPath(value, out var gidText, out var label, out var reason))
        {
            if (reason is not null
                || !Gid.TryParse(gidText, out var gid)
                || gid.Path != path)
            {
                return Sl000(
                    value,
                    $"noncanonical {label} artifact: {reason ?? InferParseFailure(value, label)}");
            }

            return AllowsTarget(gid.ToTarget(), policy)
                ? null
                : new RepositoryPathIssue(
                    RuleId.CreateKnown(15),
                    value,
                    "path is outside the FILEMAP Evidence policy or controlled domain vocabulary");
        }

        var top = value.Split('/', 2)[0];
        return top switch
        {
            ".github" => Sl000(value, "unknown GitHub control artifact"),
            "Meta" => Sl000(value, "unknown Meta artifact"),
            "tools" => Sl000(value, "unknown tools artifact"),
            _ => Sl000(value, "unknown top-level artifact"),
        };
    }

    internal static bool IsEchoResidualShardPath(string value)
    {
        const string prefix = "Generated/echo-residuals/";
        if (!value.StartsWith(prefix, StringComparison.Ordinal)
            || !value.EndsWith(".md", StringComparison.Ordinal)) return false;
        var relative = value[prefix.Length..];
        return relative.Length > ".md".Length && !relative.Contains('/', StringComparison.Ordinal);
    }

    internal static bool TryResolve(RepoPath path, ValidatedPolicy policy, out Gid? gid)
    {
        gid = null;
        return Validate(path, policy) is null
            && TryResolve(path, out gid);
    }

    internal static bool TryGetValidationProfile(
        RepoPath path,
        ValidatedPolicy policy,
        out string? profile)
    {
        profile = null;
        if (!TryResolve(path, policy, out var gid)
            || gid?.ToTarget() is not Target.Evidence evidence
            || !policy.ArtifactKinds.TryGetValue(evidence.ArtifactKind, out var artifact))
        {
            return false;
        }

        profile = artifact.Profile switch
        {
            ValidationProfile.StructuredJson => "structured-json",
            ValidationProfile.StructuredYaml => "structured-yaml",
            ValidationProfile.LeanModule => "lean-module",
            ValidationProfile.OpaqueText => "opaque-text",
        };
        return true;
    }

    internal static ImmutableArray<string> RegistrationSources(
        RepoPath path,
        ValidatedPolicy policy)
    {
        var sources = ImmutableArray.CreateBuilder<string>();
        if (Validate(path, policy) is null) sources.Add("path-policy");
        if (policy.Manifest.Match(path.Value) is [var entry]) sources.Add("filemap:files:" + entry.Pattern);

        if (TryResolve(path, policy, out var gid) && gid is not null)
        {
            if (gid.ToTarget() is Target.Evidence evidence
                && policy.ArtifactKinds.ContainsKey(evidence.ArtifactKind))
            {
                sources.Add("filemap:artifact-kinds");
            }

            if (HasControlledDomain(path, policy)) sources.Add("domains");
        }

        return sources.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToImmutableArray();
    }

    internal static bool TryResolve(RepoPath path, out Gid? gid)
    {
        gid = null;
        return TryDescribeSemanticPath(path.Value, out var gidText, out _, out var reason)
            && reason is null
            && Gid.TryParse(gidText, out gid)
            && gid.Path == path;
    }

    private static bool AllowsTarget(Target target, ValidatedPolicy policy)
    {
        if (target is Target.Library library)
        {
            var libraryCoordinates = library.Coordinates.Values;
            return libraryCoordinates.Length == 1
                || libraryCoordinates is [var bucket, _]
                && DomainId.TryCreate(bucket, out var domain)
                && policy.Domains.ContainsKey(domain);
        }

        if (target is not Target.Evidence evidence)
        {
            var targetPath = target switch
            {
                Target.Formal formal => formal.Path,
                Target.Blueprint blueprint => blueprint.Path,
                _ => null,
            };
            if (targetPath is null) return true;
            var path = targetPath.Value;
            var parts = path.Split('/');
            var offset = parts[0] == "Blueprint" ? 1 : 0;
            return parts.Length <= offset + 1 || parts[offset] != "D5"
                || !Enum.TryParse<Stratum>(parts[offset + 1], false, out _)
                || HasControlledDomain(targetPath, policy);
        }

        if (!policy.ArtifactKinds.TryGetValue(evidence.ArtifactKind, out var artifact)
            || !artifact.Selectors.Contains(evidence.Selector))
        {
            return false;
        }

        var coordinates = evidence.Coordinates.Values;
        string scope;
        if (coordinates is ["values"])
        {
            scope = "values";
        }
        else if (coordinates is ["experiments", _])
        {
            scope = "experiments";
        }
        else if (coordinates is ["kernels", _])
        {
            scope = "kernels";
        }
        else if (coordinates is [var special, _]
            && special is "X_Assumptions" or "X_Certificates" or "X_Frontier")
        {
            scope = "special";
        }
        else if (coordinates.Length >= 3
            && coordinates[0] is var stratum
            && coordinates[1] is var domain
            && Enum.TryParse<Stratum>(stratum, ignoreCase: false, out var parsedStratum)
            && DomainId.TryCreate(domain, out var domainId)
            && policy.Domains.TryGetValue(domainId, out var registeredStratum)
            && registeredStratum == parsedStratum)
        {
            scope = "formal";
        }
        else
        {
            return false;
        }

        return artifact.PathSelectors.Contains(scope);
    }

    private static bool HasControlledDomain(RepoPath path, ValidatedPolicy policy)
    {
        var parts = path.Value.Split('/');
        var offset = parts[0] is "Blueprint" or "Evidence" ? 1 : 0;
        if (parts.Length <= offset + 2
            || parts[offset] != "D5"
            || !Enum.TryParse<Stratum>(parts[offset + 1], ignoreCase: false, out var stratum)
            || !DomainId.TryCreate(parts[offset + 2], out var domain))
        {
            return false;
        }

        return policy.Domains.TryGetValue(domain, out var registered) && registered == stratum;
    }

    private static bool IsGoldenProjectionData(string path)
    {
        const string prefix = "Golden/Projection/";
        const string suffix = ".json";
        if (!path.StartsWith(prefix, StringComparison.Ordinal)
            || !path.EndsWith(suffix, StringComparison.Ordinal))
        {
            return false;
        }

        var stem = path[prefix.Length..^suffix.Length];
        return stem.Length > 0 && stem.All(static character =>
            char.IsAsciiLetterOrDigit(character) || character is '_' or '-');
    }

    private static RepositoryPathIssue Sl000(string path, string message) =>
        new(RuleId.CreateKnown(0), path, message);
}
