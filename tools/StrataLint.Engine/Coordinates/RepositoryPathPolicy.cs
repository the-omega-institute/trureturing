using System.Collections.Immutable;

namespace StrataLint.Engine;

internal sealed record RepositoryPathIssue(RuleId RuleId, string Path, string Message);

internal static partial class RepositoryPathPolicy
{
    internal const string AssumptionRegistryPath = "D5/X_Assumptions/REGISTRY.md";
    internal const string WorkflowPath = ".github/workflows/ci.yml";
    // 缓存发布 workflow（#2542）。`.github` 下是白名单而非通配，新增控制工件必须在此具名登记。
    internal const string CachePublicationWorkflowPath =
        ".github/workflows/lean-cache-publish.yml";
    internal const string HarnessGatePath = ".github/scripts/harness-gate.sh";

    // harness 不治理的 agent 运行时配置目录。内容属于本地 agent 运行时（Claude Code / codex CLI）：
    // 工具自己的配置，以及指向仓库内目录的链接。快照是 (路径 -> 字节) 的映射，symlink 在其中没有
    // 表示形式——读链接本身会把一个路径串当作内容，跟随链接则要么让同一份字节在两个路径下出现，
    // 要么走出仓库。这些目录整体退出快照、索引枚举与 changed-path 判词，harness 不看它们。
    // 具名而非按 "." 前缀通配：.github 同为点目录，却承载 required check 定义、CODEOWNERS 与
    // harness gate 脚本，必须留在治理面。新增 agent 运行时须在此具名登记。
    private static readonly ImmutableArray<string> UngovernedAgentConfigRoots =
        [".claude/", ".codex/"];

    internal static bool IsUngovernedAgentConfig(string value)
    {
        foreach (var root in UngovernedAgentConfigRoots)
        {
            if (value.StartsWith(root, StringComparison.Ordinal))
            {
                return true;
            }
        }

        return false;
    }

    internal static ImmutableArray<Diagnostic> Evaluate(
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

        var compositionProjects = snapshot.Files.Keys
            .Where(static path => IsBlueprintContentCompositionBuildFile(path.Value)
                && path.Value.EndsWith(".csproj", StringComparison.Ordinal))
            .OrderBy(static path => path.Value, StringComparer.Ordinal)
            .ToArray();
        if (compositionProjects.Length > 1)
        {
            diagnostics = diagnostics.AddRange(
                compositionProjects.Skip(1).Select(path => new Diagnostic(
                    sl015.Id,
                    sl015.Title,
                    sl015.DisplaySeverity,
                    sl015.AdmissionEffect,
                    path.Value,
                    "Blueprint composition root allows at most one direct .csproj")));
        }

        return diagnostics;
    }

    internal static RepositoryPathIssue? Validate(RepoPath path, ValidatedPolicy policy)
    {
        var value = path.Value;
        if (policy.RootFiles.Contains(path) || policy.GovernanceDocuments.Contains(path))
        {
            return null;
        }

        if (value.StartsWith("agents/", StringComparison.Ordinal))
        {
            return policy.AgentFiles.Contains(value["agents/".Length..])
                ? null
                : Sl000(value, "unknown agent charter artifact");
        }

        if (value is "Meta/domains.yaml" or "Meta/BACKFILL.yaml" or "Meta/registry.yaml"
            or "Library/queries.yaml" or AssumptionRegistryPath
            or "tools/tests/StrataLint.Tests/Fixtures/fixture-registry.yaml"
            or "Golden/values-kernels.toml"
            or WorkflowPath
            or CachePublicationWorkflowPath
            or ".github/CODEOWNERS"
            or HarnessGatePath
            || value.StartsWith("tools/", StringComparison.Ordinal)
            || DigestionCasStore.IsCanonicalPath(value)
            || BackfillInventoryLoader.IsCanonicalPath(value)
            || DigestionFormalizationReceipt.IsCanonicalPath(value)
            || IsEchoResidualShardPath(value)
            || ProblemPoolPaths.IsCanonicalPath(value)
            || FrozenLedgerChangeClassifier.IsAcceptedEventPath(value)
            || value.StartsWith("skills/", StringComparison.Ordinal)
            || value.StartsWith(".codex/skills/", StringComparison.Ordinal)
            || value.StartsWith("docs/reports/", StringComparison.Ordinal)
            // 理论卷与 docs/reports/ 同性质:第三方 PR 带进来的卷名无法预先枚举,
            // 逐个写进 registry.yaml 会让「加一个 markdown」被迫改 harness
            // (CLAUDE.md 商余结构:harness 存规则,不存代表元)。
            || value.StartsWith(DigestionOpaquePathPolicy.TheoryRootPath, StringComparison.Ordinal)
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
                    "path is outside the registry artifact kind/selector whitelist");
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
        if (policy.RootFiles.Contains(path)) sources.Add("registry:root-files");
        if (policy.GovernanceDocuments.Contains(path)) sources.Add("registry:governance-documents");
        if (path.Value.StartsWith("agents/", StringComparison.Ordinal)
            && policy.AgentFiles.Contains(path.Value["agents/".Length..]))
        {
            sources.Add("registry:agent-files");
        }

        if (TryResolve(path, policy, out var gid) && gid is not null)
        {
            if (gid.ToTarget() is Target.Evidence evidence
                && policy.ArtifactKinds.ContainsKey(evidence.ArtifactKind))
            {
                sources.Add("registry:artifact-kinds");
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
            return true;
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
        else if (coordinates.Length is 3 or 4
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
