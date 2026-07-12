using System.Collections.Immutable;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal sealed record RepositoryPathIssue(RuleId RuleId, string Path, string Message);

internal static class RepositoryPathPolicy
{
    private static readonly Regex CamelPattern = new(
        "^[A-Z][A-Za-z0-9]*$",
        RegexOptions.CultureInvariant);

    internal static ImmutableArray<Diagnostic> Evaluate(
        RepositorySnapshot snapshot,
        ValidatedPolicy policy,
        RuleDescriptor sl015)
    {
        return snapshot.Files.Keys
            .OrderBy(static path => path.Value, StringComparer.Ordinal)
            .Select(path => Validate(path, policy))
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
            or "Library/queries.yaml" or "D5/X_Assumptions/REGISTRY.md"
            or "Meta/split.py" or "Meta/papergen"
            or ".github/workflows/ci.yml" or ".github/CODEOWNERS"
            or ".github/scripts/baseline-admission.sh"
            || value.StartsWith("Meta/StrataLint/", StringComparison.Ordinal)
            || IsCanonicalFutureCoordinate(value))
        {
            return null;
        }

        if (IsCanonicalBlueprintDefinitionSource(value))
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
            _ => Sl000(value, "unknown top-level artifact"),
        };
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
        else if (coordinates is [var stratum, var domain, _]
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

    private static bool TryDescribeSemanticPath(
        string path,
        out string gid,
        out string label,
        out string? reason)
    {
        gid = string.Empty;
        reason = null;
        if (path.StartsWith("D5/", StringComparison.Ordinal))
        {
            label = "formal";
            if (!path.EndsWith(".lean", StringComparison.Ordinal))
            {
                reason = "path is not a canonical semantic artifact";
                return true;
            }

            gid = path[..^5];
            return true;
        }

        if (path.StartsWith("Blueprint/", StringComparison.Ordinal))
        {
            label = "Blueprint";
            if (!path.StartsWith("Blueprint/D5/", StringComparison.Ordinal)
                || !path.EndsWith(".md", StringComparison.Ordinal))
            {
                reason = "path is not a canonical semantic artifact";
                return true;
            }

            gid = "D5/B/" + path["Blueprint/D5/".Length..^3];
            return true;
        }

        if (path.StartsWith("Evidence/", StringComparison.Ordinal))
        {
            label = "Evidence";
            if (!path.StartsWith("Evidence/D5/", StringComparison.Ordinal))
            {
                reason = "path is not a canonical semantic artifact";
                return true;
            }

            var relative = path["Evidence/D5/".Length..];
            var slash = relative.LastIndexOf('/');
            var prefix = slash < 0 ? string.Empty : relative[..(slash + 1)];
            var file = slash < 0 ? relative : relative[(slash + 1)..];
            var pieces = file.Split('.');
            if (pieces.Length != 3)
            {
                reason = "Evidence filename needs module.selector.kind";
                return true;
            }

            gid = $"D5/E/{prefix}{pieces[0]}.{pieces[1]}--{pieces[2]}";
            return true;
        }

        var chronicle = Regex.Match(
            path,
            "^Chronicle/([0-9]{4})/([0-9]{2})/([0-9]{2})-([A-Za-z0-9_.-]+)\\.md$",
            RegexOptions.CultureInvariant);
        if (path.StartsWith("Chronicle/", StringComparison.Ordinal))
        {
            label = "Chronicle";
            if (!chronicle.Success)
            {
                reason = "path is not a canonical semantic artifact";
                return true;
            }

            gid = $"D5/C/{chronicle.Groups[1].Value}-{chronicle.Groups[2].Value}-{chronicle.Groups[3].Value}/{chronicle.Groups[4].Value}";
            return true;
        }

        if (path.StartsWith("Library/", StringComparison.Ordinal))
        {
            label = "Library";
            if (!path.StartsWith("Library/notes/", StringComparison.Ordinal)
                || !path.EndsWith(".md", StringComparison.Ordinal))
            {
                reason = "path is not a canonical semantic artifact";
                return true;
            }

            gid = "D5/L/" + path["Library/notes/".Length..^3];
            return true;
        }

        if (path.StartsWith("Papers/", StringComparison.Ordinal))
        {
            label = "Papers";
            if (path.StartsWith("Papers/recipes/", StringComparison.Ordinal)
                && path.EndsWith(".yaml", StringComparison.Ordinal))
            {
                gid = "D5/P/" + path["Papers/recipes/".Length..^5];
                return true;
            }

            var frozen = Regex.Match(
                path,
                "^Papers/frozen/(D5-P[0-9]{3})/manifest\\.sha256$",
                RegexOptions.CultureInvariant);
            if (frozen.Success)
            {
                gid = $"D5/P/{frozen.Groups[1].Value}--frozen";
                return true;
            }

            reason = "path is not a canonical semantic artifact";
            return true;
        }

        label = string.Empty;
        return false;
    }

    private static bool IsCanonicalBlueprintDefinitionSource(string path)
    {
        const string suffix = ".scribe.cs";
        if (!path.StartsWith("Blueprint/D5/", StringComparison.Ordinal)
            || !path.EndsWith(suffix, StringComparison.Ordinal))
        {
            return false;
        }

        var markdownPath = path[..^suffix.Length] + ".md";
        return TryDescribeSemanticPath(markdownPath, out var gidText, out _, out var reason)
            && reason is null
            && Gid.TryParse(gidText, out var gid)
            && string.Equals(gid.Path.Value, markdownPath, StringComparison.Ordinal);
    }

    private static string InferParseFailure(string path, string label)
    {
        var fileName = path[(path.LastIndexOf('/') + 1)..];
        var module = fileName.Split('.')[0];
        if (!CamelPattern.IsMatch(module) && label is "formal" or "Evidence")
        {
            return "formal module must be CamelCase";
        }

        if (label is "formal" or "Blueprint")
        {
            return "formal address must be Sn/Domain/Module or X_Zone/Module";
        }

        return "path is not a canonical semantic artifact";
    }

    private static bool IsCanonicalFutureCoordinate(string path)
    {
        var match = Regex.Match(
            path,
            "^(?<prefix>(?:Blueprint/|Evidence/)?)D(?<theory>[0-9]+)/",
            RegexOptions.CultureInvariant);
        if (!match.Success || match.Groups["theory"].Value == "5")
        {
            return false;
        }

        var candidate = path[..match.Groups["prefix"].Length]
            + "D5/"
            + path[(match.Index + match.Length)..];
        return RepoPath.TryCreate(candidate, out var candidatePath)
            && TryDescribeSemanticPath(candidate, out var gidText, out _, out var reason)
            && reason is null
            && Gid.TryParse(gidText, out var gid)
            && gid.Path == candidatePath;
    }

    private static RepositoryPathIssue Sl000(string path, string message) =>
        new(RuleId.CreateKnown(0), path, message);
}
