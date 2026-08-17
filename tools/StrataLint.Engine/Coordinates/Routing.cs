using System.Collections.Immutable;
using System.Text.RegularExpressions;
using Dunet;

namespace StrataLint.Engine;

public sealed record ManifestSyntax(
    string Theory,
    string Plane,
    string Domain,
    string Module,
    string Generality,
    string Selector,
    string Artifact,
    string Tag,
    string? SubDomain = null);

public sealed class ValidatedManifest
{
    private ValidatedManifest(ManifestSyntax syntax) => Syntax = syntax;

    internal ManifestSyntax Syntax { get; }

    internal static ValidatedManifest Create(ManifestSyntax syntax) => new(syntax);
}

public sealed record RouteResult(
    Gid Gid,
    RepoPath Path,
    Stratum? Stratum,
    ImmutableArray<string> Skeleton);

[Union(EnableImplicitConversions = false)]
public partial record RouteOutcome
{
    public partial record Routed(ValidatedManifest Manifest, RouteResult Result);

    public partial record Rejected(RuleId RuleId, string Message);
}

[Union(EnableImplicitConversions = false)]
public partial record ManifestLoadOutcome
{
    public partial record Loaded(ManifestSyntax Syntax);

    public partial record InfrastructureFailure(string Message);
}

public static class RouteEngine
{
    private static readonly Regex CamelPattern = new(
        "^[A-Z][A-Za-z0-9]*$",
        RegexOptions.CultureInvariant);

    private static readonly Regex SafeSegmentPattern = new(
        "^[A-Za-z0-9_.-]+$",
        RegexOptions.CultureInvariant);

    private static readonly Regex DatePattern = new(
        "^[0-9]{4}-[0-9]{2}-[0-9]{2}$",
        RegexOptions.CultureInvariant);

    private static readonly Regex PaperPattern = new(
        "^D5-P[0-9]{3}$",
        RegexOptions.CultureInvariant);

    private static readonly Regex ExperimentPattern = new(
        "^D5-X[0-9]{4}$",
        RegexOptions.CultureInvariant);

    public static RouteOutcome Route(ValidatedPolicy policy, ManifestSyntax syntax)
    {
        ArgumentNullException.ThrowIfNull(policy);
        ArgumentNullException.ThrowIfNull(syntax);
        try
        {
            if (syntax.Theory != "D5")
            {
                return new RouteOutcome.Rejected(
                    RuleId.CreateKnown(21),
                    $"{syntax.Theory} is uninstantiated under D5-T0009");
            }

            if (syntax.Generality is not ("G" or "I" or "E"))
            {
                throw new FormatException("generality must be G, I, or E");
            }

            ValidateSubDomainApplicability(syntax);

            var (gidText, stratum) = syntax.Plane switch
            {
                "F" => Formal(policy, syntax, blueprint: false),
                "B" => Formal(policy, syntax, blueprint: true),
                "E" => Evidence(policy, syntax),
                "C" => Chronicle(syntax),
                "L" => Library(policy, syntax),
                "P" => Paper(syntax),
                _ => throw new FormatException("unknown manifest plane"),
            };
            if (!Gid.TryParse(gidText, out var gid))
            {
                throw new FormatException("routed GID is not canonical");
            }

            if (!RepositoryPathPolicy.TryResolve(gid.Path, policy, out var reverse)
                || reverse is null
                || !reverse.Equals(gid))
            {
                throw new FormatException("routed path does not have a policy-admitted GID inverse");
            }

            var validated = ValidatedManifest.Create(syntax);
            return new RouteOutcome.Routed(
                validated,
                new RouteResult(gid, gid.Path, stratum, Skeleton(syntax, gid)));
        }
        catch (FormatException exception)
        {
            return new RouteOutcome.Rejected(RuleId.CreateKnown(15), exception.Message);
        }
    }

    private static (string Gid, Stratum? Stratum) Formal(
        ValidatedPolicy policy,
        ManifestSyntax syntax,
        bool blueprint)
    {
        var coordinates = Coordinates(policy, syntax.Domain, syntax.SubDomain, syntax.Module);
        if (!blueprint)
        {
            if (syntax.Artifact != "lean" || syntax.Tag.Length != 0)
            {
                throw new FormatException("F manifest requires artifact=lean and empty tag");
            }

            if (syntax.Selector.Length > 0
                && !Regex.IsMatch(syntax.Selector, "^[A-Za-z_][A-Za-z0-9_]*$", RegexOptions.CultureInvariant))
            {
                throw new FormatException("F selector is not a canonical declaration");
            }
        }
        else if (syntax.Artifact != "markdown" || syntax.Selector.Length != 0 || syntax.Tag.Length != 0)
        {
            throw new FormatException("B manifest requires markdown and empty selector/tag");
        }

        var prefix = blueprint ? "D5/B/" : "D5/";
        var gid = prefix + string.Join('/', coordinates.Parts)
            + (!blueprint && syntax.Selector.Length > 0 ? $".{syntax.Selector}" : string.Empty);
        return (gid, coordinates.Stratum);
    }

    private static (string Gid, Stratum? Stratum) Evidence(
        ValidatedPolicy policy,
        ManifestSyntax syntax)
    {
        if (syntax.Tag.Length != 0
            || syntax.Selector.Length == 0
            || !SafeSegment(syntax.Selector)
            || !ArtifactKindId.TryCreate(syntax.Artifact, out var artifactId)
            || !policy.ArtifactKinds.TryGetValue(artifactId, out var artifact))
        {
            throw new FormatException("E manifest references an unknown artifact kind or selector");
        }

        string scope;
        string coordinates;
        Stratum? stratum = null;
        if (syntax.Domain == "values")
        {
            scope = "values";
            if (syntax.Module != "values"
                || syntax.Selector != "result"
                || artifactId.Value != "json")
            {
                throw new FormatException(
                    "values route requires module=values, selector=result, and artifact=json");
            }

            coordinates = syntax.Module;
        }
        else if (syntax.Domain == "experiments")
        {
            scope = "experiments";
            if (!ExperimentPattern.IsMatch(syntax.Module)) throw new FormatException("experiment id is not canonical");
            coordinates = $"experiments/{syntax.Module}";
        }
        else if (syntax.Domain == "kernels")
        {
            scope = "kernels";
            if (!CamelPattern.IsMatch(syntax.Module)) throw new FormatException("kernel module is not CamelCase");
            coordinates = $"kernels/{syntax.Module}";
        }
        else
        {
            var routed = Coordinates(policy, syntax.Domain, syntax.SubDomain, syntax.Module);
            scope = syntax.Domain.StartsWith("X_", StringComparison.Ordinal) ? "special" : "formal";
            coordinates = string.Join('/', routed.Parts);
            stratum = routed.Stratum;
        }

        if (!artifact.Selectors.Contains(syntax.Selector) || !artifact.PathSelectors.Contains(scope))
        {
            throw new FormatException(
                $"artifact kind {artifactId.Value} does not allow selector {syntax.Selector} in scope {scope}");
        }

        return syntax.Domain == "values"
            ? ("D5/E/values--json", stratum)
            : ($"D5/E/{coordinates}.{syntax.Selector}--{artifactId.Value}", stratum);
    }

    private static (string Gid, Stratum? Stratum) Chronicle(ManifestSyntax syntax)
    {
        if (!DatePattern.IsMatch(syntax.Domain)
            || !SafeSegment(syntax.Module)
            || syntax.Artifact != "markdown"
            || syntax.Selector.Length != 0
            || syntax.Tag.Length != 0)
        {
            throw new FormatException("C manifest is not canonical");
        }

        return ($"D5/C/{syntax.Domain}/{syntax.Module}", null);
    }

    private static (string Gid, Stratum? Stratum) Library(
        ValidatedPolicy policy,
        ManifestSyntax syntax)
    {
        if (!SafeSegment(syntax.Module)
            || syntax.Artifact != "markdown"
            || syntax.Selector.Length != 0
            || syntax.Tag.Length != 0)
        {
            throw new FormatException("L manifest is not canonical");
        }

        if (syntax.Domain == "Notes")
        {
            return ($"D5/L/{syntax.Module}", null);
        }

        if (!DomainId.TryCreate(syntax.Domain, out var domain)
            || !policy.Domains.ContainsKey(domain))
        {
            throw new FormatException("L split bucket requires a controlled domain");
        }

        return ($"D5/L/{syntax.Domain}/{syntax.Module}", null);
    }

    private static (string Gid, Stratum? Stratum) Paper(ManifestSyntax syntax)
    {
        if (syntax.Domain != "Papers"
            || !PaperPattern.IsMatch(syntax.Module)
            || syntax.Selector.Length != 0
            || (syntax.Artifact, syntax.Tag) is not (("recipe", "") or ("frozen", "frozen")))
        {
            throw new FormatException("P manifest is not canonical");
        }

        return ($"D5/P/{syntax.Module}" + (syntax.Tag.Length == 0 ? string.Empty : "--frozen"), null);
    }

    private static (ImmutableArray<string> Parts, Stratum? Stratum) Coordinates(
        ValidatedPolicy policy,
        string domain,
        string? subDomain,
        string module)
    {
        if (!CamelPattern.IsMatch(module))
        {
            throw new FormatException("module must be CamelCase");
        }

        if (domain is "X_Assumptions" or "X_Certificates" or "X_Frontier")
        {
            if (subDomain is null)
            {
                return (ImmutableArray.Create(domain, module), null);
            }

            if (!string.Equals(domain, "X_Frontier", StringComparison.Ordinal))
            {
                throw new FormatException("special-zone route cannot have a subdomain");
            }

            if (!CamelPattern.IsMatch(subDomain))
            {
                throw new FormatException("subdomain must be CamelCase");
            }

            return (ImmutableArray.Create(domain, subDomain, module), null);
        }

        if (subDomain is not null && !CamelPattern.IsMatch(subDomain))
        {
            throw new FormatException("subdomain must be CamelCase");
        }

        if (string.Equals(subDomain, domain, StringComparison.Ordinal))
        {
            throw new FormatException("subdomain must differ from domain");
        }

        var match = policy.Domains.FirstOrDefault(
            item => string.Equals(item.Key.Value, domain, StringComparison.Ordinal));
        if (match.Key is null)
        {
            throw new FormatException("formal route requires a controlled domain");
        }

        return subDomain is null
            ? (ImmutableArray.Create(match.Value.ToString(), domain, module), match.Value)
            : (ImmutableArray.Create(match.Value.ToString(), domain, subDomain, module), match.Value);
    }

    internal static void ValidateSubDomainApplicability(ManifestSyntax syntax)
    {
        if (syntax.SubDomain is null)
        {
            return;
        }

        if (syntax.SubDomain.Length == 0)
        {
            throw new FormatException("subdomain must not be empty");
        }

        if (syntax.Plane is "F" or "B"
            || syntax.Plane == "E" && syntax.Domain is not ("values" or "experiments" or "kernels"))
        {
            return;
        }

        throw new FormatException("subdomain is only allowed for F, B, or formal E manifests");
    }

    private static ImmutableArray<string> Skeleton(ManifestSyntax syntax, Gid gid) => syntax.Plane switch
    {
        "F" => ImmutableArray.Create(
            $"/- GID: {gid.Value.Split('.')[0]}",
            $"   generality: {syntax.Generality}",
            $"   mirror-B: D5/B/{string.Join('/', gid.Value.Split('/').Skip(1)).Split('.')[0]}",
            "   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)",
            "   anchors: []",
            "   digest: EDIT-ME -/"),
        "B" or "C" or "L" => ImmutableArray.Create($"<!-- GID: {gid.Value} -->", $"# {syntax.Module}", string.Empty, "EDIT-ME"),
        "E" when syntax.Artifact == "json" => ImmutableArray.Create("{", $"  \"gid\": \"{gid.Value}\",", "  \"result\": \"EDIT-ME\"", "}"),
        "E" => ImmutableArray.Create($"gid: {gid.Value}", "result: EDIT-ME"),
        "P" when syntax.Artifact == "frozen" => ImmutableArray.Create("EDIT-ME  manifest.sha256"),
        "P" => ImmutableArray.Create($"id: {syntax.Module}", "decls: []", "blueprint: []", "evidence: []", "venue: EDIT-ME"),
        _ => throw new InvalidOperationException("Unknown routed plane."),
    };

    private static bool SafeSegment(string value) =>
        value is not "." and not ".." && SafeSegmentPattern.IsMatch(value);
}

internal static class RouteCapacityPreflight
{
    internal static string? Evaluate(
        RawRepositorySnapshot repository,
        ValidatedPolicy policy,
        Stratum? stratum,
        Target.Formal target) =>
        Evaluate(repository, policy, stratum, ProjectedOutputs(target));

    internal static string? Evaluate(
        RawRepositorySnapshot repository,
        ValidatedPolicy policy,
        Stratum? stratum,
        Target.Blueprint target) =>
        Evaluate(repository, policy, stratum, ProjectedOutputs(target));

    private static string? Evaluate(
        RawRepositorySnapshot repository,
        ValidatedPolicy policy,
        Stratum? stratum,
        IEnumerable<string> projectedOutputs)
    {
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(policy);

        var currentPaths = repository.Entries
            .Select(static entry => entry.Path)
            .Where(static path => !RepositoryRules.IsCapacityExcluded(path))
            .Distinct(StringComparer.Ordinal)
            .ToHashSet(StringComparer.Ordinal);
        var stratumDomains = stratum is { } routeStratum
            ? policy.Domains
                .Where(item => item.Value == routeStratum)
                .Select(static item => item.Key.Value)
                .ToArray()
            : [];
        var failures = projectedOutputs
            .Where(static path => !RepositoryRules.IsCapacityExcluded(path))
            .GroupBy(DirectoryOf, StringComparer.Ordinal)
            .Select(group => CapacityFailure(currentPaths, stratumDomains, group.Key, group))
            .Where(static failure => failure is not null)
            .Select(static failure => failure!)
            .ToArray();

        return failures.Length == 0 ? null : string.Join(" ", failures);
    }

    private static IEnumerable<string> ProjectedOutputs(Target.Formal target)
    {
        const string blueprintPrefix = "Blueprint/";
        var routedPath = target.Path.Value;
        var stem = routedPath[..^".lean".Length];
        yield return routedPath;
        yield return $"{blueprintPrefix}{stem}.scribe.cs";
        yield return $"{blueprintPrefix}{stem}.md";
    }

    private static IEnumerable<string> ProjectedOutputs(Target.Blueprint target)
    {
        const string blueprintPrefix = "Blueprint/";
        var routedPath = target.Path.Value;
        var blueprintStem = routedPath[..^".md".Length];
        var leanStem = blueprintStem[blueprintPrefix.Length..];
        yield return $"{leanStem}.lean";
        yield return $"{blueprintStem}.scribe.cs";
        yield return routedPath;
    }

    private static string? CapacityFailure(
        IReadOnlySet<string> currentPaths,
        IReadOnlyCollection<string> stratumDomains,
        string targetDirectory,
        IEnumerable<string> projectedOutputs)
    {
        // This preflight exists to predict SL-003, so it must count exactly what SL-003
        // counts. Reusing IsCapacityExcluded keeps the two in one source: a preflight that
        // bounded artifacts the rule itself exempts would refuse addresses the gate would
        // have admitted, which is a stricter policy invented in the wrong place.
        var currentOccupancy = currentPaths.Count(path =>
            DirectoryOf(path) == targetDirectory && !RepositoryRules.IsCapacityExcluded(path));
        var additions = projectedOutputs.Count(path =>
            !currentPaths.Contains(path) && !RepositoryRules.IsCapacityExcluded(path));
        var projectedOccupancy = currentOccupancy + additions;
        if (projectedOccupancy <= RepositoryRules.DirectoryFileLimit)
        {
            return null;
        }

        var stratumRoot = DirectoryOf(targetDirectory);
        var bucketPrefix = stratumRoot == "." ? string.Empty : stratumRoot + "/";
        var targetBucket = targetDirectory[(targetDirectory.LastIndexOf('/') + 1)..];
        var policySiblings = stratumDomains.Contains(targetBucket, StringComparer.Ordinal)
            ? stratumDomains
            : [];
        var presentDomains = currentPaths
            .Select(DirectoryOf)
            .Where(directory => DirectoryOf(directory) == stratumRoot)
            .Select(directory => directory[bucketPrefix.Length..]);
        var bucketCounts = policySiblings
            .Concat(presentDomains)
            .Distinct(StringComparer.Ordinal)
            .OrderBy(static domain => domain, StringComparer.Ordinal)
            .Select(domain => $"{domain}={currentPaths.Count(path =>
                DirectoryOf(path) == bucketPrefix + domain
                && !RepositoryRules.IsCapacityExcluded(path))}");
        var coordinateDirectory = targetDirectory.StartsWith("Blueprint/", StringComparison.Ordinal)
            ? targetDirectory["Blueprint/".Length..]
            : targetDirectory;
        var exits = coordinateDirectory.Count(static character => character == '/') == 3
            ? "choose a sibling subdomain or new subdomain; nesting is limited to one subdomain level"
            : "choose a sibling domain or new domain, or create a subdomain in this domain";

        return $"bucket at capacity — 只裂不迁: {targetDirectory} projected occupancy {projectedOccupancy} "
            + $"exceeds maximum {RepositoryRules.DirectoryFileLimit}; split only, {exits}. "
            + $"Same-stratum buckets: {string.Join(", ", bucketCounts)}";
    }

    private static string DirectoryOf(string path)
    {
        var slash = path.LastIndexOf('/');
        return slash < 0 ? "." : path[..slash];
    }
}
