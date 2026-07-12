using System.Collections.Immutable;
using System.Text.RegularExpressions;
using Dunet;

namespace StrataLint.Engine;

public sealed record TowerComponentSyntax(
    string Id,
    string Kind,
    ImmutableArray<string> Members,
    ImmutableArray<string> JudgedBy,
    string Verification);

public sealed record TowerBootstrapSyntax(
    string Id,
    string Judge,
    string Reason,
    string GenesisEvent,
    string Commit,
    int PullRequest,
    string Verification);

public sealed record TowerManifestSyntax(
    int SchemaVersion,
    ImmutableArray<TowerComponentSyntax> Components,
    TowerBootstrapSyntax Bootstrap);

public sealed record TowerFinding(string Code, string Component, string Message);

public sealed record TowerCheck(string Subject, string Status, string Detail);

public sealed record ValidatedTowerManifest
{
    internal ValidatedTowerManifest(
        TowerManifestSyntax syntax,
        ImmutableArray<TowerCheck> checks)
    {
        Syntax = syntax ?? throw new ArgumentNullException(nameof(syntax));
        Checks = checks;
    }

    public TowerManifestSyntax Syntax { get; }

    public ImmutableArray<TowerCheck> Checks { get; }
}

[Union(EnableImplicitConversions = false)]
public partial record TowerValidationOutcome
{
    public partial record Accepted
    {
        internal Accepted(ValidatedTowerManifest manifest) =>
            Manifest = manifest ?? throw new ArgumentNullException(nameof(manifest));

        public ValidatedTowerManifest Manifest { get; }
    }

    public partial record Rejected(ImmutableArray<TowerFinding> Findings);
}

public static class TowerManifestValidator
{
    private static readonly Regex IdPattern = new(
        "^[a-z0-9]+(?:-[a-z0-9]+)*$",
        RegexOptions.CultureInvariant);

    public static TowerValidationOutcome ValidateStructure(TowerManifestSyntax syntax)
    {
        ArgumentNullException.ThrowIfNull(syntax);
        var findings = ImmutableArray.CreateBuilder<TowerFinding>();
        if (syntax.SchemaVersion != 1)
        {
            findings.Add(new TowerFinding(
                "TOWER-SCHEMA",
                "manifest",
                "schema_version must be 1"));
        }

        var components = new Dictionary<string, TowerComponentSyntax>(StringComparer.Ordinal);
        foreach (var component in syntax.Components.OrderBy(static item => item.Id, StringComparer.Ordinal))
        {
            if (!IdPattern.IsMatch(component.Id)
                || !IdPattern.IsMatch(component.Kind)
                || !components.TryAdd(component.Id, component))
            {
                findings.Add(new TowerFinding(
                    "TOWER-COMPONENT",
                    component.Id,
                    "component id/kind is invalid or duplicated"));
            }

            if (component.JudgedBy.IsDefaultOrEmpty)
            {
                findings.Add(new TowerFinding(
                    "TOWER-UNJUDGED",
                    component.Id,
                    "component must declare judged_by"));
            }

            if (component.Members.Any(string.IsNullOrWhiteSpace)
                || component.Members.Distinct(StringComparer.Ordinal).Count() != component.Members.Length)
            {
                findings.Add(new TowerFinding(
                    "TOWER-MEMBER",
                    component.Id,
                    "component members must be nonempty and unique"));
            }
        }

        ValidateBootstrap(syntax.Bootstrap, components, findings);
        ValidateEdges(syntax.Bootstrap.Id, components, findings);
        var cycle = FindCycle(components);
        if (cycle.Length > 0)
        {
            findings.Add(new TowerFinding(
                "TOWER-CYCLE",
                cycle[0],
                string.Join(" -> ", cycle)));
        }

        if (cycle.Length == 0)
        {
            ValidateTermination(syntax.Bootstrap.Id, components, findings);
        }

        var ordered = findings
            .OrderBy(static item => item.Code, StringComparer.Ordinal)
            .ThenBy(static item => item.Component, StringComparer.Ordinal)
            .ThenBy(static item => item.Message, StringComparer.Ordinal)
            .ToImmutableArray();
        return ordered.Length == 0
            ? new TowerValidationOutcome.Accepted(
                new ValidatedTowerManifest(syntax, ImmutableArray<TowerCheck>.Empty))
            : new TowerValidationOutcome.Rejected(ordered);
    }

    public static TowerValidationOutcome Validate(
        TowerManifestSyntax syntax,
        RepositorySnapshot snapshot,
        RuleCatalog catalog)
    {
        var structure = ValidateStructure(syntax);
        if (structure is TowerValidationOutcome.Rejected rejected) return rejected;
        var actual = TowerActualValidator.Validate(syntax, snapshot, catalog);
        return actual.Findings.Length == 0
            ? new TowerValidationOutcome.Accepted(new ValidatedTowerManifest(syntax, actual.Checks))
            : new TowerValidationOutcome.Rejected(actual.Findings);
    }

    private static void ValidateBootstrap(
        TowerBootstrapSyntax bootstrap,
        IReadOnlyDictionary<string, TowerComponentSyntax> components,
        ImmutableArray<TowerFinding>.Builder findings)
    {
        if (!IdPattern.IsMatch(bootstrap.Id) || components.ContainsKey(bootstrap.Id))
        {
            findings.Add(new TowerFinding(
                "TOWER-BOOTSTRAP",
                bootstrap.Id,
                "bootstrap id is invalid or collides with a component"));
        }

        if (bootstrap.Judge != "open"
            || !(bootstrap.Reason.Contains("Godel", StringComparison.OrdinalIgnoreCase)
                || bootstrap.Reason.Contains("Gödel", StringComparison.OrdinalIgnoreCase)))
        {
            findings.Add(new TowerFinding(
                "TOWER-TOP-OPEN",
                bootstrap.Id,
                "bootstrap judge must be open with a Godel boundary reason"));
        }
    }

    private static void ValidateEdges(
        string bootstrapId,
        IReadOnlyDictionary<string, TowerComponentSyntax> components,
        ImmutableArray<TowerFinding>.Builder findings)
    {
        foreach (var component in components.Values.OrderBy(static item => item.Id, StringComparer.Ordinal))
        {
            var duplicate = component.JudgedBy
                .GroupBy(static item => item, StringComparer.Ordinal)
                .FirstOrDefault(static group => group.Count() > 1);
            if (duplicate is not null)
            {
                findings.Add(new TowerFinding(
                    "TOWER-JUDGE",
                    component.Id,
                    $"duplicate judge {duplicate.Key}"));
            }

            foreach (var judge in component.JudgedBy.Order(StringComparer.Ordinal))
            {
                if (judge != bootstrapId && !components.ContainsKey(judge))
                {
                    findings.Add(new TowerFinding(
                        "TOWER-JUDGE",
                        component.Id,
                        $"unknown judge {judge}"));
                }
            }
        }
    }

    private static ImmutableArray<string> FindCycle(
        IReadOnlyDictionary<string, TowerComponentSyntax> components)
    {
        var colors = components.Keys.ToDictionary(static id => id, static _ => (byte)0, StringComparer.Ordinal);
        var stack = new List<string>();
        foreach (var start in components.Keys.Order(StringComparer.Ordinal))
        {
            var cycle = Visit(start);
            if (cycle.Length > 0)
            {
                return CanonicalizeCycle(cycle);
            }
        }

        return ImmutableArray<string>.Empty;

        ImmutableArray<string> Visit(string id)
        {
            if (colors[id] == 2) return ImmutableArray<string>.Empty;
            if (colors[id] == 1)
            {
                var first = stack.IndexOf(id);
                return stack.Skip(first).Append(id).ToImmutableArray();
            }

            colors[id] = 1;
            stack.Add(id);
            foreach (var judge in components[id].JudgedBy
                .Where(components.ContainsKey)
                .Order(StringComparer.Ordinal))
            {
                var cycle = Visit(judge);
                if (cycle.Length > 0) return cycle;
            }

            stack.RemoveAt(stack.Count - 1);
            colors[id] = 2;
            return ImmutableArray<string>.Empty;
        }
    }

    private static ImmutableArray<string> CanonicalizeCycle(ImmutableArray<string> cycle)
    {
        var body = cycle[..^1];
        var first = 0;
        for (var index = 1; index < body.Length; index++)
        {
            if (StringComparer.Ordinal.Compare(body[index], body[first]) < 0) first = index;
        }

        return Enumerable.Range(0, body.Length)
            .Select(offset => body[(first + offset) % body.Length])
            .Append(body[first])
            .ToImmutableArray();
    }

    private static void ValidateTermination(
        string bootstrapId,
        IReadOnlyDictionary<string, TowerComponentSyntax> components,
        ImmutableArray<TowerFinding>.Builder findings)
    {
        var reachesBootstrap = new Dictionary<string, bool>(StringComparer.Ordinal);
        foreach (var component in components.Values.OrderBy(static item => item.Id, StringComparer.Ordinal))
        {
            if (!Reaches(component.Id))
            {
                findings.Add(new TowerFinding(
                    "TOWER-TERMINATION",
                    component.Id,
                    "judge chain does not terminate at bootstrap"));
            }
        }

        bool Reaches(string id)
        {
            if (reachesBootstrap.TryGetValue(id, out var cached)) return cached;
            var result = components[id].JudgedBy.Any(judge =>
                judge == bootstrapId || components.ContainsKey(judge) && Reaches(judge));
            reachesBootstrap[id] = result;
            return result;
        }
    }
}
