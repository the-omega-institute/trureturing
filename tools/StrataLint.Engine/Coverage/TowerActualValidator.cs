using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

internal sealed record TowerActualValidation(
    ImmutableArray<TowerFinding> Findings,
    ImmutableArray<TowerCheck> Checks);

internal static class TowerActualValidator
{
    private static readonly ImmutableDictionary<string, string> KnownCiNames =
        new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["candidate-engineering"] = "Candidate harness engineering checks",
            ["baseline-admission"] = "Content-addressed dev baseline admission",
            // Branch protection requires three contexts and matches them to jobs by
            // display name, so a renamed job silently stops reporting: the PR then sits
            // BLOCKED with nothing to point at, and the obvious repair is to drop the
            // context, which quietly removes a required check. Two of the three names
            // were pinned here; this is the third.
            ["lean-inspect"] = "Canonical Lean report production",
        }.ToImmutableDictionary(StringComparer.Ordinal);

    internal static TowerActualValidation Validate(
        TowerManifestSyntax syntax,
        RepositorySnapshot snapshot,
        RuleCatalog catalog)
    {
        var findings = ImmutableArray.CreateBuilder<TowerFinding>();
        var checks = ImmutableArray.CreateBuilder<TowerCheck>();
        foreach (var component in syntax.Components.OrderBy(static item => item.Id, StringComparer.Ordinal))
        {
            ValidateComponent(component, snapshot, catalog, findings, checks);
        }

        ValidateBootstrap(syntax.Bootstrap, snapshot, findings, checks);
        return new TowerActualValidation(
            findings.OrderBy(static item => item.Code, StringComparer.Ordinal)
                .ThenBy(static item => item.Component, StringComparer.Ordinal)
                .ThenBy(static item => item.Message, StringComparer.Ordinal)
                .ToImmutableArray(),
            checks.OrderBy(static item => item.Subject, StringComparer.Ordinal)
                .ThenBy(static item => item.Status, StringComparer.Ordinal)
                .ThenBy(static item => item.Detail, StringComparer.Ordinal)
                .ToImmutableArray());
    }

    private static void ValidateComponent(
        TowerComponentSyntax component,
        RepositorySnapshot snapshot,
        RuleCatalog catalog,
        ImmutableArray<TowerFinding>.Builder findings,
        ImmutableArray<TowerCheck>.Builder checks)
    {
        if (component.Verification != "verified")
        {
            findings.Add(new TowerFinding(
                "TOWER-VERIFICATION",
                component.Id,
                "machine-checkable component must be marked verified"));
        }

        switch (component.Kind)
        {
            case "rule-catalog":
                ValidateRuleCatalog(component, catalog, findings, checks);
                break;
            case "ci-jobs":
                ValidateCiJobs(component, snapshot, findings, checks);
                break;
            case "repository-files":
                ValidateFiles(component, snapshot, findings, checks);
                break;
            case "path-prefixes":
                ValidatePrefixes(component, snapshot, findings, checks);
                break;
            case "artifact-classes":
                ValidateArtifactClasses(component, findings, checks);
                break;
            default:
                findings.Add(new TowerFinding(
                    "TOWER-KIND",
                    component.Id,
                    $"unknown component kind {component.Kind}"));
                break;
        }
    }

    private static void ValidateRuleCatalog(
        TowerComponentSyntax component,
        RuleCatalog catalog,
        ImmutableArray<TowerFinding>.Builder findings,
        ImmutableArray<TowerCheck>.Builder checks)
    {
        var actual = catalog.Descriptors.Select(static item => item.Id.Value).Order(StringComparer.Ordinal).ToArray();
        var declared = component.Members.Order(StringComparer.Ordinal).ToArray();
        if (!declared.SequenceEqual(actual, StringComparer.Ordinal))
        {
            // The comparison is over the id sets, so the message has to be too: a
            // reordering or a swap leaves both counts equal and "declared N but contains N"
            // then reads as a broken tool rather than a real mismatch. See #993.
            findings.Add(new TowerFinding(
                "TOWER-RULE-CATALOG",
                component.Id,
                DescribeSetMismatch("rules", declared, actual)));
            return;
        }

        checks.Add(new TowerCheck(component.Id, "verified", $"RuleCatalog count={actual.Length}"));
    }

    private static void ValidateCiJobs(
        TowerComponentSyntax component,
        RepositorySnapshot snapshot,
        ImmutableArray<TowerFinding>.Builder findings,
        ImmutableArray<TowerCheck>.Builder checks)
    {
        if (!snapshot.TryGetFile(RepositoryPathPolicy.WorkflowPath, out var workflow))
        {
            findings.Add(new TowerFinding("TOWER-CI-JOB", component.Id, "ci.yml is missing"));
            return;
        }

        var jobs = ParseJobs(workflow.Text);
        foreach (var member in component.Members.Order(StringComparer.Ordinal))
        {
            if (!jobs.TryGetValue(member, out var name))
            {
                findings.Add(new TowerFinding("TOWER-CI-JOB", component.Id, $"missing ci job {member}"));
                continue;
            }

            if (KnownCiNames.TryGetValue(member, out var expected) && name != expected)
            {
                findings.Add(new TowerFinding(
                    "TOWER-CI-JOB",
                    component.Id,
                    $"ci job {member} name is {name}, expected {expected}"));
                continue;
            }

            checks.Add(new TowerCheck(component.Id, "verified", $"ci job {member} name={name}"));
        }
    }

    private static ImmutableDictionary<string, string> ParseJobs(string yaml)
    {
        var lines = yaml.Replace("\r\n", "\n", StringComparison.Ordinal).Split('\n');
        var jobs = ImmutableDictionary.CreateBuilder<string, string>(StringComparer.Ordinal);
        var inJobs = false;
        string? current = null;
        foreach (var line in lines)
        {
            if (line == "jobs:")
            {
                inJobs = true;
                continue;
            }
            if (!inJobs) continue;
            if (line.Length > 0 && !char.IsWhiteSpace(line[0])) break;
            if (line.StartsWith("  ", StringComparison.Ordinal)
                && !line.StartsWith("    ", StringComparison.Ordinal)
                && line.EndsWith(':'))
            {
                current = line[2..^1];
                jobs[current] = string.Empty;
                continue;
            }
            if (current is not null && line.StartsWith("    name: ", StringComparison.Ordinal))
            {
                jobs[current] = line[10..].Trim().Trim('"', '\'');
            }
        }

        return jobs.ToImmutable();
    }

    private static void ValidateFiles(
        TowerComponentSyntax component,
        RepositorySnapshot snapshot,
        ImmutableArray<TowerFinding>.Builder findings,
        ImmutableArray<TowerCheck>.Builder checks)
    {
        foreach (var member in component.Members.Order(StringComparer.Ordinal))
        {
            if (!snapshot.TryGetFile(member, out _))
            {
                findings.Add(new TowerFinding("TOWER-FILE", component.Id, $"missing member file {member}"));
            }
        }

        if (!findings.Any(item => item.Component == component.Id))
        {
            checks.Add(new TowerCheck(component.Id, "verified", $"repository files={component.Members.Length}"));
        }
    }

    private static void ValidatePrefixes(
        TowerComponentSyntax component,
        RepositorySnapshot snapshot,
        ImmutableArray<TowerFinding>.Builder findings,
        ImmutableArray<TowerCheck>.Builder checks)
    {
        foreach (var prefix in component.Members.Order(StringComparer.Ordinal))
        {
            if (!snapshot.Files.Keys.Any(path => path.Value.StartsWith(prefix, StringComparison.Ordinal)))
            {
                findings.Add(new TowerFinding("TOWER-PREFIX", component.Id, $"empty path prefix {prefix}"));
            }
        }

        if (!findings.Any(item => item.Component == component.Id))
        {
            checks.Add(new TowerCheck(component.Id, "verified", $"path prefixes={component.Members.Length}"));
        }
    }

    private static void ValidateArtifactClasses(
        TowerComponentSyntax component,
        ImmutableArray<TowerFinding>.Builder findings,
        ImmutableArray<TowerCheck>.Builder checks)
    {
        var expected = CoverageNames.ArtifactClasses.Order(StringComparer.Ordinal).ToArray();
        if (!component.Members.Order(StringComparer.Ordinal).SequenceEqual(expected, StringComparer.Ordinal))
        {
            findings.Add(new TowerFinding("TOWER-ARTIFACT-CLASSES", component.Id, "artifact class members drifted"));
        }
        else
        {
            checks.Add(new TowerCheck(component.Id, "verified", $"artifact classes={expected.Length}"));
        }
    }

    private static void ValidateBootstrap(
        TowerBootstrapSyntax bootstrap,
        RepositorySnapshot snapshot,
        ImmutableArray<TowerFinding>.Builder findings,
        ImmutableArray<TowerCheck>.Builder checks)
    {
        var found = snapshot.Files.Values
            .Where(item => FrozenLedgerChangeClassifier.IsAcceptedEventPath(item.Path.Value))
            .Any(item => IsLedgerAnchor(item.Text.TrimEnd('\n'), bootstrap.GenesisEvent));
        if (!found)
        {
            findings.Add(new TowerFinding("TOWER-GENESIS", bootstrap.Id, "declared genesis event is absent"));
        }
        else
        {
            checks.Add(new TowerCheck(bootstrap.Id, "verified", $"genesis event {bootstrap.GenesisEvent}"));
        }

        if (bootstrap.Verification != "ASSUMED-UNVERIFIED"
            || bootstrap.PullRequest != 1
            || bootstrap.Commit.Length != 40
            || !bootstrap.Commit.All(char.IsAsciiHexDigit))
        {
            findings.Add(new TowerFinding(
                "TOWER-BOOTSTRAP-RECORD",
                bootstrap.Id,
                "external bootstrap record must identify PR#1/commit and remain ASSUMED-UNVERIFIED"));
        }
        else
        {
            checks.Add(new TowerCheck(
                bootstrap.Id,
                "ASSUMED-UNVERIFIED",
                $"external PR#{bootstrap.PullRequest} commit={bootstrap.Commit}"));
        }
    }

    /// Renders the symmetric difference of two ordered id sets, capped so a wholesale
    /// divergence stays readable. Counts alone are not a faithful report of a set
    /// comparison: they coincide under reordering and under equal-sized swaps, and the
    /// reader then sees two identical numbers in a message announcing a mismatch.
    private static string DescribeSetMismatch(
        string subject,
        IReadOnlyCollection<string> declared,
        IReadOnlyCollection<string> actual)
    {
        const int Cap = 5;
        var missing = declared.Except(actual, StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray();
        var unexpected = actual.Except(declared, StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray();
        var parts = new List<string>(3) { $"declared {subject} do not match actual" };
        if (missing.Length > 0)
        {
            parts.Add($"declared but absent: {Render(missing)}");
        }

        if (unexpected.Length > 0)
        {
            parts.Add($"present but undeclared: {Render(unexpected)}");
        }

        if (missing.Length == 0 && unexpected.Length == 0)
        {
            parts.Add($"same members in a different order (count={declared.Count})");
        }

        return string.Join("; ", parts);

        static string Render(string[] values) =>
            values.Length <= Cap
                ? string.Join(", ", values)
                : string.Join(", ", values.Take(Cap)) + $", … (+{values.Length - Cap} more)";
    }

    private static bool IsLedgerAnchor(string line, string expectedHash)
    {
        try
        {
            using var document = JsonDocument.Parse(line);
            return document.RootElement.GetProperty("event_type").GetString() == "Freeze"
                && document.RootElement.GetProperty("event_hash").GetString() == expectedHash;
        }
        catch (JsonException)
        {
            return false;
        }
    }
}
