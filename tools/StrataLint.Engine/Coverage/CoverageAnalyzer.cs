using System.Collections.Immutable;

namespace StrataLint.Engine;

public static class CoverageAnalyzer
{
    public static CoverageReport Analyze(
        RepositorySnapshot snapshot,
        ValidatedPolicy policy,
        RuleCatalog catalog,
        CoverageLedgerIndex ledger)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(policy);
        ArgumentNullException.ThrowIfNull(catalog);
        ArgumentNullException.ThrowIfNull(ledger);
        var context = RuleApplicabilityContext.Create(snapshot, policy);
        var artifacts = snapshot.Files.Values
            .OrderBy(static file => file.Path.Value, StringComparer.Ordinal)
            .Select(file => AnalyzeArtifact(file, policy, catalog, context, ledger))
            .ToImmutableArray();
        var matrix = Enum.GetValues<ArtifactClass>()
            .Select(@class => MatrixRow(@class, artifacts))
            .ToImmutableArray();
        return new CoverageReport(artifacts, matrix);
    }

    private static ArtifactCoverage AnalyzeArtifact(
        RepositoryFile file,
        ValidatedPolicy policy,
        RuleCatalog catalog,
        RuleApplicabilityContext context,
        CoverageLedgerIndex ledger)
    {
        var applicable = catalog.ApplicableTo(file, context);
        var active = applicable
            .Where(static item => item.Lifecycle is RuleLifecycle.Active)
            .Select(static item => item.Id)
            .OrderBy(static item => item.Value, StringComparer.Ordinal)
            .ToImmutableArray();
        var deferred = applicable
            .Where(static item => item.Lifecycle is RuleLifecycle.Deferred)
            .Select(static item => item.Id)
            .OrderBy(static item => item.Value, StringComparer.Ordinal)
            .ToImmutableArray();
        var profile = RepositoryPathPolicy.TryGetValidationProfile(file.Path, policy, out var resolved)
            ? resolved
            : null;
        var ledgerState = ledger.TryGet(file.Path, out var state)
            ? state
            : (CoverageLedgerState?)null;
        var registrations = RepositoryPathPolicy.RegistrationSources(file.Path, policy);
        var mechanisms = new CoverageMechanisms(
            active,
            deferred,
            profile,
            active.Contains(RuleId.CreateKnown(4)),
            ledgerState,
            registrations);
        return new ArtifactCoverage(file.Path, Classify(file.Path), mechanisms);
    }

    private static CoverageMatrixRow MatrixRow(
        ArtifactClass @class,
        ImmutableArray<ArtifactCoverage> artifacts)
    {
        var selected = artifacts.Where(item => item.Class == @class).ToArray();
        return new CoverageMatrixRow(
            @class,
            selected.Length,
            selected.Count(static item => item.Mechanisms.ActiveRules.Length > 0),
            selected.Count(static item => item.Mechanisms.ValidationProfile is not null),
            selected.Count(static item => item.Mechanisms.MirrorObligation),
            selected.Count(static item => item.Mechanisms.LedgerState is not null),
            selected.Count(static item => item.Mechanisms.Registrations.Length > 0),
            selected.Count(static item => item.IsUngoverned));
    }

    private static ArtifactClass Classify(RepoPath path)
    {
        var value = path.Value;
        if (value == "Trureturing.lean"
            || value.StartsWith("D5/", StringComparison.Ordinal)
            || value.StartsWith("Metallic/", StringComparison.Ordinal)
            || value.StartsWith("Moduli/", StringComparison.Ordinal)) return ArtifactClass.F;
        if (value.StartsWith("Blueprint/", StringComparison.Ordinal)) return ArtifactClass.B;
        if (value.StartsWith("Evidence/", StringComparison.Ordinal)) return ArtifactClass.E;
        if (value.StartsWith("Chronicle/", StringComparison.Ordinal)) return ArtifactClass.C;
        if (value.StartsWith("Library/", StringComparison.Ordinal)) return ArtifactClass.L;
        if (value.StartsWith("Papers/", StringComparison.Ordinal)) return ArtifactClass.P;
        if (value.StartsWith("Meta/", StringComparison.Ordinal)) return ArtifactClass.Meta;
        if (value.StartsWith(".github/", StringComparison.Ordinal)) return ArtifactClass.GitHub;
        if (value.StartsWith(RepositoryPathPolicy.AgentFilesRootPath, StringComparison.Ordinal))
        {
            return ArtifactClass.Agents;
        }
        if (value.StartsWith("docs/", StringComparison.Ordinal)) return ArtifactClass.Docs;
        return value.Contains('/', StringComparison.Ordinal) ? ArtifactClass.Other : ArtifactClass.Root;
    }
}
