using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using Trureturing.Truth;

namespace StrataLint.Engine;

public static class CoverageCanonicalWriter
{
    public const string UngovernedDefinition =
        "active rule/profile/mirror/frozen-ledger-state/registration set is empty; closed-world enumeration is not a mechanism";

    public const string V2Proposal =
        "add a case-backed SL rule for detected UNGOVERNED classes, then promote it to admission blocking after the report-only baseline is stable";

    public static ImmutableArray<byte> WriteText(
        CoverageReport report,
        ValidatedTowerManifest tower)
    {
        ArgumentNullException.ThrowIfNull(report);
        ArgumentNullException.ThrowIfNull(tower);
        var builder = new StringBuilder();
        builder.Append("HARNESS_COVERAGE schema=1\n");
        builder.Append("SUMMARY artifacts=").Append(report.Artifacts.Length)
            .Append(" governed=").Append(report.Artifacts.Length - report.Ungoverned.Length)
            .Append(" ungoverned=").Append(report.Ungoverned.Length).Append('\n');
        builder.Append("DERIVED_FROM rules=\"RuleCatalog/IRepositoryRule.AppliesTo\"")
            .Append(" profiles=\"ValidatedPolicy/ArtifactPolicy\"")
            .Append(" mirrors=\"active SL-004 applicability\"")
            .Append(" ledger=\"FrozenLedger+TruthDAG\"")
            .Append(" registrations=\"registry/domains/path-policy\"\n");
        foreach (var row in report.Matrix)
        {
            builder.Append("MATRIX class=").Append(CoverageNames.Class(row.Class))
                .Append(" artifacts=").Append(row.Artifacts)
                .Append(" rules=").Append(row.Rules)
                .Append(" profiles=").Append(row.Profiles)
                .Append(" mirrors=").Append(row.Mirrors)
                .Append(" ledger=").Append(row.Ledger)
                .Append(" registrations=").Append(row.Registrations)
                .Append(" ungoverned=").Append(row.Ungoverned).Append('\n');
        }

        builder.Append("UNGOVERNED count=").Append(report.Ungoverned.Length)
            .Append(" definition=").Append(Quote(UngovernedDefinition)).Append('\n');
        foreach (var artifact in report.Ungoverned)
        {
            builder.Append("UNGOVERNED path=").Append(Quote(artifact.Path.Value))
                .Append(" class=").Append(CoverageNames.Class(artifact.Class)).Append('\n');
        }

        builder.Append("TOWER status=valid components=").Append(tower.Syntax.Components.Length)
            .Append(" checks=").Append(tower.Checks.Length)
            .Append(" assumed_unverified=")
            .Append(tower.Checks.Count(static item => item.Status == "ASSUMED-UNVERIFIED"))
            .Append('\n');
        foreach (var component in tower.Syntax.Components.OrderBy(static item => item.Id, StringComparer.Ordinal))
        {
            builder.Append("TOWER_COMPONENT id=").Append(component.Id)
                .Append(" kind=").Append(component.Kind)
                .Append(" members=").Append(Join(component.Members))
                .Append(" judged_by=").Append(Join(component.JudgedBy))
                .Append(" verification=").Append(component.Verification).Append('\n');
        }

        var bootstrap = tower.Syntax.Bootstrap;
        builder.Append("TOWER_BOOTSTRAP id=").Append(bootstrap.Id)
            .Append(" judge=").Append(bootstrap.Judge)
            .Append(" reason=").Append(Quote(bootstrap.Reason))
            .Append(" genesis_event=").Append(bootstrap.GenesisEvent)
            .Append(" commit=").Append(bootstrap.Commit)
            .Append(" pull_request=").Append(bootstrap.PullRequest)
            .Append(" verification=").Append(bootstrap.Verification).Append('\n');
        foreach (var check in tower.Checks)
        {
            builder.Append("TOWER_CHECK subject=").Append(check.Subject)
                .Append(" status=").Append(check.Status)
                .Append(" detail=").Append(Quote(check.Detail)).Append('\n');
        }

        builder.Append("ARTIFACTS count=").Append(report.Artifacts.Length).Append('\n');
        foreach (var artifact in report.Artifacts)
        {
            var mechanisms = artifact.Mechanisms;
            builder.Append("ARTIFACT path=").Append(Quote(artifact.Path.Value))
                .Append(" class=").Append(CoverageNames.Class(artifact.Class))
                .Append(" active_rules=").Append(Join(mechanisms.ActiveRules.Select(static item => item.Value)))
                .Append(" deferred_rules=").Append(Join(mechanisms.DeferredRules.Select(static item => item.Value)))
                .Append(" profile=").Append(mechanisms.ValidationProfile ?? "-")
                .Append(" mirror=").Append(mechanisms.MirrorObligation ? "SL-004" : "-")
                .Append(" ledger=").Append(mechanisms.LedgerState is null
                    ? "-"
                    : CoverageNames.Ledger(mechanisms.LedgerState.Value))
                .Append(" registrations=").Append(Join(mechanisms.Registrations))
                .Append(" governed=").Append(artifact.IsUngoverned ? "false" : "true")
                .Append('\n');
        }

        builder.Append("V2_ENFORCEMENT proposal=").Append(Quote(V2Proposal)).Append('\n');
        return ImmutableArray.CreateRange(new UTF8Encoding(false, true).GetBytes(builder.ToString()));
    }

    public static ImmutableArray<byte> WriteJson(
        CoverageReport report,
        ValidatedTowerManifest tower)
    {
        ArgumentNullException.ThrowIfNull(report);
        ArgumentNullException.ThrowIfNull(tower);
        var material = JsonSerializer.SerializeToElement(new
        {
            artifacts = report.Artifacts.Select(static artifact => new
            {
                active_rules = artifact.Mechanisms.ActiveRules.Select(static item => item.Value),
                artifact_class = CoverageNames.Class(artifact.Class),
                deferred_rules = artifact.Mechanisms.DeferredRules.Select(static item => item.Value),
                governed = !artifact.IsUngoverned,
                ledger_state = artifact.Mechanisms.LedgerState is null
                    ? null
                    : CoverageNames.Ledger(artifact.Mechanisms.LedgerState.Value),
                mirror_obligation = artifact.Mechanisms.MirrorObligation ? "SL-004" : null,
                path = artifact.Path.Value,
                registrations = artifact.Mechanisms.Registrations,
                validation_profile = artifact.Mechanisms.ValidationProfile,
            }),
            matrix = report.Matrix.Select(static row => new
            {
                artifact_class = CoverageNames.Class(row.Class),
                artifacts = row.Artifacts,
                ledger = row.Ledger,
                mirrors = row.Mirrors,
                profiles = row.Profiles,
                registrations = row.Registrations,
                rules = row.Rules,
                ungoverned = row.Ungoverned,
            }),
            mechanisms_derived_from = new[]
            {
                "RuleCatalog/IRepositoryRule.AppliesTo",
                "ValidatedPolicy/ArtifactPolicy",
                "active SL-004 applicability",
                "FrozenLedger+TruthDAG",
                "registry/domains/path-policy",
            },
            schema_version = 1,
            summary = new
            {
                artifacts = report.Artifacts.Length,
                governed = report.Artifacts.Length - report.Ungoverned.Length,
                ungoverned = report.Ungoverned.Length,
            },
            tower = new
            {
                bootstrap = new
                {
                    commit = tower.Syntax.Bootstrap.Commit,
                    genesis_event = tower.Syntax.Bootstrap.GenesisEvent,
                    id = tower.Syntax.Bootstrap.Id,
                    judge = tower.Syntax.Bootstrap.Judge,
                    pull_request = tower.Syntax.Bootstrap.PullRequest,
                    reason = tower.Syntax.Bootstrap.Reason,
                    verification = tower.Syntax.Bootstrap.Verification,
                },
                checks = tower.Checks.Select(static item => new
                {
                    detail = item.Detail,
                    status = item.Status,
                    subject = item.Subject,
                }),
                components = tower.Syntax.Components.OrderBy(static item => item.Id, StringComparer.Ordinal)
                    .Select(static item => new
                    {
                        id = item.Id,
                        judged_by = item.JudgedBy.Order(StringComparer.Ordinal),
                        kind = item.Kind,
                        members = item.Members.Order(StringComparer.Ordinal),
                        verification = item.Verification,
                    }),
                manifest_path = RepositoryRules.TowerManifestPath,
                status = "valid",
            },
            ungoverned = new
            {
                artifacts = report.Ungoverned.Select(static item => item.Path.Value),
                count = report.Ungoverned.Length,
                definition = UngovernedDefinition,
                v2_enforcement_proposal = V2Proposal,
            },
        });
        return StructuredCanonicalWriter.WriteJson(material);
    }

    private static string Join(IEnumerable<string> values)
    {
        var material = values.Order(StringComparer.Ordinal).ToArray();
        return material.Length == 0 ? "-" : string.Join(',', material);
    }

    private static string Quote(string value) => JsonSerializer.Serialize(value);
}
