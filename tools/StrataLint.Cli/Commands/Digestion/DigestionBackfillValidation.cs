using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class DigestionBackfillValidation
{
    internal static string RequireValidBackfill(
        BackfillInventoryDocument document,
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        ValidatedPolicy policy,
        AcceptedLeanClosure lean,
        VerifiedScribeEmissions verifiedScribeEmissions,
        RawChangeSet? changes = null,
        RawChangeSet? repositoryChanges = null,
        RawChangeSet? casChanges = null,
        RawChangeSet? projectedStatusChanges = null)
    {
        var findings = BackfillInventoryRule.EvaluateDocument(
            new BackfillInventoryValidationContext(
                current,
                baseline,
                policy,
                lean,
                verifiedScribeEmissions,
                changes,
                RepositoryChanges: repositoryChanges,
                CasChanges: casChanges,
                ProjectedStatusChanges: projectedStatusChanges),
            document);
        return RenderOrThrow(findings);
    }

    internal static string RequireValidBackfillWithoutTruthAlignment(
        BackfillInventoryDocument document,
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        ValidatedPolicy policy,
        RawChangeSet? changes = null,
        RawChangeSet? repositoryChanges = null,
        RawChangeSet? casChanges = null)
    {
        var findings = BackfillInventoryRule.EvaluateDocumentWithoutTruthAlignment(
            current,
            baseline,
            policy,
            document,
            changes,
            repositoryChanges: repositoryChanges,
            casChanges: casChanges);
        return RenderOrThrow(findings);
    }

    /// Split out from RequireValidBackfill so the two behaviours a review round found
    /// unpinned can be tested directly: that Block still throws, and that the observation
    /// order matches CliApplication's OBSERVED output. Driving those through a command
    /// fixture needs a Block-producing ledger and two observations on one run; both are
    /// reachable here with three lines of setup.
    internal static string RenderOrThrow(IEnumerable<RuleFinding> findings)
    {
        var ruleId = RuleId.CreateKnown(16);
        var descriptor = RuleCatalog.Default.Descriptors.Single(item => item.Id == ruleId);
        var diagnostics = findings.Select(finding =>
        {
            var effect = finding.Effect ?? descriptor.AdmissionEffect;
            var severity = finding.Effect is null
                ? descriptor.DisplaySeverity
                : effect is AdmissionEffect.Block ? DisplaySeverity.Error : DisplaySeverity.Warning;
            return new Diagnostic(
                descriptor.Id,
                descriptor.Title,
                severity,
                effect,
                finding.Path,
                finding.Message);
        }).ToArray();
        var blocking = diagnostics.Where(static finding =>
            finding.AdmissionEffect is AdmissionEffect.Block or AdmissionEffect.HumanGate).ToArray();
        if (blocking.Length > 0)
        {
            throw new InvalidOperationException(
                "SL-016 final ledger is invalid: "
                + string.Join("; ", blocking.Select(static finding => finding.Message)));
        }

        return string.Concat(diagnostics
            .Where(static finding => finding.AdmissionEffect is AdmissionEffect.Observe)
            .OrderBy(static finding => finding.RuleId.Value, StringComparer.Ordinal)
            .ThenBy(static finding => finding.Path, StringComparer.Ordinal)
            .ThenBy(static finding => finding.Message, StringComparer.Ordinal)
            .Select(static observation => "OBSERVED " + observation.Render() + "\n"));
    }
}
