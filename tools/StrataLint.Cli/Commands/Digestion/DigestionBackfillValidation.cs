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
        VerifiedScribeEmissions verifiedScribeEmissions)
    {
        var findings = BackfillInventoryRule.EvaluateDocument(
            new BackfillInventoryValidationContext(
                current,
                baseline,
                policy,
                lean,
                verifiedScribeEmissions),
            document);
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
