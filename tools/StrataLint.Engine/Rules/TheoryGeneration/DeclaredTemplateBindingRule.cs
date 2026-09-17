using System.Collections.Immutable;

namespace StrataLint.Engine;

internal enum InformationTemplateBindingState
{
    Undeclared,
    DeclaredUnresolved,
    DeclaredValidated,
}

internal sealed record InformationTemplateOccurrence(
    InformationOccurrenceKey Key,
    string RegistrationSourcePath,
    string StatementIdentity,
    ImmutableArray<InformationTemplateContentInput> ContentInputs,
    InformationTemplateBindingState State,
    string? EvidenceRef,
    string? Diagnostic,
    string? BindingSourcePath,
    string? UnitName = null,
    string? RealizationName = null);

internal sealed record InformationTemplateUniverse(
    ImmutableDictionary<InformationOccurrenceKey, InformationTemplateOccurrence> Occurrences,
    ImmutableHashSet<InformationOccurrenceKey> Inventory);

internal static class DeclaredTemplateBindingRule
{
    internal static bool IsAffectedBy(RuleEvaluationContext context) =>
        RepositoryRules.ChangedOrFirstPinD5Modules(context).Any();

    internal static ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var path in RepositoryRules.ChangedOrFirstPinD5Modules(context))
        {
            try
            {
                var universe = InformationTemplateEvidence.Collect(context.Current, context.Lean.Report, [path]);
                foreach (var occurrence in universe.Occurrences.Values.OrderBy(
                    occurrence => InformationTemplateJson.KeyJson(occurrence.Key).GetRawText(), StringComparer.Ordinal))
                {
                    var key = InformationTemplateJson.KeyJson(occurrence.Key).GetRawText();
                    findings.Add(occurrence.State switch
                    {
                        InformationTemplateBindingState.Undeclared => new(path.Value,
                            "DTR-Undeclared " + key, AdmissionEffect.Block),
                        InformationTemplateBindingState.DeclaredValidated when occurrence.EvidenceRef is not null =>
                            new(path.Value, "DTR-Declared " + key, AdmissionEffect.Observe),
                        _ => new(path.Value, "DTR-Evidence " + (occurrence.Diagnostic
                            ?? "selected occurrence lacks a source-bound certificate"), AdmissionEffect.Block),
                    });
                }
            }
            catch (Exception error) when (error is FormatException or IOException or InvalidOperationException)
            {
                findings.Add(new(path.Value, "DTR-Evidence " + error.Message, AdmissionEffect.Block));
            }
        }
        return findings.ToImmutable();
    }
}
