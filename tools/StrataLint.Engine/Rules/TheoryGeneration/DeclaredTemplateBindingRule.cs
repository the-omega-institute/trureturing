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
    internal static bool IsAffectedBy(DeltaRuleContext context) =>
        RepositoryRules.ChangedOrFirstPinD5Modules(context).Any();

    internal static ImmutableArray<RuleFinding> Evaluate(DeltaRuleContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var path in RepositoryRules.ChangedOrFirstPinD5Modules(context))
        {
            try
            {
                var universe = InformationTemplateEvidence.Collect(context.Current, context.Lean.Report, [path]);
                var currentNames = LeanDeclarationSourceNames.Read(context.Current.Files[path].Text);
                var baseNames = context.Baseline.Files.TryGetValue(path, out var baseline)
                    ? LeanDeclarationSourceNames.Read(baseline.Text) : ImmutableDictionary<string, string>.Empty;
                var newTheorems = context.Lean.Report.Files[path].Declarations
                    .Where(declaration => IsPublicTheorem(declaration, currentNames)
                        && !(baseNames.TryGetValue(declaration.Name, out var kind) && kind is "theorem" or "lemma"))
                    .Select(declaration => declaration.Name).ToImmutableHashSet(StringComparer.Ordinal);
                var occurrences = universe.Occurrences;
                if (!newTheorems.IsEmpty)
                    occurrences = occurrences.SetItems(InformationTemplateTheoremSelection.Collect(
                        context.Current, context.Lean.Report, newTheorems).Occurrences);
                foreach (var occurrence in occurrences.Values.OrderBy(
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
                var validated = occurrences.Values
                    .Where(occurrence => occurrence.State == InformationTemplateBindingState.DeclaredValidated
                        && occurrence.EvidenceRef is not null)
                    .Select(occurrence => occurrence.Key.Theorem).ToHashSet(StringComparer.Ordinal);
                foreach (var theorem in newTheorems.Where(name => !validated.Contains(name)).Order(StringComparer.Ordinal))
                    findings.Add(new(path.Value, "DTR-Unregistered " + InformationTemplateEvidence.ModuleForSource(path.Value)
                        + "/" + theorem, AdmissionEffect.Block));
            }
            catch (Exception error) when (error is FormatException or IOException or InvalidOperationException or ArgumentException)
            {
                findings.Add(new(path.Value, "DTR-Evidence " + error.Message, AdmissionEffect.Block));
            }
        }
        return findings.ToImmutable();
    }

    private static bool IsPublicTheorem(LeanDeclaration declaration, ImmutableDictionary<string, string> sourceNames)
    {
        // Inspector preserves the kernel name: private declarations start with
        // _private.; include_in_statement excludes internal-detail theorems.
        // Its separate --statement-identities stream's olean part is not a
        // visibility field in the admission report.
        if (declaration.Kind != "theorem" || !declaration.IncludeInStatement
            || declaration.Name.StartsWith("_private.", StringComparison.Ordinal)) return false;
        if (sourceNames.TryGetValue(declaration.Name, out var kind)) return kind is "theorem" or "lemma";
        return !GeneratedCompanionSuffixes.Any(suffix => declaration.Name.EndsWith(suffix, StringComparison.Ordinal));
    }

    // Closed naming alphabet of Registry/Entries and the seal proof builders.
    // An explicitly authored theorem never gets a suffix-based exemption.
    private static readonly string[] GeneratedCompanionSuffixes =
    [
        "__information_unit", "__primitive_realization", "__lowers_escape", "__trivial_in_catalog",
        "__escape_enriched", "__information_catalog", "__catalog_irredundant", "__catalog_redundant",
        "__system_catalog_irredundant", "__system_catalog_not_irredundant", "__information_registration_diagnostic",
    ];
}
