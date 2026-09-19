using System.Collections.Immutable;

namespace StrataLint.Engine;

internal enum InformationTemplateBindingState
{
    Undeclared,
    DeclaredUnresolved,
    DeclaredValidated,
}

internal sealed record InformationEscapeFrom(string Name, string TypeIdentity, string ObjectIdentity);
internal sealed record InformationEscapeContinuation(string Kind, string? DeclarationName,
    string? StatementIdentity, string? ChainName);

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
    string? RealizationName = null,
    InformationEscapeFrom? EscapeFrom = null,
    InformationEscapeContinuation? EscapeContinues = null,
    string BridgeKind = "legacy",
    InformationFamilyBinding? Family = null)
{
    internal bool HasOrigin => Key.Mode == "dependent-family-v1" ? Family is not null : EscapeFrom is not null;
    internal bool HasFourSlots => HasOrigin && EscapeContinues is not null
        && State == InformationTemplateBindingState.DeclaredValidated && EvidenceRef is not null;
}

internal sealed record InformationTemplateUniverse(
    ImmutableDictionary<InformationOccurrenceKey, InformationTemplateOccurrence> Occurrences,
    ImmutableHashSet<InformationOccurrenceKey> Inventory);

internal static class DeclaredTemplateBindingRule
{
    // τ=0 owner ruling (2026-09-20): every DTR finding is an observation. The
    // obligation collects registration state as warnings and never blocks admission.
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
                    findings.Add(EvaluateOccurrence(path, occurrence));
                }
                var validated = occurrences.Values
                    .Where(occurrence => occurrence.HasFourSlots)
                    .Select(occurrence => occurrence.Key.Theorem).ToHashSet(StringComparer.Ordinal);
                foreach (var theorem in newTheorems.Where(name => !validated.Contains(name)).Order(StringComparer.Ordinal))
                    findings.Add(new(path.Value, "DTR-Unregistered " + InformationTemplateEvidence.ModuleForSource(path.Value)
                        + "/" + theorem, AdmissionEffect.Observe));
            }
            catch (Exception error) when (error is FormatException or IOException or InvalidOperationException or ArgumentException)
            {
                findings.Add(new(path.Value, "DTR-Evidence " + error.Message, AdmissionEffect.Observe));
            }
        }
        return findings.ToImmutable();
    }

    // Shared verdict emission after the strict native evidence join. Owner
    // selection remains exclusively in Evaluate above.
    internal static RuleFinding EvaluateOccurrence(RepoPath path, InformationTemplateOccurrence occurrence)
    {
        var key = InformationTemplateJson.KeyJson(occurrence.Key).GetRawText();
        return occurrence.State switch
        {
            InformationTemplateBindingState.DeclaredUnresolved when occurrence.Key.Mode == "dependent-family-v1" =>
                new(path.Value, "DTR-Evidence " + occurrence.Diagnostic, AdmissionEffect.Observe),
            _ when !occurrence.HasOrigin || occurrence.EscapeContinues is null => new(path.Value,
                "DTR-Undeclared " + key, AdmissionEffect.Observe),
            InformationTemplateBindingState.Undeclared => new(path.Value,
                "DTR-Undeclared " + key, AdmissionEffect.Observe),
            InformationTemplateBindingState.DeclaredValidated when occurrence.EvidenceRef is not null =>
                new(path.Value, "DTR-Declared " + key
                    + " escape_from=" + System.Text.Json.JsonSerializer.Serialize<object?>(occurrence.Family ?? (object?)occurrence.EscapeFrom)
                    + " escape_continues=" + System.Text.Json.JsonSerializer.Serialize(occurrence.EscapeContinues)
                    + " bridge_kind=" + occurrence.BridgeKind, AdmissionEffect.Observe),
            _ => new(path.Value, "DTR-Evidence " + (occurrence.Diagnostic
                ?? "selected occurrence lacks a source-bound certificate"), AdmissionEffect.Observe),
        };
    }

    private static bool IsPublicTheorem(LeanDeclaration declaration, ImmutableDictionary<string, string> sourceNames)
    {
        // Inspector preserves the kernel name: private declarations start with
        // _private.; include_in_statement excludes internal-detail theorems.
        // Its separate --statement-identities stream's olean part is not a
        // visibility field in the admission report.
        if (declaration.Kind != "theorem" || !declaration.IncludeInStatement
            || declaration.Name.StartsWith("_private.", StringComparison.Ordinal)) return false;
        // Only theorems the module's source spells out are authored. Everything the
        // compiler or a command generates (congruence lemmas such as
        // `legendreSym.congr_simp`, equation lemmas, registration companions) has no
        // author who could register it, so it carries no obligation. A handwritten
        // theorem whose name imitates a companion suffix is still in the source map.
        return sourceNames.TryGetValue(declaration.Name, out var kind) && kind is "theorem" or "lemma";
    }
}
