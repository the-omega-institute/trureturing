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
    string? BindingSourcePath);

internal sealed record InformationTemplateUniverse(
    ImmutableDictionary<InformationOccurrenceKey, InformationTemplateOccurrence> Occurrences,
    ImmutableHashSet<InformationOccurrenceKey> Inventory,
    ImmutableHashSet<string> GovernedSources,
    ImmutableHashSet<string> AssessedSources);

internal sealed record DeclaredTemplateFinding(string Code, string Path, string Detail);

// The core consumes independently reconciled, source-bound evidence. Its domain
// observer is output-only: it cannot alter any predicate or supply an admission.
internal static class DeclaredTemplateBindingRule
{
    internal static ImmutableArray<DeclaredTemplateFinding> Evaluate(
        InformationTemplateActivation activation,
        RepositorySnapshot baseline,
        RepositorySnapshot candidate,
        ImmutableDictionary<InformationOccurrenceKey, InformationTemplateDebtRow> baseDebt,
        ImmutableDictionary<InformationOccurrenceKey, InformationTemplateDebtRow> headDebt,
        InformationTemplateUniverse before,
        InformationTemplateUniverse after,
        IReadOnlySet<string> changedPaths,
        Action<InformationOccurrenceKey>? observedInvocation = null)
    {
        var findings = ImmutableArray.CreateBuilder<DeclaredTemplateFinding>();
        void Add(string code, string detail, string? path = null) => findings.Add(new(
            code, path ?? InformationTemplateDebtStore.ActivationPath, detail));

        if (!candidate.TryGetFile(InformationTemplateDebtStore.ActivationPath, out var candidateActivation)
            || !baseline.TryGetFile(InformationTemplateDebtStore.ActivationPath, out var baseActivation))
        {
            Add("DTR-Required", "protected activation mechanism is missing");
            return findings.ToImmutable();
        }

        // Candidate bytes are never the effective activation input. The only
        // permitted transition is to the active encoding of the protected seed.
        if (!candidateActivation.RawBytes.AsSpan().SequenceEqual(baseActivation.RawBytes.AsSpan())
            && (activation.Activated || !candidateActivation.RawBytes.AsSpan().SequenceEqual(
                InformationTemplateDebtStore.WriteActivation(activation with { Activated = true }).AsSpan())))
            Add("DTR-Activation", "seed retargeting, deactivation or noncanonical activation change");

        CheckInventory(before, "base", Add);
        CheckInventory(after, "candidate", Add);
        foreach (var row in baseDebt.Values.Concat(headDebt.Values))
            if (row.SeedBase != activation.SeedBase) Add("DTR-Seed", "row differs from protected seed_base");

        if (!activation.Activated)
        {
            // Inactive installation and seed-only changes cannot start migration.
            foreach (var occurrence in after.Occurrences.Values)
                if (occurrence.State != InformationTemplateBindingState.Undeclared
                    && (!before.Occurrences.TryGetValue(occurrence.Key, out var old)
                        || old != occurrence))
                    Add("DTR-Activation", "declaration migration precedes activation", occurrence.RegistrationSourcePath);
            if (baseDebt.Count > 0 && !baseDebt.Keys.ToHashSet().SetEquals(headDebt.Keys))
                Add("DTR-Activation", "seed-only phase cannot discharge or replace debt");
            return findings.ToImmutable();
        }

        // Set inclusion, not cardinality. A same-sized replacement is new debt.
        if (headDebt.Keys.Any(key => !baseDebt.ContainsKey(key)))
            Add("DTR-Subset", "candidate debt is not a subset of protected debt");
        foreach (var (key, row) in headDebt)
            if (baseDebt.TryGetValue(key, out var old)
                && !InformationTemplateDebtStore.WriteRow(row).AsSpan().SequenceEqual(
                    InformationTemplateDebtStore.WriteRow(old).AsSpan()))
                Add("DTR-Subset", "surviving debt row changed", InformationTemplateDebtStore.PathFor(key));

        foreach (var key in before.Inventory)
            if (!after.Inventory.Contains(key))
                Add("DTR-Inventory", "removing an occurrence does not discharge its enduring obligation",
                    InformationTemplateDebtStore.PathFor(key));

        var undeclared = after.Occurrences.Values.Where(o => o.State == InformationTemplateBindingState.Undeclared)
            .Select(o => o.Key).ToHashSet();
        if (!undeclared.SetEquals(headDebt.Keys))
            Add("DTR-Residual", "debt differs from independently collected undeclared occurrences");

        var touched = baseDebt.Values.Where(row => IsTouched(row, baseline, candidate, changedPaths,
                before.Occurrences.GetValueOrDefault(row.Key), after.Occurrences.GetValueOrDefault(row.Key)))
            .Select(row => row.Key).ToHashSet();
        if (touched.Overlaps(headDebt.Keys) || touched.Count > 0 && headDebt.Count >= baseDebt.Count)
            Add("DTR-Touched", "every touched debt occurrence must discharge and the debt set must strictly shrink");

        foreach (var occurrence in after.Occurrences.Values)
        {
            if (!before.Inventory.Contains(occurrence.Key)
                && occurrence.State != InformationTemplateBindingState.DeclaredValidated)
                Add("DTR-New", "candidate-new occurrence requires validated declaration", occurrence.RegistrationSourcePath);
            if (occurrence.State == InformationTemplateBindingState.DeclaredUnresolved)
                Add("DTR-Evidence", occurrence.Diagnostic ?? "declared occurrence is unresolved", occurrence.RegistrationSourcePath);
        }

        var delta = after.Occurrences.Values.Where(o => !before.Inventory.Contains(o.Key)
                || touched.Contains(o.Key) || o.ContentInputs.Any(i => changedPaths.Contains(i.Path))
                || o.BindingSourcePath is { } binding && changedPaths.Contains(binding))
            .Select(o => o.Key).ToImmutableHashSet();
        foreach (var key in SelectDomain(headDebt.Count, after.Inventory, delta))
        {
            observedInvocation?.Invoke(key);
            if (!after.Occurrences.TryGetValue(key, out var occurrence)
                || occurrence.State != InformationTemplateBindingState.DeclaredValidated
                || occurrence.EvidenceRef is null)
                Add("DTR-Evidence", "selected occurrence lacks a source-bound certificate",
                    InformationTemplateDebtStore.PathFor(key));
        }

        return findings.ToImmutable();
    }

    internal static ImmutableHashSet<InformationOccurrenceKey> SelectDomain(int residualCount,
        ImmutableHashSet<InformationOccurrenceKey> universe, ImmutableHashSet<InformationOccurrenceKey> delta) =>
        residualCount == 0 ? universe : delta;

    private static void CheckInventory(InformationTemplateUniverse value, string side,
        Action<string, string, string?> add)
    {
        if (!value.Inventory.SetEquals(value.Occurrences.Keys)
            || !value.GovernedSources.SetEquals(value.AssessedSources))
            add("DTR-Inventory", side + " inventory/registry/source coverage mismatch", null);
    }

    private static bool IsTouched(InformationTemplateDebtRow row, RepositorySnapshot baseline,
        RepositorySnapshot candidate, IReadOnlySet<string> changed,
        InformationTemplateOccurrence? before, InformationTemplateOccurrence? after)
    {
        if (before is null || after is null || before.StatementIdentity != after.StatementIdentity
            || before.State != after.State || before.BindingSourcePath != after.BindingSourcePath)
            return true;
        if (after.BindingSourcePath is { } binding && changed.Contains(binding)) return true;
        var firstPin = "Golden/Frozen/state/" + after.RegistrationSourcePath + ".json";
        if (changed.Contains(firstPin) && !baseline.TryGetFile(firstPin, out _)) return true;
        // Judge/compiler/toolchain files do not enter the producer's content slice.
        return row.ContentInputs.Any(input =>
            !baseline.TryGetFile(input.Path, out var old) || !candidate.TryGetFile(input.Path, out var current)
            || !old.RawBytes.AsSpan().SequenceEqual(current.RawBytes.AsSpan()));
    }
}
