using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class InformationTemplateDebtWriter
{
    internal static ImmutableDictionary<InformationOccurrenceKey, InformationTemplateDebtRow> Initialize(
        InformationTemplateActivation activation, string evaluatedRevision, RepositorySnapshot seed,
        InformationTemplateUniverse inventory)
    {
        if (activation.Activated || activation.SeedBase != evaluatedRevision)
            throw new FormatException("DTR-Seed: initialization requires the original protected inactive seed");
        RequireComplete(inventory);
        var rows = ImmutableDictionary.CreateBuilder<InformationOccurrenceKey, InformationTemplateDebtRow>();
        foreach (var occurrence in inventory.Occurrences.Values)
        {
            if (occurrence.State != InformationTemplateBindingState.Undeclared)
                throw new FormatException("DTR-Seed: seed-only initialization cannot enroll or discharge");
            if (!seed.TryGetFile(occurrence.RegistrationSourcePath, out var source))
                throw new FormatException("DTR-Seed: registration source absent from protected seed");
            var row = new InformationTemplateDebtRow(occurrence.Key, activation.SeedBase,
                occurrence.StatementIdentity, InformationTemplateJson.Sha256(source.RawBytes.AsSpan()),
                occurrence.ContentInputs);
            // Same strict loader used by admission, including every immutable input.
            var bytes = InformationTemplateDebtStore.WriteRow(row);
            rows.Add(row.Key, InformationTemplateDebtStore.ReadRow(InformationTemplateDebtStore.PathFor(row.Key),
                bytes.AsSpan(), activation.SeedBase, seed));
        }

        return rows.ToImmutable();
    }

    internal static ImmutableDictionary<InformationOccurrenceKey, InformationTemplateDebtRow> Discharge(
        InformationTemplateActivation activation,
        ImmutableDictionary<InformationOccurrenceKey, InformationTemplateDebtRow> debt,
        InformationTemplateUniverse inventory)
    {
        if (!activation.Activated) throw new FormatException("DTR-Activation: discharge precedes activation");
        RequireComplete(inventory);
        var retained = debt.ToBuilder();
        foreach (var (key, row) in debt)
        {
            if (row.SeedBase != activation.SeedBase) throw new FormatException("DTR-Seed: mixed or retargeted seed");
            if (!inventory.Occurrences.TryGetValue(key, out var occurrence))
                throw new FormatException("DTR-Inventory: deleting registration cannot discharge debt");
            switch (occurrence.State)
            {
                case InformationTemplateBindingState.DeclaredValidated:
                    if (occurrence.EvidenceRef is null)
                        throw new FormatException("DTR-Evidence: validated occurrence has no certificate");
                    InformationTemplateJson.Hash(occurrence.EvidenceRef, 64);
                    retained.Remove(key);
                    break;
                case InformationTemplateBindingState.DeclaredUnresolved:
                    throw new FormatException("DTR-Evidence: unresolved declaration cannot discharge debt");
                case InformationTemplateBindingState.Undeclared:
                    break;
                default:
                    throw new FormatException("DTR-Evidence: unknown binding state");
            }
        }

        return retained.ToImmutable();
    }

    private static void RequireComplete(InformationTemplateUniverse inventory)
    {
        if (!inventory.Inventory.SetEquals(inventory.Occurrences.Keys)
            || !inventory.GovernedSources.SetEquals(inventory.AssessedSources))
            throw new FormatException("DTR-Inventory: incomplete authoritative inventory");
    }
}
