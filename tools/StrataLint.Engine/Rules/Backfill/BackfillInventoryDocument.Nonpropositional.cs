namespace StrataLint.Engine;

internal sealed partial class BackfillInventoryDocument
{
    private static DigestionStatus ParseStatus(string migration, string truth)
    {
        var status = new DigestionStatus(ParseMigration(migration), ParseTruth(truth));
        if ((status.Migration == DigestionMigrationState.Nonpropositional)
            != (status.Truth == DigestionTruthState.Inapplicable))
        {
            throw new FormatException($"invalid digestion status pair: {migration}-{truth}");
        }
        return status;
    }

    private static DigestionNonpropositional? ParseNonpropositional(
        string atomId, IReadOnlyDictionary<string, object?> receipts)
    {
        if (!receipts.ContainsKey("nonpropositional")) return null;
        var raw = Mapping(receipts["nonpropositional"], $"entry {atomId} nonpropositional must be a mapping");
        ExactKeys(raw, ["justification", "previous_atom_id", "next_atom_id"], $"entry {atomId} nonpropositional");
        var receipt = new DigestionNonpropositional(
            Scalar(raw, "justification", $"entry {atomId} nonpropositional justification"),
            NullableScalar(raw, "previous_atom_id", $"entry {atomId} nonpropositional previous_atom_id"),
            NullableScalar(raw, "next_atom_id", $"entry {atomId} nonpropositional next_atom_id"));
        if (!receipt.IsValid)
            throw new FormatException($"entry {atomId} nonpropositional requires trimmed justification and canonical atom ids or null");
        return receipt;
    }
}
