namespace StrataLint.Engine;

internal sealed partial class BackfillInventoryDocument
{
    private static DigestionUpstream? ParseUpstream(
        string atomId, IReadOnlyDictionary<string, object?> receipts)
    {
        if (!receipts.ContainsKey("upstream")) return null;
        var label = $"entry {atomId} upstream receipt:";
        var raw = Mapping(receipts["upstream"], label + " must be a mapping");
        ExactKeys(raw, ["justification", "declarations", "mathlib_rev", "probe_sha256", "probe_axioms",
            "previous_atom_id", "next_atom_id"], label);
        var receipt = new DigestionUpstream(
            Scalar(raw, "justification", label + " justification"),
            Strings(List(raw, "declarations", label + " declarations must be a list"), label + " declarations"),
            Scalar(raw, "mathlib_rev", label + " mathlib_rev"),
            Scalar(raw, "probe_sha256", label + " probe_sha256"),
            Strings(List(raw, "probe_axioms", label + " probe_axioms must be a list"), label + " probe_axioms"),
            NullableScalar(raw, "previous_atom_id", label + " previous_atom_id"),
            NullableScalar(raw, "next_atom_id", label + " next_atom_id"));
        if (receipt.ValidationError is { } error) throw new FormatException(label + " " + error);
        return receipt;
    }
}
