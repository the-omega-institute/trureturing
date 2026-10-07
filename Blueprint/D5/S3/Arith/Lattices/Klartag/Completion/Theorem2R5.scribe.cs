using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Completion;

internal sealed class Theorem2R5Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Completion/Theorem2R5.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform constants and completion of lattice packing.",
        H("Theorem2R5"),
        Blocks(
            Paragraph(Text("Uniform constants and completion of lattice packing. The results below relate theorem2r5 to the stochastic ellipsoid construction.")),
            Node("claim-3", "DriftSideW3B", "Drift Side W3B",
                "Theorem2R4.DriftSideW3 with B inside the ∀ m.", DescribeRole.Definition),
            Node("claim-4", "StateSupplyAdoptedR3B", "State Supply Adopted R3B",
                "Theorem2R4.StateSupplyAdoptedR3 with B inside the ∀ m.", DescribeRole.Definition),
            Node("claim-5", "driftSideW3B_of_stateSupplyR3B", "drift Side W3B of state Supply R3B",
                "Theorem2R4.driftSideW3_of_stateSupplyR3 at the B-family; the body is the original.", DescribeRole.Theorem),
            Node("claim-7", "klartag_packing_of_stateSupplyR3B", "klartag packing of state Supply R3B",
                "StateSupplyBypass.klartag_packing_of_stateSupplyR3 at the B-family.", DescribeRole.Theorem),
            Node("claim-8", "stateSupplyR3B_of_cut_light", "state Supply R3B of cut light",
                "CutVarianceLight.stateSupplyR3_of_cut_light at the B-family; the body is the original, which never mentions A or B.", DescribeRole.Theorem),
            Node("claim-9", "klartag_packing_final_lightB", "klartag packing final light B",
                "CutVarianceLight.klartag_packing_final_light at the B-family — the ellipsoid construction statement from a light-carrying per-line bundle whose terminal coefficient depends on the dimension.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
