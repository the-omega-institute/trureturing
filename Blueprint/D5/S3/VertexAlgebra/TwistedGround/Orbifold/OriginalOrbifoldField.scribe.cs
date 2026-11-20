using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Orbifold;

internal sealed class OriginalOrbifoldFieldDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Original Two-Sector Orbifold Field",
        H("The Original Two-Sector Orbifold Field"),
        Blocks(
            Entry("carrier", "Carrier", "State space",
                "The state space is the product of the fixed lattice sector and the negative twisted parity sector.",
                DescribeRole.Definition),
            Entry("vacuum-state", "vacuumState", "Vacuum state",
                "The vacuum is the fixed lattice vacuum paired with the zero twisted state.", DescribeRole.Definition),
            Entry("mode", "mode", "Four mode blocks",
                "The mode combines the fixed lattice field, the fixed-action parity slice, the original right coefficient, "
                + "and the original inverse-pairing coefficient.", DescribeRole.Definition),
            Entry("mode-tail", "mode_tail", "Lower truncation",
                "For each pair of states, all integer modes at and above a common bound vanish. "
                + "The bound combines the field tails and the grade bound of the inverse-pairing coefficient."),
            Entry("field", "Y", "Assembled field",
                "Use lower truncation to assemble the modes into a vertex operator that is complex-linear in its source state.",
                DescribeRole.Definition),
            Entry("normalized-mode", "Y_ncoeff", "Normalized coefficient",
                "The normalized coefficient of the assembled field is the corresponding mode."),
            Entry("mode-on-states", "Y_ncoeff_apply", "Mode on two states",
                "The fixed and inverse-pairing terms sum in the fixed sector. "
                + "The parity-slice and original right-field terms sum in the twisted sector."),
            Entry("fixed-modes", "Y_fixed_ncoeff_apply", "Fixed source",
                "Each mode of a fixed source acts on the fixed sector by the lattice mode and on the twisted sector by the parity slice."),
            Entry("fixed-parity-borcherds", "fixedParitySlice_borcherds", "Borcherds identity on the negative sector",
                "For two fixed inputs and any negative twisted input, all three signed coefficient families have "
                + "finite support. The native transport law yields the Borcherds equality for all three integer indices."),
            Entry("assembled-vvm-borcherds", "Y_borcherds_vvm", "Borcherds identity for the assembled field",
                "For two fixed states and one negative twisted state, the parity inclusion carries the three "
                + "finite coefficient families and their signed Borcherds equality into the assembled carrier."),
            Entry("twisted-modes", "Y_twisted_ncoeff_apply", "Negative twisted source",
                "A twisted source exchanges sectors through the inverse-pairing coefficient and the original right coefficient."),
            Entry("vacuum-modes", "vacuum_ncoeff", "Vacuum modes",
                "The vacuum field acts as the identity at mode minus one and vanishes at every other integer mode."),
            Entry("creation-modes", "creation_ncoeff", "Creation and regularity",
                "Acting on the vacuum, mode minus one returns the source state and every higher mode vanishes. "
                + "In the twisted part, the original right sum reduces to its zeroth term."))));

    private static DocumentBlock Entry(string id, string declaration, string heading, string prose,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
