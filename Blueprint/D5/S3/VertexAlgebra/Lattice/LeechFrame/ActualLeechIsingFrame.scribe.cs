using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.LeechFrame;

internal sealed class ActualLeechIsingFrameDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechIsingFrame.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Forty-eight explicit states whose central-charge-one-half Virasoro modes commute on the Leech orbifold.",
        H("The Leech frame of 48 Virasoro states"),
        Blocks(
            Paragraph(Text("Use both signs in each of the 24 directions of the actual norm-four frame. "
                + "The states are distinct and their sum is the conformal state of the orbifold. "
                + "The norm-four state formula retains the Dong-Mason-Zhu attribution recorded by "
                + "Shimakura, arXiv:1202.6107, equation (1.3).")),
            Entry("actual-leech-ising-axis", "axis", "The signed axes",
                "Embed the signed norm-four state from the fixed lattice sector with zero twisted component.",
                DescribeRole.Definition),
            Entry("actual-leech-ising-inverse-gram", "actualInverse_entry", "Inverse Gram matrix",
                "Each inverse Gram entry is one quarter of the corresponding sum of charge outer products. "
                + "The current-space basis has squared norm four, which determines its coordinate functionals."),
            Entry("actual-leech-ising-conformal-sum", "conformal_sum", "Sum of the axes",
                "The charged terms cancel within each signed pair. The inverse Gram identity identifies "
                + "the remaining quadratic sum with the Sugawara stress state in the orbifold."),
            Entry("actual-leech-ising-conformal-modes", "conformal_mode_sum", "Sum of the conformal modes",
                "Linearity of the original orbifold state-field map gives the mode sum on the whole carrier."),
            Entry("actual-leech-ising-virasoro", "axis_virasoro", "Virasoro action of each axis",
                "Each axis satisfies the integer-mode Virasoro relation at central charge one half "
                + "on the fixed and odd twisted sectors."),
            Entry("actual-leech-ising-lattice-mixed-products", "lattice_mixed_products",
                "Mixed products in the lattice",
                "For distinct indices in the same direction, the signs are opposite. For distinct "
                + "directions, the charges are orthogonal. In either case every nonnegative product vanishes."),
            Entry("actual-leech-ising-distinct", "axis_injective", "Distinct axis states",
                "The third product of an axis with itself is a nonzero multiple of the vacuum. "
                + "Together with mixed-product vanishing this proves injectivity."),
            Entry("actual-leech-ising-orbifold-mixed-products", "orbifold_mixed_products",
                "Mixed products in the orbifold",
                "The fixed-source coefficient of the original orbifold field carries the lattice "
                + "vanishing to the embedded axis states."),
            Entry("actual-leech-ising-commuting-modes", "axis_modes_commute", "Commuting modes of distinct axes",
                "The lattice and odd twisted commutator formulas express their commutators "
                + "through the nonnegative mixed products. Every summand vanishes."))));

    private static DocumentBlock Entry(string id, string declaration, string heading, string prose,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
