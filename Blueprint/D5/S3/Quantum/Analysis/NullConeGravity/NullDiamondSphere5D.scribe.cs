using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class NullDiamondSphere5DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Round celestial measure and the inverse square-root angular singularity.",
        H("Round measure on the celestial three-sphere"),
        Blocks(
            Entry("round-measure", "sphere5DMeasure", "Round measure",
                "Equip the unit sphere in four-dimensional Euclidean space with the surface measure "
                + "induced by Euclidean volume.", DescribeRole.Definition),
            Entry("round-mass", "sphere5D_measure_univ", "Total mass",
                "The round sphere has measure 2π², four times the volume of the four-dimensional unit ball."),
            Entry("dot-pushforward", "sphere5D_dot_pushforward", "Distribution of the dot product",
                "For a fixed unit direction n, the dot product with n sends round measure to the density "
                + "4π√(1 − x²) on the interval from −1 to 1. Slice the solid cap of directions above "
                + "a nonnegative threshold into three-dimensional balls. Integration of their volumes "
                + "gives the upper tails, and reflection gives the lower half of the distribution."),
            Entry("dot-rotation", "sphere5D_dot_rotation", "Orthogonal invariance",
                "Every orthogonal transformation of the fixed direction yields the same dot-product distribution."),
            Entry("dot-integral", "sphere5D_dot_integral", "Angular integration",
                "Integrating a measurable real function of the dot product against round measure gives "
                + "its integral against the semicircle density on the interval from −1 to 1."),
            Entry("angular-diagonal", "sphere5D_diag_null", "Angular diagonal",
                "The pairs with dot product one form a null set for the product of round measures. "
                + "Each angular section of this set has zero measure by the dot-product density."),
            Entry("singularity-integrable", "sphere5D_inv_sqrt_sq_integrable", "Integrable squared singularity",
                "The reciprocal of one minus the dot product is integrable against product round measure. "
                + "The substitution x = sin θ turns the normalized density divided by one minus x "
                + "into 1 + sin θ on the interval from −π/2 to π/2."),
            Entry("singularity-integral", "sphere5D_inv_sqrt_sq_integral", "Exact singularity integral",
                "The integral over the two spheres is 8π⁴. Each angular section contributes 4π² "
                + "and the outer sphere contributes its total measure 2π²."),
            Entry("singularity-l2", "sphere5D_inv_sqrt_memLp", "Square-integrable angular kernel",
                "The inverse square root of one minus the dot product belongs to complex L² on the product sphere. "
                + "This supplies angular control for the weighted Hilbert–Schmidt kernel in five dimensions."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
