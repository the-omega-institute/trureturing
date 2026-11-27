using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.FixedC2;

internal sealed class ActualFixedC2ChargedOrbitFiniteDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOrbitFinite.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fixed C2 image of every nonzero Leech charge orbit is finite-dimensional.",
        H("Finite Dimension of the Nonzero Charge Orbit Images"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-charged-orbit-in-single-span"),
                DeclarationHandle.Create(Prefix + "leech_charged_orbit_image_le_single_span"),
                H("The whole orbit image lies in the charged span"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Pull the span of neutral multiples back to the fixed carrier "
                    + "under the quotient map. It contains the ground and every single oscillator. "
                    + "Every neutral quadratic has its class in the neutral image, so the pullback "
                    + "is stable under all the quadratic (-1)-modes. The charged word induction then "
                    + "puts the entire fixed orbit in the pullback."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-nonzero-orbit-image-finite"),
                DeclarationHandle.Create(Prefix + "leech_fixed_charge_orbit_image_finite"),
                H("Each nonzero orbit image is finite-dimensional"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every nonzero Leech charge the orbit image injects "
                    + "as a subspace of the finite-dimensional charged span. This supplies the "
                    + "finite-dimensionality of each nonzero summand in the short charge support."))),
                DescribeRole.Theorem))));
}
