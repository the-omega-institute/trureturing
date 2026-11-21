using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class PrincipalTrianglePhaseGeometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three orthonormal pairs with all cross magnitudes above one half force a robust non-real triangle.",
        H("The complex phase obstruction for three two-vector fibres"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rt-principal-three-fibre-phase"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Recovery/PrincipalTrianglePhaseGeometry.three_fibre_complex_phase"),
                H("Quantitative complex phase obstruction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For three orthonormal pairs with each cross overlap at least m, where m is above one "
                    + "half, at least one of the eight triangular products has absolute imaginary part at "
                    + "least m cubed times the stated sine cutoff. The argument combines triangle Gram "
                    + "positivity with the constraints from the cross-fibre plaquettes."))),
                DescribeRole.Theorem))));
}
