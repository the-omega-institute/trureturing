using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMProjectionModesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal four-point occupation selectors on the signed mode diagonals",
        H("Signed Mode Projection"),
        Blocks(Describe.Lean(DescribeId.Create("fourm-project-occupations-signed-diagonal"),
            DeclarationHandle.Create(
                "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMProjectionModes.project_occupations_on_signed_diagonal"),
            H("Left lowering coefficients on the actual diagonal"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The original two selectors evaluate to one on the supported "
                + "occupations, leaving the finite negative-lowering coefficients and the "
                + "original overall parity phase."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourm-detector-selector-signed-diagonal"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMProjectionModes.detector_selector_on_signed_diagonal"),
                H("Detector displacement for arbitrary signed modes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Lowering the detector by ell shifts the signed "
                    + "diagonal by ell, directly in the original output selector."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourm-bounded-external-sewn-charge"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMProjectionModes.bounded_external_sewn_charge"),
                H("The original compact occupation inside the common mode box"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The embedding preserves the native affine coefficient "
                    + "and all four occupation factorials in the original sewn charge term."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourm-physical-chart-normalized-overlap"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMProjectionModes.physical_chart_coefficient_overlap_normalized"),
                H("Native normalization of the real overlap coefficients"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The rank-24 sector identity uses the inverse sixth "
                    + "power of the common real coordinate to normalize the B coefficient."))),
                DescribeRole.Theorem))));
}
