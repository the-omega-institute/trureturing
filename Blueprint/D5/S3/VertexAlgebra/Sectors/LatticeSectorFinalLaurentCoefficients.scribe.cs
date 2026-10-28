using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeSectorFinalLaurentCoefficientsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LatticeSectorFinalLaurentCoefficients", H("LatticeSectorFinalLaurentCoefficients"), Blocks(
            Describe.Lean(DescribeId.Create("latticesectorfinallaurentcoefficients-actual-three-field-final-laurent-coefficients"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorFinalLaurentCoefficients.actual_three_field_final_laurent_coefficients"),
                H("actual_three_field_final_laurent_coefficients"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary lattice data, charges and descendant states, a locality order k is chosen before the fourth charge and state. The original statewise bounds a and generally infinite numerator P retain their truncation and all six signed product laws. For every signed exponent, the actual left-nested canonical channel equals the existing Laurent coefficient of the triangular substitution of P. Two actual canonical truncation calls give one uniform first-coordinate cutoff and a separate second-coordinate cutoff for each fixed first exponent, uniform in the third coordinate. The Laurent expression has the same nested support by its signed cone bounds. Supported injectivity and the literal finite six-factor action then identify the two families. No energy, definiteness, charge sign, finite-series or channel-equality premise is imposed. This coefficient identity supplies no analytic, sewing or complete physical realization."))), DescribeRole.Theorem))));
}
