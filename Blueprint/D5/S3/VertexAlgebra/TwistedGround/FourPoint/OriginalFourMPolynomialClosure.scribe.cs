using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMPolynomialClosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Extending the A and D Comparison to Polynomials",
        H("Extending the A and D Comparison to Polynomials"),
        Blocks(Describe.Lean(DescribeId.Create("radial-ad-crossing-of-words"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPolynomialClosure.radial_AD_crossing_of_words"),
            H("The A and D comparison on homogeneous oscillators"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Expand each oscillator polynomial on its finite monomial support. Multilinearity includes the native lowering of the detector and retains the signed charge sum."))),
            DescribeRole.Theorem))));
}
