using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class LeechQuadraticReductionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original cocycle diagonal is the integral half-norm quadratic refinement.",
        H("The Original Quadratic Refinement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("leechquadraticreduction"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/LeechQuadraticReduction.quadratic_integral"),
                H("The Original Quadratic Refinement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For arbitrary original even integral LatticeData, the bilinear lower-triangular cocycle defines a quadratic form over F2 by evaluation on the diagonal. The original cocycle_reduction and integral_cocycle_square identities identify its value on an integral charge with half the original Gram norm modulo two.")),
                    Paragraph(Text("The literal Leech hyperbolic certificate uses this identity to certify singular frame vectors in the original charge coordinates. This is a consumed application of the existing reduction identities, not an independent new half-norm theorem."))),
                DescribeRole.Theorem))));
}
