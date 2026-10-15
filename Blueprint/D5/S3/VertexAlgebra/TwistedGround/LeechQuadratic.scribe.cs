using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class LeechQuadraticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original Leech quadratic refinement has a literal hyperbolic basis.",
        H("The Original Leech Quadratic Space"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("leechquadratic"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/LeechQuadratic.original_plus_type"),
                H("The Original Leech Quadratic Space"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let D be the literal ExplicitLeechLattice.data, with gramMatrix in its original lattice-charge coordinates. The form q(v) is the diagonal of the original modTwoCocycle, not a function on ambient Euclidean coordinates. For every integral charge a, q(reduceCharge(a)) is the reduction of bilinear(D,a,a)/2. Its polar form is the original modTwoPairing.")),
                    Paragraph(Text("The literalIntegralVectors have the order p0,...,p11,f0,...,f11. Their twenty-four singular values and all 576 polar pairings give q(p_i)=q(f_i)=0, B(p_i,p_j)=B(f_i,f_j)=0 and B(p_i,f_j)=delta_ij. The integer matrix of their Gram rows is kernel-checked against literalIntegralVectors times the original gramMatrix; it only factors the same exact arithmetic. Evaluation against partners isolates each coefficient of a linear dependence. Equality of dimension and index cardinality gives an actual basis, without enumerating the 2^24 charges. This is plus type on the original quadratic space.")),
                    Paragraph(Text("The literal frame vectors are taken from the completed mod-two hyperbolic-frame design. The general reduction and half-norm identities reuse LatticeTwistedGroundRealization.cocycle_reduction and integral_cocycle_square. The Gram data and lattice construction remain those of ExplicitLeechBasis and ExplicitLeechLattice."))),
                DescribeRole.Theorem))));
}
