using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.ChargedResidue;

internal sealed class QuadraticResidueDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Formal collision residue coefficients.",
        H("QuadraticResidue"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("charged-residue-collision-scalar-jacobian"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/ChargedResidue/QuadraticResidue.collision_scalar_jacobian"),
                H("The actual collision coefficients include the Jacobian"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("For all signed integers a and B and natural N, collisionScalar is transported under h=X*(2+X). Every signed half exponent becomes its integer exponent; the normalized collision unit becomes (2+X)/2. The coefficient formula retains the inverse (N+1)st power of 2+X and the exact derivative 2*(1+X)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("charged-residue-collision-scalar-coordinate"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/ChargedResidue/QuadraticResidue.collision_scalar_coordinate"),
                H("Normalized collision residue in the quadratic coordinate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("Combining the Jacobian with the coordinate unit gives collisionScalar(a,B,N)=2^(2*B+1) times the Nth coefficient of (1+X)^(a+1)*(2+X)^(-2*B-N-1). Integer exponents are represented by the existing binomial series and actual unit powers. This is a coefficient identity and does not by itself prove the full physical forward law."))),
                DescribeRole.Theorem))));
}
