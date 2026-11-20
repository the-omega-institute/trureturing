using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class ActualGroundRealFormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive Real Form of the Selected Twisted Ground",
        H("Positive Real Form of the Selected Twisted Ground"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-ground-real-form"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualGroundRealForm.actual_ground_real_form"),
            H("Positive Real Form of the Selected Twisted Ground"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For an integral symmetric even lattice with unit Gram determinant, let B be the literal selected ground factor of actualForm on ActualGround. The standard Euclidean Hermitian form in the existing ground coordinates is averaged over the finite quotient action. The resulting form H is invariant by reindexing the sum, Hermitian by conjugate symmetry and positive because each quotient element acts invertibly.")),
                Paragraph(Text("Finite-dimensional duality gives a conjugate-linear operator A with H(Ax,y) = B(x,y). The two invariances and positive definiteness of H imply that A commutes with the quotient action. Its square is complex-linear, so the actual scalar commutant makes it scalar. Symmetry of B gives H(A²x,x) = H(Ax,Ax), whose right side is strictly positive for nonzero x by nondegeneracy of B. The scalar is therefore a positive real number.")),
                Paragraph(Text("Write r for the positive square root of the scalar and J for A divided by r. Then J is an involution commuting with the selected action, B(Jx,y) = r H(x,y) and B(Jx,Jy) is the complex conjugate of B(x,y). On fixed points of J the bilinear form is real and positive definite. The determinant witness in the Golay–Leech construction instantiates this result on its selected ground.")),
                Paragraph(Text("Borcherds, Monstrous moonshine and monstrous Lie superalgebras (1992), Theorems 5.1 and 6.1, uses positive moonshine and contravariant forms in the no-ghost and Lie algebra arguments. Dong–Lin, Unitary vertex operator algebras, Theorems 4.12, 4.14 and 4.15, treats unitary twisted lattice modules and the moonshine extension. The finite quotient argument here determines the normalization against the repository's selected bilinear form."))),
            DescribeRole.Theorem))));
}
