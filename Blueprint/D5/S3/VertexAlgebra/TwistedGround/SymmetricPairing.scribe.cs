using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class SymmetricPairingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Symmetric Pairing on the Selected Actual Ground",
        H("A Symmetric Pairing on the Selected Actual Ground"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-symmetric-ground-pairing"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/SymmetricPairing.actual_symmetric_ground_pairing"),
            H("A Symmetric Pairing on the Selected Actual Ground"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every integral symmetric even lattice D with integer unit determinant hu, the exact selected ActualGround(D,hu) admits a nondegenerate symmetric complex bilinear form. The form is invariant under the original reflection quotient. For every integral charge alpha it satisfies B(R_alpha u,v)=(-1)^(G(alpha,alpha)/2) B(u,R_alpha v), with the same charge on both sides.")),
                Paragraph(Text("Let A be the finite average on bilinear forms and F interchange arguments. The operator S=A+F composed with A has trace two, since tr(A)=tr(F composed with A)=one. Hence S is nonzero. An elementary bilinear basis contains a seed with nonzero image. This image is symmetric by the formula B(u,v)=A(seed)(u,v)+A(seed)(v,u), and it is invariant because each summand is invariant.")),
                Paragraph(Text("The invariant nonzero form has zero radical by irreducibility of the selected representation. Finite-dimensional duality makes it nondegenerate. The original charge square law and invariance imply the signed adjointness law. The construction uses the original selected carrier and representation, including rank zero.")),
                Paragraph(Text("The finite ground pairing does not by itself construct an oscillator Wick extension, an all-source opposite covariance theorem, a two-twisted-input intertwiner, a Monster action, a fusion rule, string theory or an AdS/CFT bridge."))),
            DescribeRole.Theorem))));
}
