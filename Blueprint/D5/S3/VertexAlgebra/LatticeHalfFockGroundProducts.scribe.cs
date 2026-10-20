using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockGroundProductsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The chosen actual quotient representation realizes the lattice cocycle product and exchange.",
        H("Actual Ground Products and Cocycle Exchange"),
        Blocks(
            Paragraph(Text("For D:LatticeData and hu:IsUnit D.G.det, groundAction is the lift of a "
                + "charge through the same groundRepresentation on ActualGround D hu used by the "
                + "charged tensor coefficients. The inherited representation theorem supplies the "
                + "central sign action -1. Natural-sign induction and reduction to F2 identify every "
                + "central scalar; no new representation or exchange-law hypothesis is introduced.")),
            Describe.Lean(
                DescribeId.Create("half-fock-ground-action-product"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockGroundProducts.ground_action_product"),
                H("Actual ground actions multiply with the integral cocycle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("For all charges left and right, groundAction(left)*groundAction(right) "
                    + "equals epsilon D left right smul groundAction(left+right) as endomorphisms of "
                    + "ActualGround D hu. Multiplication in the actual sign extension and the "
                    + "representation homomorphism yield the exact cocycle normalization."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-ground-action-exchange"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockGroundProducts.ground_action_exchange"),
                H("The actual ground product exchanges by the pairing parity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("The product in left/right order equals paritySign(bilinear D left right) "
                    + "smul the product in right/left order. This consumed helper applies "
                    + "ground_action_product twice and the existing epsilon_skew identity, with "
                    + "charge-addition commutativity. PhysicalLocality uses it on the actual ground vector."))), DescribeRole.Theorem),
            Paragraph(Text("The construction and cocycle mechanism are inherited from the repository's "
                + "twisted ground realization and actual lattice cocycle. These exact consequences on "
                + "the chosen ActualGround are repository-derived. FLM is background attribution; its "
                + "full text is not an inspected source here. The determinant-unit premise is retained, "
                + "and the statements cover every charge and ground vector, including zero charges "
                + "and rank-zero data satisfying that premise. They supply ground factors, without "
                + "asserting oscillator locality, twisted Jacobi or analytic CFT.")))));
}
