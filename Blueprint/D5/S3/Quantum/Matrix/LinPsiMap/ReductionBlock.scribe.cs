using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.LinPsiMap;

internal sealed class ReductionBlockDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Matrix/LinPsiMap/ReductionBlock.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Eigenstructure/lin2016psimap");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reduction of a positive block supplies the reflected spectral comparison.",
        H("The map Psi and reduction-block positivity"), Blocks(
            Describe.Lean(DescribeId.Create("lin-psi-map"),
                DeclarationHandle.Create(Owner + "psi"),
                H("The trace reflection map"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every complex square matrix T, define Psi(T)=2 trace(T) I−T. The reduction map R(T)=trace(T) I−T is the related map used to construct the positive block in the argument."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lin-reduction-block-positivity"),
                DeclarationHandle.Create(Owner + "reduction_block_posSemidef"),
                H("Positivity of the reduction block"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Let the complex block matrix [A X; X-adjoint B] be positive semidefinite. Then [R(A) R(X-adjoint); R(X) R(B)] is positive semidefinite, in every finite dimension and without commutation or rank assumptions.")),
                    Paragraph(Text("For coordinate indices k and l, form the antisymmetric matrix F from the two matrix units at (k,l) and (l,k). One half of the sum of F T F-adjoint over all ordered pairs is trace(T) I−transpose(T). Apply these congruences simultaneously in both diagonal blocks to the transpose of the original positive block. The resulting positive sum has exactly the stated four blocks."))),
                DescribeRole.Theorem))));
}
