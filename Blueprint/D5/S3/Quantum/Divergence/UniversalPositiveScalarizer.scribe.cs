using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class UniversalPositiveScalarizerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A selected column of an actual common center controls the joint basis-residual Gram.",
        H("Actual selected-column joint Gram extraction"), Blocks(
            Describe.Lean(DescribeId.Create("actual-selected-column-joint-gram"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.selected_column_joint_gram"),
                H("One scalar family for the entire basis Gram"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let a and b be finite nonempty types, let Phi be an actual completely positive trace-preserving channel from a to b, and let k be a nonnegative real number. Its canonical normalized Kraus family defines an isometric column J, the representation pi(A)=A tensor I_Env, and the projection e=I-J J adjoint. Write Phi*(A)=J adjoint pi(A) J. Index the matrix-unit basis E_i by I=b times b. Stack C_i=J adjoint pi(E_i)e vertically into C. The universal premise tests, for every finite quantum reference R and every joint matrix Y, the scalar infimum over general complex matrix centers X against every positive-definite weight Z. Its right side is k times the actual adjoint defect Phi*_R(Y Y adjoint)-Phi*_R(Y)Phi*_R(Y) adjoint.")),
                    Paragraph(Text("For any selected index i0 in I, there exists one scalar family x:I to the complex numbers such that k C C adjoint-D D adjoint is positive semidefinite, where D stacks all Phi*(E_i)-x_i I_a. The inequality includes every cross term between distinct basis residuals and includes k=0. No density matrix, defect factorization, linear scalar functional or sparsity of a matrix center is an assumption.")),
                    Paragraph(Text("The proof derives preservation of products and adjoints by pi, the actual Kraus compression formula, and preservation of adjoints by Phi*. These identities make the actual amplified defect Hermitian. Pack E_i in column i0 of a joint matrix Y. The packed defect is exactly C C adjoint. The finite common-center theorem then provides a full matrix X. The residual P=Phi*_I(Y)-X tensor I_a has selected column D with x_i=X(i,i0). Its remaining columns form R after zeroing the selected column. Partitioning the Gram sum gives P P adjoint=D D adjoint+R R adjoint. Adding the positive Gram R R adjoint to the common-center slack yields the stated bound; the full residual Gram is not identified with D D adjoint.")),
                    Paragraph(Text("This is a partial inference for the original all-finite Umegaki coefficient problem. The heterogeneous Douglas factor, unital functional, trace density, contractive polar correction allowing singular density, supported Gram flip and simultaneous reference inequalities at the same weighted partial-trace center remain separate obligations. The coefficient equality, literature novelty and open-problem KPI are not established."))),
                DescribeRole.Theorem))));
}
