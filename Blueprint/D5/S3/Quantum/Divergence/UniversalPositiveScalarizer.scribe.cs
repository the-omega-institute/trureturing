using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class UniversalPositiveScalarizerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A selected column of an actual common center controls a joint residual Gram and yields one common positive state.",
        H("Selected-column Gram and common positive state"), Blocks(
            Describe.Lean(DescribeId.Create("actual-selected-column-joint-gram"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.selected_column_joint_gram"),
                H("One scalar family for the entire basis Gram"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let a and b be finite nonempty types, let Phi be an actual completely positive trace-preserving channel from a to b, and let k be a nonnegative real number. Its canonical normalized Kraus family defines an isometric column J, the representation pi(A)=A tensor I_Env, and the projection e=I-J J adjoint. The universal premise tests every finite reference and complex joint input against general matrix centers.")),
                    Paragraph(Text("A selected matrix-unit column supplies a scalar family whose joint residual Gram is bounded by k times the actual defect Gram, including k=0. This joint bound supplies the rectangular factor used to construct the common state.")),
                    Paragraph(Text("Pack the full matrix-unit basis into one selected column. The packed defect is C C adjoint. A general matrix center supplies the residual P, whose selected column is D. Its remaining columns form R and give P P adjoint=D D adjoint+R R adjoint. Adding the positive remainder yields the joint selected-column inequality without imposing sparsity on the center. The positive Gram remainder preserves the bound on the selected column.")),
                    Paragraph(Text("The common-state theorem below uses this joint Gram bound. The final all-finite Umegaki coefficient equality remains open."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("common-positive-state-scalarizer"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.common_positive_state_scalarizer"),
                H("One state and one ordinary partial-trace center"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For finite nonempty input and output carriers, a canonical channel and its universal positive trace test produce one DensityState on the output carrier. The state is independent of the finite reference and the complex joint input.")),
                    Paragraph(Text("For every finite reference, including the empty carrier, the center is the ordinary unnormalized weighted partial trace of the joint input. The same center satisfies both left and right residual Gram inequalities with the stated coefficient k. The construction permits singular states and uses no faithful-state, invertibility, unitary-polar, or dimension-normalization assumption.")),
                    Paragraph(Text("Apply the existing Hilbert-space Douglas theorem on the Euclidean space indexed by a disjoint sum, then extract the heterogeneous block and project it with e. This supplies C T=D, e T=T and T adjoint T bounded by k I without dividing by k. The full complex matrix-unit expansion gives J adjoint pi(Z)(J-T)=Tr(tau Z) I, where tau(v,u)=x(u,v). Orthogonality gives Tr(tau)=1 and (J-T) adjoint (J-T)=I+T adjoint T.")),
                    Paragraph(Text("The native singular polar supplier gives U adjoint tau=abs(tau) with U contractive. Finite trace-norm duality proves t=Tr(abs(tau)) at least one. Set sigma=abs(tau)/t and W=t inverse pi(U adjoint)(J-T). The correct compression uses Tr(tau Z U adjoint)=Tr(U adjoint tau Z), so it is Tr(sigma Z) I. Thus J adjoint W=I. For K=J-W, the positive congruence of I-t inverse squared pi(U U adjoint) proves K adjoint K bounded by T adjoint T. Support e K=K then earns K K adjoint bounded by k e.")),
                    Paragraph(Text("Amplify this fixed K and W by the reference identity and reindex the Kronecker representation by the product associator. The compression is the blockwise trace pairing, exactly the weighted ordinary partial trace. Congruence of the supported Gram bound gives the first residual inequality. Hermiticity of sigma makes its center preserve adjoints; applying the first inequality to the adjoint input gives the second at the same center.")),
                    Paragraph(Text("This is an intermediate on the Umegaki route. The all-channel coefficient theorem, support and regularization steps, and final ratio comparison remain open."))),
                DescribeRole.Theorem))));
}
