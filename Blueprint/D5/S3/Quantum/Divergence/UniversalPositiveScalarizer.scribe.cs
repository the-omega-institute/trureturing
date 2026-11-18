using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class UniversalPositiveScalarizerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A selected column of an actual common center controls a joint residual Gram and yields one common positive state.",
        H("Selected-column Gram and common positive state"), Blocks(
            Describe.Lean(DescribeId.Create("j"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.J"),
                H("Canonical isometric Kraus column"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The column maps an input vector to the output and environment carrier using the canonical normalized Kraus family. The common-state construction uses its isometric compression."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("phi"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.Phi"),
                H("Local channel adjoint"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Compress the local matrix acting in the canonical Kraus representation. This is the local block action in the reference trace pairing."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("phir"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.PhiR"),
                H("Reference-amplified adjoint"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Apply Phi blockwise to a complex joint matrix in the reference coordinates. The kernel estimate pairs this adjoint with the actual amplified channel."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pi"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.pi"),
                H("Local matrix representation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The representation acts by the local matrix tensor the environment identity. The selected-column residual is formed in this representation."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("kraus-complement"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.e"),
                H("Complementary Kraus projection"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The defect projection is the identity minus J J adjoint. It gives the support of the selected Gram factor and its replacement after the polar step."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("defectr"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.defectR"),
                H("Joint adjoint defect"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Subtract the product of the two adjoint images from the adjoint image of Y Y adjoint. The trace test and the weighted energy defect use this matrix for Y and its adjoint."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("phir-star"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.PhiR_star"),
                H("The reference adjoint preserves conjugate transpose"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For finite nonempty local carriers, every finite reference and arbitrary complex Y, PhiR of the conjugate transpose is the conjugate transpose of PhiR of Y. The Hilbert–Schmidt trace pairing and both Gram bounds use this equality."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("matrix-units"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.E"),
                H("Matrix units"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Each pair of output indices defines the matrix with a single unit entry. The packed column uses all these matrix units."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cblock"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.Cblock"),
                H("A defect block for a matrix unit"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The block is J adjoint times the represented matrix unit times the complementary projection e. The selected-column proof packs these blocks together."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("c"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.C"),
                H("The packed defect matrix"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Concatenate the Cblock matrices over the output index pairs. Its Gram matrix is the bound in the joint selected-column estimate."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("d"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.D"),
                H("The packed scalar residual"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Concatenate the residual blocks made from the chosen scalar family and the compressed matrix units. The selected-column estimate factors this matrix through C."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("universalpositivetracetest"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.UniversalPositiveTraceTest"),
                H("The uniform positive trace test"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every finite reference, complex output joint matrix Y and positive definite input joint Z, bound the infimum of the traced left residual Gram over all complex reference centers by the scaled traced adjoint defect. The endpoint estimate supplies this premise at c/(1-c)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("statecenter"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.stateCenter"),
                H("The weighted ordinary partial trace"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Take the ordinary partial trace after left multiplication by the embedded output state. In each reference block this is the trace of the output state times that block. The kernel estimate uses this one center with both Gram bounds."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("defectr-possemidef"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.defectR_posSemidef"),
                H("Positive semidefiniteness of the joint defect"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a finite channel between nonempty carriers, every finite reference and complex Y, the adjoint defect is positive semidefinite. The endpoint and all-parameter proofs take real trace pairings of this defect against positive joint bases."))),
                DescribeRole.Theorem),
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
                    Paragraph(Text("The kernel contraction uses both Gram bounds from this same state for the inverse direction of the amplified channel. The all-channel coefficient theorem, support and regularization steps, and final ratio comparison remain open."))),
                DescribeRole.Theorem))));
}
