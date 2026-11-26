using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class UniversalPositiveScalarizerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Amplified Kraus compression yields simultaneous residual Gram bounds from one positive state.",
        H("Common positive state for every finite reference"), Blocks(
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
