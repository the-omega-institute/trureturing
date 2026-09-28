using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class MomentGramianStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Construct orthogonal trajectory compression and finite moment coordinates. Prove exact residual-Gramian and norm error identities; actual Legendre basis construction and anisotropic Taylor estimates remain separate.", H("Orthogonal Moment Gramians and Quadratic Compression Error"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gram-inner"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/MomentGramianStability.gram_inner"),
                H("gram inner"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Gramian is the actual Hilbert-space adjoint product, with its exact bilinear observation identity."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gram-norm"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/MomentGramianStability.gram_norm"),
                H("gram norm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The linked Lean source gives the exact hypotheses and conclusion. This is a source candidate; no kernel verification is claimed."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gram-perturbation"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/MomentGramianStability.gram_perturbation"),
                H("gram perturbation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Prove first-order Gramian stability by exact operator telescoping and the adjoint norm identity."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gram-projection-residual"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/MomentGramianStability.gram_projection_residual"),
                H("gram projection residual"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The loss caused by the constructed orthogonal projection equals the positive Gramian of the discarded trajectory."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("residual-eq-difference"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/MomentGramianStability.residual_eq_difference"),
                H("residual eq difference"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A comparison trajectory with range in the retained subspace is killed by the discarded projection."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("residual-norm-le"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/MomentGramianStability.residual_norm_le"),
                H("residual norm le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The linked Lean source gives the exact hypotheses and conclusion. This is a source candidate; no kernel verification is claimed."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("moment-gramian-error"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/MomentGramianStability.moment_gramian_error"),
                H("moment gramian error"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The constructed compression loses at most the square of the trajectory-approximation error. No Gramian approximation is assumed as a premise."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("moment-gramian-quadratic-bound"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/MomentGramianStability.moment_gramian_quadratic_bound"),
                H("moment gramian quadratic bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A supplied first-order trajectory residual yields a second-order compression bound. This lemma does not supply the missing exponential Taylor estimate."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("momentobservation-gram"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/MomentGramianStability.momentObservation_gram"),
                H("momentObservation gram"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Coordinates in an actual finite orthonormal basis preserve the projected Gramian exactly."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("moments-noise-contraction"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/MomentGramianStability.moments_noise_contraction"),
                H("moments noise contraction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual finite coordinate projection does not amplify Hilbert-space trajectory noise."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-moment-gramian-error"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/MomentGramianStability.finite_moment_gramian_error"),
                H("finite moment gramian error"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Combine the constructed coordinate map with the residual-Gramian identity. An explicit Legendre realization is a separate obligation."))), DescribeRole.Theorem))));
}
