using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Hankel;

internal sealed class ProjectedRealizationErrorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Constructed reduced state models admit exact residual recurrences, finite-horizon output certificates and explicit uniform error bounds under contraction.",
        H("Residual-Certified Linear Model Reduction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("driven-state"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/ProjectedRealizationError.drivenState"),
                H("Driven discrete-time state"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The state starts at zero and evolves by x(n+1)=A x(n)+B u(n). The estimates below concern arbitrary bounded or unbounded input sequences as stated in each theorem."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reduced-dynamics"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/ProjectedRealizationError.reducedDynamics"),
                H("Construct the reduced dynamics"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The reduced carrier W has transition P A J. This is a genuine state transition, so the result is not an unconstrained low-rank approximation to a Hankel matrix."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reduced-input"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/ProjectedRealizationError.reducedInput"),
                H("Construct the reduced input map"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The reduced input is P B, built from the same projection map used in the reduced dynamics."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reduced-output"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/ProjectedRealizationError.reducedOutput"),
                H("Construct the reduced output map"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The reduced output is C J. Predicted outputs are therefore compared in the original output space."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("projected-realization"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/ProjectedRealizationError.projectedRealization"),
                H("A reduced model in the existing interface"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When W is finite-dimensional, the constructed maps give the existing FiniteLinearRealization interface. The error estimates do not require P J=id; imposing that identity gives the usual retraction interpretation. A smaller-dimensional W must be chosen separately."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("dynamics-residual"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/ProjectedRealizationError.dynamicsResidual"),
                H("Compute the transition residual"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The continuous linear map A J minus J A_r measures failure of the lift to intertwine the full and reduced dynamics. Its operator norm appears explicitly in the error certificate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("input-residual"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/ProjectedRealizationError.inputResidual"),
                H("Compute the input residual"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The continuous linear map B minus J B_r measures the missing input contribution. Its operator norm is the second computable residual in the certificate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("state-error"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/ProjectedRealizationError.stateError"),
                H("Compare full and lifted reduced states"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both states are produced by their actual driven recurrences. Their difference is x(n)-J z(n); no error equation is assumed as a premise."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("state-error-succ"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/ProjectedRealizationError.stateError_succ"),
                H("Derive the exact error recurrence"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Expanding both state updates and applying linearity gives e(n+1)=A e(n)+(A J-J A_r)z(n)+(B-J B_r)u(n). This proof is the algebraic starting point for all bounds."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("state-error-le-residual-sum"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/ProjectedRealizationError.stateError_le_residual_sum"),
                H("Finite-time residual certificate"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At horizon n the state error is bounded by a finite convolution of powers of the full operator norm with the computed transition and input residual contributions. No stability or contraction assumption is needed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("output-error-le-residual-sum"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/ProjectedRealizationError.outputError_le_residual_sum"),
                H("Finite-time output certificate"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply the original output operator to the state-error bound. The resulting computable finite sum compares outputs of the full model and the constructed reduced model."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("driven-state-norm-le-of-contraction"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/ProjectedRealizationError.drivenState_norm_le_of_contraction"),
                H("Uniform state bound for bounded inputs"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For input norm bounded by nonnegative M and operator norm of A strictly below one, every zero-initial state has norm at most norm(B) times M divided by one minus norm(A)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("output-error-uniform-of-contraction"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/ProjectedRealizationError.outputError_uniform_of_contraction"),
                H("Explicit uniform reduction error"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the actual full and reduced dynamics are both contractions, their output difference is uniformly bounded by norm(C) times the sum of the transition-residual contribution and input-residual contribution, divided by one minus norm(A). The reduced-state contribution has its own denominator one minus norm(A_r). These are strict operator-norm hypotheses in the chosen norms, not merely spectral-radius stability."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-residuals-preserve-outputs"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/ProjectedRealizationError.zero_residuals_preserve_outputs"),
                H("Exact preservation from zero residuals"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If both computed residual maps vanish, every output agrees at every time for arbitrary input sequences. This exact endpoint follows from the finite residual certificate and does not require contraction."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Observer/Hankel/HankelMinimalStateDimension"))]));
}
