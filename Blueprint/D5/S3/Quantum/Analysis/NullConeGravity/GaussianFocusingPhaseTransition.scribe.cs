using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class GaussianFocusingPhaseTransitionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition.";

    private static readonly LibraryNoteRef NullCone =
        LibraryNoteRef.Create("D5/L/HilbertOperators/chandrasekaran2026nullcone");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The weighted covariance trace determines almost-sure focusing, strong operator limits, "
        + "and vacuum sublevel probabilities for an independent Gaussian multiplication clock.",
        H("Gaussian exponential-focusing phase transition"),
        Blocks(
            Paragraph(Text("Consider independent centered Gaussian coordinates with variances vₖ and nonnegative weights αₖ. "
                + "The partial energy Tₙ sums αₖXₖ² over the first n modes. "
                + "The full energy T and the mean A = ∑ₖ αₖvₖ take values in the extended nonnegative reals.")),
            Describe.Lean(
                DescribeId.Create("gaussian-focusing-quadratic-laplace"),
                DeclarationHandle.Create(Prefix + "gaussian_quadratic_laplace"),
                H("One-mode Laplace transform"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("At positive tilt t, integrating exp(−tαX²) under a centered Gaussian law of "
                    + "variance v gives 1/√(1 + 2tαv). The formula includes zero weights and zero variances."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-focusing-finite-laplace"),
                DeclarationHandle.Create(Prefix + "finite_gaussian_laplace"),
                H("Laplace transform at finite mode cutoff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("Independence gives the product of the one-mode transforms for E[exp(−tTₙ)] at every positive t."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-focusing-infinite-laplace"),
                DeclarationHandle.Create(Prefix + "tendsto_gaussian_laplace_product"),
                H("Limit of the independent Laplace products"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("For each positive tilt the finite products converge by dominated convergence "
                    + "to E[exp(−tT)], with the integrand assigned zero at T = ∞."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-focusing-log-sum"),
                DeclarationHandle.Create(Prefix + "gaussian_laplace_eq_log_sum"),
                H("Logarithmic formula for the Laplace integral"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("For every t > 0 the full Laplace integral equals exp(−½ ∑ₖ log(1 + 2tαₖvₖ)), "
                    + "with value zero when the nonnegative sum of logarithms is infinite."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-focusing-mean"),
                DeclarationHandle.Create(Prefix + "lintegral_totalEnergy"),
                H("Mean of the full energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("Tonelli and the Gaussian second moments give the extended expectation E[T] = A, "
                    + "using only the one-coordinate laws."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-focusing-laplace-zero"),
                DeclarationHandle.Create(Prefix + "gaussian_laplace_eq_zero_of_mass_eq_top"),
                H("Vanishing transform in the divergent phase"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("The finite Laplace product is at most the inverse square root of "
                    + "1 + 2t Aₙ, where Aₙ is the sum of αₖvₖ over the first n modes. "
                    + "As the partial mean diverges, the transform tends to zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-focusing-truncated-mean"),
                DeclarationHandle.Create(Prefix + "mass_eq_top_iff_truncated"),
                H("Equivalent truncated mean criterion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("The total mean diverges exactly when the series of mode means capped at one diverges."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-focusing-dichotomy"),
                DeclarationHandle.Create(Prefix + "gaussian_focusing_dichotomy"),
                H("Almost-sure energy dichotomy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(
                    Paragraph(Text("If A is finite, T is finite almost surely and E[T] = A. "
                        + "For every ℓ > 1, Markov's inequality gives γ(T ≤ log ℓ) ≥ 1 − A/log ℓ.")),
                    Paragraph(Text("If A is infinite, the full Laplace integral vanishes and positivity on finite energies "
                        + "forces T = ∞ almost surely. The sum of min(αₖvₖ, 1) diverges exactly when A diverges."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-focusing-vacuum-threshold"),
                DeclarationHandle.Create(Prefix + "vacuum_probability_ge_one_sub"),
                H("Finite vacuum probability threshold"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("For finite A and δ > 0, a cutoff ℓ > 1 with ℓ ≥ exp(A/δ) "
                    + "gives vacuum sublevel probability at least 1 − δ."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-focusing-product-space"),
                DeclarationHandle.Create(Prefix + "exists_canonical_gaussian_focusing_space"),
                H("Canonical countable Gaussian space"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("For any variance sequence the coordinate evaluations on the countable Gaussian "
                    + "product measure give a measurable independent family with those Gaussian marginals."))),
                DescribeRole.Theorem),
            Paragraph(Text("On complex L², the finite resolvent multiplies by L/(L + exp(Tₙ)) for L > 0. "
                + "The full resolvent uses T and assigns zero at infinite energy. "
                + "A finite sublevel projection multiplies by the indicator of the event exp(T) ≤ ℓ.")),
            Describe.Lean(
                DescribeId.Create("gaussian-focusing-strong-cutoff-limit"),
                DeclarationHandle.Create(Prefix + "tendsto_finiteResolvent"),
                H("Strong removal of the mode cutoff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("For each positive L and every L² vector the finite-mode resolvent tends in norm "
                    + "to the full resolvent. Equation (C.13) removes a focusing-value cutoff. The analogous limit here removes a mode cutoff."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-focusing-vacuum-norm"),
                DeclarationHandle.Create(Prefix + "sublevelProjection_vacuum_norm_sq"),
                H("Vacuum projection probability"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("For ℓ ≥ 1 the squared norm of the projected constant-one vacuum "
                    + "equals γ(T ≤ log ℓ)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-focusing-strong-recovery"),
                DeclarationHandle.Create(Prefix + "gaussian_focusing_operators_of_mass_lt_top"),
                H("Strong recovery at finite mean"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("At finite A, the full resolvents and the sublevel projections converge strongly "
                    + "to the identity as their parameters grow. For every ℓ > 1 the squared vacuum projection norm "
                    + "is at least 1 − A/log ℓ, giving the limit in Eq. (5.19) within the model."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-focusing-operator-collapse"),
                DeclarationHandle.Create(Prefix + "gaussian_focusing_operators_of_mass_eq_top"),
                H("Operator collapse at infinite mean"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("At infinite A the full resolvent is zero at every positive L "
                    + "and every finite sublevel projection is zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-focusing-fixed-cutoff-recovery"),
                DeclarationHandle.Create(Prefix + "tendsto_finiteResolvent_atTop"),
                H("Strong recovery at fixed mode cutoff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("At every fixed mode cutoff, the resolvent tends strongly to the identity as L grows. "
                    + "At infinite A the two orders of limits therefore give different operators."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-focusing-wick-positivity"),
                DeclarationHandle.Create(Prefix + "wick_normal_ordered_focusing_below_one_pos_prob"),
                H("Wick ordering breaks the pointwise lower bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("For a positive weight α and variance v, the small ball |X| ≤ √(v/2) "
                    + "has positive Gaussian probability and bounds exp(α(X² − v)) above by exp(−αv/2) < 1. "
                    + "The Wick-ordered model thus violates the pointwise hypothesis used in Eqs. (5.21a–d)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-focusing-dense-form-domain"),
                DeclarationHandle.Create(Prefix + "dense_focusingFormDomain"),
                H("Dense form domain at finite mean"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("When A is finite, the vectors with finite weighted integral ∫ exp(T)|f|² dγ "
                    + "are dense in complex L². The sublevel projections approximate every vector by finite-form vectors."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-focusing-zero-form-domain"),
                DeclarationHandle.Create(Prefix + "focusingFormDomain_eq_singleton"),
                H("Form-domain collapse at infinite mean"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(NullCone),
                Blocks(Paragraph(Text("When A is infinite, a vector has finite weighted integral only if it vanishes "
                    + "almost everywhere, so the full multiplication form has domain {0}."))),
                DescribeRole.Theorem),
            Paragraph(Text("These results concern the independent Gaussian multiplication clock. Applying them to Eq. (4.27) "
                + "requires a comparison to its nonlinear focusing and corner-density factors.")))));
}
