using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaLinear;

internal sealed class ScaledComplexQuadraticRowBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive scaled row certificates retain individual energy weights and explicit perturbation margins.",
        H("Scaled Complex Quadratic Row Bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("scaled-complex-row-certificate"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaLinear/ScaledComplexQuadraticRowBound.norm_complex_quadratic_le_scaled_rows"),
                H("A positive scaling controls every mixed coefficient"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let p be positive and let the complex matrix have symmetric entry norms. A row bound after multiplying column j by p(j) controls the full complex quadratic by the original weighted energy. The proof applies the existing real row theorem to coefficient norms divided by p and to the matrix with entries p(i)p(j) times the original entry norm. No cross term is discarded."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("scaled-absolutely-convergent-matrix-series"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaLinear/ScaledComplexQuadraticRowBound.norm_series_quadratic_le_scaled_rows"),
                H("Absolutely convergent matrix coefficients"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each coefficient series is absolutely summable. Its norm is bounded by the sum of norms before applying the scaled row certificate. The symmetry hypothesis concerns the summed matrix, not each individual term in the series."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("geometric-scaled-envelope"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaLinear/ScaledComplexQuadraticRowBound.geometric_matrix_envelope_bound"),
                H("A fixed envelope gives geometric coefficient-uniform decay"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A fixed real envelope and a positive scaled row witness give a geometric error coefficient for all depths and all coefficient vectors. The entrywise envelope inequality remains a hypothesis. No actual zeta estimate or effective interpolation constant is supplied by this generic result."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("scaled-rows-robust-coercivity"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaLinear/ScaledComplexQuadraticRowBound.scaled_rows_robust_coercive_bound"),
                H("Retain the remaining coercive margin"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The matrix error consumes eta units of weighted energy. An independently bounded complex error consumes tau more. The conclusion retains margin minus eta minus tau as a quantitative coefficient for every vector, including the zero vector."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("scaled-rows-robust-strict-negativity"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaLinear/ScaledComplexQuadraticRowBound.scaled_rows_robust_strict_negativity"),
                H("Strict negativity with independent perturbations"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Positive energy weights and a nonzero coefficient vector make the weighted energy strictly positive. The already-owned positivity theorem is reused. A strict positive remaining margin therefore certifies negativity on the entire nonzero coefficient space."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-channel-scaling-determinant-threshold"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaLinear/ScaledComplexQuadraticRowBound.two_channel_scaling_iff"),
                H("The exact two-channel threshold"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive coupling r and positive second diagonal budget d1, a positive ratio t satisfying both strict scaled inequalities exists exactly when r squared is less than d0 times d1. The reverse implication chooses the midpoint of the nonempty interval between r divided by d1 and d0 divided by r. No positivity hypothesis on d0 is needed separately."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("scaled-success-unscaled-failure-regression"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaLinear/ScaledComplexQuadraticRowBound.two_channel_scaled_regression"),
                H("An exact case where scaling enlarges the certificate domain"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The energy weights are one and nine, and the off-diagonal complex entries are both two. Scaling by three and one yields eta equal to two thirds and certifies all nonzero complex vectors. The same matrix has no unscaled row budget below one. This exact algebraic regression is not a model of zeta zeros or an information-escape test arena."))),
                DescribeRole.Theorem),
            Paragraph(Text("These are classical Schur-test techniques adapted to the repository's mixed-form certificates. A later application must construct and check the actual matrix envelope and scaling witness. Lean compilation, axiom closure and Scribe reconciliation are separate verification steps; this source does not assert their completion.")))));
}
