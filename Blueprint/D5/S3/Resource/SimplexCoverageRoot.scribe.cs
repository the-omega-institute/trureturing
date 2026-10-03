using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Resource;

internal sealed class SimplexCoverageRootDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive-degree represented spanning polynomial has a concave degree-th real root "
        + "on the entire nonnegative orthant, including all zero-polynomial regimes.",
        H("Represented Spanning Polynomial Root Concavity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("simplex-coverage-root-line-derivative"),
                DeclarationHandle.Create(
                    "D5/S3/Resource/SimplexCoverageRoot.evaluateAt_line_hasDerivAt"),
                H("Actual Analytic Line Derivative"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any rational multivariate polynomial on a finite index set, evaluating "
                        + "at x+t y has derivative equal to the finite sum of y_i times the evaluated "
                        + "formal partial derivative. Structural polynomial induction uses the "
                        + "constant, sum and product-with-one-variable cases. No nonempty-index "
                        + "or positivity assumption is needed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("simplex-coverage-root-closed-orthant"),
                DeclarationHandle.Create(
                    "D5/S3/Resource/SimplexCoverageRoot.spanningPolynomial_root_concaveOn"),
                H("Root Concavity on the Closed Nonnegative Orthant"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The field and ambient vector space are arbitrary, the quotient by U is "
                        + "finite-dimensional, "
                        + "the finite physical index set is unchanged, and the natural degree is "
                        + "at least one. The degree-th real root of the actual reciprocal-factorial "
                        + "spanning polynomial is ConcaveOn the whole nonnegative orthant. "
                        + "No spanning, nonempty-index, analytic derivative, Hessian or induction "
                        + "premise is imposed.")),
                    Paragraph(Text(
                        "The quotient map preserves the spanning condition of each represented "
                        + "support, so the exact coefficient formula identifies the original "
                        + "polynomial with its quotient representation over the same variables. "
                        + "All physical indices are retained; no finite-dimensional ambient "
                        + "restriction is used.")),
                    Paragraph(Text(
                        "The exact line derivative applied to each partial derivative identifies "
                        + "the second line derivative with the evaluated formal-Hessian quadratic "
                        + "form. Finite sums are interchanged without assuming mixed-partial "
                        + "commutation. At positive line points the actual all-degree reverse-Hessian "
                        + "induction makes the explicit second root derivative nonpositive. "
                        + "Continuous endpoints assemble concavity on the closed unit interval.")),
                    Paragraph(Text(
                        "Zero polynomials give the constant branch. Positive degree and an empty "
                        + "index set force every coefficient to vanish. Rank obstruction and "
                        + "unspanned families use the existing exact zero-polynomial theorem. "
                        + "The nonzero branch is positive on the positive orthant. Jensen inequalities "
                        + "for positively translated endpoints pass to all boundary coordinates "
                        + "by global polynomial and real-root continuity. Degree one is included, "
                        + "and a fractional root is never differentiated at zero."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "This is an analytic dependency, not a settlement of the named simplex optimizer. "
                + "Actual all-horizon iid physical sampling probabilities and expected-time "
                + "comparisons remain separate obligations."))),
        []));
}
