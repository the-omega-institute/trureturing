using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Resource;

internal sealed class SimplexCoverageWordsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Spanning-filtered physical words equal factorial times the existing represented "
        + "reciprocal-factorial spanning polynomial, at every natural horizon.",
        H("Spanning-Filtered Physical Word Normalization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("simplex-coverage-words-factorial"),
                DeclarationHandle.Create(
                    "D5/S3/Resource/SimplexCoverageWords.wordPolynomial_eq_factorial_smul"),
                H("All-Horizon Rational Polynomial Identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural t, W[U,t] equals t! times the actual "
                        + "spanningPolynomial columns U t in the rational multivariate polynomial "
                        + "ring. The original reciprocal-factorial coefficients are unchanged. "
                        + "The equation therefore supports signed evaluations as well as "
                        + "nonnegative evaluations, without a probability hypothesis.")),
                    Paragraph(Text(
                        "A word is an actual map from Fin t to the original physical index set. "
                        + "Its summand is the product of its coordinate variables exactly when "
                        + "its represented span together with U is top, and zero otherwise. "
                        + "The first-coordinate/tail equivalence splits the word sum; the range "
                        + "of the represented concatenation is the first singleton union the "
                        + "tail range. Span union gives the actual contraction by that column.")),
                    Paragraph(Text(
                        "The field, ambient module, finite physical index set and subspace U "
                        + "are arbitrary. Empty indices, unspanned representations, zero columns, "
                        + "repeated columns and scalar-parallel columns are retained.")),
                    Paragraph(Text(
                        "The unique empty word and the degree-zero coefficient formula give "
                        + "the same top/zero indicator. Exact contraction and homogeneous Euler "
                        + "turn the word recurrence into a genuine all-degree induction. "
                        + "No finite-dimensional, full-spanning or nonempty-index assumption "
                        + "is used; no unfiltered multinomial identity replaces the span filter."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "This normalization is a dependency of the simplex optimizer, not a named "
                + "problem settlement. Probability comparisons and actual expected-time "
                + "optimization remain separate obligations."))),
        []));
}
