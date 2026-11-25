using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.HalfFock;

internal sealed class OriginalHalfCurrentWickPolynomialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentWickPolynomial.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Wick polynomials for half-current lowering",
        H("The vacuum and the lowering flow"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-half-current-wick-polynomial-creator"),
                DeclarationHandle.Create(Prefix + "creator"),
                H("Surviving oscillator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an occurrence of mode m, the coefficient of order k keeps the colour and lowers the "
                    + "mode to m minus k, with its generalized binomial weight."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-half-current-wick-polynomial-pair"),
                DeclarationHandle.Create(Prefix + "pair"),
                H("Central contraction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A pair of occurrences contracts at the sum of their modes plus one, with the Gram entry "
                    + "and the half-current contraction scalar."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-half-current-wick-polynomial-word"),
                DeclarationHandle.Create(Prefix + "word"),
                H("Finite Wick recursion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At each step the head survives or contracts with a position in the remaining word. The "
                    + "respective terms multiply the recursion on the remaining positions."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-half-current-wick-polynomial-word-coeff"),
                DeclarationHandle.Create(Prefix + "word_coeff"),
                H("Normal-order coefficients on the vacuum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At every nonnegative order, applying the normal-order coefficient to the vacuum gives the "
                    + "coefficient of the finite Wick polynomial. The induction follows the surviving and "
                    + "contracting branches, using the coefficient convolution for each product."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-half-current-wick-polynomial-eval-word-eq-lowering"),
                DeclarationHandle.Create(Prefix + "eval_word_eq_lowering"),
                H("Evaluation by inverse oscillator lowering"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a lattice with unit Gram determinant and a bound strictly exceeding the degree, "
                    + "evaluation at any complex parameter equals the finite sum of oscillator-lowering powers on "
                    + "the occurrence monomial, with the factorial coefficient at each order."))),
                DescribeRole.Theorem))));
}
