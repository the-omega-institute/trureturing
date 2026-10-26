using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class BarkerMinimalGridSeriesdocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete literal numerator and rational quotient series", H("The complete literal numerator and rational quotient series"), Blocks(
            N("numerator", "numerator", "The complete 49 integer coefficients of the source numerator include coefficient zero 0, coefficient one 2 and coefficient 48 −1. They reproduce Colin Barker, OEIS A286848, https://oeis.org/A286848, under CC-BY-SA-4.0, https://creativecommons.org/licenses/by-sa/4.0/.", DescribeRole.Definition),
            N("evaluate", "evaluate", "The integer linear functional evaluates a quotient vector against all 59 entries of the exact initial row alpha.", DescribeRole.Definition),
            N("quotientCoefficient", "quotientCoefficient", "The scalar coefficient is 0 at index zero, 2 at index one, and evaluation of orbit(n−2) thereafter. This is defined separately from the actual subset count.", DescribeRole.Definition),
            N("initialCoefficient", "initialCoefficient", "The initial range uses the exact certificate vectors values rather than assuming that they are powers.", DescribeRole.Definition),
            N("initial_convolutions", "initial convolutions", "Every convolution of the denominator with the initial coefficients in degrees zero through 49 equals the full literal numerator, with degree 49 zero.", DescribeRole.Theorem),
            N("all_later_convolutions", "all later convolutions", "For every m at least 50, the denominator convolution of quotientCoefficient at degree m is zero. Applying evaluate to shifted_annihilator(m−50) proves the entire unbounded range.", DescribeRole.Theorem),
            N("quotientSeries", "quotientSeries", "The rational formal power series has quotientCoefficient n cast to the rationals at each index n.", DescribeRole.Definition),
            N("P", "P", "The numerator formal polynomial series uses all literal numerator coefficients in degrees zero through 48 and is zero thereafter.", DescribeRole.Definition),
            N("Q", "Q", "The complete denominator is the finite sum of denominator(j) times X^j for every j in Fin 49. No leading or trailing coefficient is omitted.", DescribeRole.Definition),
            N("quotientSeries_mul_Q", "quotientSeries mul Q", "The product quotientSeries*Q equals P in rational formal power series. The proof separates the checked initial range zero through 49 from every later degree.", DescribeRole.Theorem),
            N("Q_constant", "Q constant", "The literal denominator has constant coefficient one.", DescribeRole.Theorem),
            N("quotientSeries_identity", "quotientSeries identity", "The quotient-orbit series equals P*Q inverse. This theorem alone does not identify the quotient coefficients with actual subset counts.", DescribeRole.Theorem),
            Paragraph(Text("This is internal Stage A work. The unchanged whole actual-subset generating-series endpoint requires every counting and quotient interface to be compiled; no resolution or admission follows from a partial interface."))), []));

    private static DocumentBlock N(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("bs-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
