using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class WeightedOccupationDiagonalDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/WeightedOccupationDiagonal";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive coefficient comparison bounds the diagonal of a weighted multinomial moment.",
        H("The weighted occupation diagonal"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("scaled-diagonal-le-product"),
                DeclarationHandle.Create(Owner + ".scaled_diagonal_le_product"),
                H("Product bound for the scaled diagonal"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let J be finite, w be real weights on J, p be a nonnegative integer, "
                        + "and s be a nonnegative real number. The diagonal D with subscript p "
                        + "sums the squares of the weighted multinomial coefficients of degree p. "
                        + "The envelope A(x) is 2 exp(x/2) minus one.")),
                    Paragraph(Text(
                        "Multiply the diagonal by s to the power p and divide by the square "
                        + "of p factorial. The resulting terms are coordinate products of "
                        + "(s w(j)²)^n/(n!)². Extending the sum to all vectors with coordinates "
                        + "between zero and p gives a product of nonnegative partial sums.")),
                    Paragraph(Text(
                        "For n≥1 the bound n!≥2^(n−1) follows by induction. Each positive-degree "
                        + "term is thus bounded by twice the corresponding exponential term "
                        + "at half the argument. The constant coefficient is one, so the "
                        + "coordinate partial sum is at most A(x). The product preserves these "
                        + "separate coordinate bounds."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var p = F.Id("p");
        var s = F.Id("s");
        var j = F.Id("j");
        var w = F.Id("w");
        var factorial = Seq(Open, p, Bang, Close);
        var diagonal = Seq(new Formula.Subscript(F.Id("D"), p), Open, w, Close);
        var weight = new Formula.Subscript(w, j);
        var envelope = Seq(F.Id("A"), Open, s, Sp, new Formula.Power(weight, D(2)), Close);
        var product = Seq(new Formula.Subscript(Prod, Seq(j, Sp, InMacro, Sp, F.Id("J"))),
            Sp, envelope);
        return Disp(Seq(D(0), Sp, Leq, Sp, s, Sp, Implies, Sp,
            new Formula.Power(s, p), Sp, diagonal, Sp, Leq, Sp,
            new Formula.Power(factorial, D(2)), Sp, product));
    }
}
