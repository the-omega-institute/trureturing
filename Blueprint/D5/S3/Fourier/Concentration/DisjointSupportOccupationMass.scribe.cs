using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class DisjointSupportOccupationMassDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/DisjointSupportOccupationMass";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Disjoint supports give a product bound for two multinomial count vectors.",
        H("Weighted occupation pairs with disjoint supports"),
        Blocks(Describe.Lean(
            DescribeId.Create("scaled-disjoint-mass"),
            DeclarationHandle.Create(Owner + ".scaled_disjoint_mass"),
            H("Exponential bound for disjoint occupation mass"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let J be a finite index set with nonnegative weights w. For a nonnegative "
                    + "integer d, U with subscript d sums the products of the weighted "
                    + "multinomial coefficients of two degree-d vectors with disjoint supports. "
                    + "Write W for the total weight and take s≥0. Let B be the square of d "
                    + "factorial times the product over j of 2 exp(s w(j)) minus one.")),
                Paragraph(Text(
                    "After scaling by the power of s and extracting the two factorials, each "
                    + "coordinate contributes (s w(j))^(a+b)/(a! b!). The map taking an "
                    + "occupation pair to its coordinate pairs is injective and lands in the "
                    + "product of the finite sets with 0≤a,b≤d and a=0 or b=0. Since all "
                    + "terms are nonnegative, dropping both total-degree constraints increases "
                    + "the sum. The local sum consists of two exponential partial sums with "
                    + "the common zero pair counted once.")),
                Paragraph(Text(
                    "The local factor at x=s w(j) is exp(2x) times "
                    + "1−(1−exp(−x))². Bounding each latter factor by the exponential with "
                    + "the same quadratic penalty gives the second inequality. The same "
                    + "bound applies if a frequency-resolution condition further restricts "
                    + "the disjoint occupation pairs."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var d = F.Id("d");
        var j = F.Id("j");
        var s = F.Id("s");
        var wj = new Formula.Subscript(F.Id("w"), j);
        var factorial = new Formula.Power(Seq(Open, d, Bang, Close), D(2));
        var e = F.Id("e");
        var penalty = new Formula.Power(
            Seq(Open, D(1), Minus, new Formula.Power(e, Seq(Minus, s, wj)), Close), D(2));
        var exponent = Seq(D(2), s, F.Id("W"), Sp, Minus, Sp,
            new Formula.Subscript(Sum, j), penalty);
        return Disp(Seq(new Formula.Power(s, Seq(D(2), d)),
            new Formula.Subscript(F.Id("U"), d), Sp, Leq, Sp, F.Id("B"), Sp, Leq, Sp,
            factorial, new Formula.Power(e, exponent)));
    }
}
