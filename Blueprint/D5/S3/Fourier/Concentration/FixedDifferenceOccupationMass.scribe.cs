using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class FixedDifferenceOccupationMassDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/FixedDifferenceOccupationMass";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed signed count difference determines a shifted factorial sum.",
        H("The mass at a fixed count difference"),
        Blocks(Describe.Lean(
            DescribeId.Create("fixed-difference-mass"),
            DeclarationHandle.Create(Owner + ".fixed_difference_mass"),
            H("Exact mass and diagonal bound"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let J be finite with real weights w. Let a and b be nonnegative integer vectors "
                    + "with disjoint supports and the same total degree d, with d≤p. Write M with "
                    + "subscript p for the sum, over ordered degree-p pairs with count difference "
                    + "a−b, of the product of their two multinomial weights. Write c with subscript d for the weighted "
                    + "multinomial coefficient of degree d and D with subscript k for the sum "
                    + "of their squares at degree k.")),
                Paragraph(Text(
                    "R is the sum over degree p−d vectors l of the coordinate products "
                    + "(w(j)²)^l(j)/(l(j)!(l(j)+a(j)+b(j))!). C denotes the binomial "
                    + "coefficient with parameters p and d. The inequality applies when "
                    + "all weights are nonnegative.")),
                Paragraph(Text(
                    "Given a pair with the prescribed difference, take its coordinatewise "
                    + "minimum l. The pair then equals (l+a,l+b), and every l of degree "
                    + "p−d gives such a pair. Disjointness of a and b turns the two "
                    + "coordinate factorials into l(j)! and (l(j)+a(j)+b(j))!. "
                    + "The weights contribute the residual power and one squared power "
                    + "for each common occurrence.")),
                Paragraph(Text(
                    "The factorial product for l+a dominates the products for l and a. "
                    + "This bounds its multinomial weight by C times the two separate "
                    + "weights under nonnegativity. Use the same inequality for l+b and "
                    + "sum the square of the common weight over the degree p−d vectors."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var p = F.Id("p");
        var d = F.Id("d");
        var j = F.Id("j");
        var a = F.Id("a");
        var b = F.Id("b");
        var w = F.Id("w");
        var difference = Seq(a, Minus, b);
        var mass = Seq(new Formula.Subscript(F.Id("M"), p), Open, difference, Close);
        var factorial = Seq(Open, p, Bang, Close);
        var add = Seq(new Formula.Subscript(a, j), Plus, new Formula.Subscript(b, j));
        var power = new Formula.Power(new Formula.Subscript(w, j), add);
        var product = Seq(new Formula.Subscript(Prod, Seq(j, Sp, InMacro, Sp, F.Id("J"))), Sp, power);
        var diagonal = new Formula.Subscript(F.Id("D"), Seq(p, Minus, d));
        var coefficient = new Formula.Subscript(F.Id("c"), d);
        var nonnegative = Seq(Open, Forall, Sp, j, Sp, InMacro, Sp, F.Id("J"), Comma, Sp,
            D(0), Sp, Leq, Sp, new Formula.Subscript(w, j), Close);
        return Disp(new Formula.Aligned([
            Seq(mass, Sp, Eq, Sp, new Formula.Power(factorial, D(2)), Sp, product, Sp, F.Id("R")),
            Seq(nonnegative, Sp, Implies, Sp, mass, Sp, Leq, Sp,
                new Formula.Power(F.Id("C"), D(2)), Sp, diagonal, Sp,
                coefficient, Open, a, Close, Sp, coefficient, Open, b, Close)]));
    }
}
