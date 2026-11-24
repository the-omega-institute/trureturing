using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class DisjointCharacterEnvelopeDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/DisjointCharacterEnvelope";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The mixed coefficient bound retains the two phase sums before estimating local overlaps.",
        H("A phase-sensitive bound for disjoint coefficients"),
        Blocks(Describe.Lean(
            DescribeId.Create("disjoint-coefficient-envelope"),
            DeclarationHandle.Create(Owner + ".coefficient_envelope"),
            H("Disjoint coefficient bound"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a finite set s of indices, P(x,y) is the product of the local factors "
                    + "exp(a(j)x) + exp(b(j)y) - 1. Each term at an index chooses only one axis "
                    + "or the constant, so the mixed coefficient uses disjoint supports.")),
                Paragraph(Text(
                    "Extract exp(a(j)x + b(j)y) from each factor. The remaining factor is "
                    + "1 plus the product of exp(-a(j)x) - 1 and 1 - exp(-b(j)y). Expanding this "
                    + "product over subsets gives one product of two separate series per subset. "
                    + "The original exponentials have combined to the sums of a and b. Each "
                    + "correction factor has positive degree on both axes. A subset larger than "
                    + "either target degree contributes zero to the selected coefficient.")),
                Paragraph(Text(
                    "For one variable, the sum of coefficient norms is submultiplicative on "
                    + "absolutely summable series, by the Cauchy product and the triangle inequality. "
                    + "A scaled exponential contributes exp(|a|), and removal of its constant "
                    + "term leaves exp(|a|) - 1. Applying these two bounds and summing the subsets "
                    + "gives the estimate at radius one. Rescaling both axes gives the radius factor.")),
                Paragraph(Text(
                    "For characters on a finite cyclic group, take a(j) = w(j) times the character "
                    + "of the negative residue and b(j) its complex conjugate. The numerator then "
                    + "depends on the norm of one weighted character sum and the weights' local "
                    + "overlap penalties. Estimating those character sums for actual zeta zeros "
                    + "requires additional arithmetic information."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var s = F.Id("s");
        var r = F.Id("r");
        var a = F.Id("a");
        var b = F.Id("b");
        var m = F.Id("m");
        var n = F.Id("n");
        var j = F.Id("j");
        var alphabet = F.Id("J");
        var atA = new Formula.Apply(a, [j]);
        var atB = new Formula.Apply(b, [j]);
        var sum = new Formula.Subscript(Sum, Seq(j, Sp, InMacro, Sp, s));
        var t = F.Id("T");
        var subsets = new Formula.Subscript(Sum,
            Seq(t, Sp, Subseteq, Sp, s, Comma, Bar, t, Bar, Sp, Le, Sp, Call("min", m, n)));
        var prod = new Formula.Subscript(Prod, Seq(j, Sp, InMacro, Sp, t));
        return Disp(new Formula.Aligned([
            Seq(Amp, Forall, Sp, alphabet, Colon, Sp, Call("Type"), Comma, Sp,
                s, Colon, Call("Finset", alphabet), Comma, Quad,
                Forall, Sp, a, Comma, b, Colon, alphabet, To, Sp, Mathbb, Grp(F.Id("C")), Comma),
            Seq(Amp, Forall, Sp, m, Comma, n, Colon, Mathbb, Grp(F.Id("N")), Comma,
                Quad, Forall, Sp, r, Colon, Mathbb, Grp(F.Id("R")), Comma, Quad, Sp,
                r, Gt, D(0), Implies),
            Seq(Amp, Bar, OpenBracket, new Formula.Power(F.Id("x"), m),
                new Formula.Power(F.Id("y"), n), CloseBracket, F.Id("P"), Bar, Sp, Le, Sp,
                Frac, Grp(Call("exp", Seq(r, Open, Bar, sum, atA, Bar, Plus, Bar, sum, atB, Bar, Close))),
                Grp(new Formula.Power(r, Seq(m, Plus, n)))),
            Seq(Amp, Quad, Cdot, subsets, prod,
                Open, Call("exp", Seq(r, Bar, atA, Bar)), Minus, D(1), Close,
                Open, Call("exp", Seq(r, Bar, atB, Bar)), Minus, D(1), Close, Dot)
        ]));
    }
}
