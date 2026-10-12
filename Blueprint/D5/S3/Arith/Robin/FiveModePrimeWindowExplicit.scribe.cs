using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class FiveModePrimeWindowExplicitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/FiveModePrimeWindowExplicit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite 5040 six-cell has an exact normalized five-prime vector.",
        H("Exact Five Mode Vectors on the 5040 Six Cell"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("five-mode-prime-window-explicit"),
                DeclarationHandle.Create(Prefix + "goldenCell5040_prime_window_explicit"),
                H("Finite explicit window"),
                StatementSource.FromAuthor(ExplicitFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each of the six values 5040, 10080, 15120, 20160, 30240 and "
                    + "60480, the theorem supplies u in {0,1,2} and v in {0,1} with "
                    + "n = 5040 * 2^u * 3^v.  Writing d = 13 + u + v, the coordinates "
                    + "in the order (2,3,5,7,83) are (5+u, 3+v, 2, 2, 1)/d, and "
                    + "the visible projection is (4+v, 3, 2)/d.")),
                Paragraph(Text(
                    "The six rows are 5040:(u,v,d)=(0,0,13), 10080=(1,0,14), "
                    + "15120=(0,1,14), 20160=(2,0,15), 30240=(1,1,15), "
                    + "and 60480=(2,1,16).  Their five-coordinate numerators are "
                    + "(5,3,2,2,1), (6,3,2,2,1), (5,4,2,2,1), (7,3,2,2,1), "
                    + "(6,4,2,2,1), and (7,4,2,2,1), respectively."))),
                DescribeRole.Theorem))));

    private static Formula ExplicitFormula()
    {
        Formula n = F.Id("n");
        Formula u = F.Id("u");
        Formula v = F.Id("v");
        Formula d = Add(Add(Num(13), Call("val", u)), Call("val", v));
        Formula body = All(
            Equal(n, Multiply(Multiply(Num(5040), Pow(Num(2), Call("val", u))), Pow(Num(3), Call("val", v)))),
            Equal(Call("windowDenom", n), d),
            Equal(Call("primeWindow", n, Num(0)), Fraction(Add(Num(5), Call("val", u)), d)),
            Equal(Call("primeWindow", n, Num(1)), Fraction(Add(Num(3), Call("val", v)), d)),
            Equal(Call("primeWindow", n, Num(2)), Fraction(Num(2), d)),
            Equal(Call("primeWindow", n, Num(3)), Fraction(Num(2), d)),
            Equal(Call("primeWindow", n, Num(4)), Fraction(Num(1), d)),
            Equal(Call("visible", Call("primeWindow", n)),
                Tuple(Fraction(Add(Num(4), Call("val", v)), d), Fraction(Num(3), d), Fraction(Num(2), d))));
        Formula witnesses = new Formula.BindMany(FormulaQuantifier.Exists,
            [Bound("u", Call("Fin", Num(3))), Bound("v", Call("Fin", Num(2)))], body);
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"), Naturals(),
            Implies(Call("mem", n, Call("sixCell")), witnesses)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Fraction(Formula x, Formula y) => Seq(F.Frac, Grp(x), Grp(y));
    private static Formula Tuple(params Formula[] xs) =>
        Seq(OpenBracket, Seq(xs.SelectMany((x, i) => i == 0
            ? new Formula[] { x }
            : new Formula[] { Comma, Sp, x }).ToArray()), CloseBracket);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Add(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Multiply(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula All(params Formula[] xs)
    {
        Formula result = xs[^1];
        for (int i = xs.Length - 2; i >= 0; i--)
            result = And(xs[i], result);
        return result;
    }
    private static Formula Implies(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);
}
