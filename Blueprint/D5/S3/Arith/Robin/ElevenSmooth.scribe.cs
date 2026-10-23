using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class ElevenSmoothDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Robin's strict inequality holds for every 11-smooth natural number above 5040.",
        H("Robin's Inequality for the Entire 11-Smooth Family"),
        Blocks(Describe.Lean(
            DescribeId.Create("robin-eleven-smooth"),
            DeclarationHandle.Create("D5/S3/Arith/Robin/ElevenSmooth.robin_eleven_smooth"),
            H("All five exponents are unrestricted"),
            StatementSource.FromAuthor(RobinFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Here sigma(1,n) is the sum of the positive divisors of n, and "
                        + "eulerMascheroniConstant is Euler's constant. The five exponents "
                        + "range over all natural numbers, including zero. The sole hypothesis "
                        + "is that their product n exceeds 5040. No Riemann Hypothesis premise is used.")),
                Paragraph(Text(
                    "When the exponent of 11 is zero the statement is the frozen seven-smooth theorem, "
                        + "which is applied directly. Otherwise multiplicativity and the finite geometric-sum "
                        + "formula bound sigma(1,n)/n strictly by 77/16. For n at least 2^22, frozen rational "
                        + "logarithm bounds give log(log(n)) > 271/100, and a Taylor lower bound gives "
                        + "exp(gamma) > 89/50, so the capacity exceeds 77/16.")),
                Paragraph(Text(
                    "Below 2^22 the product bound forces the exponents into the box a<22, b<14, c<10, d<8, "
                        + "e<7. For each exponent 1<=e<=6 a private kernel-checked integer calculation gives "
                        + "ratio bounds 375/100, 387/100, 406/100, 419/100, 426/100, 440/100 and 455/100 on the "
                        + "intervals separated by 10000, 20000, 40000, 80000, 160000 and 640000. "
                        + "Private logarithm bounds 1071/500, 111/50, 229/100, 1179/500, 121/50, 62/25 and "
                        + "259/100 for log(log(t)) at the left end t of each interval finish these cases. "
                        + "The finite range contains 3212 eleven-smooth integers above 5040, 1699 of them "
                        + "divisible by 11.")),
                Paragraph(Text(
                    "The theorem enlarges the certified core used by prime replacement: every integer above "
                        + "5040 whose prime support has at most five primes and whose compression to the first "
                        + "five primes exceeds 5040 is reached from this family by replacing primes with larger "
                        + "ones. It does not cover integers with six or more distinct prime factors, and the "
                        + "Riemann hypothesis remains open."))),
            DescribeRole.Theorem))));

    private static Formula RobinFormula()
    {
        Formula n = Product(Product(Product(Product(
            new Formula.Power(Num(2), F.Id("a")),
            new Formula.Power(Num(3), F.Id("b"))),
            new Formula.Power(Num(5), F.Id("c"))),
            new Formula.Power(Num(7), F.Id("d"))),
            new Formula.Power(Num(11), F.Id("e")));
        Formula ratio = new Formula.Fraction(Call("sigma", Num(1), n), n);
        Formula rhs = Product(Call("exp", F.Id("eulerMascheroniConstant")),
            Call("log", Call("log", n)));
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("a"), Bound("b"), Bound("c"), Bound("d"), Bound("e")],
            new Formula.Logic(Lt(Num(5040), n), FormulaLogicOperator.Implies,
                Lt(ratio, rhs))));
    }

    private static Formula.BoundVariable Bound(string name) =>
        new(FormulaIdentifier.Create(name), Seq(Mathbb, Grp(F.Id("N"))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Product(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
}
