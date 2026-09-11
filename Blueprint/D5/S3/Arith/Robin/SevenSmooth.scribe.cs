using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class SevenSmoothDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Robin's strict inequality holds for every 7-smooth natural number above 5040.",
        H("Robin's Inequality for the Entire 7-Smooth Family"),
        Blocks(Describe.Lean(
            DescribeId.Create("robin-seven-smooth"),
            DeclarationHandle.Create("D5/S3/Arith/Robin/SevenSmooth.robin_seven_smooth"),
            H("All four exponents are unrestricted"),
            StatementSource.FromAuthor(RobinFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Here sigma(1,n) is the sum of the positive divisors of n, and "
                        + "eulerMascheroniConstant is Euler's constant. The four exponents "
                        + "range over all natural numbers, including zero. The sole hypothesis "
                        + "is that their product n exceeds 5040, which also makes n and log n "
                        + "positive. No Riemann Hypothesis premise is used.")),
                Paragraph(Text(
                    "Multiplicativity and the finite geometric-sum formula bound sigma(1,n)/n "
                        + "strictly by 35/8. For n at least 131072, frozen logarithm bounds, "
                        + "a Taylor lower bound for exp of Euler's constant, and monotonicity "
                        + "of log log establish the analytic tail.")),
                Paragraph(Text(
                    "Below 131072, the product bound forces the exponents into a finite box. "
                        + "A private kernel-checked integer calculation gives ratio bounds "
                        + "381/100, 197/50 and 407/100 on the intervals separated by 10000 "
                        + "and 20000. Private logarithm bounds finish these cases. Only this "
                        + "universal theorem is public; the enumeration is internal to its proof."))),
            DescribeRole.Theorem))));

    private static Formula RobinFormula()
    {
        Formula n = Product(Product(Product(
            new Formula.Power(Num(2), F.Id("a")),
            new Formula.Power(Num(3), F.Id("b"))),
            new Formula.Power(Num(5), F.Id("c"))),
            new Formula.Power(Num(7), F.Id("d")));
        Formula ratio = new Formula.Fraction(Call("sigma", Num(1), n), n);
        Formula rhs = Product(Call("exp", F.Id("eulerMascheroniConstant")),
            Call("log", Call("log", n)));
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("a"), Bound("b"), Bound("c"), Bound("d")],
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
