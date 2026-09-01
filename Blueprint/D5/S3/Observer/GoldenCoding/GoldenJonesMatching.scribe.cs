using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenCoding;

internal sealed class GoldenJonesMatchingDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/GoldenCoding/GoldenJonesMatching.golden_jones_matching";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden square is the first nonintegral low Jones value and the Fibonacci dimension.",
        H("Golden Jones Matching"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-jones-matching"),
            DeclarationHandle.Create(Declaration),
            H("The golden square is the first nonintegral low Jones value"),
            StatementSource.FromAuthor(MatchingFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For J(n)=4 cos^2(pi/n), the four explicit values at n=3,4,5,6 are "
                        + "1, 2, phi^2, and 3. The central identity uses the repository's "
                        + "pentagon cosine theorem rather than reproving the special value.")),
                Paragraph(Text(
                    "The radical identity phi^2=(3+sqrt(5))/2 yields both 2<phi^2<3 and "
                        + "the sharper enclosure 2.6<phi^2<2.62. Irrationality of phi then "
                        + "shows that J(5) is not an integer, while the only earlier indices "
                        + "n>=3 are n=3 and n=4 and have explicit integer witnesses.")),
                Paragraph(Text(
                    "The source also describes the self-dual Fibonacci fusion rule. Because "
                        + "the source supplies no category, tensor product, unit, or dimension "
                        + "map, the formal statement records its exact decategorified numerical "
                        + "consequence: every positive d satisfying d^2=1+d equals phi and has "
                        + "squared dimension phi^2."))),
            DescribeRole.Theorem))));

    private static Formula MatchingFormula()
    {
        Formula natural = Call("Natural");
        Formula integer = Call("Integer");
        Formula real = Call("Real");
        Formula jones = F.Id("J");
        Formula n = F.Id("n");
        Formula m = F.Id("m");
        Formula d = F.Id("d");
        Formula phi = new Formula.LatexMacro(FormulaLatexMacro.Phi);
        Formula pi = new Formula.LatexMacro(FormulaLatexMacro.Pi);
        Formula phiSquared = Power(phi, D(2));

        Formula jonesDefinition = Multiply(
            D(4),
            Power(Call("cos", new Formula.Fraction(pi, n)), D(2)));
        Formula radical = Equal(
            phiSquared,
            new Formula.Fraction(Add(D(3), Call("sqrt", D(5))), D(2)));
        Formula earlierIntegral = ForAll(
            "n",
            natural,
            Implies(
                All(LessOrEqual(D(3), n), Less(n, D(5))),
                Exists(
                    "m",
                    integer,
                    Equal(Apply(jones, n), m))));
        Formula firstNonintegral = new Formula.Not(Exists(
            "m",
            integer,
            Equal(Apply(jones, D(5)), m)));
        Formula fusionDimension = ForAll(
            "d",
            real,
            Implies(
                All(
                    Less(D(0), d),
                    Equal(Power(d, D(2)), Add(D(1), d))),
                All(
                    Equal(d, phi),
                    Equal(Power(d, D(2)), phiSquared))));
        Formula clauses = All(
            Equal(Apply(jones, D(3)), D(1)),
            Equal(Apply(jones, D(4)), D(2)),
            Equal(Apply(jones, D(5)), phiSquared),
            Equal(Apply(jones, D(6)), D(3)),
            radical,
            Less(D(2), phiSquared),
            Less(phiSquared, D(3)),
            Less(new Formula.Fraction(D(1, 3), D(5)), phiSquared),
            Less(phiSquared, new Formula.Fraction(D(1, 3, 1), D(5, 0))),
            earlierIntegral,
            firstNonintegral,
            fusionDimension);

        return Disp(Seq(
            F.Id("let"), Sp, jones, Open, n, Close, Sp, Eq, Sp,
            jonesDefinition, Semi, Sp, clauses));
    }

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound(name, domain)],
            body);

    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound(name, domain)],
            body);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula All(params Formula[] formulas) =>
        formulas.Aggregate(And);
}
