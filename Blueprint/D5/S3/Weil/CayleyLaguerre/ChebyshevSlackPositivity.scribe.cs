using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.CayleyLaguerre;

internal sealed class ChebyshevSlackPositivityDocument : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S3/Weil/CayleyLaguerre/ChebyshevSlackPositivity."
            + "chebyshev_slack_bounds";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonnegative real spectral coordinate compactifies into the closed unit "
            + "interval, and its first-kind Chebyshev slack lies between zero and one.",
        H("Chebyshev Slack Positivity"),
        Blocks(Describe.Lean(
            DescribeId.Create("chebyshev-slack-bounds"),
            DeclarationHandle.Create(Handle),
            H("Chebyshev slack bounds"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The source rational coordinate is constructed directly from the "
                        + "nonnegative input and the scale above one quarter.")),
                Paragraph(Text(
                    "Its denominator is positive, so ordered-field division gives the "
                        + "coordinate bounds. The standard Chebyshev interval estimate "
                        + "then yields the two-sided slack bound."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Call("Nat");
        Formula real = Call("Real");
        Formula n = F.Id("N");
        Formula a = F.Id("a");
        Formula x = F.Id("x");
        Formula compactCoordinate = F.Id("compactCoordinate");
        Formula slack = F.Id("slack");
        Formula coordinateValue = new Formula.Fraction(
            Subtract(x, a),
            Add(x, a));
        Formula chebyshevValue = Call(
            "eval",
            Call("ChebyshevT", real, n),
            compactCoordinate);
        Formula slackValue = Subtract(
            D(1),
            new Formula.Power(chebyshevValue, Seq(D(2))));
        Formula premises = And(
            Less(new Formula.Fraction(D(1), D(4)), a),
            AtMost(D(0), x));
        Formula conclusions = And(
            Member(compactCoordinate, Call("Icc", new Formula.Negate(D(1)), D(1))),
            Member(slack, Call("Icc", D(0), D(1))));
        Formula definitions = Seq(
            Let("compactCoordinate", coordinateValue),
            Let("slack", slackValue),
            conclusions);

        return Disp(ForAll(
            [
                Bound("N", natural),
                Bound("a", real),
                Bound("x", real),
            ],
            Implies(premises, definitions)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Let(string name, Formula value) =>
        Seq(Operatorname, Grp(F.Id("let")), Sp, F.Id(name), Sp, Eq, Sp, value, Comma, Sp);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula ForAll(
        Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
}
