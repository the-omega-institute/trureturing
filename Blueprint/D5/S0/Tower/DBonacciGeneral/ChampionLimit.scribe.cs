using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.DBonacciGeneral;

internal sealed class ChampionLimitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var beta = Id("beta");
        var d = Id("d");
        var reals = Id("R");
        var naturals = Id("N");

        Formula Root(Formula order) => Call("dbonacciPerronRoot", order);
        Formula Value(Formula b) => Call("championValue", b);
        Formula Mid(Formula b) => Call("championMidCoordinate", b);

        var slackClosedForm = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("beta"),
            reals,
            new Formula.Logic(
                new Formula.Logic(
                    new Formula.Relation(Num(1), FormulaRelationOperator.LessThan, beta),
                    FormulaLogicOperator.And,
                    new Formula.Relation(beta, FormulaRelationOperator.LessThan, Num(2))),
                FormulaLogicOperator.Implies,
                Equal(
                    Subtract(Mid(beta), Value(beta)),
                    new Formula.Fraction(Subtract(Num(2), beta), Subtract(beta, Num(1))))));

        var limit = Call("Tendsto",
            Value(Root(d)),
            Id("atTop"),
            Call("nhds", new Formula.Fraction(Num(1), Num(3))));

        var slackPositiveAndVanishing = new Formula.Logic(
            new Formula.Bind(
                FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("d"),
                naturals,
                new Formula.Logic(
                    new Formula.Relation(Num(2), FormulaRelationOperator.LessThanOrEqual, d),
                    FormulaLogicOperator.Implies,
                    new Formula.Relation(Num(0), FormulaRelationOperator.LessThan,
                        Subtract(Mid(Root(d)), Value(Root(d)))))),
            FormulaLogicOperator.And,
            Call("Tendsto",
                Subtract(Mid(Root(d)), Value(Root(d))),
                Id("atTop"),
                Call("nhds", Num(0))));

        const string declarationPrefix =
            "D5/S0/Tower/DBonacciGeneral/ChampionLimit.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "The champion value tends to one third, and the slack that powers the finite-depth "
                + "witness equals the Perron deficit divided by the base less one.",
            H("Champion Limit"),
            Blocks(
                Paragraph(Text(
                    "Two facts about the same quantity. The champion value is continuous at the "
                        + "limiting base, so it inherits the known convergence of the Perron root "
                        + "to two. The gap between the predecessor coordinate and that value has "
                        + "a closed form in which positivity below base two is immediate.")),
                Describe.Lean(
                    DescribeId.Create("champion-slack-closed-form"),
                    DeclarationHandle.Create(declarationPrefix + "champion_slack_eq"),
                    H("The slack in closed form"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(slackClosedForm)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Written this way the numerator is the deficit below two and the "
                            + "denominator is positive, so the sign question reduces to the "
                            + "Perron bound with no further algebra."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("champion-value-tends-to-one-third"),
                    DeclarationHandle.Create(
                        declarationPrefix + "championValue_tendsto_one_third"),
                    H("The champion value tends to one third"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(limit)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Continuity at the limiting base composed with convergence of the "
                            + "Perron root. The value at base two is one third by direct "
                            + "evaluation."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("champion-slack-positive-yet-vanishing"),
                    DeclarationHandle.Create(
                        declarationPrefix + "champion_slack_pos_and_tendsto_zero"),
                    H("Positive at every order, vanishing in the limit"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(slackPositiveAndVanishing)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Both halves matter. Positivity at each order is what lets a witness "
                            + "exist at every finite depth; the limit is what stops any single "
                            + "witness from working uniformly in the order."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/DBonacciGeneral/ChampionValue")),
            ]));
    }
}
