using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.DBonacciSurvivors;

internal sealed class FiniteDepthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var n = Id("n");
        var d = Id("d");
        var state = Id("s");
        var naturals = Id("N");
        var states = Id("State");
        var strictSet = Call("strictSet", d);

        Formula Backward(Formula order, Formula set, Formula depth) =>
            Call("backward", order, set, depth);

        Formula Member(Formula value, Formula set) =>
            new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

        Formula NonemptyAt(Formula order, Formula set, Formula depth) =>
            new Formula.Bind(
                FormulaQuantifier.Exists,
                FormulaIdentifier.Create("s"),
                states,
                Member(state, Backward(order, set, depth)));

        var everyDepth = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            naturals,
            NonemptyAt(d, strictSet, n));

        var uniform = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("d"),
            naturals,
            new Formula.Logic(
                new Formula.Relation(Num(3), FormulaRelationOperator.LessThanOrEqual, d),
                FormulaLogicOperator.Implies,
                everyDepth));

        Formula Separation(Formula order) => new Formula.Logic(
            new Formula.Bind(
                FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("n"),
                naturals,
                NonemptyAt(order, Call("strictSet", order), n)),
            FormulaLogicOperator.And,
            Equal(Call("strictPermanent", order), Id("emptySet")));

        const string declarationPrefix =
            "D5/S0/Tower/DBonacciSurvivors/FiniteDepth.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "Every finite strict d-bonacci backward-survivor depth is nonempty, uniformly "
                + "in the order.",
            H("Finite Depth"),
            Blocks(
                Paragraph(Text(
                    "The champion orbit is a two-branch cycle whose large phase sits exactly on "
                        + "the strict boundary. Its two coordinates are the base divided by the "
                        + "squared base less one, and the reciprocal of that same denominator. "
                        + "Both closure identities hold for any base whose squared value differs "
                        + "from one, so they carry no order-specific content; the order enters "
                        + "only through the Perron-root bounds.")),
                Describe.Lean(
                    DescribeId.Create("dbonacci-strict-finite-depth-is-nonempty"),
                    DeclarationHandle.Create(declarationPrefix + "strict_backward_nonempty"),
                    H("Every finite strict depth is nonempty at every order"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(uniform)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The perturbation budget is the smaller of the membership slack and the "
                            + "branch slack. The membership slack is positive exactly because "
                            + "every d-bonacci Perron root lies below two, and the branch slack "
                            + "is positive unconditionally."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("dbonacci-order-four-separation"),
                    DeclarationHandle.Create(
                        declarationPrefix + "four_finite_depths_nonempty_and_permanent_empty"),
                    H("Order four separates"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(Separation(Num(4)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The levels are open sets, so a nested intersection may be empty while "
                            + "every level is nonempty. The announced emptiness at a finite "
                            + "depth is therefore not a consequence of the permanent statement, "
                            + "and is refuted here."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("dbonacci-order-five-separation"),
                    DeclarationHandle.Create(
                        declarationPrefix + "five_finite_depths_nonempty_and_permanent_empty"),
                    H("Order five separates"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(Separation(Num(5)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Same separation at order five. Together with the order-two and "
                            + "order-three modules this settles the announced family."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/DBonacciSurvivors/DBonacciPermanentSurvivors")),
            ]));
    }
}
