using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Decision;

internal sealed class NonuniqueOptimalActionSelectorDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Decision/NonuniqueOptimalActionSelector."
            + "determined_optimal_set_can_be_nonunique";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A determined optimizer set can remain non-singleton until an ordered tie-breaker is added.",
        H("Nonunique Optimal Actions and Ordered Selection"),
        Blocks(Describe.Lean(
            DescribeId.Create("determined-optimal-set-can-be-nonunique"),
            DeclarationHandle.Create(Declaration),
            H("A determined optimum need not determine one policy"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The prediction is a constant PMF on Unit and every Boolean action has zero "
                        + "loss. Expected loss and the optimizer readout are constructed from that "
                        + "same prediction and loss, so the optimizer is determined but contains "
                        + "both actions.")),
                Paragraph(Text(
                    "The fixed Boolean order selects false as the unique least optimum. The true "
                        + "action remains optimal, making explicit that single-valuedness belongs "
                        + "to the added order rather than to the original risk profile."))),
            DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula TheoremFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula unit = F.Id("Unit");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula prediction = F.Id("K");
        Formula loss = F.Id("ell");
        Formula expectedLoss = F.Id("R");
        Formula optimal = F.Id("Opt");
        Formula concept = F.Id("concept");
        Formula selector = F.Id("s");
        Formula state = F.Id("x");
        Formula action = F.Id("a");
        Formula alternative = F.Id("b");
        Formula selected = F.Id("u");
        Formula predictionType = Arrow(boolean, Call("PMF", unit));
        Formula lossType = Arrow(boolean, Arrow(unit, real));
        Formula riskAt(Formula chosen) => Apply(expectedLoss, state, chosen);
        Formula optimalAt = Apply(optimal, state);
        Formula selectedAt = Apply(selector, state);
        Formula expectedDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp, expectedLoss, Colon, Sp,
            Arrow(boolean, Arrow(boolean, real)), Comma, Sp,
            Forall, Sp, state, Colon, Sp, boolean, Comma, Sp,
            action, Colon, Sp, boolean, Comma, Sp,
            Apply(expectedLoss, state, action), Sp, Colon, Eq, Sp,
            Call("integral", Call("toMeasure", Apply(prediction, state)),
                Apply(loss, action)),
            Semi, Sp);
        Formula optimizerPredicate = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("b"),
            boolean,
            LessOrEqual(riskAt(action), riskAt(alternative)));
        Formula optimizerDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp, optimal, Colon, Sp,
            Arrow(boolean, Call("Set", boolean)), Comma, Sp,
            Forall, Sp, state, Colon, Sp, boolean, Comma, Sp,
            optimalAt, Sp, Colon, Eq, Sp,
            Left, OpenBrace, action, Colon, Sp, boolean, Sp, Mid, Sp,
            optimizerPredicate, Right, CloseBrace, Semi, Sp);
        Formula selectorDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp, selector, Colon, Sp,
            Arrow(boolean, boolean), Comma, Sp,
            Forall, Sp, state, Colon, Sp, boolean, Comma, Sp,
            selectedAt, Sp, Colon, Eq, Sp, F.Id("false"), Semi, Sp);
        Formula conceptDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp, concept, Colon, Sp,
            Arrow(boolean, unit), Comma, Sp,
            Forall, Sp, state, Colon, Sp, boolean, Comma, Sp,
            Apply(concept, state), Sp, Colon, Eq, Sp, F.Id("unit"), Semi, Sp);
        Formula determined = Call("Refines", optimal, concept);
        Formula twoActions = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            boolean,
            Equal(Call("ncard", optimalAt), Num(2)));
        Formula selectorOptimal = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            boolean,
            Member(selectedAt, optimalAt));
        Formula selectorLeast = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("x", boolean), Bound("a", boolean)],
            ImpliesFormula(Member(action, optimalAt), LessOrEqual(selectedAt, action)));
        Formula candidateLeast = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("a"),
            boolean,
            ImpliesFormula(Member(action, optimalAt), LessOrEqual(selected, action)));
        Formula uniqueLeast = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("x", boolean), Bound("u", boolean)],
            ImpliesFormula(
                And(Member(selected, optimalAt), candidateLeast),
                Equal(selected, selectedAt)));
        Formula otherOptimum = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            boolean,
            new Formula.Bind(
                FormulaQuantifier.Exists,
                FormulaIdentifier.Create("a"),
                boolean,
                And(
                    Member(action, optimalAt),
                    new Formula.Relation(
                        action, FormulaRelationOperator.NotEqual, selectedAt))));
        Formula clauses = And(
            determined,
            And(
                twoActions,
                And(
                    selectorOptimal,
                    And(selectorLeast, And(uniqueLeast, otherOptimum)))));
        Formula body = Seq(
            expectedDefinition,
            optimizerDefinition,
            conceptDefinition,
            selectorDefinition,
            clauses);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("K", predictionType), Bound("ell", lossType)],
            body));
    }
}
