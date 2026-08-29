using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma;

internal sealed class HyperbolicBudgetTubeDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/ZetaGamma/HyperbolicBudgetTube.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local correlation bounds confine completion budgets and their extremal profiles.",
        H("Hyperbolic Budget Tubes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hyperbolic-budget-tube"),
                DeclarationHandle.Create(Prefix + "hyperbolic_budget_tube"),
                H("The hyperbolic budget tube"),
                StatementSource.FromAuthor(HyperbolicFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The endpoint estimate is obtained from the local correlation law by "
                        + "closedness at the edge of the observation window. The two signs of "
                        + "the budget difference give the lower and upper walls separately."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("riemann-budget-tube"),
                DeclarationHandle.Create(Prefix + "riemann_budget_tube"),
                H("Natural-budget profile and exponential width bounds"),
                StatementSource.FromAuthor(RiemannFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The lower and upper profiles are the infimum and supremum of the actual "
                        + "completion-budget range at each scale. Their exact hyperbolic errors "
                        + "give the three leading exponential estimates and the three refined "
                        + "second-order positive-excess bounds."))),
                DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = And(clauses[index], result);
        return result;
    }

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula HyperbolicFormula()
    {
        Formula type = F.Id("Type"), real = Call("Real");
        Formula completionType = F.Id("Completion");
        Formula scale = F.Id("L"), rate = F.Id("a");
        Formula budget = F.Id("budget"), correlation = F.Id("correlation");
        Formula global = F.Id("globalCompletion"), local = F.Id("localCompletion");
        Formula completion = F.Id("completion"), time = F.Id("t");
        Formula Budget(Formula value) => Call("apply", budget, value);
        Formula Correlation(Formula value, Formula point) =>
            Call("apply", correlation, value, point);
        Formula absDifference = new Formula.Absolute(Call("sub", Budget(local), Budget(global)));
        Formula endpointFactor = Call("cosh", Call("mul", rate, time));
        Formula correlationLaw = ForAll(
            [Bound("t", real)],
            Implies(
                Less(new Formula.Absolute(time), Call("mul", D(2), scale)),
                Equal(
                    Call("sub", Correlation(local, time), Correlation(global, time)),
                    Call("mul", Call("sub", Budget(local), Budget(global)), endpointFactor))));
        Formula correlationBound = ForAll(
            [Bound("completion", completionType), Bound("t", real)],
            AtMost(new Formula.Absolute(Correlation(completion, time)), Budget(completion)));
        Formula x = Call("mul", rate, scale);
        Formula lower = Call("mul", Budget(global),
            Call("pow", Call("tanh", x), D(2)));
        Formula upper = Call("mul", Budget(global), Call("pow",
            Call("div", Call("cosh", x), Call("sinh", x)), D(2)));
        Formula assumptions = All(
            Less(D(0), scale),
            Less(D(0), rate),
            correlationBound,
            correlationLaw);
        Formula conclusion = And(AtMost(lower, Budget(local)), AtMost(Budget(local), upper));

        return F.Disp(ForAll(
            [
                Bound("Completion", type),
                Bound("L", real),
                Bound("a", real),
                Bound("budget", new Formula.TypeArrow(completionType, real)),
                Bound("correlation", new Formula.TypeArrow(
                    completionType, new Formula.TypeArrow(real, real))),
                Bound("globalCompletion", completionType),
                Bound("localCompletion", completionType),
            ],
            Implies(assumptions, conclusion)));
    }

    private static Formula RiemannFormula()
    {
        Formula type = F.Id("Type"), real = Call("Real");
        Formula completionFamily = F.Id("Completion");
        Formula lambdaOne = F.Id("lambdaOne"), scale = F.Id("L");
        Formula budget = F.Id("budget"), correlation = F.Id("correlation");
        Formula natural = F.Id("naturalCompletion"), completion = F.Id("completion");
        Formula time = F.Id("t"), lowerBudget = F.Id("lowerBudget");
        Formula upperBudget = F.Id("upperBudget"), budgetWidth = F.Id("budgetWidth");
        Formula CompletionAt(Formula level) => Call("apply", completionFamily, level);
        Formula Budget(Formula level, Formula value) => Call("apply", budget, level, value);
        Formula Correlation(Formula level, Formula value, Formula point) =>
            Call("apply", correlation, level, value, point);
        Formula Natural(Formula level) => Call("apply", natural, level);
        Formula center = Call("mul", D(2), lambdaOne);
        Formula half = Call("div", scale, D(2));
        Formula expOne = Call("exp", Call("neg", scale));
        Formula expTwo = Call("exp", Call("neg", Call("mul", D(2), scale)));
        Formula Lower(Formula level) => Call("apply", lowerBudget, level);
        Formula Upper(Formula level) => Call("apply", upperBudget, level);
        Formula Width(Formula level) => Call("apply", budgetWidth, level);
        Formula budgetRange = Call("range", Call("apply", budget, scale));
        Formula lowerDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp, lowerBudget, Sp, Eq, Sp,
            Call("lambda", Call("typed", scale, real), Call("sInf", budgetRange)), Comma);
        Formula upperDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp, upperBudget, Sp, Eq, Sp,
            Call("lambda", Call("typed", scale, real), Call("sSup", budgetRange)), Comma);
        Formula widthDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp, budgetWidth, Sp, Eq, Sp,
            Call("lambda", Call("typed", scale, real),
                Call("sub", Upper(scale), Lower(scale))), Comma);
        Formula naturalBudget = ForAll(
            [Bound("L", real)],
            Equal(Budget(scale, Natural(scale)), center));
        Formula correlationBound = ForAll(
            [
                Bound("L", real),
                Bound("completion", CompletionAt(scale)),
                Bound("t", real),
            ],
            AtMost(new Formula.Absolute(Correlation(scale, completion, time)),
                Budget(scale, completion)));
        Formula completionDifference = ForAll(
            [
                Bound("L", real),
                Bound("completion", CompletionAt(scale)),
                Bound("t", real),
            ],
            Implies(
                Less(new Formula.Absolute(time), Call("mul", D(2), scale)),
                Equal(
                    Call("sub", Correlation(scale, completion, time),
                        Correlation(scale, Natural(scale), time)),
                    Call("mul",
                        Call("sub", Budget(scale, completion), Budget(scale, Natural(scale))),
                        Call("cosh", Call("div", time, D(2)))))));
        Formula tube = ForAll(
            [Bound("L", real)],
            Implies(Less(D(0), scale), ForAll(
                [Bound("completion", CompletionAt(scale))],
                And(
                    AtMost(Call("mul", center, Call("pow", Call("tanh", half), D(2))),
                        Budget(scale, completion)),
                    AtMost(Budget(scale, completion), Call("mul", center, Call("pow",
                        Call("div", Call("cosh", half), Call("sinh", half)), D(2))))))));
        Formula lowerError = ForAll(
            [Bound("L", real)],
            Implies(Less(D(0), scale), And(
                AtMost(D(0), Call("sub", center, Lower(scale))),
                AtMost(Call("sub", center, Lower(scale)),
                    Call("div", center, Call("pow", Call("cosh", half), D(2)))))));
        Formula upperError = ForAll(
            [Bound("L", real)],
            Implies(Less(D(0), scale), And(
                AtMost(D(0), Call("sub", Upper(scale), center)),
                AtMost(Call("sub", Upper(scale), center),
                    Call("div", center, Call("pow", Call("sinh", half), D(2)))))));
        Formula BigO(Formula function, Formula comparison) =>
            Call("IsBigO", function, F.Id("atTop"), comparison);
        Formula Lambda(Formula body) =>
            Call("lambda", Call("typed", scale, real), body);
        Formula comparisonOne = Lambda(expOne);
        Formula comparisonTwo = Lambda(expTwo);
        Formula lowerGap = Call("sub", center, Lower(scale));
        Formula upperGap = Call("sub", Upper(scale), center);
        Formula leadingLower = Call("mul", D(8), lambdaOne, expOne);
        Formula leadingWidth = Call("mul", D(1, 6), lambdaOne, expOne);
        Formula asymptotics = All(
            BigO(Lambda(lowerGap), comparisonOne),
            BigO(Lambda(upperGap), comparisonOne),
            BigO(budgetWidth, comparisonOne),
            BigO(Lambda(Call("max", D(0), Call("sub", lowerGap, leadingLower))), comparisonTwo),
            BigO(Lambda(Call("max", D(0), Call("sub", upperGap, leadingLower))), comparisonTwo),
            BigO(Lambda(Call("max", D(0),
                Call("sub", Width(scale), leadingWidth))), comparisonTwo));
        Formula assumptions = All(
            Less(D(0), lambdaOne),
            naturalBudget,
            correlationBound,
            completionDifference);
        Formula conclusion = All(tube, lowerError, upperError, asymptotics);
        Formula definedConclusion = Seq(
            lowerDefinition, Sp, upperDefinition, Sp, widthDefinition, Sp, conclusion);

        return F.Disp(ForAll(
            [
                Bound("Completion", new Formula.TypeArrow(real, type)),
                Bound("lambdaOne", real),
                Bound("budget", Call("Pi", Call("typed", scale, real),
                    new Formula.TypeArrow(CompletionAt(scale), real))),
                Bound("correlation", Call("Pi", Call("typed", scale, real),
                    new Formula.TypeArrow(CompletionAt(scale),
                        new Formula.TypeArrow(real, real)))),
                Bound("naturalCompletion", Call("Pi", Call("typed", scale, real),
                    CompletionAt(scale))),
            ],
            Implies(assumptions, definedConclusion)));
    }
}
