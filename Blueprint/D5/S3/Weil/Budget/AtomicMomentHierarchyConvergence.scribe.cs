using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Budget;

internal sealed class AtomicMomentHierarchyConvergenceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Budget/AtomicMomentHierarchyConvergence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nested finite-moment completion frontiers converge to the frontier determined "
            + "by the full moment family.",
        H("Atomic Moment Hierarchy Convergence"),
        Blocks(Describe.Lean(
            DescribeId.Create("atomic-moment-hierarchy-converges"),
            DeclarationHandle.Create(Prefix + "atomic_moment_hierarchy_converges"),
            H("Finite atomic frontiers decrease to the full frontier"),
            StatementSource.FromAuthor(HierarchyFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Nested moment constraints make the finite frontiers antitone. A strict "
                    + "optimizer subsequence whose cluster satisfies every determining "
                    + "constraint identifies its order limit with the full frontier."))),
            DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Apply(Formula function, Formula value) =>
        Call("apply", function, value);

    private static Formula ApplyTwo(Formula function, Formula first, Formula second) =>
        Call("applyTwo", function, first, second);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = And(clauses[index], result);
        return result;
    }

    private static Formula Lambda(string name, Formula domain, Formula body) =>
        Seq(F.Id(name), Colon, Sp, domain, Sp, Mapsto, Sp, body);

    private static Formula Let(string name, Formula value) =>
        Seq(Operatorname, Grp(F.Id("let")), Sp, F.Id(name), Sp, Eq, Sp, value, Comma, Sp);

    private static Formula HierarchyFormula()
    {
        Formula prop = F.Id("Prop"), real = Call("Real"), natural = Call("Nat");
        Formula measure = Call("Measure", real);
        Formula c = F.Id("C"), cap = F.Id("cap"), n = F.Id("N");
        Formula k = F.Id("k"), r = F.Id("r"), nu = F.Id("nu");
        Formula levelMatch = F.Id("levelMatch"), fullMatch = F.Id("fullMatch");
        Formula budget = F.Id("resolventBudget"), whiteFloor = F.Id("whiteFloor");
        Formula optimizer = F.Id("optimizer"), cluster = F.Id("cluster");
        Formula selection = F.Id("selection"), levelValues = F.Id("levelValues");
        Formula fullValues = F.Id("fullValues"), hierarchy = F.Id("hierarchy");
        Formula fullFrontier = F.Id("fullFrontier");

        Formula Level(Formula index, Formula completion) =>
            ApplyTwo(levelMatch, index, completion);
        Formula Full(Formula completion) => Apply(fullMatch, completion);
        Formula Budget(Formula completion) => Apply(budget, completion);
        Formula Floor(Formula completion) => Apply(whiteFloor, completion);
        Formula Optimizer(Formula index) => Apply(optimizer, index);
        Formula Selection(Formula index) => Apply(selection, index);
        Formula LevelValues(Formula index) => Apply(levelValues, index);

        Formula finiteSet = new Formula.SetBuilder(
            Exists(
                [Bound("nu", measure)],
                All(Level(n, nu), AtMost(Budget(nu), c), Equal(r, Floor(nu)))),
            r,
            real);
        Formula fullSet = new Formula.SetBuilder(
            Exists(
                [Bound("nu", measure)],
                All(Full(nu), AtMost(Budget(nu), c), Equal(r, Floor(nu)))),
            r,
            real);

        Formula floorBound = ForAll(
            [Bound("nu", measure)], AtMost(Floor(nu), cap));
        Formula levelNested = ForAll(
            [Bound("N", natural), Bound("nu", measure)],
            Implies(
                Level(Call("add", n, D(1)), nu),
                Level(n, nu)));
        Formula fullImpliesLevel = ForAll(
            [Bound("nu", measure)],
            Implies(
                Full(nu),
                ForAll([Bound("N", natural)], Level(n, nu))));
        Formula determiningFamily = ForAll(
            [Bound("nu", measure)],
            Implies(
                ForAll([Bound("N", natural)], Level(n, nu)),
                Full(nu)));
        Formula optimizerLevel = ForAll(
            [Bound("N", natural)], Level(n, Optimizer(n)));
        Formula optimizerBudget = ForAll(
            [Bound("N", natural)], AtMost(Budget(Optimizer(n)), c));
        Formula optimizerOptimal = ForAll(
            [Bound("N", natural)],
            Equal(
                Floor(Optimizer(n)),
                Call("sSup", new Formula.SetBuilder(
                    Exists(
                        [Bound("nu", measure)],
                        All(Level(n, nu), AtMost(Budget(nu), c),
                            Equal(r, Floor(nu)))),
                    r,
                    real))));
        Formula clusterLevels = ForAll(
            [Bound("N", natural)], Level(n, cluster));
        Formula clusterBudget = AtMost(Budget(cluster), c);
        Formula selectionStrict = Call("StrictMono", selection);
        Formula selectedLimit = Call(
            "Tendsto",
            Seq(Open, Lambda(
                "k", natural, Floor(Optimizer(Selection(k)))), Close),
            F.Id("atTop"),
            Call("nhds", Floor(cluster)));

        Formula definitions = Seq(
            Let("levelValues", Lambda("N", natural, finiteSet)),
            Let("fullValues", fullSet),
            Let("hierarchy", Lambda("N", natural, Call("sSup", LevelValues(n)))),
            Let("fullFrontier", Call("sSup", fullValues)),
            And(
                Call("Antitone", hierarchy),
                Call(
                    "Tendsto", hierarchy, F.Id("atTop"),
                    Call("nhds", fullFrontier))));

        Formula assumptions = All(
            floorBound,
            levelNested,
            fullImpliesLevel,
            determiningFamily,
            optimizerLevel,
            optimizerBudget,
            optimizerOptimal,
            clusterLevels,
            clusterBudget,
            selectionStrict,
            selectedLimit);

        return F.Disp(ForAll(
            [
                Bound("C", real),
                Bound("cap", real),
                Bound("levelMatch", new Formula.TypeArrow(
                    natural, new Formula.TypeArrow(measure, prop))),
                Bound("fullMatch", new Formula.TypeArrow(measure, prop)),
                Bound("resolventBudget", new Formula.TypeArrow(measure, real)),
                Bound("whiteFloor", new Formula.TypeArrow(measure, real)),
                Bound("optimizer", new Formula.TypeArrow(natural, measure)),
                Bound("cluster", measure),
                Bound("selection", new Formula.TypeArrow(natural, natural)),
            ],
            Implies(assumptions, definitions)));
    }
}
