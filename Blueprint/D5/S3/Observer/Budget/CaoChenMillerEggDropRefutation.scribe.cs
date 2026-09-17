using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;

internal sealed class CaoChenMillerEggDropRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Budget/CaoChenMillerEggDropRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/caochenmiller2025eggdrop");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A correct bounded egg-drop strategy separates all hidden points by fixed-length "
            + "binary transcripts. At four dimensions, five eggs, and side length five, "
            + "the conjectured nine-drop budget has too few transcripts.",
        H("Cao-Chen-Miller Egg-Drop Refutation"),
        Blocks(
            Node("point", "Critical points and query locations",
                PointFormula(),
                "For side function N on Fin d, Point(N) is the dependent product of "
                    + "Fin(N(i)). The zero-based representatives encode the paper's "
                    + "coordinates 1 through N(i).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("drop-outcome", "Broken-or-intact query outcome",
                DropOutcomeFormula(),
                "The value is one exactly when every query coordinate is strictly below "
                    + "the corresponding hidden coordinate; otherwise it is zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("egg-strategy", "Adaptive strategies with egg and drop budgets",
                EggStrategyFormula(),
                "A stop node returns a point at any remaining budget. A drop node asks one "
                    + "query, sends outcome zero to a child with one fewer egg, sends outcome "
                    + "one to a child with the same egg count, and consumes one drop.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("prediction", "Terminal prediction",
                PredictionFormula(),
                "Prediction follows the outcome-selected branch until a stop node and returns "
                    + "that node's point.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("padded-transcript", "Fixed-length padded transcript",
                PaddedTranscriptFormula(),
                "The first coordinate at a drop node is its observed outcome. Later "
                    + "coordinates recurse into the selected child, while every coordinate "
                    + "after a stop node is zero. Thus every transcript has the full budgeted "
                    + "function type Fin h to Fin 2.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("correct", "Exact recovery",
                CorrectFormula(),
                "A strategy is correct when its terminal prediction equals every possible "
                    + "hidden point.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("paper-bound", "The conjectured drop budget",
                PaperBoundFormula(),
                "The natural offset k-d+1 and each side length are coerced to the reals. "
                    + "The exponent is the real inverse of the coerced offset, rpow is real "
                    + "exponentiation, and natCeil is the natural ceiling.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Universal budget assertion",
                ClaimFormula(),
                "For every positive dimension, sufficient egg count, and positive side "
                    + "function, claim asks for some correct strategy within paperBound. This "
                    + "existence statement is weaker than success of a particular named "
                    + "strategy.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "The universal assertion is false",
                ResultFormula(),
                "At d=4, k=5, and constant side length five, paperBound is nine. Correctness "
                    + "makes paddedTranscript injective, but the hidden-point space has 625 "
                    + "elements and the nine-bit transcript space has 512.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(
        string id,
        string title,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + DeclarationName(id)),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static string DeclarationName(string id) => id switch
    {
        "point" => "Point",
        "drop-outcome" => "dropOutcome",
        "egg-strategy" => "EggStrategy",
        "prediction" => "prediction",
        "padded-transcript" => "paddedTranscript",
        "correct" => "Correct",
        "paper-bound" => "paperBound",
        "claim" => "claim",
        "result" => "result",
        _ => throw new ArgumentOutOfRangeException(nameof(id)),
    };

    private static Formula PointFormula()
    {
        Formula d = F.Id("d"), n = F.Id("N"), i = F.Id("i");
        Formula pointBody = ForAll("i", Fin(d), Fin(Apply(n, i)));
        return Disp(ModelBinders(Equal(Call("Point", n), pointBody)));
    }

    private static Formula DropOutcomeFormula()
    {
        Formula d = F.Id("d"), n = F.Id("N"), i = F.Id("i");
        Formula query = F.Id("q"), hidden = F.Id("x");
        Formula condition = ForAll("i", Fin(d),
            Less(Call("val", Apply(query, i)), Call("val", Apply(hidden, i))));
        Formula equation = Equal(
            Call("dropOutcome", query, hidden),
            Call("if", condition, D(1), D(0)));
        return Disp(ModelBinders(
            ForAll("q", Call("Point", n),
                ForAll("x", Call("Point", n), equation))));
    }

    private static Formula EggStrategyFormula()
    {
        Formula n = F.Id("N"), eggs = F.Id("e"), drops = F.Id("h");
        Formula point = Call("Point", n);
        Formula strategy = Call("EggStrategy", n, eggs, drops);
        Formula intactStrategy = Call("EggStrategy", n, Add(eggs, D(1)), drops);
        Formula nextStrategy = Call(
            "EggStrategy", n, Add(eggs, D(1)), Add(drops, D(1)));
        Formula stopType = ForAll("e", Naturals(), ForAll("h", Naturals(),
            Arrow(point, Call("EggStrategy", n, eggs, drops))));
        Formula dropType = ForAll("e", Naturals(), ForAll("h", Naturals(),
            Arrow(point, Arrow(strategy, Arrow(intactStrategy, nextStrategy)))));

        return Disp(ModelBinders(new Formula.Aligned([
            Seq(Call("EggStrategy", n), Sp, Colon, Sp,
                Arrow(Naturals(), Arrow(Naturals(), Types())), Comma),
            Seq(Call("stop"), Sp, Colon, Sp, stopType, Comma),
            Seq(Call("drop"), Sp, Colon, Sp, dropType, Dot),
        ])));
    }

    private static Formula PredictionFormula()
    {
        Formula n = F.Id("N"), eggs = F.Id("e"), drops = F.Id("h");
        Formula guess = F.Id("g"), hidden = F.Id("x"), query = F.Id("q");
        Formula broken = F.Id("b"), intact = F.Id("t");
        Formula stopEquation = Equal(
            Call("prediction", Call("stop", guess), hidden), guess);
        Formula dropEquation = Equal(
            Call("prediction", Call("drop", query, broken, intact), hidden),
            Call("if", Equal(Call("dropOutcome", query, hidden), D(0)),
                Call("prediction", broken, hidden), Call("prediction", intact, hidden)));
        Formula stopClause = ForAll("e", Naturals(), ForAll("h", Naturals(),
            ForAll("g", Call("Point", n), ForAll("x", Call("Point", n), stopEquation))));
        Formula dropClause = StrategyStepBinders(
            n, eggs, drops, query, broken, intact, hidden, dropEquation);
        return Disp(ModelBinders(And(stopClause, dropClause)));
    }

    private static Formula PaddedTranscriptFormula()
    {
        Formula n = F.Id("N"), eggs = F.Id("e"), drops = F.Id("h");
        Formula guess = F.Id("g"), hidden = F.Id("x"), query = F.Id("q");
        Formula broken = F.Id("b"), intact = F.Id("t"), coordinate = F.Id("j");
        Formula node = Call("drop", query, broken, intact);
        Formula answer = Call("dropOutcome", query, hidden);
        Formula stopEquation = Equal(
            Call("paddedTranscript", Call("stop", guess), hidden, coordinate), D(0));
        Formula headEquation = Equal(
            Call("paddedTranscript", node, hidden, D(0)), answer);
        Formula tailEquation = Equal(
            Call("paddedTranscript", node, hidden, Call("succ", coordinate)),
            Call("if", Equal(answer, D(0)),
                Call("paddedTranscript", broken, hidden, coordinate),
                Call("paddedTranscript", intact, hidden, coordinate)));
        Formula stopClause = ForAll("e", Naturals(), ForAll("h", Naturals(),
            ForAll("g", Call("Point", n), ForAll("x", Call("Point", n),
                ForAll("j", Fin(drops), stopEquation)))));
        Formula headClause = StrategyStepBinders(
            n, eggs, drops, query, broken, intact, hidden, headEquation);
        Formula tailClause = StrategyStepBinders(
            n, eggs, drops, query, broken, intact, hidden,
            ForAll("j", Fin(drops), tailEquation));
        return Disp(ModelBinders(And(stopClause, headClause, tailClause)));
    }

    private static Formula CorrectFormula()
    {
        Formula n = F.Id("N"), eggs = F.Id("e"), drops = F.Id("h");
        Formula strategy = F.Id("s"), hidden = F.Id("x");
        Formula exact = ForAll("x", Call("Point", n),
            Equal(Call("prediction", strategy, hidden), hidden));
        Formula definition = Iff(Call("Correct", strategy), exact);
        return Disp(ModelBinders(
            ForAll("e", Naturals(), ForAll("h", Naturals(),
                ForAll("s", Call("EggStrategy", n, eggs, drops), definition)))));
    }

    private static Formula PaperBoundFormula()
    {
        Formula d = F.Id("d"), k = F.Id("k"), n = F.Id("N"), i = F.Id("i");
        Formula offset = Add(Subtract(k, d), D(1));
        Formula realOffset = Coerce(offset, Reals());
        Formula exponent = new Formula.Power(realOffset, new Formula.Negate(D(1)));
        Formula sideSum = Summation(i, Fin(d), Coerce(Apply(n, i), Reals()));
        Formula value = Call("natCeil", Multiply(
            realOffset, Call("rpow", sideSum, exponent)));
        Formula equation = Equal(Call("paperBound", d, k, n), value);
        return Disp(ForAll("d", Naturals(), ForAll("k", Naturals(),
            ForAll("N", Arrow(Fin(d), Naturals()), equation))));
    }

    private static Formula ClaimFormula()
    {
        Formula d = F.Id("d"), k = F.Id("k"), n = F.Id("N");
        Formula strategy = F.Id("s"), i = F.Id("i");
        Formula positiveSides = ForAll("i", Fin(d), Less(D(0), Apply(n, i)));
        Formula existsStrategy = Exists("s",
            Call("EggStrategy", n, k, Call("paperBound", d, k, n)),
            Call("Correct", strategy));
        Formula quantified = ForAll("d", Naturals(), ForAll("k", Naturals(),
            ForAll("N", Arrow(Fin(d), Naturals()),
                Implies(LessEqual(D(1), d),
                    Implies(LessEqual(d, k),
                        Implies(positiveSides, existsStrategy))))));
        return Disp(Iff(F.Id("claim"), quantified));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula ModelBinders(Formula body)
    {
        Formula d = F.Id("d");
        return ForAll("d", Naturals(),
            ForAll("N", Arrow(Fin(d), Naturals()), body));
    }

    private static Formula StrategyStepBinders(
        Formula n,
        Formula eggs,
        Formula drops,
        Formula query,
        Formula broken,
        Formula intact,
        Formula hidden,
        Formula body) =>
        ForAll("e", Naturals(), ForAll("h", Naturals(),
            ForAll("q", Call("Point", n),
                ForAll("b", Call("EggStrategy", n, eggs, drops),
                    ForAll("t", Call("EggStrategy", n, Add(eggs, D(1)), drops),
                        ForAll("x", Call("Point", n), body))))));

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (int index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(
                Parenthesized(clauses[index]), FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Summation(Formula index, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(index, Sp, InMacro, Sp, domain)),
            Sp, Parenthesized(body));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Coerce(Formula value, Formula type) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, type));

    private static Formula Fin(Formula size) => Call("Fin", size);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Reals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Real"));

    private static Formula Types() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Type"));
}
