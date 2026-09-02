using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma;

internal sealed class ObserverModeConfinementDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/ZetaGamma/ObserverModeConfinement.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Proper joint growth of the completed-zeta Archimedean mode confines every "
            + "bounded-prime strict sublevel in both observer mode and frequency.",
        H("Observer-Mode Confinement"),
        Blocks(Describe.Lean(
            DescribeId.Create("observer-mode-confinement"),
            DeclarationHandle.Create(Prefix + "two_direction_archimedean_confinement"),
            H("Finite dangerous modes and a common frequency window"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The observer shift is the canonical integer multiple of the golden angular "
                        + "frequency. The Archimedean term is the symmetric average of the "
                        + "existing completed-zeta digamma multiplier 2 pi mu.")),
                Paragraph(Text(
                    "The public hypotheses state proper growth on the full integer-by-real "
                        + "carrier and a uniform bound for the fixed-support prime multiplier. "
                        + "No mode or frequency is specialized.")),
                Paragraph(Text(
                    "A compact complement of a sufficiently high Archimedean superlevel contains "
                        + "both the threshold danger set and the negativity set. Its integer "
                        + "projection is finite, while its real projection is bounded."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula integer = Seq(Mathbb, Grp(F.Id("Z")));
        Formula product = Seq(integer, Sp, Times, Sp, real);
        Formula primeMultiplier = F.Id("primeMultiplier");
        Formula scale = F.Id("L");
        Formula threshold = F.Id("A");
        Formula bound = F.Id("B");
        Formula n = F.Id("n");
        Formula t = F.Id("t");
        Formula nt = F.Id("nt");
        Formula modeShift = F.Id("modeShift");
        Formula archimedeanMode = F.Id("archimedeanMode");
        Formula jointMultiplier = F.Id("jointMultiplier");
        Formula dangerousSet = F.Id("dangerousSet");
        Formula modes = F.Id("modes");
        Formula radius = F.Id("radius");

        Formula pair = Pair(n, t);
        Formula primeAt = Apply(primeMultiplier, scale, n, t);
        Formula primeBound = ForAll(
            [Bound("n", integer), Bound("t", real)],
            LessOrEqual(new Formula.Norm(primeAt), bound));
        Formula modeShiftValue = Lambda(
            n,
            integer,
            Mul(n, F.Id("goldenAngularFrequency")));
        Formula archimedeanValue = Lambda(
            nt,
            product,
            Mul(
                new Formula.Fraction(D(1), D(2)),
                Add(
                    Mul(
                        Mul(D(2), Pi),
                        Call("mu", Add(
                            Call("snd", nt),
                            Apply(modeShift, Call("fst", nt))))),
                    Mul(
                        Mul(D(2), Pi),
                        Call("mu", Sub(
                            Call("snd", nt),
                            Apply(modeShift, Call("fst", nt))))))));
        Formula growth = Call(
            "Tendsto",
            archimedeanMode,
            Call("cocompact", product),
            F.Id("atTop"));
        Formula jointValue = Lambda(
            nt,
            product,
            Sub(
                Apply(archimedeanMode, nt),
                Apply(
                    primeMultiplier,
                    scale,
                    Call("fst", nt),
                    Call("snd", nt))));
        Formula dangerousValue = SetBuilder(
            nt,
            product,
            Less(Apply(jointMultiplier, nt), threshold));
        Formula dangerousModes = SetBuilder(
            n,
            integer,
            Exists(
                [Bound("t", real)],
                Member(pair, dangerousSet)));
        Formula section = SetBuilder(t, real, Member(pair, dangerousSet));
        Formula finiteModes = Call("Finite", dangerousModes);
        Formula boundedSections = ForAll(
            [Bound("n", integer)],
            Call("IsBounded", section));
        Formula negativeBox = Exists(
            [Bound("modes", Call("Finset", integer)), Bound("radius", real)],
            And(
                LessOrEqual(D(0), radius),
                ForAll(
                    [Bound("n", integer), Bound("t", real)],
                    Implies(
                        Less(Apply(jointMultiplier, pair), D(0)),
                        And(
                            Member(n, modes),
                            LessOrEqual(new Formula.Norm(t), radius))))));

        return F.Disp(new Formula.Aligned([
            ForAll(
                [Bound("primeMultiplier", Arrow(real, Arrow(integer, Arrow(real, real)))),
                 Bound("L", real), Bound("A", real), Bound("B", real)],
                Implies(primeBound, Seq(
                    Let("modeShift", Arrow(integer, real), modeShiftValue),
                    Let("archimedeanMode", Arrow(product, real), archimedeanValue),
                    Implies(growth, Seq(
                        Let("jointMultiplier", Arrow(product, real), jointValue),
                        Let("dangerousSet", Call("Set", product), dangerousValue),
                        And(finiteModes, And(boundedSections, negativeBox)))))))
        ]));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula Let(string name, Formula type, Formula value) => Seq(
        Operatorname, Grp(F.Id("let")), Sp, F.Id(name), Colon, Sp, type,
        Sp, Eq, Sp, value, Comma, Sp);

    private static Formula SetBuilder(Formula value, Formula type, Formula condition) => Seq(
        OpenBrace, value, Sp, InMacro, Sp, type, Sp, Mid, Sp, condition, CloseBrace);

    private static Formula Pair(Formula left, Formula right) =>
        Seq(Open, left, Comma, Sp, right, Close);

    private static Formula Lambda(Formula name, Formula domain, Formula body) =>
        Seq(name, Colon, Sp, domain, Sp, Mapsto, Sp, body);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Member(Formula value, Formula set) =>
        Seq(value, Sp, InMacro, Sp, set);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
