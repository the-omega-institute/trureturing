using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class GoldenPositivityInductionDocument : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S3/Weil/TestFunctions/GoldenPositivityInduction.golden_positivity_induction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A two-step positive recurrence propagates through cofinal Fibonacci support layers.",
        H("Golden Positivity Induction"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-positivity-induction"),
            DeclarationHandle.Create(Handle),
            H("Fibonacci-layer positivity reaches every compact Weil test"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The carrier is the canonical compactly supported Weil-test space. "
                    + "Layer n consists of tests supported within the Fibonacci radius "
                    + "fib(n+5). Two-step induction proves positivity on every layer, "
                    + "and compact support together with Fibonacci cofinality places every "
                    + "Weil test in one of those layers."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Call("Nat"), real = Call("Real");
        Formula test = Call("WeilTestFunction");
        Formula n = F.Id("n"), x = F.Id("x"), f = F.Id("f");
        Formula q = F.Id("Q"), a = F.Id("A"), b = F.Id("B"), r = F.Id("R");
        Formula layer = F.Id("Layer");

        Formula Layer(Formula index) => Call("Layer", index);
        Formula Value(Formula value) => Call("val", value);
        Formula QAt(Formula value) => Apply(q, Value(value));
        Formula AAt(Formula index, Formula value) => Call("A", index, value);
        Formula BAt(Formula index, Formula value) => Call("B", index, value);
        Formula RAt(Formula index, Formula value) => Call("R", index, value);

        Formula next = Add(n, D(2));
        Formula layerBody = new Formula.SetBuilder(
            ForAll(
                [Bound("x", real)],
                Implies(
                    NotEqual(Apply(f, x), D(0)),
                    LessOrEqual(
                        new Formula.Absolute(x),
                        Call("fib", Add(n, D(5)))))),
            f,
            test);

        Formula aType = ForAll(
            [Bound("n", natural)],
            new Formula.TypeArrow(Layer(next), Layer(Add(n, D(1)))));
        Formula bType = ForAll(
            [Bound("n", natural)],
            new Formula.TypeArrow(Layer(next), Layer(n)));
        Formula rType = ForAll(
            [Bound("n", natural)],
            new Formula.TypeArrow(Layer(next), real));

        Formula baseZero = ForAll(
            [Bound("f", Layer(D(0)))],
            LessOrEqual(D(0), QAt(f)));
        Formula baseOne = ForAll(
            [Bound("f", Layer(D(1)))],
            LessOrEqual(D(0), QAt(f)));
        Formula recurrence = ForAll(
            [Bound("n", natural), Bound("f", Layer(next))],
            Equal(
                QAt(f),
                Add(Add(QAt(AAt(n, f)), QAt(BAt(n, f))), RAt(n, f))));
        Formula residualPositive = ForAll(
            [Bound("n", natural), Bound("f", Layer(next))],
            LessOrEqual(D(0), RAt(n, f)));

        Formula layerConclusion = ForAll(
            [Bound("n", natural), Bound("f", Layer(n))],
            LessOrEqual(D(0), QAt(f)));
        Formula globalConclusion = ForAll(
            [Bound("f", test)],
            LessOrEqual(D(0), Apply(q, f)));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, q, Colon, Sp, new Formula.TypeArrow(test, real), Comma),
            Seq(Operatorname, Grp(F.Id("let")), Sp, layer, Open, n, Close, Sp,
                Colon, Eq, Sp, layerBody, Comma),
            Seq(Forall, Sp, a, Colon, Sp, aType, Comma),
            Seq(b, Colon, Sp, bType, Comma, Sp, r, Colon, Sp, rType, Comma),
            Seq(All(baseZero, baseOne, recurrence, residualPositive), Sp, Rightarrow),
            Seq(All(layerConclusion, globalConclusion), Dot),
        ]));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = And(clauses[index], result);
        return result;
    }

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
}
