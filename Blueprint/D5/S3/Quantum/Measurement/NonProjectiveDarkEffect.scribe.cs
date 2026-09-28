using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class NonProjectiveDarkEffectDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Measurement/NonProjectiveDarkEffect.non_projective_dark_effect";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A permanent no-click effect can retain fractional weight outside its certain dark directions.",
        H("A Permanent Dark Effect Need Not Be a Projection"),
        Blocks(Describe.Lean(
            DescribeId.Create("non-projective-dark-effect"),
            DeclarationHandle.Create(Declaration),
            H("A two-dimensional non-projective dark effect"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For each real a strictly between zero and one, two no-click Kraus operators and one click "
                        + "Kraus operator satisfy the completeness equation. The dual no-click map depends only "
                        + "on the upper-left entry and the survival effect is constant after the first step.")),
                Paragraph(Text(
                    "The limiting effect has diagonal entries one and a, so it is not idempotent. A unit vector "
                        + "has expectation one exactly when its second coordinate vanishes.")),
                Paragraph(Text(
                    "The second basis state has permanent no-click probability a even though its weight on the "
                        + "certain dark direction is zero."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(Open, source, Close, Sp, To, Sp, target);

    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(
                Parenthesized(clauses[index]), FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula ForAll(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);

    private static Formula Product(params Formula[] factors)
    {
        Formula result = factors[0];
        for (var index = 1; index < factors.Length; index++)
            result = Seq(result, Sp, Cdot, Sp, factors[index]);
        return result;
    }

    private static Formula SumOver(Formula index, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(index, Sp, InMacro, Sp, type), Sp, body);

    private static Formula Adjoint(Formula value) => Seq(Grp(value), Caret, Grp(Star));

    private static Formula Entry(Formula matrix, Formula row, Formula column) =>
        Seq(matrix, Underscore, Grp(row, column));

    private static Formula TheoremFormula()
    {
        Formula a = F.Id("a"), q = F.Id("Q"), l = F.Id("L"), effect = F.Id("F");
        Formula i = F.Id("i"), x = F.Id("X"), n = F.Id("N"), v = F.Id("v");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula nat = Seq(Operatorname, Grp(F.Id("Nat")));
        Formula fin1 = Call("Fin", D(1)), fin2 = Call("Fin", D(2));
        Formula matrix = Call("Matrix", fin2, fin2, complex);
        Formula vector = Arrow(fin2, complex);
        Formula p0 = Call("basisProjector", D(0));
        Formula p1 = Call("basisProjector", D(1));
        Formula qa = Arrow(fin2, matrix), la = Arrow(fin1, matrix);
        Formula qAt(Formula index) => Apply(q, index);
        Formula lAt(Formula index) => Apply(l, index);
        Formula sqrtA = Call("sqrt", a);
        Formula sqrtOneSubA = Call("sqrt", Seq(Open, D(1), Sp, Minus, Sp, a, Close));
        Formula explicitEffect = Seq(p0, Sp, Plus, Sp, Product(a, p1));
        Formula completeness = Eq(
            Seq(SumOver(i, fin2, Product(Adjoint(qAt(i)), qAt(i))), Sp, Plus, Sp,
                SumOver(i, fin1, Product(Adjoint(lAt(i)), lAt(i)))),
            D(1));
        Formula dualClosed = ForAll("X", matrix,
            Eq(Call("noClickDual", q, x), Product(Entry(x, D(0), D(0)), effect)));
        Formula stable = ForAll("N", nat,
            Imp(Le(D(1), n), Eq(Call("survival", q, n), effect)));
        Formula converges = Call("Tendsto", Call("survival", q), F.Id("atTop"), Call("nhds", effect));
        Formula inner(Formula left, Formula right) =>
            Call("dotProduct", Call("star", left), right);
        Formula unitClassification = ForAll("v", vector,
            Imp(Eq(inner(v, v), D(1)),
                Iff(Eq(inner(v, Call("mulVec", effect, v)), D(1)), Eq(Apply(v, D(1)), D(0)))));
        Formula trace(Formula value) => Call("trace", value);
        Formula conclusions = And(
            Eq(qAt(D(0)), p0),
            Eq(qAt(D(1)), Call("single", D(0), D(1), sqrtA)),
            Eq(lAt(D(0)), Product(sqrtOneSubA, p1)),
            completeness,
            dualClosed,
            stable,
            converges,
            Eq(effect, explicitEffect),
            Ne(Product(effect, effect), effect),
            unitClassification,
            Eq(trace(Product(p1, effect)), a),
            Eq(trace(Product(p1, Adjoint(lAt(D(0))), lAt(D(0)))),
                Parenthesized(Seq(D(1), Sp, Minus, Sp, a))),
            Eq(trace(Product(p1, p0)), D(0)));
        Formula witnesses = Exists("Q", qa, Exists("L", la, Exists("F", matrix, conclusions)));
        Formula hypotheses = Imp(Lt(D(0), a), Imp(Lt(a, D(1)), witnesses));
        return Disp(ForAll("a", real, hypotheses));
    }
}
