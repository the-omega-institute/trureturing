using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class LatinEulerianPermutationsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/LatinEulerianPermutations.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/mirzavaziri2026latin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three explicit row orders realize the low targets and the odd midpoint of the ascent spectrum.",
        H("Explicit Permutation Statistics"),
        Blocks(
            Node("two-value", "Two-target entries", "twoVal", TwoValFormula(),
                "The two-target order is given entry by entry by its initial swap, descending middle block, and final two values.",
                DescribeRole.Definition),
            Node("two-permutation", "Two-target permutation", "twoPermutation", PermutationFormula("twoPermutation", "twoVal", D(5)),
                "For n at least five, the two-target entries form a permutation of Fin n.",
                DescribeRole.Definition),
            Node("low-value", "Low-target entries", "lowVal", LowValFormula(),
                "The low-target order is the concatenation of an initial singleton, an increasing block, a descending block, and a final descending block.",
                DescribeRole.Definition),
            Node("low-permutation", "Low-target permutation", "lowPermutation", PermutationFormula("lowPermutation", "lowVal", D(3)),
                "When k is at least three and 2 k plus 2 is at most n, the low-target entries form a permutation of Fin n.",
                DescribeRole.Definition),
            Node("midpoint-value", "Odd-midpoint entries", "midpointVal", MidpointValFormula(),
                "The odd-midpoint order starts with zero, rises through the lower half, descends through the upper half, and ends at one.",
                DescribeRole.Definition),
            Node("midpoint-permutation", "Odd-midpoint permutation", "midpointPermutation",
                PermutationFormula("midpointPermutation", "midpointVal", D(2)),
                "For m at least two, the odd-midpoint entries form a permutation of Fin (2 m plus 1).",
                DescribeRole.Definition),
            Node("two-statistics", "Statistics for target two", "two_statistics", TwoStatisticsFormula(),
                "The two-target order has two ordinary ascents, no forward unit steps, n minus three backward unit steps, and endpoint values one and n minus two.",
                DescribeRole.Theorem),
            Node("low-statistics", "Statistics for low targets", "low_statistics", LowStatisticsFormula(),
                "The low-target order has k ordinary ascents, k minus two forward unit steps, n minus k minus two backward unit steps, and the stated endpoint values.",
                DescribeRole.Theorem),
            Node("midpoint-statistics", "Statistics at the odd midpoint", "midpoint_statistics", MidpointStatisticsFormula(),
                "The odd-midpoint order has m ordinary ascents, m minus two forward unit steps, m minus one backward unit steps, and endpoint values zero and one.",
                DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula TwoValFormula()
    {
        var n = F.Id("n"); var i = F.Id("i");
        var value = Call("if", Eq(i, D(0)), D(1), Call("if", Eq(i, D(1)), D(0),
            Call("if", Le(i, Sub(n, D(3))), Sub(Sub(n, D(1)), i),
                Call("if", Eq(i, Sub(n, D(2))), Sub(n, D(1)), Sub(n, D(2))))));
        return Disp(All("n", Nat(), All("i", Nat(), Eq(Call("twoVal", n, i), value))));
    }

    private static Formula LowValFormula()
    {
        var n = F.Id("n"); var k = F.Id("k"); var i = F.Id("i");
        var value = Call("if", Eq(i, D(0)), Sub(k, D(1)),
            Call("if", Lt(i, k), Sub(i, D(1)),
                Call("if", Lt(i, Sub(n, Add(k, D(1)))), Sub(Sub(n, D(2)), i),
                    Sub(Sub(Mul(D(2), n), k), Add(D(2), i)))));
        return Disp(All("n", Nat(), All("k", Nat(), All("i", Nat(),
            Eq(Call("lowVal", n, k, i), value)))));
    }

    private static Formula MidpointValFormula()
    {
        var m = F.Id("m"); var i = F.Id("i");
        var value = Call("if", Eq(i, D(0)), D(0), Call("if", Lt(i, m), Add(i, D(1)),
            Call("if", Lt(i, Mul(D(2), m)), Sub(Mul(D(3), m), i), D(1))));
        return Disp(All("m", Nat(), All("i", Nat(), Eq(Call("midpointVal", m, i), value))));
    }

    private static Formula PermutationFormula(string name, string valueName, Formula lower)
    {
        var n = F.Id("n"); var k = F.Id("k"); var h = F.Id("h");
        var domain = name == "twoPermutation" ? Le(lower, n) :
            name == "lowPermutation" ? And(Le(D(3), k), Le(Add(Mul(D(2), k), D(2)), n)) :
            Le(lower, k);
        var argument = name == "twoPermutation" ? Seq(n, Comma, Sp, h) :
            name == "lowPermutation" ? Seq(n, Comma, Sp, k, Comma, Sp, h, Comma, Sp, F.Id("hn")) :
            Seq(k, Comma, Sp, h);
        return Disp(All("n", Nat(), Imp(domain,
            Call("IsPermutation", Call(name, n, argument)))));
    }

    private static Formula TwoStatisticsFormula()
    {
        var n = F.Id("n"); var h = F.Id("h"); var hp = F.Id("hp");
        var p = Call("twoPermutation", n, h);
        var body = And(Eq(Call("ordinaryAscents", hp, p), D(2)),
            And(Eq(Call("forwardUnits", hp, p), D(0)),
            And(Eq(Call("backwardUnits", hp, p), Sub(n, D(3))),
            And(Eq(Call("val", Call("rowAt", hp, p, D(0))), D(1)),
                Eq(Call("val", Call("rowAt", hp, p, Sub(n, D(1)))), Sub(n, D(2)))))));
        var quantified = All("hp", Call("Prop"), body);
        quantified = All("h", Call("Prop"), quantified);
        quantified = All("n", Nat(), Imp(And(Le(D(5), n), Lt(D(0), n)), quantified));
        return Disp(quantified);
    }

    private static Formula LowStatisticsFormula()
    {
        var n = F.Id("n"); var k = F.Id("k"); var hk = F.Id("hk"); var hn = F.Id("hn"); var hp = F.Id("hp");
        var p = Call("lowPermutation", n, k, hk, hn);
        var body = And(Eq(Call("ordinaryAscents", hp, p), k),
            And(Eq(Call("forwardUnits", hp, p), Sub(k, D(2))),
            And(Eq(Call("backwardUnits", hp, p), Sub(Sub(n, k), D(2))),
            And(Eq(Call("val", Call("rowAt", hp, p, D(0))), Sub(k, D(1))),
                Eq(Call("val", Call("rowAt", hp, p, Sub(n, D(1)))), Sub(Sub(n, k), D(1)))))));
        var hypotheses = And(And(Le(D(3), k), Le(Add(Mul(D(2), k), D(2)), n)), Lt(D(0), n));
        var quantified = All("hp", Call("Prop"), Imp(hypotheses, body));
        quantified = All("hn", Call("Prop"), quantified);
        quantified = All("hk", Call("Prop"), quantified);
        quantified = All("k", Nat(), quantified);
        quantified = All("n", Nat(), quantified);
        return Disp(quantified);
    }

    private static Formula MidpointStatisticsFormula()
    {
        var m = F.Id("m"); var hm = F.Id("hm"); var hp = F.Id("hp");
        var p = Call("midpointPermutation", m, hm);
        var body = And(Eq(Call("ordinaryAscents", hp, p), m),
            And(Eq(Call("forwardUnits", hp, p), Sub(m, D(2))),
            And(Eq(Call("backwardUnits", hp, p), Sub(m, D(1))),
            And(Eq(Call("val", Call("rowAt", hp, p, D(0))), D(0)),
                Eq(Call("val", Call("rowAt", hp, p, Mul(D(2), m))), D(1))))));
        return Disp(All("m", Nat(), All("hm", Call("Prop"), All("hp", Call("Prop"),
            Imp(And(Le(D(2), m), Lt(D(0), Add(Mul(D(2), m), D(1)))), body)))));
    }
}
