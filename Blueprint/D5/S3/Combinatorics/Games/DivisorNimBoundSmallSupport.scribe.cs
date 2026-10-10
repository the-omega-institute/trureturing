using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Games;

internal sealed class DivisorNimBoundSmallSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Games/DivisorNimBoundSmallSupport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two removals of the same dyadic amount from a heap deeper than the unique "
            + "minimum produce exactly two minimum-depth heaps.",
        H("Paired Dyadic Removals"),
        Blocks(
            Node("paired-structure", "The intermediate heap and its second remainder",
                "paired_pivot_structure", StructureFormula(),
                "After the first removal, erasing the new heap recovers the unchanged "
                    + "heaps. They retain exactly one heap of depth k plus one. The second "
                    + "removal leaves a positive heap of that same depth.")),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Val(Formula h) => Call("valuation", h);
    private static Formula Power(Formula k) => Seq(D(2), Caret, Grp(k));
    private static Formula Count(Formula p, Formula k) => Call("countAt", p, k);
    private static Formula Next(Formula p, Formula h, Formula d) => Call("successor", p, h, d);
    private static Formula Erase(Formula p, Formula h) => Call("erase", p, h);
    private static Formula Premise(Formula p, Formula h, Formula k) =>
        And(Call("Positive", p), And(Call("HasDepth", p, Add(k, D(1))),
            And(Eq(Count(p, Add(k, D(1))), D(1)),
                And(Call("mem", h, p), Lt(Add(k, D(1)), Val(h))))));
    private static Formula General(Formula p, Formula h, Formula k, Formula body) =>
        All("P", Call("Multiset", Nat()), All("h", Nat(), All("k", Nat(),
            Imp(Premise(p, h, k), body))));

    private static Formula StructureFormula()
    {
        var p = F.Id("P"); var h = F.Id("h"); var k = F.Id("k"); var x = F.Id("x");
        var d = Power(k); var q = Next(p, h, d); var z = Sub(h, d);
        var remainder = Sub(z, d); var unchanged = Erase(q, z);
        return Disp(General(p, h, k, And(Eq(unchanged, Erase(p, h)),
            And(All("x", Nat(), Imp(Call("mem", x, unchanged), Le(Add(k, D(1)), Val(x)))),
                And(Eq(Count(unchanged, Add(k, D(1))), D(1)),
                    And(Lt(D(0), remainder), Eq(Val(remainder), Add(k, D(1)))))))));
    }
}
