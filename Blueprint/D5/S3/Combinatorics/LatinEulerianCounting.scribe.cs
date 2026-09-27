using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class LatinEulerianCountingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/LatinEulerianCounting.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/mirzavaziri2026latin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Row and column counting are interchangeable, and reversing the rows complements the total ascent count.",
        H("Row Counting and Row Reversal"),
        Blocks(
            Node("row-ascents", "Row ascent count", "rowAscents", RowAscentsFormula(),
                "For adjacent rows, count the columns whose entries increase from the first row to the second.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("reverse-rows", "Row reversal", "reverseRows", ReverseRowsFormula(),
                "ReverseRows reads the original square at the reversed row index and leaves columns unchanged.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("reversed-row-pair", "Complementary row pair counts", "rowAscents_reverse_add",
                RowPairFormula(),
                "For a Latin square, each reversed adjacent row pair has a complementary ascent count, summing to the order.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("total-reverse", "Reversal identity", "total_reverse", TotalReverseFormula(),
                "Reversing all rows exchanges ascent and descent in every column comparison, so the two totals sum to n times n minus one.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role,
        AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula LType(Formula n) =>
        new Formula.TypeArrow(Fin(n), new Formula.TypeArrow(Fin(n), Fin(n)));

    private static Formula RowAscentsFormula()
    {
        var n = F.Id("n"); var l = F.Id("L"); var j = F.Id("j"); var c = F.Id("c");
        var predicate = And(Lt(Add(j, D(1)), n),
            Lt(Call("L", j, c), Call("L", Add(j, D(1)), c)));
        var set = Seq(OpenBrace, c, Sp, InMacro, Sp, Fin(n), Bar, Sp, predicate, CloseBrace);
        return Disp(All("n", Nat(), All("L", LType(n), All("j", Nat(),
            Eq(Call("rowAscents", n, l, j), Call("card", set))))));
    }

    private static Formula ReverseRowsFormula()
    {
        var n = F.Id("n"); var l = F.Id("L"); var i = F.Id("i"); var c = F.Id("c");
        var type = LType(n);
        return Disp(All("n", Nat(), All("L", type, Eq(Call("reverseRows", n, l),
            Call("fun", i, c, Call("L", Call("rev", i), c))))));
    }

    private static Formula RowPairFormula()
    {
        var n = F.Id("n"); var l = F.Id("L"); var j = F.Id("j");
        var hyp = And(Le(D(2), n), And(Call("IsLatin", n, l), Lt(j, Sub(n, D(1)))));
        var sum = Add(Call("rowAscents", n, Call("reverseRows", n, l), j),
            Call("rowAscents", n, l, Sub(Sub(n, D(2)), j)));
        return Disp(All("n", Nat(), All("L", LType(n), All("j", Nat(),
            Imp(hyp, Eq(sum, n))))));
    }

    private static Formula TotalReverseFormula()
    {
        var n = F.Id("n"); var l = F.Id("L");
        var hyp = And(Le(D(2), n), Call("IsLatin", n, l));
        var lhs = Add(Call("totalAscents", n, Call("reverseRows", n, l)),
            Call("totalAscents", n, l));
        return Disp(All("n", Nat(), All("L", LType(n), Imp(hyp,
            Eq(lhs, Mul(n, Sub(n, D(1))))))));
    }
}
