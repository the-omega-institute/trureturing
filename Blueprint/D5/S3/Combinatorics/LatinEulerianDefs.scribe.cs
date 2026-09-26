using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class LatinEulerianDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/LatinEulerianDefs.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/mirzavaziri2026latin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Latin squares carry a column-ascent statistic whose interior multiples are the target values.",
        H("Latin Squares and Column Ascents"),
        Blocks(
            Node("is-latin", "Latin square", "IsLatin", IsLatinFormula(),
                "A map on a finite square is Latin when every row and every column is a bijection on the symbols.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("column-ascents", "Column ascent count", "colAscents", ColAscentsFormula(),
                "For a fixed column, count the adjacent row positions whose entries increase.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("total-ascents", "Total column ascents", "totalAscents", TotalAscentsFormula(),
                "The total ascent number is the sum of the column ascent counts over all columns.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("interior-multiples-claim", "Interior multiples", "claim", ClaimFormula(),
                "For every order at least five and every integer k from two through n minus three, an order-n Latin square has total ascent number k n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source))),
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
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
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

    private static Formula IsLatinFormula()
    {
        var n = F.Id("n"); var l = F.Id("L"); var i = F.Id("i"); var c = F.Id("c");
        var row = All("i", Fin(n), Call("Bijective", Call("row", l, i)));
        var column = All("c", Fin(n), Call("Bijective", Call("column", l, c)));
        return Disp(All("n", Nat(), All("L", new Formula.TypeArrow(Fin(n),
            new Formula.TypeArrow(Fin(n), Fin(n))),
            Iff(Call("IsLatin", n, l), And(row, column)))));
    }

    private static Formula ColAscentsFormula()
    {
        var n = F.Id("n"); var l = F.Id("L"); var c = F.Id("c"); var j = F.Id("j");
        var predicate = And(Lt(Add(j, D(1)), n),
            Lt(Call("L", j, c), Call("L", Add(j, D(1)), c)));
        var set = Seq(OpenBrace, j, Sp, InMacro, Sp, Nat(), Bar, Sp, predicate, CloseBrace);
        return Disp(All("n", Nat(), All("L", new Formula.TypeArrow(Fin(n),
            new Formula.TypeArrow(Fin(n), Fin(n))), All("c", Fin(n),
            Eq(Call("colAscents", n, l, c), Call("card", set))))));
    }

    private static Formula TotalAscentsFormula()
    {
        var n = F.Id("n"); var l = F.Id("L"); var c = F.Id("c");
        var sum = Seq(Sum, Sp, c, Sp, InMacro, Sp, Fin(n), Sp,
            Call("colAscents", n, l, c));
        return Disp(All("n", Nat(), All("L", new Formula.TypeArrow(Fin(n),
            new Formula.TypeArrow(Fin(n), Fin(n))),
            Eq(Call("totalAscents", n, l), sum))));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n"); var k = F.Id("k"); var l = F.Id("L");
        var type = new Formula.TypeArrow(Fin(n), new Formula.TypeArrow(Fin(n), Fin(n)));
        var body = All("n", Nat(), Imp(Le(D(5), n), All("k", Nat(),
            Imp(And(Le(D(2), k), Le(k, Sub(n, D(3)))),
                Exists("L", type, And(Call("IsLatin", n, l),
                    Eq(Call("totalAscents", n, l), Mul(k, n))))))));
        return Disp(Iff(F.Id("claim"), body));
    }
}
