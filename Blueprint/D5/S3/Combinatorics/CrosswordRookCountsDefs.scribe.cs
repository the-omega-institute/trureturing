using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class CrosswordRookCountsDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CrosswordRookCountsDefs.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/lewis2026crossword");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete rook placements meet every maximal horizontal and vertical white run exactly once.",
        H("Crossword Grids and Rook Placements"),
        Blocks(
            Node("cell", "Square-grid cell", "Cell", CellFormula(),
                "A cell is a pair of finite row and column indices.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("same-across", "Common across word", "SameAcross", SameWordFormula(true),
                "Two cells share an across word when their rows agree and the inclusive horizontal interval is white.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("same-down", "Common down word", "SameDown", SameWordFormula(false),
                "Two cells share a down word when their columns agree and the inclusive vertical interval is white.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rook-placement", "Complete rook placement", "IsRookPlacement", PlacementFormula(),
                "The rooks occupy white cells, no distinct pair shares a word, and every white cell shares each of its two words with a rook.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rook-count", "Rook-placement count", "rookCount", CountFormula(),
                "Count the subsets of the white cells that are complete rook placements.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Every natural count occurs", "claim", ClaimFormula(),
                "Every natural number is the complete rook-placement count of some square crossword grid.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("grid-size", "Square side length", "gridSize", GridSizeFormula(),
                "The side length accommodates five columns and the first two r minus one rows, using subtraction in Nat.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("side", "Alternating side column", "side", SideFormula(),
                "The side column is three for an even block index and one for an odd block index.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("tip", "Alternating outer column", "tip", TipFormula(),
                "The outer column is four for an even block index and zero for an odd block index.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("row-left", "Left row endpoint", "rowLeft", RowLeftFormula(),
                "The left endpoint depends on row parity, its residue modulo four, and the two boundary rows.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("row-right", "Right row endpoint", "rowRight", RowRightFormula(),
                "The right endpoint depends on row parity and the last even row.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("white", "White-cell family", "white", WhiteFormula(),
                "The occupied rows contain exactly the cells between their inclusive row endpoints.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("candidate", "Placement with central index k", "candidate", CandidateFormula(),
                "Choose the central cell in row two k, every outer tip, and the top side endpoint before k or the bottom side endpoint from k onward.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(Formula body, params (string Name, Formula Domain)[] variables)
    {
        for (var i = variables.Length - 1; i >= 0; i--)
            body = new Formula.Bind(FormulaQuantifier.ForAll,
                FormulaIdentifier.Create(variables[i].Name), variables[i].Domain, body);
        return body;
    }
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula And(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula SubsetOf(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.SubsetOf, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Mod(Formula a, Formula b) => new Formula.Modulo(a, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Cell(Formula n) => Call("Cell", n);
    private static Formula Finset(Formula a) => Call("Finset", a);
    private static Formula Row(Formula c) => Seq(c, Dot, D(1));
    private static Formula Col(Formula c) => Seq(c, Dot, D(2));
    private static Formula Val(Formula c) => Call("val", c);
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, Sp, b, Close);
    private static Formula If(Formula p, Formula a, Formula b) => Call("if", p, a, b);
    private static Formula Set(string name, Formula domain, Formula predicate) =>
        Seq(OpenBrace, Sp, F.Id(name), Sp, InMacro, Sp, domain, Sp, Bar, Sp, predicate, CloseBrace, Sp);

    private static Formula CellFormula()
    {
        var n = F.Id("N");
        return Disp(All(Eq(Cell(n), Seq(Fin(n), Sp, Times, Sp, Fin(n))), ("N", Nat())));
    }

    private static Formula SameWordFormula(bool across)
    {
        var n = F.Id("N"); var w = F.Id("W"); var c = F.Id("c"); var d = F.Id("d");
        var j = F.Id("j");
        var fixedC = across ? Row(c) : Col(c); var fixedD = across ? Row(d) : Col(d);
        var movingC = across ? Col(c) : Row(c); var movingD = across ? Col(d) : Row(d);
        var interval = All(Imp(Le(Call("min", movingC, movingD), j),
            Imp(Le(j, Call("max", movingC, movingD)),
                Mem(across ? Pair(Row(c), j) : Pair(j, Col(c)), w))), ("j", Fin(n)));
        return Disp(All(Iff(Call(across ? "SameAcross" : "SameDown", w, c, d),
            And(Eq(fixedC, fixedD), interval)), ("N", Nat()), ("W", Finset(Cell(n))),
            ("c", Cell(n)), ("d", Cell(n))));
    }

    private static Formula PlacementFormula()
    {
        var n = F.Id("N"); var w = F.Id("W"); var r = F.Id("R");
        var c = F.Id("c"); var d = F.Id("d");
        var pairwise = All(Imp(Mem(c, r), All(Imp(Mem(d, r), Imp(Ne(c, d),
            And(new Formula.Not(Call("SameAcross", w, c, d)),
                new Formula.Not(Call("SameDown", w, c, d))))), ("d", Cell(n)))), ("c", Cell(n)));
        var cover = All(Imp(Mem(c, w), And(
            Ex("d", Cell(n), And(Mem(d, r), Call("SameAcross", w, c, d))),
            Ex("d", Cell(n), And(Mem(d, r), Call("SameDown", w, c, d))))), ("c", Cell(n)));
        return Disp(All(Iff(Call("IsRookPlacement", w, r), And(SubsetOf(r, w), pairwise, cover)),
            ("N", Nat()), ("W", Finset(Cell(n))), ("R", Finset(Cell(n)))));
    }

    private static Formula CountFormula()
    {
        var n = F.Id("N"); var w = F.Id("W"); var r = F.Id("R");
        return Disp(All(Eq(Call("rookCount", w), Call("card",
            Set("R", Call("powerset", w), Call("IsRookPlacement", w, r)))),
            ("N", Nat()), ("W", Finset(Cell(n)))));
    }

    private static Formula ClaimFormula()
    {
        var r = F.Id("r"); var n = F.Id("N"); var w = F.Id("W");
        return Disp(Iff(F.Id("claim"), All(Ex("N", Nat(), Ex("W", Finset(Cell(n)),
            Eq(Call("rookCount", w), r))), ("r", Nat()))));
    }

    private static Formula GridSizeFormula()
    {
        var r = F.Id("r");
        return Disp(All(Eq(Call("gridSize", r), Call("max", D(5), Sub(Mul(D(2), r), D(1)))), ("r", Nat())));
    }

    private static Formula SideFormula()
    {
        var i = F.Id("i");
        return Disp(All(Eq(Call("side", i), If(Eq(Mod(i, D(2)), D(0)), D(3), D(1))), ("i", Nat())));
    }

    private static Formula TipFormula()
    {
        var i = F.Id("i");
        return Disp(All(Eq(Call("tip", i), If(Eq(Mod(i, D(2)), D(0)), D(4), D(0))), ("i", Nat())));
    }

    private static Formula RowLeftFormula()
    {
        var r = F.Id("r"); var a = F.Id("a");
        var boundary = Or(Eq(a, D(0)), And(Eq(a, Sub(Mul(D(2), r), D(2))), Eq(Mod(a, D(4)), D(2))));
        return Disp(All(Eq(Call("rowLeft", r, a), If(Eq(Mod(a, D(2)), D(1)),
            If(Eq(Mod(a, D(4)), D(1)), D(2), D(0)), If(boundary, D(2), D(1)))),
            ("r", Nat()), ("a", Nat())));
    }

    private static Formula RowRightFormula()
    {
        var r = F.Id("r"); var a = F.Id("a");
        var boundary = And(Eq(a, Sub(Mul(D(2), r), D(2))), Eq(Mod(a, D(4)), D(0)));
        return Disp(All(Eq(Call("rowRight", r, a), If(Eq(Mod(a, D(2)), D(1)),
            If(Eq(Mod(a, D(4)), D(1)), D(4), D(2)), If(boundary, D(2), D(3)))),
            ("r", Nat()), ("a", Nat())));
    }

    private static Formula WhiteFormula()
    {
        var r = F.Id("r"); var c = F.Id("c"); var a = Val(Row(c)); var b = Val(Col(c));
        return Disp(All(Eq(Call("white", r), Set("c", Cell(Call("gridSize", r)),
            And(Lt(a, Sub(Mul(D(2), r), D(1))), Le(Call("rowLeft", r, a), b),
                Le(b, Call("rowRight", r, a))))), ("r", Nat())));
    }

    private static Formula CandidateFormula()
    {
        var r = F.Id("r"); var k = F.Id("k"); var c = F.Id("c"); var i = F.Id("i");
        var a = Val(Row(c)); var b = Val(Col(c)); var twice = Mul(D(2), i);
        var central = And(Eq(a, Mul(D(2), k)), Eq(b, D(2)));
        var tips = Ex("i", Nat(), And(Lt(Add(i, D(1)), r), Eq(a, Add(twice, D(1))), Eq(b, Call("tip", i))));
        var sides = Ex("i", Nat(), And(Lt(Add(i, D(1)), r), Eq(b, Call("side", i)),
            Or(And(Lt(i, k), Eq(a, twice)), And(Le(k, i), Eq(a, Add(twice, D(2)))))));
        return Disp(All(Eq(Call("candidate", r, k), Set("c", Cell(Call("gridSize", r)),
            Or(central, Or(tips, sides)))), ("r", Nat()), ("k", Nat())));
    }
}
