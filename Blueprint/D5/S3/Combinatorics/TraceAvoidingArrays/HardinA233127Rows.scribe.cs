using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233127RowsDocument : IScribeDocumentDefinition
{
    private const string Root =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip.";
    private const string Owner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.";
    private const string RowOwner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233254TriangleStrip.";
    private const string BoundaryOwner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer.";
    private const string Scanner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.";
    private const string Gid =
        "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Rows.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2013a233127");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal six-column complementary-pair square-strip definitions.",
        H("Literal arrays and boundary classes"),
        Blocks(
            Paragraph(Text(
                "OEIS A233127 revision 6 defines the count and records Hardin’s empirical "
                + "recurrence. All declaration names below are fully "
                + "qualified Lean names. val explicitly converts a finite index or colour "
                + "to Nat. Nat.div denotes natural quotient and Nat.mod its nonnegative "
                + "remainder; neither operation occurs in these definitions. The six-column "
                + "Row type and horizontal predicate rowLegal are reused from "
                + "HardinA233254TriangleStrip. Boundary is reused from "
                + "HardinA233255PairTransfer. A valid boundary records that colour 1 "
                + "has occurred, adjacent labels differ, and before colour 2 occurs "
                + "neither member of its complementary pair occurs.")),
            Entry("vertical", "bonds", "Vertical bonds", Vertical(),
                "Only equal columns in consecutive rows are joined. Diagonals are free."),
            Entry("count", "a", "The literal filtered finite count", Count(),
                "The filter uses the owner predicate widthLegal directly. It fixes the "
                + "upper-left cell to zero, applies rowLegal to every row and bonds between "
                + "successive rows, and applies the owner's widthNormal with initial flags "
                + "(false,false). Thus every 2, 3 or 4 has an earlier 1, and every 3 has an "
                + "earlier 2, in row-major order. The first-cell existential is false at "
                + "height zero, so a 0 = 0.", true),
            Entry("labels", "labels", "Complementary-pair labels", Labels(),
                "The label map is the published beta, applied separately to each cell.", true),
            Entry("compatible", "compatible", "Vertical label compatibility", Compatible(),
                "Every preceding label excludes the same label in the following row."),
            Entry("valid", "Valid", "Valid scanner boundaries", Valid(),
                "The first flag is true; the second flag excludes label 2 when false."),
            Entry("class", "boundaryClass", "Boundary classes", BoundaryClass(),
                "Class 0 precedes colour 2. The ten completed classes are represented by "
                + "010101, 010102, 010120, 010121, 010201, 010210, 010212, "
                + "012012, 012021 and 012120. Their orbit sizes under label permutation "
                + "and reversal are 6,12,12,12,12,12,6,6,12,6."),
            Entry("transfer", "transfer", "Class transition matrix", Transfer(),
                "Rows are source classes and columns are destination classes."),
            Entry("classcount", "classCount", "Single-row continuation counts", ClassCount(),
                "The sum is over all 6^6 individual colour rows with the original scanner."),
            Entry("firstcount", "firstCount", "First-row class distribution", FirstCount(),
                "The first colour is fixed to zero and both initial scanner flags are false."))));


    private static DocumentBlock Entry(string id, string declaration, string title,
        Formula formula, string prose, bool literature = false) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Gid + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source)
                : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Vertical()
    {
        var c = V("c"); var d = V("d"); var j = V("j");
        var x = At(c, j); var y = At(d, j);
        return All("c", Name(RowOwner + "Row"), All("d", Name(RowOwner + "Row"),
            Eq(Call(Root + "bonds", c, d), All("j", Fin(6),
                And(Ne(x, y), Ne(Add(Val(x), Val(y)), D(5)))))));
    }

    private static Formula Count()
    {
        var n = V("n"); var a = V("A");
        var arrays = Arrow(Product(Call("Fin", n), Fin(6)), Fin(6));
        var predicate = Fn("A", arrays, Call(Owner + "widthLegal",
            Name(RowOwner + "rowLegal"), Name(Root + "bonds"), a));
        var universe = Typed(Name("Finset.univ"), Call("Finset", arrays));
        return All("n", Name("Nat"), Eq(Call(Root + "a", n),
            Call("Finset.card", Call("Finset.filter", predicate, universe))));
    }

    private static Formula Seen() => Name(Scanner + "Seen");
    private static Formula PairRow() => Name(BoundaryOwner + "Boundary");
    private static Formula Proj(Formula a, bool first) =>
        Call(first ? "Prod.fst" : "Prod.snd", a);
    private static Formula Flags() => Pair(Name("Bool.false"), Name("Bool.false"));
    private static Formula Labels()
    {
        var c = V("c"); var j = V("j");
        return All("c", Name(RowOwner + "Row"), Eq(Call(Root + "labels", c),
            Fn("j", Fin(6), Call("D5.S3.Observer.Separation.BooleanRankThreeK4.beta", At(c, j)))));
    }

    private static Formula Compatible()
    {
        var p = V("p"); var c = V("c"); var j = V("j");
        return All("p", PairRow(), All("c", Name(RowOwner + "Row"),
            Eq(Call(Root + "compatible", p, c), All("j", Fin(6),
                Ne(At(p, j), Call("D5.S3.Observer.Separation.BooleanRankThreeK4.beta",
                    At(c, j)))))));
    }

    private static Formula Valid()
    {
        var s = V("s"); var p = V("p"); var j = V("j");
        var adjacent = All("j", Fin(5), Ne(At(p, Call("Fin.castSucc", j)),
            At(p, Call("Fin.succ", j))));
        return All("s", Seen(), All("p", PairRow(), Eq(Call(Root + "Valid", s, p),
            And(Eq(Proj(s, true), Name("Bool.true")), And(adjacent,
                Imp(Eq(Proj(s, false), Name("Bool.false")),
                    All("j", Fin(6), Ne(At(p, j), Typed(D(2), Fin(3))))))))));
    }

    private static Formula BoundaryClass()
    {
        var s = V("s"); var p = V("p");
        Formula P(byte j) => At(p, Typed(D(j), Fin(6)));
        Formula K(byte j) => Typed(Numeral(j), Fin(11));
        return All("s", Seen(), All("p", PairRow(),
            Eq(Call(Root + "boundaryClass", s, p), Conditional(Proj(s, false),
                Conditional(Eq(P(2), P(0)), Conditional(Eq(P(3), P(1)), Conditional(Eq(P(4),
            P(2)), Conditional(Eq(P(5), P(3)), K(1), K(2)), Conditional(Eq(P(5), P(3)), K(4),
            K(3))), Conditional(Eq(P(4), P(2)), Conditional(Eq(P(5), P(3)), K(4), K(5)),
            Conditional(Eq(P(5), P(3)), K(7), K(6)))), Conditional(Eq(P(3), P(1)),
            Conditional(Eq(P(4), P(2)), Conditional(Eq(P(5), P(3)), K(2), K(10)),
            Conditional(Eq(P(5), P(3)), K(5), K(9))), Conditional(Eq(P(4), P(2)),
            Conditional(Eq(P(5), P(3)), K(3), K(9)), Conditional(Eq(P(5), P(3)), K(6), K(8))))),
            K(0)))));
    }

    private static Formula Transfer()
    {
        var table = Vector(Vector(D(6,4), D(6,4), D(1,2,8), D(6,4), D(1,2,8), D(1,2,8), D(0),
            D(3,2), D(0), D(6,4), D(3,2)),
            Vector(D(0), D(1,9,2), D(2,5,6), D(1,2,8), D(2,5,6), D(2,5,6), D(0), D(6,4), D(0),
            D(1,2,8), D(6,4)),
            Vector(D(0), D(1,2,8), D(2,5,6), D(6,4), D(1,9,2), D(1,9,2), D(6,4), D(6,4), D(0),
            D(1,2,8), D(6,4)),
            Vector(D(0), D(6,4), D(6,4), D(1,9,2), D(1,2,8), D(6,4), D(1,2,8), D(6,4), D(6,4),
            D(6,4), D(6,4)),
            Vector(D(0), D(1,2,8), D(1,9,2), D(1,2,8), D(2,5,6), D(1,9,2), D(6,4), D(6,4), D(0),
            D(1,2,8), D(6,4)),
            Vector(D(0), D(1,2,8), D(1,9,2), D(6,4), D(1,9,2), D(2,5,6), D(0), D(6,4), D(0),
            D(1,2,8), D(6,4)),
            Vector(D(0), D(0), D(6,4), D(1,2,8), D(6,4), D(0), D(1,9,2), D(6,4), D(6,4), D(6,4),
            D(6,4)),
            Vector(D(0), D(6,4), D(1,2,8), D(1,2,8), D(1,2,8), D(1,2,8), D(1,2,8), D(1,2,8),
            D(0), D(1,2,8), D(6,4)),
            Vector(D(0), D(0), D(0), D(1,2,8), D(0), D(0), D(1,2,8), D(0), D(1,2,8), D(0), D(6,4)),
            Vector(D(0), D(6,4), D(1,2,8), D(6,4), D(1,2,8), D(1,2,8), D(6,4), D(6,4), D(0),
            D(1,9,2), D(0)),
            Vector(D(0), D(6,4), D(1,2,8), D(1,2,8), D(1,2,8), D(1,2,8), D(1,2,8), D(6,4),
            D(6,4), D(0), D(1,2,8)));
        return All("i", Fin(11), All("k", Fin(11),
            Eq(Call(Root + "transfer", V("i"), V("k")), At(table, V("i"), V("k")))));
    }

    private static Formula ClassCount()
    {
        var s = V("s"); var p = V("p"); var k = V("k"); var c = V("c");
        var condition = And(Call(RowOwner + "rowLegal", c),
            And(Call(Root + "compatible", p, c), And(Call(Scanner + "good", s, c),
                Eq(Call(Root + "boundaryClass", Call(Scanner + "finish", s, c),
                    Call(Root + "labels", c)), k))));
        return All("s", Seen(), All("p", PairRow(), All("k", Fin(11),
            Eq(Call(Root + "classCount", s, p, k), SumOver("c", Name(RowOwner + "Row"),
                Typed(Conditional(condition, D(1), D(0)), Name("Int")))))));
    }

    private static Formula FirstCount()
    {
        var k = V("k"); var c = V("c");
        var condition = And(Eq(At(c, Typed(D(0), Fin(6))), Typed(D(0), Fin(6))),
            And(Call(RowOwner + "rowLegal", c), And(Call(Scanner + "good", Flags(), c),
                Eq(Call(Root + "boundaryClass", Call(Scanner + "finish", Flags(), c),
                    Call(Root + "labels", c)), k))));
        return All("k", Fin(11), Eq(Call(Root + "firstCount", k),
            SumOver("c", Name(RowOwner + "Row"),
                Typed(Conditional(condition, D(1), D(0)), Name("Int")))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Name(string name) => Seq(name.Split('.').SelectMany((p, i) =>
        (i == 0 ? Array.Empty<Formula>() : new Formula[] { Dot }).Append(
            Seq(Operatorname, Grp(p.Select((c, j) => c >= '0' && c <= '9'
                ? D((byte)(c - '0')) : V(p.Substring(j, 1))).ToArray())))).ToArray());
    private static Formula Call(string name, params Formula[] args) => At(Name(name), args);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula f, Formula type) =>
        Parenthesized(Seq(f, Colon, Sp, type));
    private static Formula Numeral(byte k) => k switch
    {
        10 => D(1,0),
        11 => D(1,1),
        _ => D(k)
    };
    private static Formula Fin(byte k) => Call("Fin", Numeral(k));
    private static Formula Val(Formula f) => Call("val", f);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Product(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Pair(Formula a, Formula b) =>
        Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Vector(params Formula[] entries) => Seq(
        new Formula[] { Bang, OpenBracket }.Concat(entries.SelectMany((f, i) =>
            i == 0 ? new[] { f } : new[] { Comma, Sp, f }))
            .Append(CloseBracket).ToArray());
    private static Formula Conditional(Formula test, Formula yes, Formula no) =>
        Parenthesized(Seq(Name("if"), Sp, Parenthesized(test), Sp, Name("then"), Sp,
            Parenthesized(yes), Sp, Name("else"), Sp, Parenthesized(no)));
    private static Formula SumOver(string n, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(V(n), Colon, Sp, type), Sp, Parenthesized(body));
    private static Formula Imp(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula All(string n, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(n), type), Comma, Sp, Parenthesized(body));
    private static Formula Fn(string n, Formula type, Formula body) =>
        Parenthesized(Seq(Typed(V(n), type), Sp, Mapsto, Sp, Parenthesized(body)));
}
