using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233125SquareStripDocument : IScribeDocumentDefinition
{
    private const string Root =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233125SquareStrip.";
    private const string Owner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.";
    private const string Gid =
        "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2013a233125");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The generating function for normalized four-column complementary-pair square strips.",
        H("Literal arrays and boundary classes"),
        Blocks(
            Paragraph(Text(
                "OEIS A233125 revision 10 defines the count. The generating function is "
                + "attributed there to R. J. Mathar. All declaration names below are fully "
                + "qualified Lean names. Fin.val explicitly converts a finite index or colour "
                + "to Nat. Nat.div denotes natural quotient and Nat.mod its nonnegative "
                + "remainder; neither operation occurs in these definitions.")),
            Entry("row", "Row", "Rows", Eq(Name(Root + "Row"), Arrow(Fin(4), Fin(6))),
                "A row contains four individual colours."),
            Entry("horizontal", "rowLegal", "Horizontal bonds", Horizontal(),
                "Fin.castSucc and Fin.succ select consecutive columns."),
            Entry("vertical", "bonds", "Vertical bonds", Vertical(),
                "Only equal columns in consecutive rows are joined. Diagonals are free."),
            Entry("count", "a", "The literal filtered finite count", Count(),
                "The filter uses the owner predicate widthLegal directly. It fixes the "
                + "upper-left cell to zero, applies rowLegal to every row and bonds between "
                + "successive rows, and applies the owner's widthNormal with initial flags "
                + "(false,false). Thus every 2, 3 or 4 has an earlier 1, and every 3 has an "
                + "earlier 2, in row-major order. The first-cell existential is false at "
                + "height zero, so a 0 = 0.", true),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Gid + "result"),
                H("The power-series identity"), StatementSource.FromAuthor(Disp(Result())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The complementary-pair labels are the fibres {0,5}, {1,4}, {2,3} of "
                    + "BooleanRankThreeK4.beta. The original scanner and its exact weighted "
                    + "pushforward are reused. Before colour 2 occurs there is one boundary "
                    + "class. Afterwards the proper label rows split into alternating rows, "
                    + "the two reversal-related types, and rows with equal endpoints. "
                    + "In this order the transfer rows are (16,16,32,8), (0,48,64,16), "
                    + "(0,32,64,16), (0,16,32,32), and the first-row distribution is "
                    + "(4,0,4,2). Induction proves that these classes suffice at every "
                    + "height. The first sector has factor 1-16X; the remaining three "
                    + "classes have factor 1-144X+3840X²-24576X³. This proves the "
                    + "displayed identity for the literal count, with no empirical "
                    + "recurrence assumed."))), DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string declaration, string title,
        Formula formula, string prose, bool literature = false) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Gid + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source)
                : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Horizontal()
    {
        var c = V("c"); var j = V("j");
        var x = At(c, Call("Fin.castSucc", j));
        var y = At(c, Call("Fin.succ", j));
        return All("c", Name(Root + "Row"), Eq(Call(Root + "rowLegal", c),
            All("j", Fin(3), And(Ne(x, y), Ne(Add(Val(x), Val(y)), D(5))))));
    }

    private static Formula Vertical()
    {
        var c = V("c"); var d = V("d"); var j = V("j");
        var x = At(c, j); var y = At(d, j);
        return All("c", Name(Root + "Row"), All("d", Name(Root + "Row"),
            Eq(Call(Root + "bonds", c, d), All("j", Fin(4),
                And(Ne(x, y), Ne(Add(Val(x), Val(y)), D(5)))))));
    }

    private static Formula Count()
    {
        var n = V("n"); var a = V("A");
        var arrays = Arrow(Product(Call("Fin", n), Fin(4)), Fin(6));
        var predicate = Fn("A", arrays, Call(Owner + "widthLegal",
            Name(Root + "rowLegal"), Name(Root + "bonds"), a));
        var universe = Typed(Name("Finset.univ"), Call("Finset", arrays));
        return All("n", Name("Nat"), Eq(Call(Root + "a", n),
            Call("Finset.card", Call("Finset.filter", predicate, universe))));
    }

    private static Formula Result()
    {
        var x = Typed(Name("PowerSeries.X"), Call("PowerSeries", Name("Int")));
        var series = Call("PowerSeries.mk", Fn("n", Name("Nat"),
            Typed(Call(Root + "a", V("n")), Name("Int"))));
        return Eq(Mul(Mul(Sub(D(1), Mul(D(1,6), x)),
            Sub(Add(Sub(D(1), Mul(D(1,4,4), x)), Mul(D(3,8,4,0), Pow(x, 2))),
                Mul(D(2,4,5,7,6), Pow(x, 3)))), series),
            Mul(x, Sub(Add(Sub(D(1,0), Mul(D(7,0,4), x)),
                Mul(D(1,4,3,3,6), Pow(x, 2))), Mul(D(8,1,9,2,0), Pow(x, 3)))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Name(string name) => Seq(name.Split('.').SelectMany((p, i) =>
        (i == 0 ? Array.Empty<Formula>() : new Formula[] { Dot }).Append(
            Seq(Operatorname, Grp(System.Text.RegularExpressions.Regex.Matches(
                p, "[A-Za-z]+|[0-9]").Select(m => char.IsDigit(m.Value[0])
                    ? D((byte)(m.Value[0] - '0')) : V(m.Value)).ToArray())))).ToArray());
    private static Formula Call(string name, params Formula[] args) => At(Name(name), args);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula f, Formula type) =>
        Parenthesized(Seq(f, Colon, Sp, type));
    private static Formula Fin(byte k) => Call("Fin", D(k));
    private static Formula Val(Formula f) => Call("Fin.val", f);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Product(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Pow(Formula a, byte b) => new Formula.Power(Parenthesized(a), D(b));
    private static Formula All(string n, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(n), type), Comma, Sp, Parenthesized(body));
    private static Formula Fn(string n, Formula type, Formula body) =>
        Parenthesized(Seq(Typed(V(n), type), Sp, Mapsto, Sp, Parenthesized(body)));
}
