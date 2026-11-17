using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233172DiagonalStripDocument : IScribeDocumentDefinition
{
    private const string Root =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233172DiagonalStrip.";
    private const string Owner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.";
    private const string RowOwner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233254TriangleStrip.";
    private const string Gid =
        "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233172DiagonalStrip.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2013a233172");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hardin's order-ten recurrence for literal six-column diagonal strips.",
        H("Literal arrays and an eleven-class transfer"), Blocks(
            Paragraph(Text("Rows have six cells, with colours 0 through 5. The complementary "
                + "pairs are {0,5}, {1,4}, {2,3}. The horizontal predicate and its decision "
                + "procedure are HardinA233254TriangleStrip.rowLegal and instDecidableRowLegal. "
                + "Fin.val converts a finite index or colour to a natural number.")),
            Entry("bonds", "bonds", "Both diagonal exclusions", Diagonal(),
                "Both diagonals connect consecutive rows. There is no vertical or wraparound bond."),
            Entry("count", "a", "The literal filtered count", Count(),
                "The filter ranges over every array function. HardinA233251TriangleStrip.widthLegal "
                + "requires a zero first cell, rowLegal on each row, and bonds between consecutive "
                + "rows. Its widthNormal predicate starts with both flags false. In strict row-major "
                + "order, every 2, 3 or 4 has an earlier 1, and every 3 has an earlier 2. Colours may "
                + "be absent. At height zero the first-cell existential is false. There is no orbit "
                + "divisor.", true),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Gid + "result"),
                H("The recurrence at every height at least eleven"),
                StatementSource.FromAuthor(Disp(Result())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Exact scanner fibres reduce the colour rows to their pair "
                    + "labels, retaining each colour's multiplicity. Proper six-cell boundaries have "
                    + "ten classes under label permutation and reversal. One further class has not "
                    + "yet seen colour 2. In order, the complete-sector classes are indexed by the "
                    + "lexicographically least reversal of the four Boolean tests p(j)=p(j+2), "
                    + "with false before true. Their sizes are 6,12,12,12,12,6,12,6,12,6. "
                    + "The initial distribution is (16,8,16,16,16,16,8,16,8,16,0). "
                    + "The finite transfer certificate identifies all continuation counts with "
                    + "powers of the eleven-class transfer by induction. Multiplying the initial "
                    + "distribution by ten transfer powers gives the displayed integer linear "
                    + "combination of its preceding ten vectors. Pairing this vector identity "
                    + "with any continuation vector proves the recurrence for every natural n. "
                    + "Thus the first applicable sequence index is eleven."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin233172"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Entry(string id, string declaration, string title,
        Formula formula, string prose, bool literature = false) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Gid + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source)
                : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Diagonal()
    {
        var c = V("c"); var d = V("d"); var j = V("j");
        var l = Call("Fin.castSucc", j); var r = Call("Fin.succ", j);
        Formula Bond(Formula x, Formula y) => And(Ne(x, y), Ne(Add(Val(x), Val(y)), D(5)));
        return All("c", Name(RowOwner + "Row"), All("d", Name(RowOwner + "Row"),
            Eq(Call(Root + "bonds", c, d), All("j", Fin(5),
                And(Bond(At(c, l), At(d, r)), Bond(At(c, r), At(d, l)))))));
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

    private static Formula Result()
    {
        var n = V("n");
        Formula A(byte k) => Typed(Call(Root + "a", Add(n, Small(k))), Name("Int"));
        var rhs = Mul(D(1, 2, 1, 6), A(10));
        rhs = Sub(rhs, Mul(D(3, 0, 3, 1, 0, 4), A(9)));
        rhs = Sub(rhs, Mul(D(6, 5, 5, 3, 6, 0, 0), A(8)));
        rhs = Add(rhs, Mul(D(6, 0, 5, 6, 5, 7, 4, 9, 7, 6), A(7)));
        rhs = Sub(rhs, Mul(D(2, 8, 7, 7, 6, 2, 8, 0, 8, 8, 3, 2), A(6)));
        rhs = Sub(rhs, Mul(D(1, 8, 6, 2, 2, 9, 7, 8, 1, 9, 5, 4, 5, 6), A(5)));
        rhs = Add(rhs, Mul(D(1, 4, 8, 2, 1, 4, 1, 6, 7, 4, 2, 4, 2, 0, 4, 8), A(4)));
        rhs = Sub(rhs, Mul(D(1, 5, 1, 9, 9, 6, 4, 8, 7, 4, 2, 3, 7, 5, 4, 2, 4), A(3)));
        rhs = Sub(rhs, Mul(D(5, 2, 2, 4, 1, 7, 5, 5, 6, 7, 7, 4, 9, 7, 7, 5, 3, 6), A(2)));
        rhs = Add(rhs, Mul(D(5, 7, 6, 4, 6, 0, 7, 5, 2, 3, 0, 3, 4, 2, 3, 4, 8, 8, 0), A(1)));
        return All("n", Name("Nat"), Eq(A(11), rhs));
    }

    private static Formula Small(byte k) => k switch
    {
        10 => D(1, 0),
        11 => D(1, 1),
        _ => D(k)
    };

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
    private static Formula All(string n, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(n), type), Comma, Sp, Parenthesized(body));
    private static Formula Fn(string n, Formula type, Formula body) =>
        Parenthesized(Seq(Typed(V(n), type), Sp, Mapsto, Sp, Parenthesized(body)));
}
