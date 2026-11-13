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
    private const string Scanner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.";
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
            Entry("decidable-horizontal", "decidableRowLegal", "Deciding horizontal bonds",
                DecidableHorizontal(),
                "The defining expression is inferInstanceAs for the displayed universally quantified conjunction."),
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
                "The label map is the published beta, applied separately to each cell."),
            Entry("compatible", "compatible", "Vertical label compatibility", Compatible(),
                "Every preceding label excludes the same label in the following row."),
            Entry("valid", "Valid", "Reachable boundaries", Valid(),
                "Colour 1 has occurred. Adjacent labels differ. Before colour 2 occurs, "
                + "neither member of its complementary pair occurs."),
            Entry("class", "boundaryClass", "Boundary classes", BoundaryClass(),
                "Class 0 is the unseen sector. Classes 1, 2, 3 are alternating, "
                + "unequal endpoints without alternation, and equal endpoints."),
            Entry("transfer", "transfer", "Class transition matrix", Transfer(),
                "Rows are source classes and columns are destination classes."),
            Entry("classcount", "classCount", "Single-row continuation counts", ClassCount(),
                "The sum is over all 6^4 individual colour rows with the original scanner."),
            Entry("firstcount", "firstCount", "First-row class distribution", FirstCount(),
                "The first colour is fixed to zero and both initial scanner flags are false."),
            Describe.Lean(DescribeId.Create("label-sum"),
                DeclarationHandle.Create(Gid + "label_sum"), H("Summing over label rows"),
                StatementSource.FromAuthor(Disp(LabelSum())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The sum over all four-column label rows equals four nested sums "
                    + "over the three labels, for every integer-valued function."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("certificate"),
                DeclarationHandle.Create(Gid + "finite_certificate"), H("Single-row certificate"),
                StatementSource.FromAuthor(Disp(Certificate())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Exact scanner fibres reduce the transition counts to 3^4 label rows. "
                    + "The single-row certificate supplies the numerical premises of the "
                    + "all-height induction."))), DescribeRole.Theorem),
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
                    + "recurrence assumed."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin233125"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Entry(string id, string declaration, string title,
        Formula formula, string prose, bool literature = false) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Gid + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source)
                : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula LabelSum()
    {
        var g = V("g"); var q = V("q");
        var summand = At(g, Parenthesized(Vector(V("a"), V("b"), V("c"), V("d"))));
        var nested = SumOver("a", Fin(3), SumOver("b", Fin(3),
            SumOver("c", Fin(3), SumOver("d", Fin(3), summand))));
        return All("g", Arrow(Parenthesized(PairRow()), Name("Int")),
            Eq(SumOver("q", PairRow(), At(g, q)), nested));
    }

    private static Formula DecidableHorizontal()
    {
        var c = V("c"); var j = V("j");
        var x = At(c, Call("Fin.castSucc", j));
        var y = At(c, Call("Fin.succ", j));
        var body = All("j", Fin(3), And(Ne(x, y), Ne(Add(Val(x), Val(y)), D(5))));
        return All("c", Name(Root + "Row"),
            Eq(Typed(Call(Root + "decidableRowLegal", c), Call("Decidable", Parenthesized(Call(Root + "rowLegal", c)))),
                Call("inferInstanceAs", Parenthesized(Call("Decidable", Parenthesized(body))))));
    }

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

    private static Formula Seen() => Name(Scanner + "Seen");
    private static Formula PairRow() => Arrow(Fin(4), Fin(3));
    private static Formula Proj(Formula a, bool first) =>
        Call(first ? "Prod.fst" : "Prod.snd", a);
    private static Formula Flags() => Pair(Name("Bool.false"), Name("Bool.false"));
    private static Formula Labels()
    {
        var c = V("c"); var j = V("j");
        return All("c", Name(Root + "Row"), Eq(Call(Root + "labels", c),
            Fn("j", Fin(4), Call("D5.S3.Observer.Separation.BooleanRankThreeK4.beta", At(c, j)))));
    }

    private static Formula Compatible()
    {
        var p = V("p"); var c = V("c"); var j = V("j");
        return All("p", PairRow(), All("c", Name(Root + "Row"),
            Eq(Call(Root + "compatible", p, c), All("j", Fin(4),
                Ne(At(p, j), Call("D5.S3.Observer.Separation.BooleanRankThreeK4.beta",
                    At(c, j)))))));
    }

    private static Formula Valid()
    {
        var s = V("s"); var p = V("p"); var j = V("j");
        var proper = All("j", Fin(3),
            Ne(At(p, Call("Fin.castSucc", j)), At(p, Call("Fin.succ", j))));
        var unseen = Imp(Eq(Proj(s, false), Name("Bool.false")),
            All("j", Fin(4), Ne(At(p, j), Typed(D(2), Fin(3)))));
        return All("s", Seen(), All("p", PairRow(), Eq(Call(Root + "Valid", s, p),
            And(Eq(Proj(s, true), Name("Bool.true")), And(proper, unseen)))));
    }

    private static Formula BoundaryClass()
    {
        var s = V("s"); var p = V("p");
        Formula P(byte j) => At(p, Typed(D(j), Fin(4)));
        return All("s", Seen(), All("p", PairRow(),
            Eq(Call(Root + "boundaryClass", s, p), Conditional(Proj(s, false),
                Conditional(And(Eq(P(0), P(2)), Eq(P(1), P(3))), Typed(D(1), Fin(4)),
                    Conditional(Eq(P(0), P(3)), Typed(D(3), Fin(4)),
                        Typed(D(2), Fin(4)))), Typed(D(0), Fin(4))))));
    }

    private static Formula Transfer()
    {
        var table = Vector(Vector(D(1,6), D(1,6), D(3,2), D(8)),
            Vector(D(0), D(4,8), D(6,4), D(1,6)),
            Vector(D(0), D(3,2), D(6,4), D(1,6)),
            Vector(D(0), D(1,6), D(3,2), D(3,2)));
        return All("i", Fin(4), All("k", Fin(4),
            Eq(Call(Root + "transfer", V("i"), V("k")), At(table, V("i"), V("k")))));
    }

    private static Formula ClassCount()
    {
        var s = V("s"); var p = V("p"); var k = V("k"); var c = V("c");
        var condition = And(Call(Root + "rowLegal", c),
            And(Call(Root + "compatible", p, c), And(Call(Scanner + "good", s, c),
                Eq(Call(Root + "boundaryClass", Call(Scanner + "finish", s, c),
                    Call(Root + "labels", c)), k))));
        return All("s", Seen(), All("p", PairRow(), All("k", Fin(4),
            Eq(Call(Root + "classCount", s, p, k), SumOver("c", Name(Root + "Row"),
                Typed(Conditional(condition, D(1), D(0)), Name("Int")))))));
    }

    private static Formula FirstCount()
    {
        var k = V("k"); var c = V("c");
        var condition = And(Eq(At(c, Typed(D(0), Fin(4))), Typed(D(0), Fin(6))),
            And(Call(Root + "rowLegal", c), And(Call(Scanner + "good", Flags(), c),
                Eq(Call(Root + "boundaryClass", Call(Scanner + "finish", Flags(), c),
                    Call(Root + "labels", c)), k))));
        return All("k", Fin(4), Eq(Call(Root + "firstCount", k),
            SumOver("c", Name(Root + "Row"),
                Typed(Conditional(condition, D(1), D(0)), Name("Int")))));
    }

    private static Formula Certificate()
    {
        var s = V("s"); var p = V("p"); var k = V("k");
        return And(All("s", Seen(), All("p", PairRow(), Imp(Call(Root + "Valid", s, p),
            All("k", Fin(4), Eq(Call(Root + "classCount", s, p, k),
                Call(Root + "transfer", Call(Root + "boundaryClass", s, p), k)))))),
            All("k", Fin(4), Eq(Call(Root + "firstCount", k),
                At(Vector(D(4), D(0), D(4), D(2)), k))));
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
