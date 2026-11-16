using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233126SquareStripDocument : IScribeDocumentDefinition
{
    private const string Root =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233126SquareStrip.";
    private const string Owner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.";
    private const string RowOwner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233253TriangleStrip.";
    private const string BoundaryOwner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233254TriangleStrip.";
    private const string Scanner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.";
    private const string Gid =
        "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2013a233126");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hardin’s recurrence for normalized five-column complementary-pair square strips.",
        H("Literal arrays and boundary classes"),
        Blocks(
            Paragraph(Text(
                "OEIS A233126 revision 6 defines the count and records Hardin’s empirical "
                + "recurrence. All declaration names below are fully "
                + "qualified Lean names. Fin.val explicitly converts a finite index or colour "
                + "to Nat. Nat.div denotes natural quotient and Nat.mod its nonnegative "
                + "remainder; neither operation occurs in these definitions. The five-column "
                + "Row type and horizontal predicate rowLegal are reused from "
                + "HardinA233253TriangleStrip. Boundary and Valid are reused from "
                + "HardinA233254TriangleStrip. A valid boundary records that colour 1 "
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
                "The label map is the published beta, applied separately to each cell."),
            Entry("compatible", "compatible", "Vertical label compatibility", Compatible(),
                "Every preceding label excludes the same label in the following row."),
            Entry("class", "boundaryClass", "Boundary classes", BoundaryClass(),
                "Class 0 precedes colour 2. Classes 1 through 6 are the label-permutation "
                + "and reversal orbits represented by 01010, 01012, 01020, 01021, "
                + "01201 and 01210, respectively. Their sizes are 6,12,6,12,6,6."),
            Entry("transfer", "transfer", "Class transition matrix", Transfer(),
                "Rows are source classes and columns are destination classes."),
            Entry("classcount", "classCount", "Single-row continuation counts", ClassCount(),
                "The sum is over all 6^5 individual colour rows with the original scanner."),
            Entry("firstcount", "firstCount", "First-row class distribution", FirstCount(),
                "The first colour is fixed to zero and both initial scanner flags are false."),
            Describe.Lean(DescribeId.Create("labelsum"),
                DeclarationHandle.Create(Gid + "label_sum"), H("Expanding the label sum"),
                StatementSource.FromAuthor(Disp(LabelSum())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The function-space sum expands into five independent label sums."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rowvalid"),
                DeclarationHandle.Create(Gid + "row_valid"), H("Compatibility-free row validity"),
                StatementSource.FromAuthor(Disp(RowValid())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Horizontal legality and the scanner preserve validity "
                    + "once colour one has occurred, independently of inter-row bonds."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("initialvalid"),
                DeclarationHandle.Create(Gid + "initial_valid"), H("First-row validity"),
                StatementSource.FromAuthor(Disp(InitialValid())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A legal normalized first row determines a valid scanner boundary."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("certificate"),
                DeclarationHandle.Create(Gid + "finite_certificate"), H("Single-row certificate"),
                StatementSource.FromAuthor(Disp(Certificate())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Exact scanner fibres reduce the transition counts to 3^5 label rows. "
                    + "The single-row certificate supplies the numerical premises of the "
                    + "all-height induction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Gid + "result"),
                H("The recurrence at every height"), StatementSource.FromAuthor(Disp(Result())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The complementary-pair labels are the fibres {0,5}, {1,4}, {2,3} of "
                    + "D5.S3.Observer.Separation.BooleanRankThreeK4.beta. Exact scanner fibres "
                    + "retain the original order restrictions and colour multiplicities. "
                    + "The first-row distribution is (8,0,8,4,8,4,4). The displayed matrix "
                    + "gives continuation counts from every valid boundary. The class "
                    + "reduction at all heights is the linear semiconjugacy iteration: "
                    + "a class-constant continuation remains class-constant after one row, "
                    + "hence after every number of rows. The unseen sector has eigenvalue "
                    + "32. The six-class seen sector has characteristic polynomial (x+32) times "
                    + "(x^5-512x^4+66560x^3-3014656x^2+50331648x-268435456). "
                    + "The initial row distribution annihilates the -32 mode. Multiplying "
                    + "this quintic by x-32 gives precisely the six coefficients in the "
                    + "recurrence. The integer calculation therefore applies to the literal "
                    + "filtered count for every n+7, with n a natural number."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin233126"),
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
        var g = V("g");
        Formula rhs = At(g, Vector(V("a"), V("b"), V("c"), V("d"), V("e")));
        foreach (var name in new[] { "e", "d", "c", "b", "a" })
            rhs = SumOver(name, Fin(3), rhs);
        return All("g", Arrow(PairRow(), Name("Int")),
            Eq(SumOver("q", PairRow(), At(g, V("q"))), rhs));
    }

    private static Formula RowValid()
    {
        var s = V("s"); var c = V("c");
        return All("s", Seen(), All("c", Name(RowOwner + "Row"),
            Imp(Eq(Proj(s, true), Name("Bool.true")),
                Imp(Call(RowOwner + "rowLegal", c), Imp(Call(Scanner + "good", s, c),
                    Call(BoundaryOwner + "Valid", Call(Scanner + "finish", s, c),
                        Call(Root + "labels", c)))))));
    }

    private static Formula InitialValid()
    {
        var c = V("c");
        return All("c", Name(RowOwner + "Row"), Imp(
            And(Eq(At(c, Typed(D(0), Fin(5))), D(0)), And(
                Call(RowOwner + "rowLegal", c), Call(Scanner + "good", Flags(), c))),
            Call(BoundaryOwner + "Valid", Call(Scanner + "finish", Flags(), c),
                Call(Root + "labels", c))));
    }

    private static Formula Vertical()
    {
        var c = V("c"); var d = V("d"); var j = V("j");
        var x = At(c, j); var y = At(d, j);
        return All("c", Name(RowOwner + "Row"), All("d", Name(RowOwner + "Row"),
            Eq(Call(Root + "bonds", c, d), All("j", Fin(5),
                And(Ne(x, y), Ne(Add(Val(x), Val(y)), D(5)))))));
    }

    private static Formula Count()
    {
        var n = V("n"); var a = V("A");
        var arrays = Arrow(Product(Call("Fin", n), Fin(5)), Fin(6));
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
            Fn("j", Fin(5), Call("D5.S3.Observer.Separation.BooleanRankThreeK4.beta", At(c, j)))));
    }

    private static Formula Compatible()
    {
        var p = V("p"); var c = V("c"); var j = V("j");
        return All("p", PairRow(), All("c", Name(RowOwner + "Row"),
            Eq(Call(Root + "compatible", p, c), All("j", Fin(5),
                Ne(At(p, j), Call("D5.S3.Observer.Separation.BooleanRankThreeK4.beta",
                    At(c, j)))))));
    }

    private static Formula BoundaryClass()
    {
        var s = V("s"); var p = V("p");
        Formula P(byte j) => At(p, Typed(D(j), Fin(5)));
        Formula K(byte j) => Typed(D(j), Fin(7));
        return All("s", Seen(), All("p", PairRow(),
            Eq(Call(Root + "boundaryClass", s, p), Conditional(Proj(s, false),
                Conditional(And(Eq(P(0), P(2)), Eq(P(2), P(4))),
                    Conditional(Eq(P(1), P(3)), K(1), K(3)),
                    Conditional(Eq(P(1), P(3)),
                        Conditional(Eq(P(0), P(4)), K(6), K(2)),
                        Conditional(And(Eq(P(0), P(3)), Eq(P(1), P(4))), K(5), K(4)))),
                K(0)))));
    }

    private static Formula Transfer()
    {
        var table = Vector(Vector(D(3,2), D(3,2), D(6,4), D(3,2), D(3,2), D(0), D(3,2)),
            Vector(D(0), D(9,6), D(1,2,8), D(6,4), D(6,4), D(0), D(6,4)),
            Vector(D(0), D(6,4), D(9,6), D(6,4), D(6,4), D(3,2), D(3,2)),
            Vector(D(0), D(6,4), D(1,2,8), D(6,4), D(6,4), D(0), D(6,4)),
            Vector(D(0), D(3,2), D(6,4), D(3,2), D(9,6), D(3,2), D(3,2)),
            Vector(D(0), D(0), D(6,4), D(0), D(6,4), D(6,4), D(0)),
            Vector(D(0), D(6,4), D(6,4), D(6,4), D(6,4), D(0), D(6,4)));
        return All("i", Fin(7), All("k", Fin(7),
            Eq(Call(Root + "transfer", V("i"), V("k")), At(table, V("i"), V("k")))));
    }

    private static Formula ClassCount()
    {
        var s = V("s"); var p = V("p"); var k = V("k"); var c = V("c");
        var condition = And(Call(RowOwner + "rowLegal", c),
            And(Call(Root + "compatible", p, c), And(Call(Scanner + "good", s, c),
                Eq(Call(Root + "boundaryClass", Call(Scanner + "finish", s, c),
                    Call(Root + "labels", c)), k))));
        return All("s", Seen(), All("p", PairRow(), All("k", Fin(7),
            Eq(Call(Root + "classCount", s, p, k), SumOver("c", Name(RowOwner + "Row"),
                Typed(Conditional(condition, D(1), D(0)), Name("Int")))))));
    }

    private static Formula FirstCount()
    {
        var k = V("k"); var c = V("c");
        var condition = And(Eq(At(c, Typed(D(0), Fin(5))), Typed(D(0), Fin(6))),
            And(Call(RowOwner + "rowLegal", c), And(Call(Scanner + "good", Flags(), c),
                Eq(Call(Root + "boundaryClass", Call(Scanner + "finish", Flags(), c),
                    Call(Root + "labels", c)), k))));
        return All("k", Fin(7), Eq(Call(Root + "firstCount", k),
            SumOver("c", Name(RowOwner + "Row"),
                Typed(Conditional(condition, D(1), D(0)), Name("Int")))));
    }

    private static Formula Certificate()
    {
        var s = V("s"); var p = V("p"); var k = V("k");
        return And(All("s", Seen(), All("p", PairRow(), Imp(Call(BoundaryOwner + "Valid", s, p),
            All("k", Fin(7), Eq(Call(Root + "classCount", s, p, k),
                Call(Root + "transfer", Call(Root + "boundaryClass", s, p), k)))))),
            All("k", Fin(7), Eq(Call(Root + "firstCount", k),
                At(Vector(D(8), D(0), D(8), D(4), D(8), D(4), D(4)), k))));
    }

    private static Formula Result()
    {
        var n = V("n");
        Formula A(byte k) => Typed(Call(Root + "a", Add(n, D(k))), Name("Int"));
        return All("n", Name("Nat"), Eq(A(7),
            Sub(Add(Sub(Add(Sub(Mul(D(5,4,4), A(6)), Mul(D(8,2,9,4,4), A(5))),
                Mul(D(5,1,4,4,5,7,6), A(4))), Mul(D(1,4,6,8,0,0,6,4,0), A(3))),
                Mul(D(1,8,7,9,0,4,8,1,9,2), A(2))),
                Mul(D(8,5,8,9,9,3,4,5,9,2), A(1)))));
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
    private static Formula All(string n, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(n), type), Comma, Sp, Parenthesized(body));
    private static Formula Fn(string n, Formula type, Formula body) =>
        Parenthesized(Seq(Typed(V(n), type), Sp, Mapsto, Sp, Parenthesized(body)));
}
