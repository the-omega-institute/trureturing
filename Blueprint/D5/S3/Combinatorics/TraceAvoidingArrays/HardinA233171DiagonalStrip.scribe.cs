using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233171DiagonalStripDocument : IScribeDocumentDefinition
{
    private const string Root =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233171DiagonalStrip.";
    private const string Owner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.";
    private const string RowOwner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233253TriangleStrip.";
    private const string BoundaryOwner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233254TriangleStrip.";
    private const string Scanner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.";
    private const string Gid =
        "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233171DiagonalStrip.";
    private const string ClassOwner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233126SquareStrip.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2013a233171");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hardin's recurrence for literal normalized five-column diagonal strips.",
        H("Literal arrays and seven boundary classes"), Blocks(
            Paragraph(Text("Rows are functions on Fin 5 with values in Fin 6. The horizontal "
                + "predicate and its decision procedure belong to HardinA233253TriangleStrip. "
                + "Boundary and Valid belong to HardinA233254TriangleStrip. The labels, "
                + "boundaryClass and firstCount belong to HardinA233126SquareStrip. "
                + "All declaration names are fully qualified. Fin.val converts a finite "
                + "index or colour to Nat. The pair labels have fibres {0,5}, {1,4}, {2,3}.")),
            Entry("bonds", "bonds", "Both diagonal exclusions", Diagonal(),
                "Both diagonals join consecutive rows; no vertical or wraparound bond is imposed."),
            Entry("count", "a", "The literal filtered count", Count(),
                "The filter is over all array functions. The owner widthLegal fixes the "
                + "first cell to zero, checks horizontal bonds and the displayed diagonals, "
                + "and applies widthNormal at (false,false). For every occurrence of 2, 3 "
                + "or 4 there is an earlier 1, and for every 3 an earlier 2, in strict "
                + "row-major order. Colours may be absent. There is no orbit divisor. "
                + "At height zero the first-cell existential is false.", true),
            Entry("compatible", "compatible", "Diagonal label compatibility", Compatible(),
                "Every diagonal bond excludes the preceding complementary-pair label."),
            Entry("transfer", "transfer", "The seven-class transfer", Transfer(),
                "Source classes index rows and destination classes index columns. Class zero "
                + "has not yet seen colour 2. The remaining classes use the owner's six "
                + "label-permutation and reversal shapes. Their sizes are 6,12,6,12,6,6."),
            Entry("classcount", "classCount", "Exact continuation counts", ClassCount(),
                "The sum ranges over the original individual colour rows with the original scanner."),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Gid + "result"),
                H("Hardin's recurrence for every height at least eight"),
                StatementSource.FromAuthor(Disp(Result())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The width-independent literal counting bridge and exact "
                    + "scanner fibres give the displayed class transfer. The owner's "
                    + "compatibility-free row_valid supplies boundary validity. The private "
                    + "finite_certificate proves the diagonal graph's class transfer and is "
                    + "used in the induction identifying all continuations with powers of this "
                    + "transfer. The reused first-row distribution is "
                    + "(8,0,8,4,8,4,4). Its eighth Krylov row is the stated integer linear "
                    + "combination of its first seven rows. The numerical premises are "
                    + "finite_certificate, distribution_step for consecutive row products, "
                    + "and distribution_relation for this integer relation; all feed result. "
                    + "Multiplying this identity by every "
                    + "continuation vector proves the recurrence for all n+8. Thus the "
                    + "literal count, defined independently of the recurrence, satisfies the "
                    + "displayed order-seven relation."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin233171"),
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
            Eq(Call(Root + "bonds", c, d), All("j", Fin(4),
                And(Bond(At(c, l), At(d, r)), Bond(At(c, r), At(d, l)))))));
    }

    private static Formula Compatible()
    {
        var p = V("p"); var c = V("c"); var j = V("j");
        var l = Call("Fin.castSucc", j); var r = Call("Fin.succ", j);
        Formula Beta(Formula x) => Call("D5.S3.Observer.Separation.BooleanRankThreeK4.beta", x);
        return All("p", PairRow(), All("c", Name(RowOwner + "Row"),
            Eq(Call(Root + "compatible", p, c), All("j", Fin(4),
                And(Ne(At(p, l), Beta(At(c, r))), Ne(At(p, r), Beta(At(c, l))))))));
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
    private static Formula Transfer()
    {
        var table = Vector(Vector(D(3,2), D(3,2), D(6,4), D(3,2), D(3,2), D(0), D(3,2)),
            Vector(D(0), D(9,6), D(1,2,8), D(6,4), D(6,4), D(0), D(6,4)),
            Vector(D(0), D(6,4), D(1,2,8), D(3,2), D(3,2), D(0), D(6,4)),
            Vector(D(0), D(6,4), D(6,4), D(6,4), D(6,4), D(3,2), D(0)),
            Vector(D(0), D(3,2), D(3,2), D(3,2), D(6,4), D(3,2), D(0)),
            Vector(D(0), D(0), D(0), D(3,2), D(6,4), D(3,2), D(0)),
            Vector(D(0), D(6,4), D(1,2,8), D(0), D(0), D(0), D(6,4)));
        return All("i", Fin(7), All("k", Fin(7),
            Eq(Call(Root + "transfer", V("i"), V("k")),
                Typed(At(At(table, V("i")), V("k")), Name("Int")))));
    }

    private static Formula ClassCount()
    {
        var s = V("s"); var p = V("p"); var k = V("k"); var c = V("c");
        var condition = And(Call(RowOwner + "rowLegal", c),
            And(Call(Root + "compatible", p, c), And(Call(Scanner + "good", s, c),
                Eq(Call(ClassOwner + "boundaryClass", Call(Scanner + "finish", s, c),
                    Call(ClassOwner + "labels", c)), k))));
        return All("s", Seen(), All("p", PairRow(), All("k", Fin(7),
            Eq(Call(Root + "classCount", s, p, k), SumOver("c", Name(RowOwner + "Row"),
                Typed(Conditional(condition, D(1), D(0)), Name("Int")))))));
    }

    private static Formula Result()
    {
        var n = V("n");
        Formula A(byte k) => Typed(Call(Root + "a", Add(n, D(k))), Name("Int"));
        return All("n", Name("Nat"), Eq(A(8),
            Sub(Add(Sub(Add(Add(Sub(Mul(D(4,8,0), A(7)), Mul(D(6,0,4,1,6), A(6))),
                Mul(D(1,9,6,6,0,8,0), A(5))), Mul(D(2,2,0,2,0,0,9,6), A(4))),
                Mul(D(1,8,4,5,4,9,3,7,6,0), A(3))), Mul(D(2,2,5,4,8,5,7,8,3,0,4), A(2))),
                Mul(D(6,8,7,1,9,4,7,6,7,3,6), A(1)))));
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
    private static Formula Vector(params Formula[] entries) => Seq(
        new Formula[] { Bang, OpenBracket }.Concat(entries.SelectMany((f, i) =>
            i == 0 ? new[] { f } : new[] { Comma, Sp, f }))
            .Append(CloseBracket).ToArray());
    private static Formula Conditional(Formula test, Formula yes, Formula no) =>
        Parenthesized(Seq(Name("if"), Sp, Parenthesized(test), Sp, Name("then"), Sp,
            Parenthesized(yes), Sp, Name("else"), Sp, Parenthesized(no)));
    private static Formula SumOver(string n, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(V(n), Colon, Sp, type), Sp, Parenthesized(body));
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
