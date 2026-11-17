using System.Globalization;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233128RowsDocument : IScribeDocumentDefinition
{
    private const string Root =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip.";
    private const string Owner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.";
    private const string RowOwner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer.";
    private const string BoundaryOwner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer.";
    private const string Scanner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.";
    private const string Gid =
        "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Rows.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2013a233128");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal seven-column complementary-pair square strips.",
        H("Literal counts and boundary classes"),
        Blocks(
            Paragraph(Text(
                "OEIS A233128 revision 6 specifies the count. Every displayed name is its "
                + "full Lean name. Fin.val converts a finite index or colour to Nat. "
                + "Nat.div is natural quotient division and Nat.mod its nonnegative "
                + "remainder; neither operation occurs here. The public Row, rowLegal and "
                + "PairRow are reused from HardinA233255PairTransfer. Horizontal and "
                + "vertical bonds exclude equal colours and complementary colours; "
                + "diagonal neighbours are unconstrained.")),
            Entry("bonds", "bonds", "Vertical bonds", Vertical(),
                "Only equal columns in consecutive rows are joined."),
            Entry("count", "a", "Literal filtered finite count", Count(),
                "The filter uses widthLegal rowLegal bonds directly. Its first-cell "
                + "condition fixes zero, its widthNormal conjunct enforces that every "
                + "2, 3 or 4 has an earlier 1 and every 3 an earlier 2 in row-major order. "
                + "The initial scanner flags are false. At height zero the first-cell "
                + "existential is false, so a 0 = 0.", true),
            Entry("labels", "labels", "Complementary-pair labels", Labels(),
                "The published beta has fibres {0,5}, {1,4}, {2,3}."),
            Entry("compatible", "compatible", "Vertical label compatibility", Compatible(),
                "Every column excludes the same label in the next row."),
            Entry("valid", "Valid", "Reachable boundary condition", Valid(),
                "Colour 1 has occurred; the row is proper; before colour 2 no label is 2."),
            Entry("class", "boundaryClass", "Twenty completed classes and one unseen sector",
                BoundaryClass(),
                "Class 0 precedes colour 2 and has 128 continuations within that sector. "
                + "For a proper boundary, record the five bits indicating whether each "
                + "label differs from the label two positions earlier. Relabelling leaves "
                + "these bits fixed; reversal reverses them. The 32 bit words have 20 "
                + "reversal orbits. Their representatives, in class order, are "
                + "0101010, 0101012, 0101020, 0101021, 0101212, 0101210, 0101202, 0101201, "
                + "0102021, 0102010, 0102012, 0102120, 0102101, 0102102, 0121210, 0120201, "
                + "0121012, 0120102, 0120210, 0120120. "
                + "The class sizes in the same order are "
                + "6,12,12,12,6,12,12,12,12,6,12,12,6,12,6,12,6,12,6,6."),
            Entry("transfer", "transfer", "Exact class transitions", Transfer(),
                "The source class indexes rows and the destination class indexes columns. "
                + "The entries include individual-colour scanner multiplicities."),
            Entry("classcount", "classCount", "Single-row counts", ClassCount(),
                "The sum is over the owner's individual-colour Row type."),
            Entry("firstcount", "firstCount", "Anchored first-row distribution", FirstCount(),
                "The first colour is zero and both initial flags are false."))));

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
            Eq(Call(Root + "bonds", c, d), All("j", Fin(7),
                And(Ne(x, y), Ne(Add(Val(x), Val(y)), D(5)))))));
    }

    private static Formula Count()
    {
        var n = V("n"); var a = V("A");
        var arrays = Arrow(Product(Call("Fin", n), Fin(7)), Fin(6));
        var predicate = Fn("A", arrays, Call(Owner + "widthLegal",
            Name(RowOwner + "rowLegal"), Name(Root + "bonds"), a));
        var universe = Typed(Name("Finset.univ"), Call("Finset", arrays));
        return All("n", Name("Nat"), Eq(Call(Root + "a", n),
            Call("Finset.card", Call("Finset.filter", predicate, universe))));
    }

    private static Formula Seen() => Name(Scanner + "Seen");
    private static Formula PairRow() => Name(BoundaryOwner + "PairRow");
    private static Formula Proj(Formula a, bool first) =>
        Call(first ? "Prod.fst" : "Prod.snd", a);
    private static Formula Flags() => Pair(Name("Bool.false"), Name("Bool.false"));
    private static Formula Labels()
    {
        var c = V("c"); var j = V("j");
        return All("c", Name(RowOwner + "Row"), Eq(Call(Root + "labels", c),
            Fn("j", Fin(7), Call("D5.S3.Observer.Separation.BooleanRankThreeK4.beta", At(c, j)))));
    }

    private static Formula Compatible()
    {
        var p = V("p"); var c = V("c"); var j = V("j");
        return All("p", PairRow(), All("c", Name(RowOwner + "Row"),
            Eq(Call(Root + "compatible", p, c), All("j", Fin(7),
                Ne(At(p, j), Call("D5.S3.Observer.Separation.BooleanRankThreeK4.beta",
                    At(c, j)))))));
    }

    private static Formula Valid()
    {
        var s = V("s"); var p = V("p"); var j = V("j");
        return All("s", Seen(), All("p", PairRow(), Eq(Call(Root + "Valid", s, p),
            And(Eq(Proj(s, true), Name("Bool.true")),
                And(Call(RowOwner + "rowProper", p),
                    Imp(Eq(Proj(s, false), Name("Bool.false")),
                        All("j", Fin(7), Ne(At(p, j), Typed(D(2), Fin(3))))))))));
    }

    private static Formula BoundaryClass()
    {
        var s = V("s"); var p = V("p");
        Formula P(byte j) => At(p, Typed(D(j), Fin(7)));
        Formula K(int j) =>
            Typed(Number(j.ToString(CultureInfo.InvariantCulture)), Fin(21));
        var classes = new[] { 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20 };
        Formula Tree(int depth, int code)
        {
            if (depth == 5)
            {
                var reversed = 0;
                for (var i = 0; i < 5; i++) reversed = 2 * reversed + ((code >> i) & 1);
                var canonical = code < reversed ? code : reversed;
                var codes = new[] { 0,1,2,3,4,5,6,7,9,10,11,13,14,15,17,19,21,23,27,31 };
                return K(classes[Array.IndexOf(codes, canonical)]);
            }
            return Conditional(Eq(P((byte)(depth + 2)), P((byte)depth)),
                Tree(depth + 1, 2 * code), Tree(depth + 1, 2 * code + 1));
        }
        return All("s", Seen(), All("p", PairRow(),
            Eq(Call(Root + "boundaryClass", s, p), Conditional(Proj(s, false),
                Tree(0, 0), K(0)))));
    }

    private static Formula Transfer()
    {
        var table = Vector(
            Vector(Number("128"), Number("128"), Number("256"), Number("256"), Number("128"),
                Number("128"), Number("256"), Number("128"), Number("0"), Number("128"),
                Number("128"), Number("128"), Number("128"), Number("0"), Number("0"),
                Number("128"), Number("0"), Number("128"), Number("0"), Number("64"),
                Number("0")),
            Vector(Number("0"), Number("384"), Number("512"), Number("512"), Number("256"),
                Number("256"), Number("512"), Number("256"), Number("0"), Number("256"),
                Number("256"), Number("256"), Number("256"), Number("0"), Number("0"),
                Number("256"), Number("0"), Number("256"), Number("0"), Number("128"),
                Number("0")),
            Vector(Number("0"), Number("256"), Number("384"), Number("512"), Number("256"),
                Number("128"), Number("256"), Number("128"), Number("128"), Number("256"),
                Number("256"), Number("256"), Number("256"), Number("0"), Number("0"),
                Number("128"), Number("256"), Number("128"), Number("128"), Number("0"),
                Number("0")),
            Vector(Number("0"), Number("256"), Number("512"), Number("384"), Number("128"),
                Number("256"), Number("512"), Number("256"), Number("0"), Number("256"),
                Number("128"), Number("256"), Number("256"), Number("128"), Number("0"),
                Number("256"), Number("0"), Number("256"), Number("0"), Number("128"),
                Number("0")),
            Vector(Number("0"), Number("128"), Number("256"), Number("128"), Number("256"),
                Number("128"), Number("256"), Number("256"), Number("128"), Number("256"),
                Number("0"), Number("128"), Number("128"), Number("128"), Number("128"),
                Number("128"), Number("128"), Number("128"), Number("128"), Number("128"),
                Number("0")),
            Vector(Number("0"), Number("256"), Number("256"), Number("512"), Number("256"),
                Number("256"), Number("256"), Number("256"), Number("256"), Number("256"),
                Number("256"), Number("256"), Number("256"), Number("0"), Number("0"),
                Number("0"), Number("256"), Number("0"), Number("256"), Number("0"),
                Number("0")),
            Vector(Number("0"), Number("256"), Number("256"), Number("512"), Number("256"),
                Number("128"), Number("384"), Number("128"), Number("0"), Number("256"),
                Number("256"), Number("256"), Number("256"), Number("0"), Number("0"),
                Number("128"), Number("0"), Number("128"), Number("128"), Number("128"),
                Number("0")),
            Vector(Number("0"), Number("128"), Number("128"), Number("256"), Number("256"),
                Number("128"), Number("128"), Number("384"), Number("256"), Number("256"),
                Number("128"), Number("128"), Number("256"), Number("128"), Number("128"),
                Number("0"), Number("256"), Number("0"), Number("256"), Number("0"),
                Number("0")),
            Vector(Number("0"), Number("0"), Number("128"), Number("0"), Number("128"),
                Number("128"), Number("0"), Number("256"), Number("384"), Number("128"),
                Number("0"), Number("128"), Number("0"), Number("128"), Number("256"),
                Number("0"), Number("256"), Number("0"), Number("128"), Number("0"),
                Number("128")),
            Vector(Number("0"), Number("128"), Number("256"), Number("256"), Number("256"),
                Number("128"), Number("256"), Number("256"), Number("128"), Number("384"),
                Number("128"), Number("128"), Number("128"), Number("128"), Number("128"),
                Number("128"), Number("256"), Number("128"), Number("128"), Number("0"),
                Number("0")),
            Vector(Number("0"), Number("256"), Number("512"), Number("256"), Number("0"),
                Number("256"), Number("512"), Number("256"), Number("0"), Number("256"),
                Number("256"), Number("256"), Number("256"), Number("0"), Number("0"),
                Number("256"), Number("0"), Number("256"), Number("0"), Number("128"),
                Number("0")),
            Vector(Number("0"), Number("128"), Number("256"), Number("256"), Number("128"),
                Number("128"), Number("256"), Number("128"), Number("128"), Number("128"),
                Number("128"), Number("256"), Number("256"), Number("0"), Number("0"),
                Number("128"), Number("128"), Number("128"), Number("128"), Number("128"),
                Number("0")),
            Vector(Number("0"), Number("128"), Number("256"), Number("256"), Number("128"),
                Number("128"), Number("256"), Number("256"), Number("0"), Number("128"),
                Number("128"), Number("256"), Number("384"), Number("128"), Number("0"),
                Number("128"), Number("0"), Number("128"), Number("128"), Number("128"),
                Number("0")),
            Vector(Number("0"), Number("0"), Number("0"), Number("256"), Number("256"),
                Number("0"), Number("0"), Number("256"), Number("256"), Number("256"),
                Number("0"), Number("0"), Number("256"), Number("256"), Number("256"),
                Number("0"), Number("256"), Number("0"), Number("256"), Number("0"),
                Number("0")),
            Vector(Number("0"), Number("0"), Number("0"), Number("0"), Number("128"),
                Number("0"), Number("0"), Number("128"), Number("256"), Number("128"),
                Number("0"), Number("0"), Number("0"), Number("128"), Number("384"), Number("0"),
                Number("256"), Number("0"), Number("128"), Number("0"), Number("128")),
            Vector(Number("0"), Number("256"), Number("256"), Number("512"), Number("256"),
                Number("0"), Number("256"), Number("0"), Number("0"), Number("256"),
                Number("256"), Number("256"), Number("256"), Number("0"), Number("0"),
                Number("256"), Number("0"), Number("0"), Number("256"), Number("128"),
                Number("0")),
            Vector(Number("0"), Number("0"), Number("256"), Number("0"), Number("128"),
                Number("128"), Number("0"), Number("256"), Number("256"), Number("256"),
                Number("0"), Number("128"), Number("0"), Number("128"), Number("256"),
                Number("0"), Number("384"), Number("128"), Number("0"), Number("0"),
                Number("128")),
            Vector(Number("0"), Number("256"), Number("256"), Number("512"), Number("256"),
                Number("0"), Number("256"), Number("0"), Number("0"), Number("256"),
                Number("256"), Number("256"), Number("256"), Number("0"), Number("0"),
                Number("0"), Number("256"), Number("256"), Number("0"), Number("0"),
                Number("0")),
            Vector(Number("0"), Number("0"), Number("128"), Number("0"), Number("128"),
                Number("128"), Number("128"), Number("256"), Number("128"), Number("128"),
                Number("0"), Number("128"), Number("128"), Number("128"), Number("128"),
                Number("128"), Number("0"), Number("0"), Number("256"), Number("128"),
                Number("0")),
            Vector(Number("0"), Number("128"), Number("0"), Number("256"), Number("256"),
                Number("0"), Number("256"), Number("0"), Number("0"), Number("0"), Number("128"),
                Number("256"), Number("256"), Number("0"), Number("0"), Number("128"),
                Number("0"), Number("0"), Number("256"), Number("256"), Number("0")),
            Vector(Number("0"), Number("0"), Number("0"), Number("0"), Number("0"), Number("0"),
                Number("0"), Number("0"), Number("256"), Number("0"), Number("0"), Number("0"),
                Number("0"), Number("0"), Number("256"), Number("0"), Number("256"), Number("0"),
                Number("0"), Number("0"), Number("256")));
        return All("i", Fin(21), All("k", Fin(21),
            Eq(Call(Root + "transfer", V("i"), V("k")), At(table, V("i"), V("k")))));
    }

    private static Formula ClassCount()
    {
        var s = V("s"); var p = V("p"); var k = V("k"); var c = V("c");
        var condition = And(Call(RowOwner + "rowLegal", c),
            And(Call(Root + "compatible", p, c), And(Call(Scanner + "good", s, c),
                Eq(Call(Root + "boundaryClass", Call(Scanner + "finish", s, c),
                    Call(Root + "labels", c)), k))));
        return All("s", Seen(), All("p", PairRow(), All("k", Fin(21),
            Eq(Call(Root + "classCount", s, p, k), SumOver("c", Name(RowOwner + "Row"),
                Typed(Conditional(condition, D(1), D(0)), Name("Int")))))));
    }

    private static Formula FirstCount()
    {
        var k = V("k"); var c = V("c");
        var condition = And(Eq(At(c, Typed(D(0), Fin(7))), Typed(D(0), Fin(6))),
            And(Call(RowOwner + "rowLegal", c), And(Call(Scanner + "good", Flags(), c),
                Eq(Call(Root + "boundaryClass", Call(Scanner + "finish", Flags(), c),
                    Call(Root + "labels", c)), k))));
        return All("k", Fin(21), Eq(Call(Root + "firstCount", k),
            SumOver("c", Name(RowOwner + "Row"),
                Typed(Conditional(condition, D(1), D(0)), Name("Int")))));
    }

    private static Formula Number(string n) => D(n.Select(c => (byte)(c - '0')).ToArray());
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
    private static Formula Fin(byte k) =>
        Call("Fin", Number(((int)k).ToString(CultureInfo.InvariantCulture)));
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
    private static Formula All(string n, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(n), type), Comma, Sp, Parenthesized(body));
    private static Formula Fn(string n, Formula type, Formula body) =>
        Parenthesized(Seq(Typed(V(n), type), Sp, Mapsto, Sp, Parenthesized(body)));
}
