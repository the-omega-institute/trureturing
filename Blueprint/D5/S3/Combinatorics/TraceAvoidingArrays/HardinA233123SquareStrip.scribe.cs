using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233123SquareStripDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233123SquareStrip.";
    private const string Root =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233123SquareStrip.";
    private const string Scanner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.";
    private const string Transfer =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.";
    private const string PairMap = "D5.S3.Observer.Separation.BooleanRankThreeK4.beta";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2013a233123");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Barker's generating function for normalized six-colour two-column square strips.",
        H("A two-class transfer for complementary-pair exclusion"),
        Blocks(
            Paragraph(Text(
                "OEIS A233123, revision 7, counts n by 2 arrays over Fin 6. Horizontal and "
                + "vertical neighbours are unequal and do not sum to five. Diagonal neighbours "
                + "are unconstrained. The upper-left colour is zero. In row-major order every "
                + "2, 3 or 4 has an earlier 1, and every 3 has an earlier 2. The coefficient "
                + "at index zero is zero. All declaration names below retain their full Lean "
                + "namespaces. Fin.val maps a finite index or colour to its natural value. "
                + "Typed numerals specify their Fin domains. Nat.div is natural quotient "
                + "division and Nat.mod is the nonnegative remainder; neither enters these "
                + "definitions. HardinA233175PairStrip.Col is literally Fin 2 to Fin 6. "
                + "All sums range over the displayed finite type.")),
            Def("rowlegal", "rowLegal", "The horizontal bond", RowLegalFormula(),
                "There is exactly one horizontal bond in a two-column row."),
            Def("decidable-rowlegal", "instDecidableRowLegal", "Deciding the horizontal bond", DecidableRowLegalFormula(),
                "The defining expression is inferInstanceAs for the displayed conjunction."),
            Def("bonds", "bonds", "The two vertical bonds", BondsFormula(),
                "The same column index is used in both consecutive rows."),
            Def("count", "a", "The literal filtered count", CountFormula(),
                "Every function from Fin n times Fin 2 to Fin 6 occurs in Finset.univ. "
                + "Filtering by the owner widthLegal predicate, specialized to rowLegal and bonds, and taking its cardinality is the sequence definition. The shared widthNormal definition says that, at cell (i,j), each required predecessor is at (r,t) with r<i or r=i and t<j; the initial seen flags are both false. "
                + "Thus a 0 = 0 by the first-cell condition.", true),
            Def("compatible", "compatible", "Boundary compatibility", CompatibleFormula(),
                "BooleanRankThreeK4.beta has fibres {0,5}, {1,4}, {2,3}. Its value for each "
                + "preceding colour must differ from the next colour's value in that column. "
                + "HardinA233175PairStrip.pairs c is literally (beta (c 0), beta (c 1))."),
            Def("classcount", "classCount", "One-row class counts", ClassCountFormula(),
                "HardinA233251TriangleStrip.Valid s p says that 1 has been seen, the "
                + "boundary labels differ, and before 2 is seen neither label is 2. "
                + "Seen is Bool times Bool, tracking occurrences of colours 1 and 2. "
                + "The shared good predicate checks the row in column order using allowed "
                + "and advance. The shared finish function returns its final seen flags."),
            Def("firstcount", "firstCount", "First-row class counts", FirstCountFormula(),
                "The first colour is zero and both initial seen flags are false."),
            Thm("certificate", "finite_certificate", "The finite transfer certificate",
                CertificateFormula(),
                "From a boundary with 2 unseen, four rows keep 2 unseen and four see it. "
                + "From a boundary with 2 seen, twelve rows keep it seen and none forget it. "
                + "The unique first row is (0,1); it leaves 2 unseen. These are counts of "
                + "single rows, each drawn from the 36 functions Fin 2 to Fin 6."),
            Resolution("result", "result", "Barker's generating-function identity",
                ResultFormula(),
                "Let U(k) count continuations after 2 has been seen, and V(k) those before "
                + "2 has been seen, under the invariant Valid. The finite certificate gives "
                + "U(0)=V(0)=1, U(k+1)=12U(k), and V(k+1)=4V(k)+4U(k). The width-generic "
                + "width_counting_bridge of HardinA233251TriangleStrip applies with the "
                + "vertical relation bonds and boundary map HardinA233175PairStrip.pairs. "
                + "It identifies the literal count a(k+1) with V(k). Hence "
                + "a(n+3)=16a(n+2)-48a(n+1), with a(1)=1 and a(2)=8. Comparing every "
                + "coefficient gives the identity in PowerSeries Int, including index zero. "
                + "The first values are 1, 8, 80, 896, 10496 and 124928. The statement "
                + "concerns formal power series and does not assume analytic convergence."))));

    private static DocumentBlock Def(string id, string name, string title, Formula formula,
        string prose, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source)
                : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Thm(string id, string name, string title, Formula formula,
        string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static DocumentBlock Resolution(string id, string name, string title,
        Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem,
            new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin233123"),
                ResolutionKind.Proved));

    private static Formula DecidableRowLegalFormula()
    {
        var c = V("c");
        var x = App(c, Index(0)); var y = App(c, Index(1));
        return All("c", Col(), Eq(
            Typed(Self("instDecidableRowLegal", c), Call("Decidable", Parenthesized(Self("rowLegal", c)))),
            Call("inferInstanceAs", Parenthesized(Call("Decidable",
                Parenthesized(And(Ne(x, y), Ne(Add(Val(x), Val(y)), D(5)))))))));
    }

    private static Formula RowLegalFormula()
    {
        var c = V("c");
        var x = App(c, Index(0)); var y = App(c, Index(1));
        return All("c", Col(), Eq(Self("rowLegal", c),
            And(Ne(x, y), Ne(Add(Val(x), Val(y)), D(5)))));
    }

    private static Formula BondsFormula()
    {
        var c = V("c"); var d = V("d"); var j = V("j");
        var x = App(c, j); var y = App(d, j);
        return All("c", Col(), All("d", Col(), Eq(Self("bonds", c, d),
            All("j", Fin(2), And(Ne(x, y), Ne(Add(Val(x), Val(y)), D(5)))))));
    }

    private static Formula CountFormula()
    {
        var n = V("n");
        var predicate = Fn("A", ArrayType(n),
            Call(Transfer + "widthLegal", Qualified(Root + "rowLegal"),
                Qualified(Root + "bonds"), V("A")));
        var univ = Typed(Qualified("Finset.univ"), Call("Finset", ArrayType(n)));
        return All("n", Nat(), Eq(Self("a", n),
            Call("Finset.card", Call("Finset.filter", predicate, univ))));
    }

    private static Formula CompatibleFormula()
    {
        var p = V("p"); var c = V("c");
        return All("p", Boundary(), All("c", Col(), Eq(Self("compatible", p, c),
            And(Ne(Proj(p, 1), Call(PairMap, App(c, Index(0)))),
                Ne(Proj(p, 2), Call(PairMap, App(c, Index(1))))))));
    }

    private static Formula ClassCountFormula()
    {
        var s = V("s"); var p = V("p"); var b = V("b"); var c = V("c");
        var condition = And(Self("rowLegal", c), And(Self("compatible", p, c),
            And(Call(Scanner + "good", s, c),
                Eq(Proj(Call(Scanner + "finish", s, c), 2), b))));
        return All("s", Seen(), All("p", Boundary(), All("b", Qualified("Bool"),
            Eq(Self("classCount", s, p, b),
                SumOver("c", Col(), Conditional(condition, Int(1), Int(0)))))));
    }

    private static Formula FirstCountFormula()
    {
        var b = V("b"); var c = V("c");
        var condition = And(Eq(App(c, Index(0)), Colour(0)), And(Self("rowLegal", c),
            And(Call(Scanner + "good", Flags(), c),
                Eq(Proj(Call(Scanner + "finish", Flags(), c), 2), b))));
        return All("b", Qualified("Bool"), Eq(Self("firstCount", b),
            SumOver("c", Col(), Conditional(condition, Int(1), Int(0)))));
    }

    private static Formula CertificateFormula()
    {
        var s = V("s"); var p = V("p");
        var rows = All("s", Seen(), All("p", Boundary(), Imp(Call(Transfer + "Valid", s, p),
            And(Eq(Self("classCount", s, p, Bool(true)),
                    Conditional(Proj(s, 2), Int(1, 2), Int(4))),
                Eq(Self("classCount", s, p, Bool(false)),
                    Conditional(Proj(s, 2), Int(0), Int(4)))))));
        return And(rows, And(Eq(Self("firstCount", Bool(true)), Int(0)),
            Eq(Self("firstCount", Bool(false)), Int(1))));
    }

    private static Formula ResultFormula()
    {
        var x = Qualified("PowerSeries.X");
        var series = Call("PowerSeries.mk", Fn("n", Nat(),
            Typed(Self("a", V("n")), Qualified("Int"))));
        return Eq(Typed(Mul(Mul(Sub(D(1), Mul(D(4), x)),
            Sub(D(1), Mul(D(1, 2), x))), series), Call("PowerSeries", Qualified("Int"))),
            Mul(x, Sub(D(1), Mul(D(8), x))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Qualified(string name) => Seq(name.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { Seq(Operatorname, Grp(V(part))) }
            : new[] { Dot, Seq(Operatorname, Grp(V(part))) }).ToArray());
    private static Formula App(Formula f, params Formula[] args) =>
        new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) =>
        App(Qualified(name), args);
    private static Formula Self(string name, params Formula[] args) => Call(Root + name, args);
    private static Formula Nat() => Qualified("Nat");
    private static Formula Fin(byte n) => Call("Fin", D(n));
    private static Formula Col() => Qualified(Scanner + "Col");
    private static Formula Seen() => Qualified(Scanner + "Seen");
    private static Formula Boundary() => Product(Fin(3), Fin(3));
    private static Formula ArrayType(Formula n) => Arrow(Product(Call("Fin", n), Fin(2)), Fin(6));
    private static Formula Bool(bool value) => Qualified(value ? "Bool.true" : "Bool.false");
    private static Formula Flags() => Pair(Bool(false), Bool(false));
    private static Formula Index(byte n) => Typed(D(n), Fin(2));
    private static Formula Colour(byte n) => Typed(D(n), Fin(6));
    private static Formula Int(params byte[] digits) => Typed(D(digits), Qualified("Int"));
    private static Formula Val(Formula f) => Call("Fin.val", f);
    private static Formula Proj(Formula f, byte i) => Call(i == 1 ? "Prod.fst" : "Prod.snd", f);
    private static Formula Typed(Formula f, Formula type) =>
        Parenthesized(Seq(f, Colon, Sp, type));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Product(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Arrow(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, To, Sp, b);
    private static Formula Fn(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, V(name), Colon, Sp, type, Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(V(name), Colon, Sp, type), Sp, Parenthesized(body));
    private static Formula Eq(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, F.Eq, Sp, Parenthesized(b));
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula And(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Conditional(Formula condition, Formula yes, Formula no) =>
        Parenthesized(Seq(Qualified("if"), Sp, Parenthesized(condition), Sp,
            Qualified("then"), Sp, yes, Sp, Qualified("else"), Sp, no));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
}
