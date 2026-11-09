using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233196StripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.";
    private const string Root = "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233196Strip.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2013a233196");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Barker's generating function for normalized eight-colour two-column arrays.",
        H("Eight-colour complementary-pair exclusion"),
        Blocks(
            Paragraph(Text(
                "OEIS A233196, revision 12, counts arrays on n rows and two columns. "
                + "Horizontal, vertical and antidiagonal bonds exclude equal colours and "
                + "colours summing to seven. Main-diagonal neighbours are unconstrained. "
                + "The first colour is zero. The three flags record previous occurrences "
                + "of colours one, two and three, respectively. All Fin indices are "
                + "zero-based; Fin.val is their natural value. Nat.sub is truncated "
                + "subtraction, Nat.div is natural quotient division, and Nat.mod is its "
                + "nonnegative remainder. Fin.ofNat 4 t has value Nat.mod t 4. "
                + "No division enters the count or the power-series identity.")),
            Def("seen", "Seen", "Three scanning flags",
                Eq(Name("Seen"), Product(Q("Bool"), Product(Q("Bool"), Q("Bool")))),
                "The right-associated product records colours one, two and three."),
            Def("allowed", "allowed", "The literal precedence restrictions", AllowedFormula(),
                "A colour from 2,3,4,5,6 requires flag one. A colour from 3,4,5 requires "
                + "flag two. Colour four requires flag three."),
            Def("advance", "advance", "Advancing the scanner", AdvanceFormula(),
                "The current colour can set its corresponding flag; flags never reset."),
            Def("good", "good", "Scanning a finite row", GoodFormula(),
                "The empty row satisfies the condition. A nonempty row checks its first "
                + "colour before advancing the flags and scanning Fin.tail."),
            Def("finish", "finish", "Flags at the end of a row", FinishFormula(),
                "The terminal flags include every occurrence in the scanned row."),
            Def("beta", "beta", "The complementary-pair map", BetaFormula(),
                "The fibres are {0,7}, {1,6}, {2,5}, {3,4}. The minimum lies below four, "
                + "so the Fin.ofNat remainder preserves it."),
            Def("widthrow", "WidthRow", "Rows of arbitrary width",
                All("k", NatType(), Eq(Call("WidthRow", V("k")),
                    Arrow(Fin(V("k")), Fin(D(8))))),
                "The scanner is independent of the strip width."),
            Def("prior", "prior", "An earlier row-major occurrence", PriorFormula(),
                "Strict lexicographic order first compares rows, then columns. This is "
                + "equivalent to the order of i.val*k+j.val for indices in Fin n times Fin k."),
            Def("normal", "widthNormal", "Literal normalization at arbitrary width",
                NormalFormula(),
                "The initial flags represent occurrences before the displayed array. "
                + "Within the array, prior supplies the required earlier colour."),
            Def("row", "Row", "Two-column rows",
                Eq(Name("Row"), Arrow(Fin(D(2)), Fin(D(8)))),
                "Each row is an ordered pair of colours."),
            Def("rowlegal", "rowLegal", "Horizontal exclusion", RowLegalFormula(),
                "The endpoints in columns zero and one must differ and not sum to seven."),
            Def("bonds", "bonds", "Vertical and antidiagonal exclusion", BondsFormula(),
                "Both vertical bonds and the bond from column one to the next column "
                + "zero are constrained. The other diagonal is absent."),
            Def("legal", "Legal", "The literal array predicate", LegalFormula(),
                "The first-cell existential is false when n is zero. Every positive n "
                + "fixes the unique row-zero, column-zero cell to colour zero."),
            Def("count", "a", "The literal filtered Finset count", CountFormula(),
                "Every function Fin n times Fin 2 to Fin 8 is filtered by Legal. "
                + "The convention is a(0)=0, because the first-cell existential fails.", true),
            Def("pairs", "pairs", "Boundary pair labels", PairsFormula(),
                "The boundary retains the complementary-pair label of both columns."),
            Def("compatible", "compatible", "Boundary compatibility", CompatibleFormula(),
                "These three pair-label inequalities express the two vertical and one "
                + "antidiagonal exclusion constraints."),
            Def("valid", "Valid", "Reachable boundary states", ValidFormula(),
                "After the first row, colour one has occurred. Before colour two occurs "
                + "the labels are below two; before colour three occurs they are below "
                + "three. A third flag implies the second flag."),
            Def("class", "seenClass", "The three continuation classes", ClassFormula(),
                "Class zero has only colour one seen; class one has colour two seen "
                + "but not three; class two has colour three seen."),
            Def("matrix", "T", "The class transfer matrix",
                Eq(Name("T"), Vector(Vector(Z(0), Z(2), Z(1)),
                    Vector(Z(0), Z(4), Z(6)), Vector(Z(0), Z(0), Z(16)))),
                "Rows and columns are indexed by Fin 3 in increasing order. The vector "
                + "notation is expanded as Matrix.vecCons and Matrix.vecEmpty."),
            Def("classcount", "classCount", "One-row class counts", ClassCountFormula(),
                "The integer sum ranges over all two-column rows and records the final class."),
            Def("firstcount", "firstCount", "First-row class counts", FirstCountFormula(),
                "Only (0,1) is admissible as the first row, and it enters class zero."),
            Thm("certificate", "finite_certificate", "The finite class certificate",
                CertificateFormula(),
                "From class zero the counts are (0,2,1); from class one they are (0,4,6); "
                + "from class two they are (0,0,16). The initial vector is (1,0,0). "
                + "The last identity annihilates the transient zero eigenvalue and gives "
                + "the quadratic recurrence on every later continuation."),
            Resolution("result", "result", "Barker's generating function", ResultFormula(),
                "Let w(n) be Matrix.mulVec (T^n) 1. Splitting a literal array into its "
                + "first row and remaining rows gives a(n+1)=w(n)(0). The finite "
                + "certificate and TransferMatrix.scalarRelationShift give "
                + "a(n+4)=20*a(n+3)-64*a(n+2) for every natural n. The first three "
                + "positive counts are 1,3,36. Comparing coefficients, including "
                + "a(0)=0, proves the identity in PowerSeries Int. The counts are "
                + "cast from Nat to Int before forming the series."))));

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
            new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin233196"),
                ResolutionKind.Proved));

    private static Formula AllowedFormula()
    {
        var s = V("s"); var c = V("c");
        return All("s", Name("Seen"), All("c", Fin(D(8)),
            Eq(Call("allowed", s, c), And(
                Imp(Colours(c, 2, 3, 4, 5, 6), Eq(First(s), Q("true"))),
                And(Imp(Colours(c, 3, 4, 5), Eq(Second(s), Q("true"))),
                    Imp(Eq(c, Colour(4)), Eq(Third(s), Q("true"))))))));
    }
    private static Formula AdvanceFormula()
    {
        var s = V("s"); var c = V("c");
        Formula Flag(Formula previous, byte d) =>
            At(Q("Bool.or"), previous, At(Q("decide"), Eq(c, Colour(d))));
        return All("s", Name("Seen"), All("c", Fin(D(8)),
            Eq(Call("advance", s, c), Triple(Flag(First(s), 1),
                Flag(Second(s), 2), Flag(Third(s), 3)))));
    }
    private static Formula GoodFormula()
    {
        var s = V("s"); var f = V("f");
        var first = At(f, Typed(D(0), Fin(Add(V("n"), D(1)))));
        return And(All("s", Name("Seen"), All("f", Arrow(Fin(D(0)), Fin(D(8))),
            Eq(Call("good", s, f), Q("True")))),
            All("n", NatType(), All("s", Name("Seen"),
                All("f", Arrow(Fin(Add(V("n"), D(1))), Fin(D(8))),
                    Eq(Call("good", s, f), And(Call("allowed", s, first),
                        Call("good", Call("advance", s, first), At(Q("Fin.tail"), f))))))));
    }
    private static Formula FinishFormula()
    {
        var s = V("s"); var f = V("f");
        var first = At(f, Typed(D(0), Fin(Add(V("n"), D(1)))));
        return And(All("s", Name("Seen"), All("f", Arrow(Fin(D(0)), Fin(D(8))),
            Eq(Call("finish", s, f), s))),
            All("n", NatType(), All("s", Name("Seen"),
                All("f", Arrow(Fin(Add(V("n"), D(1))), Fin(D(8))),
                    Eq(Call("finish", s, f),
                        Call("finish", Call("advance", s, first), At(Q("Fin.tail"), f)))))));
    }
    private static Formula BetaFormula()
    {
        var c = V("c");
        return All("c", Fin(D(8)), Eq(Call("beta", c),
            At(Q("Fin.ofNat"), D(4), At(Q("Nat.min"), Val(c), Sub(D(7), Val(c))))));
    }
    private static Formula PriorFormula()
    {
        var i = V("i"); var j = V("j"); var r = V("r"); var t = V("t");
        return NormalParameters(All("i", Fin(V("n")), All("j", Fin(V("k")),
            All("d", Fin(D(8)), Eq(Call("prior", V("f"), i, j, V("d")),
                Ex("r", Fin(V("n")), Ex("t", Fin(V("k")),
                    And(Or(Lt(r, i), And(Eq(r, i), Lt(t, j))),
                        Eq(At(At(V("f"), r), t), V("d"))))))))));
    }
    private static Formula NormalFormula()
    {
        var s = V("s"); var i = V("i"); var j = V("j");
        var c = At(At(V("f"), i), j);
        Formula Earlier(byte d) => Call("prior", V("f"), i, j, Colour(d));
        return NormalParameters(All("s", Name("Seen"),
            Eq(Call("widthNormal", s, V("f")), All("i", Fin(V("n")),
                All("j", Fin(V("k")), And(
                    Imp(Colours(c, 2, 3, 4, 5, 6),
                        Or(Eq(First(s), Q("true")), Earlier(1))),
                    And(Imp(Colours(c, 3, 4, 5),
                        Or(Eq(Second(s), Q("true")), Earlier(2))),
                        Imp(Eq(c, Colour(4)),
                            Or(Eq(Third(s), Q("true")), Earlier(3))))))))));
    }
    private static Formula NormalParameters(Formula body)
    {
        return All("k", NatType(), All("n", NatType(),
            All("f", Arrow(Fin(V("n")), Call("WidthRow", V("k"))), body)));
    }
    private static Formula RowLegalFormula()
    {
        var c = V("c");
        var x = At(c, Index(0)); var y = At(c, Index(1));
        return All("c", Name("Row"), Eq(Call("rowLegal", c),
            And(Ne(x, y), Ne(Add(Val(x), Val(y)), D(7)))));
    }
    private static Formula BondsFormula()
    {
        var c = V("c"); var d = V("d"); var j = V("j");
        var x = At(c, j); var y = At(d, j);
        var right = At(c, Index(1)); var left = At(d, Index(0));
        return All("c", Name("Row"), All("d", Name("Row"), Eq(Call("bonds", c, d),
            And(All("j", Fin(D(2)), And(Ne(x, y), Ne(Add(Val(x), Val(y)), D(7)))),
                And(Ne(right, left), Ne(Add(Val(right), Val(left)), D(7)))))));
    }
    private static Formula LegalFormula()
    {
        var n = V("n"); var a = V("A"); var i = V("i"); var j = V("j");
        var cells = Product(Fin(n), Fin(D(2)));
        Formula Row(Formula r) => Fn("j", Fin(D(2)), At(a, Pair(r, j)));
        var first = Ex("i", Fin(n), And(Eq(Val(i), D(0)),
            Eq(At(a, Pair(i, Index(0))), Colour(0))));
        var rows = All("i", Fin(n), Call("rowLegal", Row(i)));
        var next = Typed(At(Q("Fin.mk"), Add(Val(i), D(1)), V("h")), Fin(n));
        var edges = All("i", Fin(n), All("h", Lt(Add(Val(i), D(1)), n),
            Call("bonds", Row(i), Row(next))));
        var norm = Call("widthNormal", Initial(), Fn("i", Fin(n), Row(i)));
        return All("n", NatType(), All("A", Arrow(cells, Fin(D(8))),
            Eq(Call("Legal", a), And(first, And(rows, And(edges, norm))))));
    }
    private static Formula CountFormula()
    {
        var n = V("n"); var arrays = Arrow(Product(Fin(n), Fin(D(2))), Fin(D(8)));
        return All("n", NatType(), Eq(Call("a", n), At(Q("Finset.card"),
            At(Q("Finset.filter"), Fn("A", arrays, Call("Legal", V("A"))),
                Typed(Q("Finset.univ"), At(Q("Finset"), arrays))))));
    }
    private static Formula PairsFormula()
    {
        var c = V("c");
        return All("c", Name("Row"), Eq(Call("pairs", c),
            Pair(Call("beta", At(c, Index(0))), Call("beta", At(c, Index(1))))));
    }
    private static Formula CompatibleFormula()
    {
        var p = V("p"); var c = V("c");
        return All("p", Product(Fin(D(4)), Fin(D(4))), All("c", Name("Row"),
            Eq(Call("compatible", p, c), And(Ne(First(p), Call("beta", At(c, Index(0)))),
                And(Ne(At(Q("Prod.snd"), p), Call("beta", At(c, Index(1)))),
                    Ne(At(Q("Prod.snd"), p), Call("beta", At(c, Index(0)))))))));
    }
    private static Formula ValidFormula()
    {
        var s = V("s"); var p = V("p");
        var x = First(p); var y = At(Q("Prod.snd"), p);
        Formula Below(byte d) => And(Lt(Val(x), D(d)), Lt(Val(y), D(d)));
        return All("s", Name("Seen"), All("p", Product(Fin(D(4)), Fin(D(4))),
            Eq(Call("Valid", s, p), And(Eq(First(s), Q("true")), And(Ne(x, y),
                And(Imp(Eq(Second(s), Q("false")), Below(2)),
                    And(Imp(Eq(Third(s), Q("false")), Below(3)),
                        Imp(Eq(Third(s), Q("true")), Eq(Second(s), Q("true"))))))))));
    }
    private static Formula ClassFormula()
    {
        var s = V("s");
        return All("s", Name("Seen"), Eq(Call("seenClass", s),
            Conditional(Third(s), Typed(D(2), Fin(D(3))),
                Conditional(Second(s), Typed(D(1), Fin(D(3))), Typed(D(0), Fin(D(3)))))));
    }
    private static Formula ClassCountFormula()
    {
        var s = V("s"); var p = V("p"); var b = V("b"); var c = V("c");
        var condition = And(Call("rowLegal", c), And(Call("compatible", p, c),
            And(Call("good", s, c), Eq(Call("seenClass", Call("finish", s, c)), b))));
        return All("s", Name("Seen"), All("p", Product(Fin(D(4)), Fin(D(4))),
            All("b", Fin(D(3)), Eq(Call("classCount", s, p, b),
                SumOver("c", Name("Row"), Conditional(condition, Z(1), Z(0)))))));
    }
    private static Formula FirstCountFormula()
    {
        var b = V("b"); var c = V("c");
        var condition = And(Eq(At(c, Index(0)), Colour(0)), And(Call("rowLegal", c),
            And(Call("good", Initial(), c),
                Eq(Call("seenClass", Call("finish", Initial(), c)), b))));
        return All("b", Fin(D(3)), Eq(Call("firstCount", b),
            SumOver("c", Name("Row"), Conditional(condition, Z(1), Z(0)))));
    }
    private static Formula CertificateFormula()
    {
        var s = V("s"); var p = V("p"); var b = V("b"); var j = V("j");
        Formula W(Formula n) => At(Q("Matrix.mulVec"), Power(Name("T"), n),
            Typed(D(1), Arrow(Fin(D(3)), Q("Int"))));
        var counts = All("s", Name("Seen"), All("p", Product(Fin(D(4)), Fin(D(4))),
            Imp(Call("Valid", s, p), All("b", Fin(D(3)),
                Eq(Call("classCount", s, p, b), At(Name("T"), Call("seenClass", s), b))))));
        var first = All("b", Fin(D(3)), Eq(Call("firstCount", b),
            Conditional(Eq(b, Typed(D(0), Fin(D(3)))), Z(1), Z(0))));
        var vector = Eq(W(Add(D(1), D(2))), SumOver("j", Fin(D(2)),
            At(Q("HSMul.hSMul"), At(Vector(new Formula.Negate(Z(64)), Z(20)), j),
                W(Add(D(1), Val(j))))));
        return And(counts, And(first, vector));
    }
    private static Formula ResultFormula()
    {
        var x = Typed(Q("PowerSeries.X"), At(Q("PowerSeries"), Q("Int")));
        var series = At(Q("PowerSeries.mk"), Fn("n", NatType(),
            Typed(At(Q("Nat.cast"), Call("a", V("n"))), Q("Int"))));
        var left = Mul(Mul(Sub(D(1), Mul(D(4), x)),
            Sub(D(1), Mul(new Formula.Number(16), x))), series);
        var right = Mul(x, Add(Sub(D(1), Mul(new Formula.Number(17), x)),
            Mul(new Formula.Number(40), Power(x, D(2)))));
        return Eq(left, right);
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { Seq(Operatorname, Grp(V(part))) }
            : new[] { Dot, Seq(Operatorname, Grp(V(part))) }).ToArray());
    private static Formula Name(string name) => Q(Root + name);
    private static Formula Call(string name, params Formula[] args) => At(Name(name), args);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula NatType() => Q("Nat");
    private static Formula Fin(Formula n) => At(Q("Fin"), n);
    private static Formula Typed(Formula f, Formula type) =>
        Parenthesized(Seq(f, Colon, Sp, type));
    private static Formula Colour(byte d) => Typed(D(d), Fin(D(8)));
    private static Formula Index(byte d) => Typed(D(d), Fin(D(2)));
    private static Formula Z(long n) => Typed(new Formula.Number(n), Q("Int"));
    private static Formula First(Formula s) => At(Q("Prod.fst"), s);
    private static Formula Second(Formula s) => First(At(Q("Prod.snd"), s));
    private static Formula Third(Formula s) => At(Q("Prod.snd"), At(Q("Prod.snd"), s));
    private static Formula Val(Formula f) => At(Q("Fin.val"), f);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Product(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Pair(Formula a, Formula b) =>
        Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Triple(Formula a, Formula b, Formula c) => Pair(a, Pair(b, c));
    private static Formula Initial() => Triple(Q("false"), Q("false"), Q("false"));
    private static Formula Vector(params Formula[] entries) => entries.Reverse().Aggregate(
        Q("Matrix.vecEmpty"), (tail, head) => At(Q("Matrix.vecCons"), head, tail));
    private static Formula Colours(Formula c, params byte[] ds) => ds.Reverse().Select(
        d => Eq(c, Colour(d))).Aggregate((tail, head) => Or(head, tail));
    private static Formula Arrow(Formula a, Formula b) =>
        new Formula.TypeArrow(Parenthesized(a), Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Power(Formula a, Formula b) =>
        new Formula.Power(Parenthesized(a), Parenthesized(b));
    private static Formula Bound(string n, Formula t) => Parenthesized(Seq(V(n), Colon, Sp, t));
    private static Formula All(string n, Formula t, Formula body) =>
        Seq(Forall, Sp, Bound(n, t), Comma, Sp, Parenthesized(body));
    private static Formula Ex(string n, Formula t, Formula body) =>
        Seq(Exists, Sp, Bound(n, t), Comma, Sp, Parenthesized(body));
    private static Formula Fn(string n, Formula t, Formula body) =>
        Parenthesized(Seq(Bound(n, t), Sp, Mapsto, Sp, body));
    private static Formula Conditional(Formula p, Formula y, Formula n) => Parenthesized(
        Seq(Q("if"), Sp, Parenthesized(p), Sp, Q("then"), Sp, y, Sp, Q("else"), Sp, n));
    private static Formula SumOver(string n, Formula t, Formula body) =>
        Seq(Sum, Underscore, Grp(Bound(n, t)), Sp, Parenthesized(body));
}
