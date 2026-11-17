using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233124SquareStripDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233124SquareStrip";
    private const string Scanner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip";
    private const string Triangle =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip";
    private const string PairMap = "D5.S3.Observer.Separation.BooleanRankThreeK4.beta";
    private const string PairLabels =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder.pairs";
    private const string Prefix =
        "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2013a233124");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Barker's generating function for normalized six-colour square strips.",
        H("Horizontal and vertical complementary-pair exclusion"),
        Blocks(
            Paragraph(Text(
                "OEIS A233124, revision 7, counts arrays on n rows and three columns. "
                + "Horizontal and vertical neighbours are unequal and do not sum to five; "
                + "diagonals are unconstrained. The first colour is zero. In row-major "
                + "order every 2, 3 or 4 has an earlier 1, and every 3 has an earlier 2. "
                + "The coefficient a 0 is zero. All names in the formulas are their full "
                + "Lean names. Fin.val is the explicit embedding into Nat; numeric Fin "
                + "indices have their displayed finite type. Nat.div is natural quotient "
                + "division and Nat.mod is the nonnegative remainder, with the Lean "
                + "zero-divisor conventions n / 0 = 0 and n % 0 = n; neither operation "
                + "is used in these definitions.")),
            Def("bonds", "bonds", "Vertical neighbours", BondsFormula(),
                "The three bonds connect equal column indices in consecutive rows."),
            Def("legal", "Legal", "The literal array predicate", LegalFormula(),
                "The owner predicate widthLegal is specialized to width three, rowLegal "
                + "and the vertical predicate bonds. Its widthNormal imposes the stated "
                + "row-major normalization. The filtered count keeps every array in scope."),
            Def("count", "a", "The literal filtered count", CountFormula(),
                "The filter ranges over every function on Fin n times Fin 3. The "
                + "first-cell existential is false when n is zero.", true),
            Def("compatible", "compatible", "Vertical label compatibility", CompatibleFormula(),
                "Each new label differs from the preceding label in the same column."),
            Def("valid", "Valid", "Reachable boundaries", ValidFormula(),
                "Colour one has occurred, adjacent boundary labels differ, and before "
                + "colour two occurs every label differs from two."),
            Def("decidable-valid", "instDecidableValid", "Deciding reachable boundaries",
                DecidableValidFormula(),
                "The defining expression infers decidability for the conjunction defining Valid."),
            Def("boundaryclass", "boundaryClass", "The three boundary classes", ClassFormula(),
                "Class zero has not seen colour two. Classes one and two have seen it; "
                + "their endpoint labels are respectively equal and different."),
            Def("transfer", "transfer", "The row transfer matrix", TransferFormula(),
                "The matrix rows and columns have the boundaryClass order zero, one, two."),
            Def("classcount", "classCount", "One-row transitions", ClassCountFormula(),
                "The shared scanner good and finish checks and updates normalization "
                + "within the three cells of the new row."),
            Def("firstcount", "firstCount", "The first-row distribution", FirstCountFormula(),
                "The initial scanner flags are false and the first colour is zero."),
            Thm("certificate", "finite_certificate", "The class counts", CertificateFormula(),
                "For each valid boundary the three counts are the corresponding row "
                + "of the transfer matrix. The first-row distribution is [2,0,1]."),
            Resolution("result", "result", "Barker's generating-function identity",
                ResultFormula(),
                "Let B(k), E(k), D(k) be the continuation counts for the three classes. "
                + "All equal one at k=0. The matrix gives B(k+1)=8B(k)+8E(k)+8D(k), "
                + "E(k+1)=24E(k)+16D(k), D(k+1)=16E(k)+16D(k). Decomposing "
                + "an array into its first row and tail gives a(k+1)=2B(k)+D(k). "
                + "Hence a(n+4)=48a(n+3)-448a(n+2)+1024a(n+1) for every natural n. "
                + "The initial values are a(0)=0, a(1)=3, a(2)=80, a(3)=2688. "
                + "Coefficient comparison in PowerSeries Int gives the displayed "
                + "identity. This is an identity of formal series; it needs no analytic "
                + "convergence assumption."))));

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
            new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin233124"),
                ResolutionKind.Proved));

    private static Formula BondsFormula()
    {
        var c = V("c"); var d = V("d"); var j = V("j");
        var x = At(c, j); var y = At(d, j);
        return All("c", Row(), All("d", Row(), Eq(Call("bonds", c, d),
            All("j", Fin(3), And(Ne(x, y), Ne(Add(Val(x), Val(y)), D(5)))))));
    }
    private static Formula LegalFormula()
    {
        var n = V("n"); var a = V("A"); var i = V("i"); var j = V("j");
        var h = V("h");
        Formula Cell(Formula r, Formula k) => At(a, Pair(r, k));
        Formula RowAt(Formula r) => Fn("j", Fin(3), Cell(r, j));
        var first = Ex("i", Fin(n), And(Eq(Val(i), D(0)), Eq(Cell(i, Index(0)), Colour(0))));
        var horizontal = All("i", Fin(n), At(Q(Triangle + ".rowLegal"), RowAt(i)));
        var next = Cast(At(Q("Fin.mk"), Add(Val(i), D(1)), h), Fin(n));
        var vertical = All("i", Fin(n), All("h", Lt(Add(Val(i), D(1)), n),
            Call("bonds", RowAt(i), RowAt(next))));
        var normal = At(Q(Triangle + ".widthNormal"), EmptySeen(),
            Fn("i", Fin(n), RowAt(i)));
        return All("n", Q("Nat"), All("A", Arrow(Product(Fin(n), Fin(3)), Fin(6)),
            And(Eq(Call("Legal", a), At(Q(Triangle + ".widthLegal"),
                    Q(Triangle + ".rowLegal"), Q(Owner + ".bonds"), a)),
                Eq(Call("Legal", a),
                    Parenthesized(And(first, And(horizontal, And(vertical, normal))))))));
    }
    private static Formula CountFormula()
    {
        var n = V("n"); var a = V("A");
        return All("n", Q("Nat"), Eq(Call("a", n), At(Q("Finset.card"),
            At(Q("Finset.filter"), Fn("A", Arrow(Product(Fin(n), Fin(3)), Fin(6)),
                Call("Legal", a)), Q("Finset.univ")))));
    }
    private static Formula CompatibleFormula()
    {
        var p = V("p"); var c = V("c"); var j = V("j");
        return All("p", Labels(), All("c", Row(), Eq(Call("compatible", p, c),
            All("j", Fin(3), Ne(At(p, j), At(Q(PairMap), At(c, j)))))));
    }
    private static Formula DecidableValidFormula()
    {
        var s = V("s"); var p = V("p"); var j = V("j");
        var body = And(Eq(Proj(s, 1), Q("Bool.true")),
            And(Ne(At(p, Index(0)), At(p, Index(1))),
                And(Ne(At(p, Index(1)), At(p, Index(2))),
                    Imp(Eq(Proj(s, 2), Q("Bool.false")),
                        All("j", Fin(3), Ne(At(p, j), Index(2)))))));
        return All("s", Seen(), All("p", Labels(),
            Eq(Cast(Call("instDecidableValid", s, p),
                    At(Q("Decidable"), Parenthesized(Call("Valid", s, p)))),
                At(Q("inferInstanceAs"),
                    Parenthesized(At(Q("Decidable"), Parenthesized(body)))))));
    }
    private static Formula ValidFormula()
    {
        var s = V("s"); var p = V("p"); var j = V("j");
        return All("s", Seen(), All("p", Labels(), Eq(Call("Valid", s, p),
            Parenthesized(And(Eq(Proj(s, 1), Q("Bool.true")),
                And(Ne(At(p, Index(0)), At(p, Index(1))),
                And(Ne(At(p, Index(1)), At(p, Index(2))),
                    Imp(Eq(Proj(s, 2), Q("Bool.false")),
                        All("j", Fin(3), Ne(At(p, j), Index(2)))))))))));
    }
    private static Formula ClassFormula()
    {
        var s = V("s"); var p = V("p");
        return All("s", Seen(), All("p", Labels(), Eq(Call("boundaryClass", s, p),
            Conditional(Proj(s, 2),
                Conditional(Eq(At(p, Index(0)), At(p, Index(2))), Index(1), Index(2)),
                Index(0)))));
    }
    private static Formula TransferFormula()
    {
        var i = V("i"); var k = V("k");
        return All("i", Fin(3), All("k", Fin(3), Eq(Call("transfer", i, k),
            At(Vec(Vec(Z(8), Z(8), Z(8)), Vec(Z(0), Z(24), Z(16)),
                Vec(Z(0), Z(16), Z(16))), i, k))));
    }
    private static Formula ClassCountFormula()
    {
        var s = V("s"); var p = V("p"); var k = V("k"); var c = V("c");
        var condition = And(At(Q(Triangle + ".rowLegal"), c), And(Call("compatible", p, c),
            And(At(Q(Scanner + ".good"), s, c), Eq(
                Call("boundaryClass", At(Q(Scanner + ".finish"), s, c),
                    At(Q(PairLabels), c)), k))));
        return All("s", Seen(), All("p", Labels(), All("k", Fin(3),
            Eq(Call("classCount", s, p, k), SumOver("c", Row(),
                Conditional(condition, Z(1), Z(0)))))));
    }
    private static Formula FirstCountFormula()
    {
        var k = V("k"); var c = V("c");
        var condition = And(Eq(At(c, Index(0)), Colour(0)),
            And(At(Q(Triangle + ".rowLegal"), c),
                And(At(Q(Scanner + ".good"), EmptySeen(), c), Eq(Call("boundaryClass",
                    At(Q(Scanner + ".finish"), EmptySeen(), c), At(Q(PairLabels), c)), k))));
        return All("k", Fin(3), Eq(Call("firstCount", k),
            SumOver("c", Row(), Conditional(condition, Z(1), Z(0)))));
    }
    private static Formula CertificateFormula()
    {
        var s = V("s"); var p = V("p"); var k = V("k");
        return And(All("s", Seen(), All("p", Labels(), Imp(Call("Valid", s, p),
            All("k", Fin(3), Eq(Call("classCount", s, p, k),
                Call("transfer", Call("boundaryClass", s, p), k)))))),
            All("k", Fin(3), Eq(Call("firstCount", k), At(Vec(Z(2), Z(0), Z(1)), k))));
    }
    private static Formula ResultFormula()
    {
        var x = Q("PowerSeries.X"); var n = V("n");
        var series = At(Q("PowerSeries.mk"),
            Fn("n", Q("Nat"), Cast(Call("a", n), Q("Int"))));
        return Eq(Mul(Mul(Sub(D(1), Mul(D(8), x)),
            Add(Sub(D(1), Mul(D(4,0), x)), Mul(D(1,2,8), Pow(x, D(2))))), series),
            Mul(x, Add(Sub(D(3), Mul(D(6,4), x)), Mul(D(1,9,2), Pow(x, D(2))))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((p, i) =>
        i == 0 ? new[] { Seq(Operatorname, Grp(V(p))) }
            : new[] { Dot, Seq(Operatorname, Grp(V(p))) }).ToArray());
    private static Formula Call(string name, params Formula[] args) =>
        At(Q(Owner + "." + name), args);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Fin(byte n) => At(Q("Fin"), D(n));
    private static Formula Fin(Formula n) => At(Q("Fin"), n);
    private static Formula Row() => Q(Triangle + ".Row");
    private static Formula Seen() => Q(Scanner + ".Seen");
    private static Formula Labels() => Arrow(Fin(3), Fin(3));
    private static Formula EmptySeen() => Pair(Q("Bool.false"), Q("Bool.false"));
    private static Formula Index(byte n) => Cast(D(n), Fin(3));
    private static Formula Colour(byte n) => Cast(D(n), Fin(6));
    private static Formula Z(byte n) => Cast(D(n >= 10 ? new[] { (byte)(n / 10), (byte)(n % 10) }
        : new[] { n }), Q("Int"));
    private static Formula Val(Formula f) => At(Q("Fin.val"), f);
    private static Formula Proj(Formula f, byte n) => At(Q(n == 1 ? "Prod.fst" : "Prod.snd"), f);
    private static Formula Cast(Formula f, Formula t) => Parenthesized(Seq(f, Colon, Sp, t));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Product(Formula a, Formula b) => Seq(
        Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Arrow(Formula a, Formula b) =>
        new Formula.TypeArrow(Parenthesized(a), b);
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula Imp(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula And(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Conditional(Formula c, Formula y, Formula n) =>
        Parenthesized(Seq(Q("if"), Sp, Parenthesized(c), Sp, Q("then"), Sp, y,
            Sp, Q("else"), Sp, n));
    private static Formula Vec(params Formula[] xs) => Seq(new[] { Bang, OpenBracket }
        .Concat(xs.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Comma, Sp, x }))
        .Append(CloseBracket).ToArray());
    private static Formula SumOver(string v, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(V(v), Colon, Sp, type), Sp, Parenthesized(body));
    private static Formula Fn(string v, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, V(v), Colon, Sp, type, Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula All(string v, Formula type, Formula body) =>
        Seq(Forall, Sp, V(v), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula Ex(string v, Formula type, Formula body) =>
        Seq(Exists, Sp, V(v), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
}
