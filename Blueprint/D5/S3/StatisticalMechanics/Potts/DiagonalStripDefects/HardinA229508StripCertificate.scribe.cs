using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects;

internal sealed class HardinA229508StripCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.";
    private const string Note = "D5/L/SpinModels/hardin2013a229508";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite checks for the order-twelve recurrence", H("Finite checks for the order-twelve recurrence"), Blocks(
        Describe.Lean(DescribeId.Create("budget-cut"), DeclarationHandle.Create(Prefix + "budget_cut"),
            H("Exact spending of a natural-number budget"), StatementSource.FromAuthor(Disp(
                All("c", V("Nat"), All("d", V("Nat"), Seq(
                    Parenthesized(And(Leq(V("c"), V("d")), Eq(Sub(V("d"), V("c")), N("0")))),
                    Sp, F.Iff, Sp, Parenthesized(Eq(V("c"), V("d")))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("Truncated subtraction gives zero whenever the cost is at least the budget. Together with the cost being at most the budget, this forces equality."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("one-exact"), DeclarationHandle.Create(Prefix + "one_exact"),
            H("Exact one-cost half-strip counts"), StatementSource.FromAuthor(Disp(All("a", Call("HardinA233258PairTransfer.Col"), All("j", Fin("5"),
                Eq(SumOver("b", Call("HardinA233258PairTransfer.Col"),
                    If(And(Eq(Call("HardinA203981StripCertificate.halfCost", V("a"), V("b")), N("1")),
                        Eq(Call("HardinA233258PairTransfer.cls", V("b")), V("j"))), CastInt(N("1")), CastInt(N("0")))),
                    Call("HardinA229508StripData.halfOne", Call("HardinA233258PairTransfer.cls", V("a")), V("j"))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The transition clause of HardinA229588Strip.finite_certificate at budget one gives the count into its terminal sector."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("one-counts"), DeclarationHandle.Create(Prefix + "one_counts"),
            H("Exact-one-cost class counts"), StatementSource.FromAuthor(Disp(All("p", Row("6"), All("j", Fin("15"), Eq(SumOver("r", Row("6"), If(And(Eq(Call("DefectTransfer.bondDefects", Call("HardinA229637RowColumn.betw", N("6")), V("p"), V("r")), N("1")), Eq(Call("HardinA203981StripData.boundary", V("r")), V("j"))), CastInt(N("1")), CastInt(N("0")))), Call("HardinA229508StripData.costOne", Call("HardinA203981StripData.boundary", V("p")), V("j"))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The exact cost splits as zero plus one or one plus zero. Parity recolouring and reflection extend the representative counts to every source row."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("transition-counts"), DeclarationHandle.Create(Prefix + "transition_counts"),
            H("Exact remaining-budget transitions"), StatementSource.FromAuthor(Disp(All("p", Row("6"), All("d", Fin("2"), All("s", Call("Sum", Fin("15"), Fin("15")), Eq(SumOver("r", Row("6"), If(And(Leq(Call("DefectTransfer.bondDefects", Call("HardinA229637RowColumn.betw", N("6")), V("p"), V("r")), Call("Fin.val", V("d"))), Eq(Call("HardinA229508StripData.cl", V("r"), Sub(Call("Fin.val", V("d")), Call("DefectTransfer.bondDefects", Call("HardinA229637RowColumn.betw", N("6")), V("p"), V("r")))), V("s"))), CastInt(N("1")), CastInt(N("0")))), Call("HardinA229508StripData.T", Call("HardinA229508StripData.cl", V("p"), Call("Fin.val", V("d"))), V("s")))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("A step stays in its sector when it has no defects, or enters the second sector by spending one defect. Spending a defect beyond the budget contributes zero."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("block-projection"), DeclarationHandle.Create(Prefix + "block_projection"),
            H("Forward projection of an upper-block transfer"), StatementSource.FromAuthor(Disp(BlockProjectionFormula())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The finite enumerations and semiring operations define the matrix-vector sums. The zero lower-left block makes left projection commute with one step, and iteration preserves that identity."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("forward-zeroth"), DeclarationHandle.Create(Prefix + "forward_zeroth"),
            H("Reuse of the zero-cost iteration"), StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(Call("Function.comp", Call("DefectTransfer.forward", Call("HardinA229508StripData.T"), Call("HardinA229508StripData.initial"), V("n")), Call("Sum.inl")), Call("DefectTransfer.forward", Call("HardinA203981StripData.T"), Call("HardinA203981StripData.initial"), V("n")))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The upper-block projection specializes to the first sector, whose transition matrix is the zero-cost matrix."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("half-forward-one"), DeclarationHandle.Create(Prefix + "halfForwardOne"),
            H("The half-strip forward vectors in degree 1"),
            StatementSource.FromAuthor(Disp(HalfForwardFormula())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The 21 by 5 integer table begins with the zero vector and the final five coordinates of HardinA229588Strip.W at exponent one. Exponent two uses the final five coordinates of the same frozen row at exponent two, with classes 1 and 3 exchanged. The later rows are tabulated half-strip samples. The unordered products are checked against the full-strip update in HardinA229508StripCertificate.forward_one."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("w"), DeclarationHandle.Create(Prefix + "W"),
            H("Forward vectors in total cost degree 1"), StatementSource.FromAuthor(Disp(ForwardWeightsFormula())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The degree-zero and degree-one half-strip vectors contribute in both orders at each exponent through twenty."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("square-monic-coeff"), DeclarationHandle.Create(Prefix + "squareMonicCoeff"),
            H("Squared monic polynomial coefficients"), StatementSource.FromAuthor(Disp(SquareMonicCoeffFormula())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The antidiagonal lists pairs of nonnegative exponents whose sum is the output exponent. IntegralDiscriminant.integerConvolution evaluates the displayed Cauchy sum over the corresponding range of first indices."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("coeff"), DeclarationHandle.Create(Prefix + "coeff"),
            H("Order-twelve coefficients"), StatementSource.FromAuthor(Disp(CoeffFormula())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The recurrence weights are the negatives of the coefficients below degree 12 in the square of the order-six monic polynomial."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("coeff-values"), DeclarationHandle.Create(Prefix + "coeff_values"),
            H("Numerical expansion"), StatementSource.FromAuthor(Disp(Eq(Typed(Call("HardinA229508StripCertificate.coeff"), Arr(Fin("12"), V("Int"))), Vec(N("43046721", true), N("47829690"), N("13286025"), N("27398736", true), N("2329155"), N("4556250"), N("940491", true), N("180630", true), N("50175"), N("324"), N("715", true), N("50"))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The coefficients are listed in increasing order of input index."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("forward-step"), DeclarationHandle.Create(Prefix + "forward_step"),
            H("Update on both sectors"), StatementSource.FromAuthor(Disp(ForwardStepFormula())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The left component uses the zero-degree update. The right component adds the incoming degree-one transitions to the degree-zero transfers within that sector."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("forward-one"), DeclarationHandle.Create(Prefix + "forward_one"),
            H("Second-sector forward vectors"), StatementSource.FromAuthor(Disp(All("i", Fin("21"), Eq(Call("Function.comp", Call("DefectTransfer.forward", Call("HardinA229508StripData.T"), Call("HardinA229508StripData.initial"), Call("Fin.val", V("i"))), Call("Sum.inr")), Call("HardinA229508StripCertificate.W", V("i")))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("Each update combines transitions with one new defect from the first sector and zero new defects from the second."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("shifted-coordinate"), DeclarationHandle.Create(Prefix + "shifted_coordinate"),
            H("A shifted forward relation in one coordinate"), StatementSource.FromAuthor(Disp(ShiftedCoordinateFormula())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The finite enumeration defines the matrix-vector sums. Taking the terminal vector equal to one at the selected coordinate and zero elsewhere reads that coordinate from the shifted relation.")),
                Paragraph(Text("The seed equation is needed even at shift zero. For a one-state identity transfer with initial entry one, base zero, order one and coefficient zero, the left-hand side is one and the right-hand side is zero."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("finite-certificate"), DeclarationHandle.Create(Prefix + "finite_certificate"),
            H("Forward relation at exponent thirteen"), StatementSource.FromAuthor(Disp(Eq(Call("DefectTransfer.forward", Call("HardinA229508StripData.T"), Call("HardinA229508StripData.initial"), Add(N("1"), N("12"))), SumOver("k", Fin("12"), Call("SMul.smul", Call("HardinA229508StripCertificate.coeff", V("k")), Call("DefectTransfer.forward", Call("HardinA229508StripData.T"), Call("HardinA229508StripData.initial"), Add(N("1"), Call("Fin.val", V("k"))))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("Seven applications of the coordinate shift to the order-six relation give the inherited sector relation. The other sector follows from the tabulated update."))), DescribeRole.Theorem))));
    private static Formula BlockProjectionFormula()
    {
        var l = V("l"); var r = V("r"); var a = V("a"); var b = V("b"); var c = V("c");
        var v = V("v"); var n = V("n");
        var alpha = V("alpha");
        var sumType = Call("Sum", l, r);
        Formula Block(Formula x, Formula y) => Call("Matrix", x, y, alpha);
        Formula Iteration(Formula t, Formula index, Formula start)
        {
            var step = Seq(LambdaLower, Sp, V("w"), Colon, Sp, Arr(index, alpha), Sp, Mapsto, Sp,
                Parenthesized(Call("Matrix.vecMul", V("w"), t)));
            return Call("Nat.iterate", Parenthesized(step), n, start);
        }
        var matrix = Call("Matrix.fromBlocks", a, b, Typed(N("0"), Block(r, l)), c);
        var projection = Typed(Call("Sum.inl"), Arr(l, sumType));
        var lhs = Call("Function.comp", Iteration(matrix, sumType, v), projection);
        var rhs = Iteration(a, l, Call("Function.comp", v, projection));
        var body = All("a", Block(l, l), All("b", Block(l, r), All("c", Block(r, r),
            All("v", Arr(sumType, alpha), All("n", V("Nat"), Eq(lhs, rhs))))));
        return Seq(Forall, Sp, Typed(l, V("Type")), Sp, Typed(r, V("Type")), Sp,
            Typed(alpha, V("Type")), Sp, Instance("Fintype", l), Sp, Instance("Fintype", r), Sp,
            Instance("NonUnitalNonAssocSemiring", alpha), Comma, Sp, Parenthesized(body));
    }

    private static Formula Matrix(Formula l, Formula r) => Call("Matrix", l, r, V("Int"));

    private static Formula ShiftedCoordinateFormula()
    {
        var s = V("s"); var t = V("t"); var v = V("v"); var d = V("d"); var b = V("b");
        var c = V("c"); var n = V("n"); var j = V("j"); var k = V("k");
        var fin = Call("Fin", d);
        Formula Forward(Formula exponent) => Call("DefectTransfer.forward", t, v, exponent);
        var relation = Eq(Forward(Add(b, d)), SumOver("k", fin,
            Call("SMul.smul", App(c, k), Forward(Add(b, Call("Fin.val", k))))));
        var conclusion = Eq(App(Forward(Add(Add(n, b), d)), j), SumOver("k", fin,
            Mul(App(c, k), App(Forward(Add(Add(n, b), Call("Fin.val", k))), j))));
        var body = All("t", Matrix(s, s), All("v", Arr(s, V("Int")),
            All("d", V("Nat"), All("b", V("Nat"), All("c", Arr(fin, V("Int")),
                Seq(Parenthesized(relation), Sp, Implies, Sp,
                    Parenthesized(All("n", V("Nat"), All("j", s, conclusion)))))))));
        return Seq(Forall, Sp, Typed(s, V("Type")), Sp,
            Instance("Fintype", s),
            Comma, Sp, Parenthesized(body));
    }

    private static Formula Instance(string name, Formula type) =>
        Seq(OpenBracket, Call(name, type), CloseBracket);

    private static Formula CoeffFormula()
    {
        var k = V("k");
        return All("k", Fin("12"), Eq(Call("HardinA229508StripCertificate.coeff", k),
            Seq(Minus, Call("HardinA229508StripCertificate.squareMonicCoeff", Call("Fin.val", k)))));
    }

    private static Formula SquareMonicCoeffFormula()
    {
        var n = V("n");
        var p = V("p");
        Formula Monic(Formula i) => Call("HardinA203981StripCertificate.monicCoeff", i);
        var product = new Formula.Binary(Monic(Call("Prod.fst", p)), FormulaBinaryOperator.Multiply,
            Monic(Call("Prod.snd", p)));
        var sum = Seq(new Formula.Subscript(Sum,
            Seq(p, Sp, InMacro, Sp, Call("Finset.HasAntidiagonal.antidiagonal", n))),
            Sp, Parenthesized(product));
        return All("n", V("Nat"), Eq(Call("HardinA229508StripCertificate.squareMonicCoeff", n), sum));
    }

    private static Formula ForwardStepFormula()
    {
        var k = V("k");
        Formula RowAt(Formula i) => Call("Sum.elim",
            Call("HardinA203981StripCertificate.W", i), Call("HardinA229508StripCertificate.W", i));
        return All("k", Fin("20"), Eq(
            Call("Matrix.vecMul", RowAt(Call("Fin.castSucc", k)), Call("HardinA229508StripData.T")),
            RowAt(Call("Fin.succ", k))));
    }

    private static Formula HalfForwardFormula()
    {
        const string table = "HardinA229508StripCertificate.halfForwardOne";
        var j = V("j");
        var swapped = Call("Equiv.swap", N("1"), N("3"), j);
        Formula RowAt(string index) => Call(table, N(index));
        return new Formula.Aligned([
            Typed(Call(table), Arr(Fin("21"), Arr(Fin("5"), V("Int")))),
            Eq(RowAt("0"), Vec(N("0"), N("0"), N("0"), N("0"), N("0"))),
            All("j", Fin("5"), Eq(Call(table, N("1"), j),
                Call("HardinA229588Strip.W", N("1"), Call("Fin.natAdd", N("5"), j)))),
            All("j", Fin("5"), Eq(Call(table, N("2"), j),
                Call("HardinA229588Strip.W", N("2"), Call("Fin.natAdd", N("5"), swapped)))),
            Eq(RowAt("3"), Vec(N("1644"), N("2406"), N("1602"), N("2436"), N("1632"))),
            Eq(RowAt("4"), Vec(N("10380"), N("13470"), N("8892"), N("13908"), N("8286"))),
            Eq(RowAt("5"), Vec(N("59946"), N("73344"), N("49104"), N("75966"), N("41160"))),
            Eq(RowAt("6"), Vec(N("331590"), N("387510"), N("261558"), N("404562"), N("203100"))),
            Eq(RowAt("7"), Vec(N("1777398"), N("2010720"), N("1367730"), N("2110506"), N("995358"))),
            Eq(RowAt("8"), Vec(N("9320448"), N("10280940"), N("7035318"), N("10841808"), N("4855182"))),
            Eq(RowAt("9"), Vec(N("48062886"), N("51972294"), N("35741484"), N("55012938"), N("23584278"))),
            Eq(RowAt("10"), Vec(N("244626816"), N("260291310"), N("179732718"), N("276379104"), N("114154620"))),
            Eq(RowAt("11"), Vec(N("1232038140"), N("1293572766"), N("896272632"), N("1377107340"), N("550794234"))),
            Eq(RowAt("12"), Vec(N("6151560582"), N("6386839908"), N("4438054080"), N("6814356114"), N("2650075116"))),
            Eq(RowAt("13"), Vec(N("30493060134"), N("31358474490"), N("21844483506"), N("33521267202"), N("12718073172"))),
            Eq(RowAt("14"), Vec(N("150226357422"), N("153222899172"), N("106966659546"), N("164061769962"), N("60895203666"))),
            Eq(RowAt("15"), Vec(N("736199319228"), N("745515804252"), N("521439011046"), N("799411222140"), N("290960009814"))),
            Eq(RowAt("16"), Vec(N("3591284854602"), N("3613865018010"), N("2531889435744"), N("3880090505550"), N("1387554925614"))),
            Eq(RowAt("17"), Vec(N("17448371454444"), N("17460226198758"), N("12250924641810"), N("18767880996324"), N("6605447597328"))),
            Eq(RowAt("18"), Vec(N("84472101194124"), N("84109078953726"), N("59093625304332"), N("90500741777316"), N("31394234901822"))),
            Eq(RowAt("19"), Vec(N("407656599056970"), N("404091950193120"), N("284249234984832"), N("435200551114398"), N("148986407380296"))),
            Eq(RowAt("20"), Vec(N("1961740076499606"), N("1936745253298374"), N("1363840823481174"), N("2087584250909826"), N("706057576313820")))
        ]);
    }

    private static Formula ForwardWeightsFormula()
    {
        var i = V("i"); var j = V("j");
        Formula PairWeights(Formula a, Formula b) => Call("HardinA203981StripData.unordered", a, b, j);
        return All("i", Fin("21"), All("j", Fin("15"),
            Eq(Call("HardinA229508StripCertificate.W", i, j), Add(PairWeights(Call("HardinA203981StripCertificate.halfForwardZero", i), Call("HardinA229508StripCertificate.halfForwardOne", i)), PairWeights(Call("HardinA229508StripCertificate.halfForwardOne", i), Call("HardinA203981StripCertificate.halfForwardZero", i))))));
    }

    private static Formula N(string digits, bool negative = false) => negative ? Seq(Minus, N(digits)) :
        D(digits.Select(c => (byte)(c - '0')).ToArray());
    private static Formula V(string s) => new Formula.Symbol(FormulaIdentifier.Create(s));
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((part, i) => i == 0
        ? new[] { Seq(Operatorname, Grp(V(part))) }
        : new[] { Dot, Seq(Operatorname, Grp(V(part))) }).ToArray());
    private static Formula App(Formula f, params Formula[] xs) => new Formula.Apply(f, [..xs]);
    private static Formula Call(string s, params Formula[] xs) => xs.Length == 0 ? Q(s) : App(Q(s), xs);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Typed(Formula x, Formula t) => Parenthesized(Seq(x, Colon, Sp, t));
    private static Formula Arr(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Leq(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula CastInt(Formula a) => Typed(a, V("Int"));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula SumOver(string n, Formula t, Formula b) => Seq(Sum, Underscore, Grp(V(n), Colon, Sp, t), Sp, Parenthesized(b));
    private static Formula Fin(string n) => Call("Fin", N(n));
    private static Formula Row(string n) => Arr(Fin(n), Fin("3"));
    private static Formula If(Formula c, Formula y, Formula n) =>
        Parenthesized(Seq(Q("if"), Sp, Parenthesized(c), Sp, Q("then"), Sp, y, Sp, Q("else"), Sp, n));
    private static Formula Vec(params Formula[] xs) =>
        Seq(new[] { OpenBracket }.Concat(xs.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Comma, Sp, x }))
            .Append(CloseBracket).ToArray());
}
