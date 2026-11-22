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
            Blocks(Paragraph(Text("The index types have finite enumerations and decidable equality. The zero lower-left block makes left projection commute with one step, and iteration preserves that identity."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("forward-zeroth"), DeclarationHandle.Create(Prefix + "forward_zeroth"),
            H("Reuse of the zero-cost iteration"), StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(Call("Function.comp", Call("DefectTransfer.forward", Call("HardinA229508StripData.T"), Call("HardinA229508StripData.initial"), V("n")), Call("Sum.inl")), Call("DefectTransfer.forward", Call("HardinA203981StripData.T"), Call("HardinA203981StripData.initial"), V("n")))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The upper-block projection specializes to the first sector, whose transition matrix is the zero-cost matrix."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("half-forward-one"), DeclarationHandle.Create(Prefix + "halfForwardOne"),
            H("The half-strip forward vectors in degree 1"),
            StatementSource.FromAuthor(Disp(Typed(Call("HardinA229508StripCertificate.halfForwardOne"), Arr(Fin("21"), Arr(Fin("5"), V("Int")))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The 21 by 5 integer table begins with the zero vector and the final five coordinates of HardinA229588Strip.W at exponent one. Exponent two uses the final five coordinates of the same frozen row at exponent two, with classes 1 and 3 exchanged. The later rows are tabulated half-strip samples. The unordered products are checked against the full-strip update in HardinA229508StripCertificate.forward_one."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("w"), DeclarationHandle.Create(Prefix + "W"),
            H("Forward vectors in total cost degree 1"), StatementSource.FromAuthor(Disp(ForwardWeightsFormula())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The degree-zero and degree-one half-strip vectors contribute in both orders at each exponent through twenty."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("square-monic-coeff"), DeclarationHandle.Create(Prefix + "squareMonicCoeff"),
            H("Squared monic polynomial coefficients"), StatementSource.FromAuthor(Disp(SquareMonicCoeffFormula())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The antidiagonal lists pairs of nonnegative exponents whose sum is the output exponent."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("coeff"), DeclarationHandle.Create(Prefix + "coeff"),
            H("Order-twelve coefficients"), StatementSource.FromAuthor(Disp(CoeffFormula())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The recurrence weights are the negatives of the coefficients below degree 12 in the square of the order-six monic polynomial."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("coeff-values"), DeclarationHandle.Create(Prefix + "coeff_values"),
            H("Numerical expansion"), StatementSource.FromAuthor(Disp(Eq(Typed(Call("HardinA229508StripCertificate.coeff"), Arr(Fin("12"), V("Int"))), Vec(N("43046721", true), N("47829690"), N("13286025"), N("27398736", true), N("2329155"), N("4556250"), N("940491", true), N("180630", true), N("50175"), N("324"), N("715", true), N("50"))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The coefficients are listed in increasing order of input index."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("forward-one"), DeclarationHandle.Create(Prefix + "forward_one"),
            H("Second-sector forward vectors"), StatementSource.FromAuthor(Disp(All("i", Fin("21"), Eq(Call("Function.comp", Call("DefectTransfer.forward", Call("HardinA229508StripData.T"), Call("HardinA229508StripData.initial"), Call("Fin.val", V("i"))), Call("Sum.inr")), Call("HardinA229508StripCertificate.W", V("i")))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("Each update combines transitions with one new defect from the first sector and zero new defects from the second."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("shifted-coordinate"), DeclarationHandle.Create(Prefix + "shifted_coordinate"),
            H("A shifted forward relation in one coordinate"), StatementSource.FromAuthor(Disp(ShiftedCoordinateFormula())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The index type has a finite enumeration and decidable equality. Taking the terminal vector equal to one at the selected coordinate and zero elsewhere reads that coordinate from the shifted relation."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("finite-certificate"), DeclarationHandle.Create(Prefix + "finite_certificate"),
            H("Forward relation at exponent thirteen"), StatementSource.FromAuthor(Disp(Eq(Call("DefectTransfer.forward", Call("HardinA229508StripData.T"), Call("HardinA229508StripData.initial"), Add(N("1"), N("12"))), SumOver("k", Fin("12"), Call("SMul.smul", Call("HardinA229508StripCertificate.coeff", V("k")), Call("DefectTransfer.forward", Call("HardinA229508StripData.T"), Call("HardinA229508StripData.initial"), Add(N("1"), Call("Fin.val", V("k"))))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("Seven applications of the coordinate shift to the order-six relation give the inherited sector relation. The other sector follows from the tabulated update."))), DescribeRole.Theorem))));
    private static Formula BlockProjectionFormula()
    {
        var l = V("l"); var r = V("r"); var a = V("a"); var b = V("b"); var c = V("c");
        var v = V("v"); var n = V("n");
        var sumType = Call("Sum", l, r);
        var zero = Typed(N("0"), Matrix(r, l));
        var matrix = Call("Matrix.fromBlocks", a, b, zero, c);
        var projection = Typed(Call("Sum.inl"), Arr(l, sumType));
        var lhs = Call("Function.comp", Call("DefectTransfer.forward", matrix, v, n), projection);
        var rhs = Call("DefectTransfer.forward", a, Call("Function.comp", v, projection), n);
        var body = All("a", Matrix(l, l),
            All("b", Matrix(l, r), All("c", Matrix(r, r), All("v", Arr(sumType, V("Int")),
                All("n", V("Nat"), Eq(lhs, rhs))))));
        return Seq(Forall, Sp, Typed(l, V("Type")), Sp, Typed(r, V("Type")), Sp,
            Instance("Fintype", l), Sp, Instance("Fintype", r), Sp,
            Instance("DecidableEq", l), Sp, Instance("DecidableEq", r),
            Comma, Sp, Parenthesized(body));
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
                Seq(Parenthesized(relation), Sp, To, Sp,
                    Parenthesized(All("n", V("Nat"), All("j", s, conclusion)))))))));
        return Seq(Forall, Sp, Typed(s, V("Type")), Sp,
            Instance("Fintype", s), Sp, Instance("DecidableEq", s),
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
        var sum = Seq(Sum, Underscore, Grp(p, Sp, InMacro, Sp, Call("Finset.antidiagonal", n)),
            Sp, Parenthesized(product));
        return All("n", V("Nat"), Eq(Call("HardinA229508StripCertificate.squareMonicCoeff", n), sum));
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
