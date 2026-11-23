using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects;

internal sealed class HardinA203981StripCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripCertificate.";
    private const string Note = "D5/L/SpinModels/hardin2012a203981";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite checks for the zero-defect recurrence", H("Finite checks for the zero-defect recurrence"), Blocks(
        Describe.Lean(DescribeId.Create("half-cost"), DeclarationHandle.Create(Prefix + "halfCost"),
            H("Exact cost on one parity class"), StatementSource.FromAuthor(Disp(All("a", Col(), All("b", Col(), Eq(Call("HardinA203981StripCertificate.halfCost", V("a"), V("b")),
                Bond(Call("HardinA203981StripData.columnRows", V("a")), ReversedRow(V("b")))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The five half-strip bonds read the target triple in reverse order."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("allocated-counts"), DeclarationHandle.Create(Prefix + "allocated_counts"),
            H("Allocate exact cost between the parity classes"), StatementSource.FromAuthor(Disp(AllocatedCountsFormula())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The half-strip class counts give the summands for all ordered allocations of the cost. Each summand reads the unordered target class. For k in Fin(d+1), Fin.rev(k) has natural value d minus Fin.val(k)."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("reversed-count"), DeclarationHandle.Create(Prefix + "reversed_count"),
            H("Reindex the target triple under reversal"), StatementSource.FromAuthor(Disp(ReversedCountFormula())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("Reversing a triple exchanges classes 1 and 3 and preserves the other three classes."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("zero-exact"), DeclarationHandle.Create(Prefix + "zero_exact"),
            H("Exact zero-cost half-strip counts"), StatementSource.FromAuthor(Disp(All("a", Col(), All("j", Fin("5"), Eq(HalfCount(V("a"), N("0"), V("j")),
                Call("HardinA203981StripData.halfZero", Class(V("a")), V("j"))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The zero-budget transition clause of HardinA229588Strip.finite_certificate gives the count."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("counts"), DeclarationHandle.Create(Prefix + "counts"),
            H("Exact zero-cost class counts"), StatementSource.FromAuthor(Disp(All("p", Row("6"), All("j", Fin("15"), Eq(SumOver("r", Row("6"), If(And(Eq(Call("DefectTransfer.bondDefects", Call("HardinA229637RowColumn.betw", N("6")), V("p"), V("r")), N("0")), Eq(Call("HardinA203981StripData.boundary", V("r")), V("j"))), CastInt(N("1")), CastInt(N("0")))), Call("HardinA203981StripData.T", Call("HardinA203981StripData.boundary", V("p")), V("j"))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The ten bonds split into two copies of the three-position compatibility relation. Each half count uses the zero-budget clause of HardinA229588Strip.finite_certificate with the reversed target classes. Their products count the possible orders of the two target classes, and parity recolouring and reflection extend the result to every source row."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("initial-counts"), DeclarationHandle.Create(Prefix + "initial_counts"),
            H("Labelled row populations"), StatementSource.FromAuthor(Disp(All("j", Fin("15"), Eq(SumOver("r", Row("6"), If(Eq(Call("HardinA203981StripData.boundary", V("r")), V("j")), CastInt(N("1")), CastInt(N("0")))), Call("HardinA203981StripData.initial", V("j")))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The initial clause of HardinA229588Strip.finite_certificate gives the labelled populations on each parity. Equal classes contribute once and distinct classes contribute in both orders."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("half-forward-zero"), DeclarationHandle.Create(Prefix + "halfForwardZero"),
            H("The half-strip forward vectors in degree 0"),
            StatementSource.FromAuthor(Disp(Typed(Call("HardinA203981StripCertificate.halfForwardZero"), Arr(Fin("21"), Arr(Fin("5"), V("Int")))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The 21 by 5 integer table begins with HardinA203981StripData.halfInitial and HardinA233258PairTransfer.weights. Exponents two and three use the first five coordinates of HardinA229588Strip.W, with classes 1 and 3 exchanged at exponent three. The later rows are tabulated half-strip samples. The unordered products are checked against the full-strip update in HardinA203981StripCertificate.forward_table."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("w"), DeclarationHandle.Create(Prefix + "W"),
            H("Forward vectors in total cost degree 0"), StatementSource.FromAuthor(Disp(ForwardWeightsFormula())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The two half-strip vectors of degree zero are combined at each exponent through twenty."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("coeff"), DeclarationHandle.Create(Prefix + "coeff"),
            H("Recurrence coefficients"), StatementSource.FromAuthor(Disp(Eq(Typed(Call("HardinA203981StripCertificate.coeff"), Arr(Fin("6"), V("Int"))), Vec(N("6561", true), N("3645"), N("2025"), N("963", true), N("45", true), N("25"))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The entries are in increasing order of the input index."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("monic-coeff"), DeclarationHandle.Create(Prefix + "monicCoeff"),
            H("Monic polynomial coefficients"), StatementSource.FromAuthor(Disp(MonicCoeffFormula())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("Below degree six, the polynomial coefficients are the negatives of the recurrence weights. The leading coefficient is one and all higher coefficients vanish."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("forward-table-of-steps"), DeclarationHandle.Create(Prefix + "forward_table_of_steps"),
            H("Forward vectors from adjacent updates"), StatementSource.FromAuthor(Disp(ForwardTableOfStepsFormula())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The list of table rows starts at the initial vector. Its adjacent update equations determine the forward vector at each index."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("forward-step"), DeclarationHandle.Create(Prefix + "forward_step"),
            H("Zero-degree table update"), StatementSource.FromAuthor(Disp(ForwardStepFormula())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The finite calculation checks the transfer on each adjacent pair of rows."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("forward-table"), DeclarationHandle.Create(Prefix + "forward_table"),
            H("Forward iteration agrees with the table"), StatementSource.FromAuthor(Disp(All("i", Fin("21"), Eq(Call("DefectTransfer.forward", Call("HardinA203981StripData.T"), Call("HardinA203981StripData.initial"), Call("Fin.val", V("i"))), Call("HardinA203981StripCertificate.W", V("i")))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The integer vectors are obtained from the initial vector by repeated right multiplication."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("finite-certificate"), DeclarationHandle.Create(Prefix + "finite_certificate"),
            H("The forward relation at exponent seven"), StatementSource.FromAuthor(Disp(Eq(Call("DefectTransfer.forward", Call("HardinA203981StripData.T"), Call("HardinA203981StripData.initial"), Add(N("1"), N("6"))), SumOver("j", Fin("6"), Call("SMul.smul", Call("HardinA203981StripCertificate.coeff", V("j")), Call("DefectTransfer.forward", Call("HardinA203981StripData.T"), Call("HardinA203981StripData.initial"), Add(N("1"), Call("Fin.val", V("j"))))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The entrywise relation follows from the tabulated forward vectors."))), DescribeRole.Theorem))));
    private static Formula MonicCoeffFormula()
    {
        var n = V("n");
        var k = Typed(Seq(Langle, Sp, n, Comma, Sp, V("h"), Rangle), Fin("6"));
        var below = Seq(V("h"), Colon, Sp, n, Sp, Lt, Sp, N("6"));
        return All("n", V("Nat"), Eq(Call("HardinA203981StripCertificate.monicCoeff", n),
            If(below, Seq(Minus, Call("HardinA203981StripCertificate.coeff", k)),
                If(Eq(n, N("6")), CastInt(N("1")), CastInt(N("0"))))));
    }

    private static Formula Col() => Call("HardinA233258PairTransfer.Col");
    private static Formula Class(Formula b) => Call("HardinA233258PairTransfer.cls", b);
    private static Formula Bond(Formula a, Formula b) =>
        Call("DefectTransfer.bondDefects", Call("HardinA229588Strip.between"), a, b);
    private static Formula ReversedRow(Formula b)
    {
        var tail = Call("Prod.snd", b);
        return Vec(Call("Prod.snd", tail), Call("Prod.fst", tail), Call("Prod.fst", b));
    }

    private static Formula HalfCount(Formula a, Formula n, Formula j) => SumOver("b", Col(),
        If(And(Eq(Call("HardinA203981StripCertificate.halfCost", a, V("b")), n), Eq(Class(V("b")), j)),
            CastInt(N("1")), CastInt(N("0"))));

    private static Formula ReversedCountFormula()
    {
        var n = V("n"); var a = V("a"); var j = V("j"); var b = V("b");
        Formula RowOf(Formula x) => Call("HardinA203981StripData.columnRows", x);
        var target = Call("Equiv.swap", N("1"), N("3"), j);
        var sum = SumOver("b", Col(), If(And(Eq(Bond(RowOf(a), RowOf(b)), n), Eq(Class(b), target)),
            CastInt(N("1")), CastInt(N("0"))));
        return All("n", V("Nat"), All("a", Col(), All("j", Fin("5"), Eq(HalfCount(a, n, j), sum))));
    }

    private static Formula AllocatedCountsFormula()
    {
        var d = V("d"); var m = V("m"); var k = V("k"); var a = V("a"); var c = V("c");
        var i = V("i"); var j = V("j"); var r = V("r");
        var allocations = Call("Fin", Add(d, N("1")));
        var matrix = Call("Matrix", Fin("5"), Fin("5"), V("Int"));
        var half = All("k", allocations, All("a", Col(), All("c", Fin("5"),
            Eq(HalfCount(a, Call("Fin.val", k), c), App(m, k, Class(a), c)))));
        var representative = Call("HardinA203981StripData.representatives", i);
        var boundary = Call("HardinA203981StripData.boundary", r);
        var cost = Call("DefectTransfer.bondDefects", Call("HardinA229637RowColumn.betw", N("6")), representative, r);
        var full = SumOver("r", Row("6"), If(And(Eq(cost, d), Eq(boundary, j)), CastInt(N("1")), CastInt(N("0"))));
        var residual = Call("Fin.rev", k);
        var sum = SumOver("k", allocations,
            Call("HardinA203981StripData.classProduct", App(m, k), App(m, residual), i, j));
        return All("d", V("Nat"), All("m", Arr(allocations, matrix),
            Seq(Parenthesized(half), Sp, To, Sp, Parenthesized(All("i", Fin("15"), All("j", Fin("15"), Eq(full, sum)))))));
    }

    private static Formula ForwardTableOfStepsFormula()
    {
        var s = V("s"); var n = V("n"); var t = V("t"); var v = V("v"); var w = V("w");
        var k = V("k"); var i = V("i");
        var index = Call("Fin", Add(n, N("1")));
        var vector = Arr(s, V("Int"));
        var zero = Eq(App(w, Typed(N("0"), index)), v);
        var update = All("k", Call("Fin", n), Eq(
            Call("Matrix.vecMul", App(w, Call("Fin.castSucc", k)), t),
            App(w, Call("Fin.succ", k))));
        var value = All("i", index, Eq(Call("DefectTransfer.forward", t, v, Call("Fin.val", i)), App(w, i)));
        var body = All("n", V("Nat"), All("t", Call("Matrix", s, s, V("Int")),
            All("v", vector, All("w", Arr(index, vector),
                Seq(Parenthesized(zero), Sp, To, Sp,
                    Parenthesized(Seq(Parenthesized(update), Sp, To, Sp, Parenthesized(value))))))));
        return Seq(Forall, Sp, Typed(s, V("Type")), Sp,
            OpenBracket, Call("Fintype", s), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", s), CloseBracket, Comma, Sp, Parenthesized(body));
    }

    private static Formula ForwardStepFormula()
    {
        var k = V("k");
        Formula RowAt(Formula i) => Call("HardinA203981StripCertificate.W", i);
        return All("k", Fin("20"), Eq(
            Call("Matrix.vecMul", RowAt(Call("Fin.castSucc", k)), Call("HardinA203981StripData.T")),
            RowAt(Call("Fin.succ", k))));
    }

    private static Formula ForwardWeightsFormula()
    {
        var i = V("i"); var j = V("j");
        Formula PairWeights(Formula a, Formula b) => Call("HardinA203981StripData.unordered", a, b, j);
        return All("i", Fin("21"), All("j", Fin("15"),
            Eq(Call("HardinA203981StripCertificate.W", i, j), PairWeights(Call("HardinA203981StripCertificate.halfForwardZero", i), Call("HardinA203981StripCertificate.halfForwardZero", i)))));
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
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
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
