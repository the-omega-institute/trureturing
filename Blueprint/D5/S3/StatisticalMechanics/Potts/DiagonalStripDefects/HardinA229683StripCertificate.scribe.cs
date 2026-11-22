using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects;

internal sealed class HardinA229683StripCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683StripCertificate.";
    private const string Note = "D5/L/SpinModels/hardin2013a229683";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite checks for the order-eighteen recurrence", H("Finite checks for the order-eighteen recurrence"), Blocks(
        Describe.Lean(DescribeId.Create("two-counts"), DeclarationHandle.Create(Prefix + "two_counts"),
            H("Exact-two-cost class counts"), StatementSource.FromAuthor(Disp(All("p", Row("6"), All("j", Fin("15"), Eq(SumOver("r", Row("6"), If(And(Eq(Call("DefectTransfer.bondDefects", Call("HardinA229637RowColumn.betw", N("6")), V("p"), V("r")), N("2")), Eq(Call("HardinA203981StripData.boundary", V("r")), V("j"))), CastInt(N("1")), CastInt(N("0")))), Call("HardinA229683StripData.costTwo", Call("HardinA203981StripData.boundary", V("p")), V("j"))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The exact cost splits as zero plus two, one plus one, or two plus zero. The half-strip counts use HardinA229696Strip.finite_certificate at budget two and the lower-budget laws. Parity symmetries extend the representative counts to every source row."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("transition-counts"), DeclarationHandle.Create(Prefix + "transition_counts"),
            H("Exact remaining-budget transitions"), StatementSource.FromAuthor(Disp(All("p", Row("6"), All("d", Fin("3"), All("s", Call("Sum", Call("Sum", Fin("15"), Fin("15")), Fin("15")), Eq(SumOver("r", Row("6"), If(And(Leq(Call("DefectTransfer.bondDefects", Call("HardinA229637RowColumn.betw", N("6")), V("p"), V("r")), Call("Fin.val", V("d"))), Eq(Call("HardinA229683StripData.cl", V("r"), Sub(Call("Fin.val", V("d")), Call("DefectTransfer.bondDefects", Call("HardinA229637RowColumn.betw", N("6")), V("p"), V("r")))), V("s"))), CastInt(N("1")), CastInt(N("0")))), Call("HardinA229683StripData.T", Call("HardinA229683StripData.cl", V("p"), Call("Fin.val", V("d"))), V("s")))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("A transition within the inherited block uses its earlier count. A step to the last sector spends the full remaining budget."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("forward-inherited"), DeclarationHandle.Create(Prefix + "forward_inherited"),
            H("Forward vectors in the first two sectors"), StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(Call("Function.comp", Call("DefectTransfer.forward", Call("HardinA229683StripData.T"), Call("HardinA229683StripData.initial"), V("n")), Call("Sum.inl")), Call("DefectTransfer.forward", Call("HardinA229508StripData.T"), Call("HardinA229508StripData.initial"), V("n")))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The upper-block projection gives the one-budget transfer on the first two sectors."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("w"), DeclarationHandle.Create(Prefix + "W"),
            H("Forward vectors in total cost degree 2"), StatementSource.FromAuthor(Disp(ForwardWeightsFormula())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("Here v₂ is the 21 by 5 table of degree-two half-strip vectors. Each unordered product reads a single target coordinate, counting both orders when its classes differ. The degree-two half-strip table starts at zero and uses the last five coordinates of HardinA229696StripData.W for exponents one and two, with classes 1 and 3 exchanged at exponent two. The theorem forward_two pins the entries against the three-sector update."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("coeff"), DeclarationHandle.Create(Prefix + "coeff"),
            H("Order-eighteen coefficients"), StatementSource.FromAuthor(Disp(Eq(Typed(Call("HardinA229683StripCertificate.coeff"), Arr(Fin("18"), V("Int"))), Vec(N("282429536481", true), N("470715894135"), N("0"), N("366499782594", true), N("132368667075"), N("92909172825"), N("54520532190", true), N("6257717775", true), N("8082823950"), N("601275555", true), N("435322350", true), N("70536825"), N("7404210"), N("2206575", true), N("60075"), N("19486"), N("2010", true), N("75"))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The entries are in increasing order of input index. The zero coefficient is at lag sixteen."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("forward-two"), DeclarationHandle.Create(Prefix + "forward_two"),
            H("Last-sector forward vectors"), StatementSource.FromAuthor(Disp(All("i", Fin("21"), Eq(Call("Function.comp", Call("DefectTransfer.forward", Call("HardinA229683StripData.T"), Call("HardinA229683StripData.initial"), Call("Fin.val", V("i"))), Call("Sum.inr")), Call("HardinA229683StripCertificate.W", V("i")))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("Each update sums exact-two, exact-one and exact-zero transitions from the three sectors."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("finite-certificate"), DeclarationHandle.Create(Prefix + "finite_certificate"),
            H("Forward relation at exponent twenty"), StatementSource.FromAuthor(Disp(Eq(Call("DefectTransfer.forward", Call("HardinA229683StripData.T"), Call("HardinA229683StripData.initial"), Add(N("2"), N("18"))), SumOver("k", Fin("18"), Call("HSMul.hSMul", Call("HardinA229683StripCertificate.coeff", V("k")), Call("DefectTransfer.forward", Call("HardinA229683StripData.T"), Call("HardinA229683StripData.initial"), Add(N("2"), Call("Fin.val", V("k"))))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("Seven coordinate shifts of the order-twelve relation give the relation on the first two sectors. The last sector follows from the tabulated update."))), DescribeRole.Theorem))));
    private static Formula ForwardWeightsFormula()
    {
        var i = V("i");
        var j = V("j");
        var v0 = Call("HardinA203981StripCertificate.halfForwardZero", i);
        var v1 = Call("HardinA229508StripCertificate.halfForwardOne", i);
        var v2 = App(Seq(V("v"), Underscore, Grp(N("2"))), i);
        Formula ProductAt(Formula a, Formula b) => Call("HardinA203981StripData.unordered", a, b, j);
        return All("i", Fin("21"), All("j", Fin("15"), Eq(
            Call("HardinA229683StripCertificate.W", i, j),
            Add(Add(ProductAt(v0, v2), ProductAt(v1, v1)), ProductAt(v2, v0)))));
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
