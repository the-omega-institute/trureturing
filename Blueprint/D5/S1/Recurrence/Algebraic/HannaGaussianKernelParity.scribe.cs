using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class HannaGaussianKernelParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/HannaGaussianKernelParity.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2019a323689");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rational Gaussian kernel has symmetric integer weights and even paired coefficients.",
        H("Gaussian kernel coefficients and parity"),
        Blocks(
            Node("weight", "The recursive integer array", Disp(WeightBody()),
                "The boundary entries are 1. Every interior entry is the sum of its west, south and southwest predecessors. All values lie in the integers.", DescribeRole.Definition),
            Node("weight_odd", "Every recursive weight is odd", Disp(All("m", Nat(), All("k", Nat(),
                Call("Odd", Call("weight", V("m"), V("k")))))),
                "Nested induction gives oddness: the three predecessor entries are odd and their sum is odd.", DescribeRole.Theorem),
            Node("kernel", "The rational Gaussian kernel", Disp(All("m", Nat(),
                Equal(Call("kernel", V("m")), RationalKernel(V("m"), V("X"))))),
                "The kernel is (X + C Complex.I)^m times the formal inverse of (1 + C Complex.I*X)^(m+1). The denominator has constant coefficient 1.", DescribeRole.Definition),
            Node("kernel_expansion", "Expansion of the rational kernel", Disp(All("m", Nat(), All("p", Nat(),
                All("hp", Seq(V("p"), Sp, Neq, Sp, D(0)), Equal(
                    Call("expand", V("p"), V("hp"), Call("kernel", V("m"))),
                    RationalKernel(V("m"), Power(V("X"), V("p")))))))),
                "Replacing X by X^p commutes with the rational expression when p is nonzero.", DescribeRole.Theorem),
            Node("expansion_coefficient", "Finite coefficient extraction", Disp(ExpansionBody(false)),
                "A finite set containing every solution of p*k = N collects exactly the N-th coefficient of expand p hp f.", DescribeRole.Theorem),
            Node("shifted_expansion_coefficient", "Finite shifted coefficient extraction", Disp(ExpansionBody(true)),
                "For d at most N, the coefficient of X^d times expand p hp f is the sum over d+p*k = N.", DescribeRole.Theorem),
            Node("supported_matrix_integral", "Symmetric support and diagonal parity", Disp(SupportedBody()),
                "On any finite set of natural indices, a symmetric decidable support selects an integer coefficient sum. Its difference from the supported integer diagonal sum is even. The coefficient identity is obtained by induction from the rational kernel; symmetry pairs all off-diagonal terms.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Q(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Ints() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Complexes() => Seq(Mathbb, Grp(V("C")));
    private static Formula Series() => Call("PowerSeries", Complexes());
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Power(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula SumOn(string n, Formula s, Formula body) => Seq(
        new Formula.Subscript(Sum, Seq(V(n), Sp, InMacro, Sp, s)), Sp, Parenthesized(body));
    private static Formula If(Formula test, Formula yes, Formula no) => Seq(
        Named("if"), Sp, Parenthesized(test), Sp, Named("then"), Sp, yes,
        Sp, Named("else"), Sp, no);
    private static Formula Coeff(Formula n, Formula f) => Call("coeff", n, f);
    private static Formula UnitI() => Q("Complex", "I");
    private static Formula RationalKernel(Formula m, Formula x) => Mul(
        Power(Add(x, App(V("C"), UnitI())), m),
        Power(Power(Add(D(1), Mul(App(V("C"), UnitI()), x)), Add(m, D(1))), Seq(Minus, D(1))));


    private static Formula WeightBody()
    {
        var first = Equal(Call("weight", D(0), V("k")), D(1));
        var second = Equal(Call("weight", Add(V("m"), D(1)), D(0)), D(1));
        var rhs = Add(Add(Call("weight", V("m"), Add(V("k"), D(1))),
            Call("weight", Add(V("m"), D(1)), V("k"))), Call("weight", V("m"), V("k")));
        var third = Equal(Call("weight", Add(V("m"), D(1)), Add(V("k"), D(1))), rhs);
        return All("m", Nat(), All("k", Nat(), And(first, And(second, third))));
    }
    private static Formula ExpansionBody(bool shifted)
    {
        var exponent = shifted ? Add(V("d"), Mul(V("p"), V("k"))) : Mul(V("p"), V("k"));
        var equation = Equal(exponent, V("N"));
        var extracted = Call("expand", V("p"), V("hp"), V("f"));
        if (shifted) extracted = Mul(Power(V("X"), V("d")), extracted);
        var support = All("k", Nat(), Imp(equation, Seq(V("k"), Sp, InMacro, Sp, V("s"))));
        var equality = Equal(Coeff(V("N"), extracted), SumOn("k", V("s"),
            If(equation, Coeff(V("k"), V("f")), D(0))));
        var body = All("f", Series(), All("s", Call("Finset", Nat()), Imp(support, equality)));
        if (shifted) body = Imp(Seq(V("d"), Sp, Leq, Sp, V("N")), body);
        body = All("hp", Seq(V("p"), Sp, Neq, Sp, D(0)), body);
        body = All("p", Nat(), All("N", Nat(), body));
        return shifted ? All("d", Nat(), body) : body;
    }
    private static Formula SupportedBody()
    {
        var symmetric = All("m", Nat(), All("k", Nat(), Seq(
            App(V("P"), V("m"), V("k")), Sp, Iff, Sp, App(V("P"), V("k"), V("m")))));
        var total = SumOn("m", V("s"), SumOn("k", V("s"),
            If(App(V("P"), V("m"), V("k")), Coeff(V("k"), Call("kernel", V("m"))), D(0))));
        var diagonal = SumOn("m", V("s"),
            If(App(V("P"), V("m"), V("m")), Call("weight", V("m"), V("m")), D(0)));
        var even = Call("Even", new Formula.Binary(V("z"), FormulaBinaryOperator.Subtract, diagonal));
        var conclusion = Some("z", Ints(), And(Equal(total, Cast(V("z"), Complexes())), even));
        var body = Seq(OpenBracket, Call("DecidableRel", V("P")), CloseBracket, Comma, Sp, Imp(symmetric, conclusion));
        return All("s", Call("Finset", Nat()), All("P", Arrow(Nat(), Arrow(Nat(), V("Prop"))), body));
    }
}
