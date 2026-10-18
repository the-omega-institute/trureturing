using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class A400361PillaiMeanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/A400361PillaiMean.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/oeis2026a400361");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The classical Pillai mean and elementary kernels used by the full A400361 proof.",
        H("Pillai mean and shared kernels"),
        Blocks(
            Paragraph(Text("P(n) is the original Pillai gcd sum. The second-order "
                + "Pillai asymptotic is classical mathematics and is not a separate "
                + "open-problem resolution. The full A400361 proof consumes this "
                + "mean and the elementary finite-sum and limit kernels below.")),
            Node("realZeta", "The real restriction of zeta", All("x", "Real", Equal(
                Call("zetaR", V("x")), Call("re", Call("zeta", Call("ofReal", V("x")))))),
                "For every real x, zetaR(x) is the real part of complex zeta at x. "
                + "Its real derivative at two equals the real part of the complex "
                + "derivative; the proof uses differentiability at two.", DescribeRole.Definition),
            Node("kernel_one_prefix", "The telescoping kernel prefix", All("N", "Nat", Equal(
                Sum("j", Call("range", V("N")), Kernel()),
                Sub(D(1), Div(D(1), Add(V("N"), D(1)))))),
                "For every natural N, the sum from j=0 to N-1 of "
                + "1/((j+1)*(j+2)) is 1-1/(N+1), including the empty prefix. "
                + "It is the reciprocal specialization of Mathlib's Finset.sum_range_sub'. "
                + "This identity is consumed by the kernel sum and reciprocal-square tail.", DescribeRole.Theorem),
            Node("hasSum_kernel_one", "The telescoping kernel series", Disp(Call("HasSum",
                Seq(V("j"), Sp, Mapsto, Sp, Kernel()), D(1))),
                "The index j ranges over all natural numbers. The nonnegative "
                + "kernel series sums to one. It supplies both the d=1 digamma "
                + "boundary and the reciprocal-square tail estimate.", DescribeRole.Theorem),
            Node("sum_Icc_cast", "The triangular sum", All("q", "Nat", Equal(
                Sum("r", Call("Icc", D(1), V("q")), Call("toReal", V("r"))),
                Div(Mul(Call("toReal", V("q")), Add(Call("toReal", V("q")), D(1))), D(2)))),
                "Every positive integer through q is included. The equality "
                + "is in the reals and holds also at q=0. It follows from Mathlib's "
                + "Finset.sum_range_id_mul_two by casting and changing the summation interval.", DescribeRole.Theorem),
            Node("quotient_ratio_limit", "The quotient ratio limit", QuotientFormula(),
                "N tends to infinity through all natural numbers. The parameter d "
                + "is any natural number, including zero: natural division and real "
                + "inversion both use their total zero conventions there. Positive "
                + "parameters give the usual floor quotient ratio.", DescribeRole.Theorem),
            Node("pillai_second_term", "The classical second-order Pillai mean", PillaiFormula(),
                "The exact weighted divisor-pair hyperbola identity at floor(sqrt(N)) "
                + "and the harmonic-number limit give W(N)/N^2-log(N)/2 -> gamma-1/4. "
                + "The original Pillai divisor formula yields its Mobius convolution. "
                + "Dominated convergence and explicit quotient-square and tail estimates "
                + "transfer the full second term without restricting N. The actual "
                + "zeta-Mobius Dirichlet identity and its derivative at two evaluate "
                + "the two Mobius moments, supplying the literal zeta derivative. "
                + "This result is consumed by the complete A400361 theorem.", DescribeRole.Theorem))));

    private static Formula QuotientFormula()
    {
        var numerator = Call("toReal", Call("natDiv", V("N"), V("d")));
        var observation = Seq(V("N"), Sp, Mapsto, Sp, Div(numerator, Call("toReal", V("N"))));
        return All("d", "Nat", Call("TendstoAtTop", observation, Div(D(1), Call("toReal", V("d")))));
    }
    private static Formula PillaiFormula()
    {
        var numerator = Sum("n", Call("Icc", D(1), V("N")), Call("toReal", Call("P", V("n"))));
        var ratio = Div(numerator, Pow(Call("toReal", V("N")), 2));
        var main = Mul(Div(D(3), Pow(V("pi"), 2)), Call("log", V("N")));
        var observation = Seq(V("N"), Sp, Mapsto, Sp, Sub(ratio, main));
        var first = Add(Div(Seq(Minus, D(1)), D(2)), Mul(D(2), V("gamma")));
        var correction = Div(Mul(D(6), Call("derivZetaR", D(2))), Pow(V("pi"), 2));
        var limit = Mul(Div(D(3), Pow(V("pi"), 2)), Sub(first, correction));
        return Disp(Call("TendstoAtTop", observation, limit));
    }

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("a400361-pillai-" + name.ToLowerInvariant().Replace("_", "-")), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), role);
    private static Formula Kernel() => Div(D(1), Mul(Add(V("j"), D(1)), Add(V("j"), D(2))));
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, int n) => new Formula.Power(a, D((byte)n));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula All(string n, string type, Formula body) => Disp(Seq(
        Forall, Sp, V(n), Sp, InMacro, Sp, Call(type), Comma, Sp, body));
    private static Formula Sum(string n, Formula range, Formula body) => Seq(
        new Formula.Subscript(F.Sum, Seq(V(n), Sp, InMacro, Sp, range)), Sp, Grp(body));
}
