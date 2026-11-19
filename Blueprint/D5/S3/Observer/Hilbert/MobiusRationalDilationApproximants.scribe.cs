using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Hilbert;

internal sealed class MobiusRationalDilationApproximantsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.";
    private static Formula N => F.Id("N");
    private static Formula n => F.Id("n");
    private static Formula j => F.Id("j");
    private static Formula u => F.Id("u");
    private static Formula J => Seq(j, Plus, D(1));
    private static Formula NN => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula RR => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula QQ => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Sq(Formula a) => Seq(a, Caret, Grp(D(2)));
    private static Formula Inv(Formula a) => Div(D(1), a);
    private static Formula SumTo(Formula count, Formula term) => Seq(
        new Formula.Subscript(Sum, Seq(D(0), Le, Sp, j, Lt, Sp, count)), term);
    private static Formula Block(Formula k) => Seq(Left, OpenBracket, Inv(Seq(k, Plus, D(1))),
        Comma, Inv(k), Right, Close);
    private static Formula Indicator(Formula set, Formula x) => Seq(
        new Formula.Subscript(Seq(Mathbf, Grp(D(1))), set), Open, x, Close);
    private static Formula Interval => Seq(Open, D(0), Comma, D(1), Close);
    private static Formula Integral(Formula term) => Seq(
        new Formula.Subscript(Int, Interval), term, Sp, F.Id("d"), u);
    private static Formula Bind(Formula k) => Seq(Forall, Sp, k, InMacro, Sp, NN, Comma, Sp);
    private static Formula Positive(Formula k) => Seq(D(1), Le, Sp, k, Rightarrow, Sp);
    private static Formula InUnit => Seq(Forall, Sp, u, InMacro, Sp, Interval, Comma, Sp);
    private static Formula Error => Sq(Seq(Open, D(1), Minus, Call("F", N, u), Close));
    private static Formula MuJ => Call("mu", J);
    private static Formula MJ => Call("m", J);

    private static DocumentBlock Entry(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
            DescribeId.Create("mobius-rational-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite rational Mobius dilations have exact squared error equal to the reciprocal coefficient energy.",
        H("Finite Mobius rational-dilation approximants"),
        Blocks(
            Paragraph(Text("Let mu(k) be the integer arithmetic Moebius function. muQ and muR "
                + "are its rational and real casts. Every finite coefficient and every dilation "
                + "parameter n/(j+1) is formed in Q before applying the canonical embedding into R. "
                + "All integrals below use Lebesgue volume; (0,1) denotes the open unit interval. "
                + "The natural indices include zero, and a sum over an empty range is zero.")),
            Entry("phi", "The literal rational dictionary", Seq(
                Forall, Sp, Alpha, InMacro, Sp, QQ, Comma, Forall, Sp, u, InMacro, Sp, RR, Comma,
                Call("phi", Alpha, u), Eq, Div(Seq(Call("fract", Seq(Alpha, Sp, u)), Minus, u), u)),
                "The fractional part is Int.fract, and alpha is rational. Division is Lean's total "
                + "real division, so this definition also assigns a value at u=0. Pointwise "
                + "identities used below impose 0<u<1.", DescribeRole.Definition),
            Entry("m", "Rational finite Moebius coefficients", Seq(Bind(n), Call("m", n), Eq,
                SumTo(n, Div(MuJ, J))),
                "m(n) is the rational sum of mu(k)/k for 1<=k<=n. In particular m(1)=1.",
                DescribeRole.Definition),
            Entry("H", "Finite rational dilations", Seq(Bind(n), Forall, Sp, u, InMacro, Sp, RR,
                Comma, Call("H", n, u), Eq,
                SumTo(n, Seq(MuJ, Call("phi", Div(n, J), u)))),
                "H(n,u) uses exactly the rational parameters n/(j+1), weighted by the real "
                + "Moebius coefficients. No real-parameter closure is used.", DescribeRole.Definition),
            Entry("e", "Half-open reciprocal blocks", Seq(Bind(n), Forall, Sp, u, InMacro, Sp, RR,
                Comma, Call("e", n, u), Eq, Inv(u), Indicator(Block(n), u)),
                "e(n,u) is u inverse times the indicator of [1/(n+1),1/n). The left endpoint "
                + "is included and the right endpoint excluded. Its definition is total for n=0; "
                + "the block identities assume n>=1.", DescribeRole.Definition),
            Entry("S", "Rational coefficient energy", Seq(Bind(N), Call("S", N), Eq,
                SumTo(N, Sq(MJ))),
                "S(N) is rational and sums the squares of m(1) through m(N). A displayed real "
                + "identity uses its canonical real cast.", DescribeRole.Definition),
            Entry("F", "The normalized finite approximant", Seq(Bind(N), Forall, Sp, u,
                InMacro, Sp, RR, Comma, Call("F", N, u), Eq, Inv(Call("S", N)),
                SumTo(N, Seq(MJ, Open, Call("H", Seq(j, Plus, D(2)), u), Minus,
                    Call("H", J, u), Close))),
                "F is defined for every natural N and real u. The theorems about its error "
                + "assume N>=1, which makes S(N) strictly positive.", DescribeRole.Definition),
            Entry("floorMoebiusSum", "The literal finite floor sum", Seq(Bind(n), Forall, Sp,
                u, InMacro, Sp, RR, Comma, Call("floorMoebiusSum", n, u), Eq,
                SumTo(n, Seq(MuJ, Lfloor, Div(n, J), u, Rfloor))),
                "The floor is Int.floor, cast to R after evaluation. The dilation n/(j+1) "
                + "is still formed in Q before coercion.", DescribeRole.Definition),
            Entry("indicatorThreshold", "The threshold indicator", Seq(Bind(n), Forall, Sp,
                u, InMacro, Sp, RR, Comma, Call("indicatorThreshold", n, u), Eq,
                Indicator(Seq(OpenBracket, D(1), Comma, Infty, Close), Seq(n, u))),
                "indicatorThreshold(n,u) is 1 when 1<=n*u and 0 otherwise.", DescribeRole.Definition),
            Entry("floor_moebius_bridge", "The finite floor bridge", Seq(Bind(n), D(0), Lt,
                n, Rightarrow, InUnit, Call("floorMoebiusSum", n, u), Eq,
                Call("indicatorThreshold", n, u)),
                "For every positive natural n and every real u in (0,1), the finite floor "
                + "sum equals the exact threshold indicator. The arithmetic input is the "
                + "existing MoebiusLogarithmic floor_cancellation identity at the real cutoff n*u. "
                + "Converting the rational floors to natural division and removing zero terms "
                + "above floor(n*u) supplies the bridge."),
            Entry("h_step", "The exact block recurrence", Seq(Bind(n), Positive(n), InUnit,
                Call("H", Seq(n, Plus, D(1)), u), Minus, Call("H", n, u), Eq,
                Call("m", n), Minus, Call("e", n, u)),
                "For every natural n>=1 and u in (0,1), H(n+1,u)-H(n,u)=m(n)-e(n,u). "
                + "Subtracting the two threshold indicators gives precisely the half-open "
                + "block, including the n=1 boundary."),
            Entry("block_integral", "Each block has squared integral one", Seq(Bind(n),
                Positive(n), Integral(Sq(Call("e", n, u))), Eq, D(1)),
                "For every natural n>=1, integrating u to the power -2 over "
                + "[1/(n+1),1/n) gives 1. Its support lies in (0,1), and changing an endpoint "
                + "does not change the Lebesgue integral."),
            Entry("block_orthogonality", "Distinct blocks are orthogonal", Seq(Bind(F.Id("p")),
                Bind(n), Positive(F.Id("p")), Positive(n), F.Id("p"), Neq, Sp, n, Rightarrow,
                Integral(Seq(Call("e", F.Id("p"), u), Call("e", n, u))), Eq, D(0)),
                "For every two distinct positive natural indices, the half-open supports "
                + "are disjoint. Their product vanishes at every real u, so its integral is zero."),
            Entry("s_pos", "Strict positivity of the energy", Seq(Bind(N), Positive(N),
                D(0), Lt, Sp, Call("S", N)),
                "For every N>=1, the nonnegative square sum contains m(1)^2=1. "
                + "The theorem states positivity of the real cast of S(N)."),
            Entry("error_sq_integrable", "Integrability of the squared error", Seq(Bind(N),
                Positive(N), Call("Integrable", Seq(Open, u, Mapsto, Sp, Error, Close),
                    Seq(Call("volume"), Mid, Interval))),
                "For every N>=1, u |-> (1-F(N,u))^2 is integrable for volume restricted "
                + "to (0,1), exactly IntegrableOn in Lean. On this interval, 1-F(N,u) is "
                + "S(N) inverse times the sum of m(j+1)e(j+1,u). Disjointness eliminates "
                + "the cross terms; each remaining squared block has compact support away from zero."),
            Entry("finite_error", "The exact finite squared error", Seq(Bind(N), Positive(N),
                Integral(Error), Eq, Div(D(1), Call("S", N))),
                "For every natural N>=1, the squared error integral is exactly 1/S(N). "
                + "The recurrence expresses the error as a finite weighted block sum. "
                + "Disjoint supports and the unit squared integrals reduce its integral to "
                + "S(N)^(-2) times S(N). The theorem itself is exactly this finite identity."),
            Paragraph(Text("The coefficient energy also gives a convergence application. "
                + "Set a(n)=(m(n):R). Casting the finite rational sum and specializing "
                + "Finset.sum_Ico_add' at f(k)=mu(k)/k, 0, n, 1 gives "
                + "(m(n):R)=sum_{k=1}^n mu(k)/k. Hence a(Nat.floor(x)) is exactly "
                + "MobiusPartialSumL2Divergence.mobiusPartialSum(x). If the series "
                + "sum_{n>=0} a(n+1)^2 were summable, "
                + "Mathlib's integrableOn_iUnion_of_summable_integral_norm, applied to "
                + "x |-> a(Nat.floor(x))^2 on the unit cells [n+1,n+2), gives integrability "
                + "on [1,infinity). Nat.floor_eq_on_Ico identifies each cell "
                + "value as a(n+1), whose square is its norm integral. Nat.floor_eq_iff', "
                + "Nat.mem_range_succ and Nat.floor_pos identify the union with [1,infinity). "
                + "Restricting to (1,infinity) and applying memLp_two_iff_integrable_sq "
                + "to the measurable floor composition gives L2 membership, with no "
                + "condition on a(0), contradicting "
                + "MobiusPartialSumL2Divergence.mobiusPartialSum_not_memLp. Thus the "
                + "nonnegative coefficient-square series is not summable. Its partial sums "
                + "(S(N):R) tend to positive infinity, as does S(N) in Q, and "
                + "1/(S(N):R) tends to zero. Applying finite_error eventually for N>=1 "
                + "shows that the integral over (0,1) of (1-F(N,u))^2 tends to zero.")),
            Paragraph(Text("This application has genuine Lp content: F(N) is measurable, "
                + "and error_sq_integrable makes u |-> 1-F(N,u) a MemLp function of "
                + "exponent 2 for every N>=1. Write E(N) for the toLp class of "
                + "u |-> 1-F(N+1,u) in Lp R 2 for volume restricted to (0,1). "
                + "L2.inner_def and MemLp.coeFn_toLp identify its squared norm with "
                + "the squared error integral, so ||E(N)||^2=1/(S(N+1):R). "
                + "Continuity of the square root gives ||E(N)|| -> 0 and E(N) -> 0 "
                + "in Lp. The shift by one ensures every index is positive; "
                + "no explicit rate in N is supplied.")),
            Paragraph(Text("These convergence statements concern the direct rational-dilation "
                + "dictionary phi(alpha,u)=(fract(alpha*u)-u)/u defined here. "
                + "The genuine Nyman-Beurling family in NymanUnitIntervalMellin uses "
                + "fract(theta/x), with 0<theta<=1 and coefficient balance "
                + "sum c_j*theta_j=0. No bridge placing the present approximants in that "
                + "family or its closure is supplied, and no Riemann-hypothesis "
                + "consequence follows from this application."))), [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Arith/MoebiusLogarithmic/ReciprocalBound"))
        ]));
}
