using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class InfiniteCalibrationControlDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/InfiniteCalibrationControl.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One positive real parameter gives a strictly feasible analytic scalar control "
            + "whose simultaneous value and derivative calibration points are exactly "
            + "the positive-natural sequence converging to one.",
        H("Infinite Calibration Sets for Analytic Scalar Controls"),
        Blocks(
            Paragraph(Text(
                "All scalar parameters are real. Assume 0 < a < 1, 0 < delta, "
                    + "delta < (1-a)/4, delta < (1-a squared)/16, and "
                    + "0 < b < 1-a/(1-delta). The delta bound involving a squared "
                    + "is retained even though it is not needed in the scalar argument. "
                    + "The domain of physicality and calibration is the open interval (a,1).")),
            Paragraph(Text(
                "Use the scalar parameters L(a)=1-a, lam(a,delta)=L(a)-delta, "
                    + "gamma(a,delta)=lam(a,delta)/(2 delta), and "
                    + "center(a,delta)=lam(a,delta)/L(a). The radius is "
                    + "sqrt(a/lam(a,delta)) times sqrt((1-p)/p). The energy at s is "
                    + "s squared plus gamma squared times (s+1/s-2) squared, "
                    + "and beta(p)=1/(2 p (1-p)). Division uses total real inversion; "
                    + "all denominators used on the stated interval are nonzero.")),
            Describe.Lean(
                DescribeId.Create("oscillatory-phase"),
                DeclarationHandle.Create(Module + "omega"),
                H("The oscillatory phase"),
                StatementSource.FromAuthor(PhaseStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive b the phase increases without bound as p approaches "
                        + "one from below."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("decaying-amplitude"),
                DeclarationHandle.Create(Module + "amplitude"),
                H("The decaying amplitude"),
                StatementSource.FromAuthor(AmplitudeStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For b > 0 and 0 < p < 1 the amplitude is positive. "
                        + "It tends to zero as p tends to one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("oscillatory-interpolant"),
                DeclarationHandle.Create(Module + "phaseH"),
                H("The oscillatory interpolant"),
                StatementSource.FromAuthor(InterpolantStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The bounded sine factor and decaying amplitude make this "
                        + "interpolant tend to one at the upper endpoint."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nonnegative-damping"),
                DeclarationHandle.Create(Module + "phaseD"),
                H("The nonnegative damping factor"),
                StatementSource.FromAuthor(DampingStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The damping factor is a square. Below one, with b positive, "
                        + "it vanishes exactly at points 1-b/n with n a positive natural number."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("analytic-control"),
                DeclarationHandle.Create(Module + "phaseControl"),
                H("The scalar control"),
                StatementSource.FromAuthor(ScalarStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When k is positive the denominator is at least one. "
                        + "The control is a convex combination of the interpolant "
                        + "and the fixed center, with interpolant weight 1/(1+k phaseD(b,p))."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("calibration-nodes"),
                DeclarationHandle.Create(Module + "phaseNode"),
                H("The positive-natural calibration sequence"),
                StatementSource.FromAuthor(NodeStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The definition is total on natural numbers. Only positive indices "
                        + "occur in the calibration set. Under the parameter hypotheses, "
                        + "these nodes lie above a/(1-delta), are strictly increasing, "
                        + "and converge to one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("infinite-scalar-control"),
                DeclarationHandle.Create(Module + "InfiniteScalarControl"),
                H("All scalar control requirements for the same parameter"),
                StatementSource.FromAuthor(ControlStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The conjunction requires k > 0, positivity and strict physicality "
                        + "at every point of (a,1), analyticity in a neighborhood of each "
                        + "point of that interval, and the complete simultaneous jet "
                        + "characterization. Value one alone does not characterize the nodes: "
                        + "the derivative must also equal beta at the same point."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("exact-infinite-calibration"),
                DeclarationHandle.Create(Module + "result"),
                H("One finite parameter realizes the entire infinite calibration set"),
                StatementSource.FromAuthor(ResultStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The center lies strictly between three quarters and one and is "
                            + "strictly feasible throughout [a,1]. The energy is convex "
                            + "on the positive half-line. Near one, the interpolant tends "
                            + "to one and radius squared times its energy tends to zero. "
                            + "This gives a whole terminal interval where every positive "
                            + "k is feasible by convexity.")),
                    Paragraph(Text(
                        "On the remaining compact interval, zeros of the damping factor "
                            + "give value one above the strict feasibility threshold. "
                            + "At every other point, increasing k makes the control tend "
                            + "to the strictly feasible center. The open sets of feasible "
                            + "points increase with k; a directed compactness argument "
                            + "selects one positive real k for the entire complement. "
                            + "Together these intervals give full physicality on (a,1).")),
                    Paragraph(Text(
                        "Analyticity holds for every positive k because the constituent "
                            + "functions are analytic on (a,1) and the denominator is positive. "
                            + "The half-phase sine vanishes exactly at the positive-natural "
                            + "nodes. At these zeros the control has value one and derivative "
                            + "beta. At any other point where the control equals one, "
                            + "differentiation and the double-angle identities give a "
                            + "strictly negative derivative. Since beta is positive on "
                            + "the interval, such extra roots cannot be calibration jets. "
                            + "These conclusions apply to the same k chosen for physicality."))),
                DescribeRole.Theorem))));

    private static Formula RealType => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula NaturalType => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula A => F.Id("a");
    private static Formula DeltaValue => F.Id("delta");
    private static Formula B => F.Id("b");
    private static Formula K => F.Id("k");
    private static Formula P => F.Id("p");
    private static Formula N => F.Id("n");
    private static Formula OneMinusP => Seq(Num(1), Sp, Minus, Sp, P);
    private static Formula Function => Call("phaseControl", A, DeltaValue, B, K);
    private static Formula ControlAt => Call("phaseControl", A, DeltaValue, B, K, P);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Quotient(Formula x, Formula y) => Seq(Frac, Grp(x), Grp(y));
    private static Formula Square(Formula x) => Seq(Grp(x), Caret, Grp(Num(2)));
    private static Formula Conjunction(params Formula[] clauses) =>
        Seq(clauses.SelectMany((clause, index) => index == 0
            ? new[] { clause }
            : new[] { Sp, Land, Sp, clause }).ToArray());
    private static Formula RealQuantifiers(params Formula[] variables) => Seq(
        Forall, Sp,
        Seq(variables.SelectMany((variable, index) => index == 0
            ? new[] { variable }
            : new[] { Comma, Sp, variable }).ToArray()),
        Colon, Sp, RealType, Comma, Sp);

    private static Formula PhaseStatement() => Disp(Seq(
        RealQuantifiers(B, P), Call("omega", B, P), Sp, Eq, Sp,
        Quotient(Seq(Num(2), Sp, Pi, Sp, B), OneMinusP)));

    private static Formula AmplitudeStatement() => Disp(Seq(
        RealQuantifiers(B, P), Call("amplitude", B, P), Sp, Eq, Sp,
        Quotient(OneMinusP, Seq(Num(4), Sp, Pi, Sp, B, Sp, P))));

    private static Formula InterpolantStatement() => Disp(Seq(
        RealQuantifiers(B, P), Call("phaseH", B, P), Sp, Eq, Sp,
        Num(1), Sp, Plus, Sp, Call("amplitude", B, P), Sp,
        Call("sin", Call("omega", B, P))));

    private static Formula DampingStatement() => Disp(Seq(
        RealQuantifiers(B, P), Call("phaseD", B, P), Sp, Eq, Sp,
        Square(Call("sin", Seq(Quotient(Num(1), Num(2)), Sp, Call("omega", B, P))))));

    private static Formula ScalarStatement() => Disp(Seq(
        RealQuantifiers(A, DeltaValue, B, K, P), ControlAt, Sp, Eq, Sp,
        Quotient(
            Seq(Call("phaseH", B, P), Sp, Plus, Sp, K, Sp,
                Call("center", A, DeltaValue), Sp, Call("phaseD", B, P)),
            Seq(Num(1), Sp, Plus, Sp, K, Sp, Call("phaseD", B, P)))));

    private static Formula NodeStatement() => Disp(Seq(
        RealQuantifiers(B), Forall, Sp, N, Colon, Sp, NaturalType, Comma, Sp,
        Call("phaseNode", B, N), Sp, Eq, Sp, Num(1), Sp, Minus, Sp, Quotient(B, N)));

    private static Formula Requirements()
    {
        Formula domain = Call("Ioo", A, Num(1));
        Formula physicality = Seq(Forall, Sp, P, Sp, InMacro, Sp, domain, Comma, Sp,
            Parenthesized(Conjunction(
                Seq(Num(0), Sp, Lt, Sp, ControlAt),
                Seq(Square(Call("radius", A, DeltaValue, P)), Sp,
                    Call("energy", A, DeltaValue, ControlAt), Sp, Lt, Sp, Num(1)))));
        Formula jets = Seq(Forall, Sp, P, Sp, InMacro, Sp, domain, Comma, Sp,
            Parenthesized(Seq(
                Parenthesized(Conjunction(
                    Seq(ControlAt, Sp, Eq, Sp, Num(1)),
                    Seq(Call("deriv", Function, P), Sp, Eq, Sp, Call("beta", P)))),
                Sp, Iff, Sp,
                Parenthesized(Seq(Exists, Sp, N, Colon, Sp, NaturalType, Comma, Sp,
                    Num(0), Sp, Lt, Sp, N, Sp, Land, Sp,
                    P, Sp, Eq, Sp, Call("phaseNode", B, N))))));
        return Conjunction(
            Seq(Num(0), Sp, Lt, Sp, K),
            Parenthesized(physicality),
            Call("AnalyticOnNhd", RealType, Function, domain),
            Parenthesized(jets));
    }

    private static Formula ControlStatement() => Disp(Seq(
        RealQuantifiers(A, DeltaValue, B, K),
        Call("InfiniteScalarControl", A, DeltaValue, B, K), Sp, Iff, Sp,
        Parenthesized(Requirements())));

    private static Formula ResultStatement()
    {
        Formula assumptions = Conjunction(
            Seq(Num(0), Sp, Lt, Sp, A),
            Seq(A, Sp, Lt, Sp, Num(1)),
            Seq(Num(0), Sp, Lt, Sp, DeltaValue),
            Seq(DeltaValue, Sp, Lt, Sp,
                Quotient(Seq(Num(1), Sp, Minus, Sp, A), Num(4))),
            Seq(DeltaValue, Sp, Lt, Sp,
                Quotient(Seq(Num(1), Sp, Minus, Sp, Square(A)), Num(16))),
            Seq(Num(0), Sp, Lt, Sp, B),
            Seq(B, Sp, Lt, Sp, Num(1), Sp, Minus, Sp,
                Quotient(A, Seq(Num(1), Sp, Minus, Sp, DeltaValue))));
        return Disp(Seq(RealQuantifiers(A, DeltaValue, B),
            Parenthesized(assumptions), Sp, Rightarrow, Sp,
            Exists, Sp, K, Colon, Sp, RealType, Comma, Sp,
            Parenthesized(Requirements())));
    }
}
