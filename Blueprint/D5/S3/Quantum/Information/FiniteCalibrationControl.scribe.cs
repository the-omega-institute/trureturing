using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class FiniteCalibrationControlDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/FiniteCalibrationControl.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite set above the fixed threshold is exactly the calibration jet set of "
            + "a strictly feasible rational scalar control with degree at most twice its cardinality.",
        H("Finite Calibration Sets for Rational Scalar Controls"),
        Blocks(
            Paragraph(Text(
                "The parameters a and delta are real, with 0 < a < 1, 0 < delta, "
                    + "delta < (1-a)/4, and delta < (1-a squared)/16. The last inequality "
                    + "is retained among the hypotheses although the scalar proof does not use it. "
                    + "The finite set S consists of arbitrary real nodes i satisfying "
                    + "a/(1-delta) < i < 1; its cardinality has no fixed upper bound.")),
            Paragraph(Text(
                "The scalar parameters are L(a) = 1-a, lam(a,delta) = L(a)-delta, "
                    + "gamma(a,delta) = lam(a,delta)/(2 delta), and "
                    + "center(a,delta) = lam(a,delta)/L(a). The radius is the product "
                    + "of the square roots of a/lam(a,delta) and (1-p)/p. "
                    + "The energy at s is s squared plus gamma squared times "
                    + "the square of s + 1/s - 2. The required derivative is "
                    + "beta(p) = 1/(2 p (1-p)), taken with respect to p.")),
            Describe.Lean(
                DescribeId.Create("full-scalar-control"),
                DeclarationHandle.Create(Module + "FullControl"),
                H("All scalar control requirements"),
                StatementSource.FromAuthor(ControlStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Here N and D are real polynomials and s(p) denotes N(p)/D(p). "
                            + "Both natural degrees are at most twice card S. D is strictly "
                            + "positive on the entire real line. For every p in the closed "
                            + "interval [a,1], s(p) is positive and radius squared times "
                            + "energy is strictly less than one, including both endpoints.")),
                    Paragraph(Text(
                        "The quotient is real analytic in a neighborhood of every point of "
                            + "(a,1). At each point of that open interval, value one together "
                            + "with derivative beta(p) holds if and only if p belongs to S. "
                            + "This specifies the complete set of first jets. When S is "
                            + "empty, the quotient equals center(a,delta) at every real p."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-calibration-control"),
                DeclarationHandle.Create(Module + "result"),
                H("Every prescribed finite set is realized exactly"),
                StatementSource.FromAuthor(ResultStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let P be the nodal polynomial of S and let B_i be its Lagrange "
                            + "basis polynomials. The polynomial hermite(S) is one plus the "
                            + "sum of beta(i) times (X-i) times B_i squared. Its value is "
                            + "one and its derivative is beta(i) at every prescribed node.")),
                    Paragraph(Text(
                        "For nonempty S the construction uses N = H + k center P squared "
                            + "and D = 1 + k P squared, with one positive real k. The center "
                            + "is strictly feasible throughout [a,1]. Convexity of the "
                            + "energy preserves feasibility as k increases. Pointwise "
                            + "eventual feasibility gives a directed open cover of the "
                            + "compact interval; compactness supplies a single k valid "
                            + "at every point. The polynomial degrees satisfy the stated bound.")),
                    Paragraph(Text(
                        "Away from S, (H-1)/P squared is a sum of positive weights divided "
                            + "by p-i. Its derivative is strictly negative. At every "
                            + "additional root where s(p)=1, the derivative of s is "
                            + "therefore strictly negative, whereas beta(p) is positive "
                            + "on (a,1). Such roots cannot supply additional calibration "
                            + "jets. For empty S take N constant equal to the center and D=1; "
                            + "the center is strictly below one.")),
                    Paragraph(Text(
                        "The conclusion concerns the rational scalar control and its complete "
                            + "calibration jet set. Constructing a completely positive, trace "
                            + "preserving processor, an actual pure-state program, its quantum "
                            + "Fisher information, and a minimum program dimension requires "
                            + "separate operator and state results. Those conclusions are "
                            + "not asserted here."))),
                DescribeRole.Theorem))));

    private static Formula RealType => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula A => F.Id("a");
    private static Formula DeltaValue => F.Id("delta");
    private static Formula Nodes => F.Id("S");
    private static Formula Point => F.Id("p");
    private static Formula N => F.Id("N");
    private static Formula D => F.Id("D");
    private static Formula SAt(Formula p) => Call("s", p);
    private static Formula Full => Call("FullControl", A, DeltaValue, Nodes, N, D);
    private static Formula Quotient(Formula x, Formula y) => Seq(Frac, Grp(x), Grp(y));
    private static Formula Square(Formula x) => Seq(Grp(x), Caret, Grp(Num(2)));
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Conjunction(params Formula[] clauses) =>
        Seq(clauses.SelectMany((clause, index) => index == 0
            ? new[] { clause }
            : new[] { Sp, Land, Sp, clause }).ToArray());

    private static Formula ControlStatement()
    {
        Formula degreeBound = Seq(Num(2), Sp, Call("card", Nodes));
        Formula globalDenominator = Seq(Forall, Sp, Point, Colon, Sp, RealType, Comma, Sp,
            Num(0), Sp, Lt, Sp, Call("D", Point));
        Formula feasible = Seq(Forall, Sp, Point, Sp, InMacro, Sp, Call("Icc", A, Num(1)),
            Comma, Sp, Parenthesized(Conjunction(
                Seq(Num(0), Sp, Lt, Sp, SAt(Point)),
                Seq(Square(Call("radius", A, DeltaValue, Point)), Sp,
                    Call("energy", A, DeltaValue, SAt(Point)), Sp, Lt, Sp, Num(1)))));
        Formula exactJets = Seq(Forall, Sp, Point, Sp, InMacro, Sp, Call("Ioo", A, Num(1)),
            Comma, Sp, Open, SAt(Point), Sp, Eq, Sp, Num(1), Sp, Land, Sp,
            Call("deriv", F.Id("s"), Point), Sp, Eq, Sp, Call("beta", Point), Close,
            Sp, Iff, Sp, Point, Sp, InMacro, Sp, Nodes);
        Formula emptyCase = Seq(Nodes, Sp, Eq, Sp, Emptyset, Sp, Rightarrow, Sp,
            Forall, Sp, Point, Colon, Sp, RealType, Comma, Sp,
            SAt(Point), Sp, Eq, Sp, Call("center", A, DeltaValue));
        return Disp(Seq(Full, Sp, Iff, Sp, Conjunction(
            Seq(Call("natDegree", N), Sp, Le, Sp, degreeBound),
            Seq(Call("natDegree", D), Sp, Le, Sp, degreeBound),
            Parenthesized(globalDenominator), Parenthesized(feasible),
            Call("AnalyticOnNhd", RealType, F.Id("s"), Call("Ioo", A, Num(1))),
            Parenthesized(exactJets), Parenthesized(emptyCase))));
    }

    private static Formula ResultStatement()
    {
        Formula i = F.Id("i");
        Formula oneMinusA = Seq(Num(1), Sp, Minus, Sp, A);
        Formula nodeCondition = Seq(Forall, Sp, i, Sp, InMacro, Sp, Nodes, Comma, Sp,
            Quotient(A, Seq(Num(1), Sp, Minus, Sp, DeltaValue)), Sp, Lt, Sp, i,
            Sp, Land, Sp, i, Sp, Lt, Sp, Num(1));
        Formula assumptions = Conjunction(
            Seq(Num(0), Sp, Lt, Sp, A),
            Seq(A, Sp, Lt, Sp, Num(1)),
            Seq(Num(0), Sp, Lt, Sp, DeltaValue),
            Seq(DeltaValue, Sp, Lt, Sp, Quotient(oneMinusA, Num(4))),
            Seq(DeltaValue, Sp, Lt, Sp,
                Quotient(Seq(Num(1), Sp, Minus, Sp, Square(A)), Num(16))),
            Parenthesized(nodeCondition));
        return Disp(Seq(Forall, Sp, A, Comma, Sp, DeltaValue, Colon, Sp, RealType, Comma, Sp,
            Nodes, Colon, Sp, Call("Finset", RealType), Comma, Sp,
            Parenthesized(assumptions), Sp, Rightarrow, Sp,
            Exists, Sp, N, Comma, Sp, D, Colon, Sp,
            Seq(RealType, OpenBracket, F.Id("X"), CloseBracket), Comma, Sp, Full));
    }
}
