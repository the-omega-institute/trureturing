using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class RealL2FirstReturnMomentsDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Dynamics/RealL2FirstReturnMoments.endpoint_moments";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete real half-line and its finite path have identical endpoint moments "
            + "before the first boundary return.",
        H("Real Half-Line First Return Moments"),
        Blocks(Describe.Lean(
            DescribeId.Create("real-l2-first-return-moments"),
            DeclarationHandle.Create(Declaration),
            H("The first boundary return contributes exactly one"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let H be the complete real Hilbert space of square-summable sequences "
                        + "on the positive integers. Its unilateral shift satisfies S e_j = e_(j+1), "
                        + "and K_infinity = 3I-S-S*. Natural coordinate j represents source "
                        + "coordinate j+1. For n at least one, A_n is the n-point path adjacency "
                        + "matrix, K_n = 3I_n-A_n, and b_n is its first coordinate vector. "
                        + "The finite matrix acts on the Euclidean space of n real coordinates. "
                        + "For every natural k, define S_k^(n) to be the real Euclidean inner "
                        + "product of b_n with K_n^k b_n, and S_k^(infinity) to be the real "
                        + "Hilbert inner product of e_1 with K_infinity^k e_1 in H.")),
                Paragraph(Text(
                    "Write J_n for extension by zero into H. For k less than n, "
                        + "K_infinity^k e_1 = J_n K_n^k b_n. At order n the infinite iterate "
                        + "has the additional coordinate (-1)^n e_(n+1). "
                        + "Self-adjointness splits an endpoint moment into a pairing of two "
                        + "iterates. Below order 2n at least one factor has not reached the "
                        + "boundary; at order 2n the new coordinate is paired with itself "
                        + "and contributes one.")),
                Paragraph(
                    Text(
                        "For a natural n at least one, let hn witness 1 <= n. "
                            + "For the actual carriers, put A_infinity = S + S* on "
                            + "ell2(Nat, Real), A_n = Matrix.toEuclideanCLM(pathAdjacency n) "
                            + "on EuclideanSpace Real (Fin n), e_infinity = endpoint, and "
                            + "e_n = finiteEndpoint n hn. Thus K_X = 3 I_X - A_X for "
                            + "X equal to infinity or n, with the same source-coordinate shift "
                            + "and the original endpoint on each carrier. The scalar adjacency "
                            + "coefficient is defined by "),
                    Math(Coefficient(F.Id("X"), F.Id("k"))),
                    Text(" = "),
                    Math(Inner(Endpoint(F.Id("X")),
                        Apply(Power(Adjacency(F.Id("X")), F.Id("k")), Endpoint(F.Id("X"))))),
                    Text(" for every natural k. Since A_X = 3 I_X - K_X, the commuting "
                        + "binomial expansion of A_X^k expresses this coefficient as a linear "
                        + "combination of the K_X endpoint moments of orders zero through k. "
                        + "Applying endpoint_moments, for every natural n at least one and "
                        + "every natural k < 2 n, the finite and infinite adjacency coefficients "
                        + "agree. At k = 2 n all lower-order moment differences vanish, and "
                        + "the coefficient of the order-2 n difference is (-1)^(2 n) = 1. "
                        + "Thus the infinite adjacency coefficient minus the finite one is "
                        + "exactly one. These clauses include k = 0 and n = 1.")),
                Paragraph(
                    Text("For a real time t, define the endpoint-exponential kernel by "),
                    Math(Kernel(F.Id("X"), F.Id("t"))),
                    Text(" = "),
                    Math(ExpKernelFormula(F.Id("X"), F.Id("t"))),
                    Text(". The commuting scalar decomposition "
                        + "-t K_X = -3 t I_X + t A_X gives the displayed scalar factor "
                        + "and the adjacency power series, indexed by every natural k. "
                        + "Here the adjacency operators have nonnegative entries in their "
                        + "coordinate bases. The identities hold for all real times t. "
                        + "For every natural n at least one "
                        + "and every real t, the finite identity is "),
                    Math(HasSumFormula(F.Id("n"), F.Id("t"))),
                    Text("; for every real t, the complete real ell2 identity is "),
                    Math(HasSumFormula(Infty, F.Id("t"))),
                    Text(". In the first formula the carrier is exactly "
                        + "EuclideanSpace Real (Fin n) with finiteEndpoint n hn; in the "
                        + "second it is the complete real ell2(Nat, Real) carrier with "
                        + "endpoint. The identities follow by factoring the scalar exponential "
                        + "from the commuting operator exponential and applying the exponential "
                        + "power-series identity to the real endpoint pairing."))),
            DescribeRole.Theorem))));

    private static Formula Coefficient(Formula x, Formula k) =>
        Seq(F.Id("c"), Underscore, Grp(x), Open, k, Close);

    private static Formula Inner(Formula left, Formula right) =>
        Seq(Langle, Sp, left, Comma, Sp, right, Rangle,
            Underscore, Grp(Mathbb, Grp(F.Id("R"))));

    private static Formula Endpoint(Formula x) =>
        Seq(F.Id("e"), Underscore, Grp(x));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(Grp(value), Caret, Grp(exponent));

    private static Formula Adjacency(Formula x) =>
        Seq(F.Id("A"), Underscore, Grp(x));

    private static Formula Kernel(Formula x, Formula t) =>
        Seq(F.Id("M"), Underscore, Grp(x), Open, t, Close);

    private static Formula ExpKernelFormula(Formula x, Formula t) =>
        Inner(Endpoint(x), Apply(
            Seq(Exp, Open, Minus, t, Sp, F.Id("K"), Underscore, Grp(x), Close),
            Endpoint(x)));

    private static Formula HasSumFormula(Formula x, Formula t)
    {
        Formula k = F.Id("k");
        return Seq(Operatorname, Grp(F.Id("HasSum")), Open,
            Open, k, Colon, Sp, Mathbb, Grp(F.Id("N")), Close, Sp, Mapsto, Sp,
            Exp, Open, Minus, D(3), t, Close, Sp, Cdot, Sp,
            Frac, Grp(Power(t, k)), Grp(k, Bang), Sp, Cdot, Sp,
            Coefficient(x, k), Comma, Sp, Kernel(x, t), Close);
    }

    private static Formula Moment(string kind, Formula k) =>
        Seq(F.Id("S"), Underscore, Grp(k), Caret, Grp(kind == "infinity" ? Infty : F.Id(kind)));

    private static Formula TheoremFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k");
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula twoN = Seq(D(2), n);
        return Disp(Seq(
            Forall, Sp, n, Sp, InMacro, Sp, nat, Comma, Sp,
            D(1), Sp, Leq, Sp, n, Sp, Rightarrow, Sp,
            Open, Forall, Sp, k, Sp, InMacro, Sp, nat, Comma, Sp,
            k, Sp, Lt, Sp, twoN, Sp, Rightarrow, Sp,
            Moment("n", k), Sp, Eq, Sp, Moment("infinity", k), Close,
            Sp, Land, Sp,
            Moment("infinity", twoN), Sp, Minus, Sp, Moment("n", twoN),
            Sp, Eq, Sp, D(1), Dot));
    }
}
