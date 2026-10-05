using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class ActualMarkedPathPgfPoissonEnvelopeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Estimation/TimeArrow/ActualMarkedPathPgfPoissonEnvelope.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compensated finite paths have a uniform complex Poisson generating-function envelope.",
        H("Marked Native Path Generating Function"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("marked-tilt-u"), DeclarationHandle.Create(Module + "tiltU"),
                H("Symmetric tilt"), StatementSource.FromAuthor(TiltFormula(false)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each marked positive departure state has two arbitrary complex tilt coordinates, "
                    + "one for each destination parity. The symmetric coordinate is their half-sum minus one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("marked-tilt-v"), DeclarationHandle.Create(Module + "tiltV"),
                H("Antisymmetric tilt"), StatementSource.FromAuthor(TiltFormula(true)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The antisymmetric coordinate is half the difference of the positive and negative destination tilts."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("marked-drift-a"), DeclarationHandle.Create(Module + "driftA"),
                H("Total-mass drift"), StatementSource.FromAuthor(DriftFormula(false)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The drift A averages u_j + b_j v_j over the 2M states. Here b_j is the native compensated "
                    + "profile at the marked positive state: b is r on positive support states, -c on the positive complement, and zero on negative states; c = rq/(M-q). Marks may lie in the support or its complement."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("marked-drift-b"), DeclarationHandle.Create(Module + "driftB"),
                H("Endpoint-parity drift"), StatementSource.FromAuthor(DriftFormula(true)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The drift B averages v_j + b_j u_j over the same state space. The compensating profile "
                    + "has zero total mass and vanishes on negative states."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-marked-pgf"), DeclarationHandle.Create(Module + "actualPGF"),
                H("Actual count generating function"), StatementSource.FromAuthor(PgfFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The sum ranges over all complete histories of T transitions, with the native uniform-start "
                    + "path mass. The positive and negative exponents count departures from each marked state "
                    + "followed by the corresponding destination parity. These counts share one history. "
                    + "A history is a function from Fin(T+1) to Fin(M) + Fin(M). Its mass w_T is (2M)^(-1) times the product of (1 + b(x) chi(y))/(2M) over its T edges, where chi is 1 on positive states and -1 on negative states. C_j^+ and C_j^- count edges whose departure is the positive state m(j) and whose destination chi is respectively 1 and -1. The symbol z denotes the pair (z^+, z^-). Natural powers include zero tilt coordinates and use the convention zero to the zeroth power equals one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-marked-pgf-poisson-envelope"),
                DeclarationHandle.Create(Module + "actual_marked_path_pgf_poisson_envelope"),
                H("Finite Poisson envelope"), StatementSource.FromAuthor(EnvelopeFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let 1 <= q < M, 0 < r < 1, and c = rq/(M-q) < 1, where M-q is the natural difference. "
                        + "A support has exactly q positive states. There are one or two distinct positive marked "
                        + "states, with arbitrary complex tilts. If 0 <= eta <= 1/4, both drift norms are at most eta, "
                        + "and T eta squared is at most 1/10, the native generating function differs from exp(TA) "
                        + "by at most 20 T eta squared times exp(T Re A).")),
                    Paragraph(Text(
                        "Finite product identities turn actual count powers into edge factors without dividing by a tilt. "
                        + "Appending the last state to a complete history gives the forward endpoint sum. Its tilted mass "
                        + "at y is (F_t + chi(y) G_t)/(2M), with F_0 = 1 and G_0 = 0. The physical endpoint recurrence "
                        + "is F_(t+1) = (1+A) F_t + A G_t and G_(t+1) = B F_t + B G_t. Summing endpoints gives F_T.")),
                    Paragraph(Text(
                        "Normalize by h = 1+A, whose norm is at least 3/4. The parity feedback is a finite geometric "
                        + "sum with ratio B/h. Running maxima bound the normalized increments using "
                        + "theta = norm(AB)/(norm(h)(norm(h)-norm(B))) <= (8/3) eta squared. "
                        + "The total normalized error is at most 2 T theta.")),
                    Paragraph(Text(
                        "The complex logarithm remainder is bounded by kappa = norm(A) squared/(2(1-norm(A))) "
                        + "<= (2/3) eta squared. Exponentiation then compares h to exp(A), and the two errors combine "
                        + "with coefficient 52/3 <= 20. The sole logarithm is applied to h. All divisions have positive "
                        + "uniform bounds, so T = 0, eta = 0, A = 0, B = 0, and zero tilt coordinates remain included.")),
                    Paragraph(Text(
                        "This finite generating-function estimate does not supply relative point-mass estimates, "
                        + "coefficient extraction, growing-window uniformity, or entropy asymptotics."))),
                DescribeRole.Theorem))));

    private static Formula Sub(Formula x, Formula j) => Seq(Grp(x), Underscore, Grp(j));
    private static Formula Pow(Formula x, Formula j) => Seq(Grp(x), Caret, Grp(j));
    private static Formula Norm(Formula x) => Seq(Lvert, Sp, x, Sp, Rvert);
    private static Formula Z(bool negative, Formula j) =>
        Sub(Pow(F.Id("z"), negative ? Minus : Plus), j);
    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) parts.AddRange([Comma, Sp]);
            parts.Add(args[i]);
        }
        parts.Add(Close);
        return Seq([.. parts]);
    }
    private static Formula TiltFormula(bool antisymmetric)
    {
        Formula j = F.Id("j");
        Formula value = Seq(Frac, Grp(Z(false, j), antisymmetric ? Minus : Plus, Z(true, j)), Grp(D(2)));
        return Disp(Seq(Sub(F.Id(antisymmetric ? "v" : "u"), j), Eq,
            antisymmetric ? value : Seq(value, Minus, D(1))));
    }
    private static Formula DriftFormula(bool parity)
    {
        Formula j = F.Id("j");
        return Disp(Seq(F.Id(parity ? "B" : "A"), Eq,
            Frac, Grp(D(1)), Grp(D(2), F.Id("M")), Sp,
            Sum, Underscore, Grp(j, Colon, Call("Fin", F.Id("k"))), Sp,
            Open, Sub(F.Id(parity ? "v" : "u"), j), Plus,
            Sub(F.Id("b"), j), Sub(F.Id(parity ? "u" : "v"), j), Close));
    }
    private static Formula PgfFormula()
    {
        Formula j = F.Id("j"), o = F.Id("o"), t = F.Id("T");
        return Disp(Seq(Call("ActualPGF", t, F.Id("z")), Eq,
            Sum, Underscore, Grp(o, Colon, Call("path", t)), Sp,
            Sub(F.Id("w"), t), Open, o, Close, Sp,
            Prod, Underscore, Grp(j, Colon, Call("Fin", F.Id("k"))), Sp,
            Pow(Z(false, j), Seq(Sub(Pow(F.Id("C"), Plus), j), Open, o, Close)), Sp,
            Pow(Z(true, j), Seq(Sub(Pow(F.Id("C"), Minus), j), Open, o, Close))));
    }
    private static Formula EnvelopeFormula()
    {
        Formula m = F.Id("M"), q = F.Id("q"), t = F.Id("T"), k = F.Id("k"),
            r = F.Id("r"), e = F.Id("eta"), a = F.Id("A"), b = F.Id("B"), s = F.Id("S");
        return Disp(Seq(
            Forall, Sp, m, Comma, q, Comma, t, Comma, k, Colon, F.Id("Nat"), Comma, Sp,
            r, Comma, e, Colon, F.Id("Real"), Comma, Sp,
            s, Subseteq, Call("Fin", m), Comma, Sp,
            F.Id("m"), Colon, Call("Fin", k), To, Call("Fin", m), Comma, Sp,
            Pow(F.Id("z"), Plus), Comma, Pow(F.Id("z"), Minus), Colon,
            Call("Fin", k), To, Sp, F.Id("Complex"), Comma, Sp,
            D(1), Leq, Sp, q, Lt, m, Sp, Land, Sp,
            D(0), Lt, r, Lt, D(1), Sp, Land, Sp,
            F.Id("c"), Eq, Frac, Grp(r, q), Grp(m, Minus, q), Lt, D(1), Sp, Land, Sp,
            Norm(s), Eq, q, Sp, Land, Sp,
            Open, k, Eq, D(1), Lor, Sp, k, Eq, D(2), Close, Sp, Land, Sp,
            Call("injective", F.Id("m")), Sp, Land, Sp,
            D(0), Leq, Sp, e, Leq, Frac, Grp(D(1)), Grp(D(4)), Sp, Land, Sp,
            Norm(a), Leq, Sp, e, Sp, Land, Sp, Norm(b), Leq, Sp, e, Sp, Land, Sp,
            t, Pow(e, D(2)), Leq, Frac, Grp(D(1)), Grp(D(1,0)), Sp, Rightarrow, Sp,
            Norm(Seq(Call("ActualPGF", t, F.Id("z")), Minus, Call("exp", Seq(t, a)))), Leq,
            D(2,0), t, Pow(e, D(2)), Call("exp", Seq(t, Call("Re", a)))));
    }
}
