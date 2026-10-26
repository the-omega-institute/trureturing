using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class ActualMarkedPathPgfPoissonEnvelopeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Estimation/TimeArrow/ActualMarkedPathPgfPoissonEnvelope.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual forward paths and their finite transfer.", H("Forward Marked Path Transfer"), Blocks(
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

    private static Formula Pow(Formula x, Formula j) => Seq(Grp(x), Caret, Grp(j));
    private static Formula Norm(Formula x) => Seq(Lvert, Sp, x, Sp, Rvert);
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
    private static Formula EnvelopeFormula()
    {
        Formula m = F.Id("M"), q = F.Id("q"), t = F.Id("T"), k = F.Id("k"),
            r = F.Id("r"), e = F.Id("eta"), support = F.Id("S"), mark = F.Id("m"), zp = F.Id("zp"), zm = F.Id("zm");
        Formula a = Call("driftA", r, support, mark, zp, zm), b = Call("driftB", r, support, mark, zp, zm);
        Formula Product(Formula x, Formula y) => Seq(Open, x, Close, Sp, Cdot, Sp, Open, y, Close);
        return Disp(Seq(
            Forall, Sp, m, Comma, q, Comma, t, Comma, k, Colon, F.Id("Nat"), Comma, Sp,
            Forall, Sp, r, Comma, e, Colon, F.Id("Real"), Comma, Sp,
            Forall, Sp, support, Colon, Call("Support", m, q), Comma, Sp,
            Forall, Sp, mark, Colon, Call("Fin", k), To, Sp, Call("Fin", m), Comma, Sp,
            Forall, Sp, zp, Comma, zm, Colon, Call("Fin", k), To, Sp, F.Id("Complex"), Comma, Sp,
            D(1), Leq, Sp, q, Lt, m, Sp, Land, Sp,
            D(0), Lt, r, Lt, D(1), Sp, Land, Sp,
            Call("compensation", m, q, r), Lt, D(1), Sp, Land, Sp,
            Open, k, Eq, D(1), Sp, Lor, Sp, k, Eq, D(2), Close, Sp, Land, Sp,
            Call("injective", mark), Sp, Land, Sp,
            D(0), Leq, Sp, e, Leq, Sp, Frac, Grp(D(1)), Grp(D(4)), Sp, Land, Sp,
            Norm(a), Leq, Sp, e, Sp, Land, Sp, Norm(b), Leq, Sp, e, Sp, Land, Sp,
            Product(t, Pow(e, D(2))), Leq, Sp, Frac, Grp(D(1)), Grp(D(1,0)), Sp, Rightarrow, Sp,
            Norm(Seq(Call("actualPGF", r, support, mark, zp, zm, t), Minus, Call("exp", Product(t, a)))), Leq, Sp,
            Product(Product(Product(D(2,0), t), Pow(e, D(2))), Call("exp", Product(t, Call("Re", a))))));
    }
}
