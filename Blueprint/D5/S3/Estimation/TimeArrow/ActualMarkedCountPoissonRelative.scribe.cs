using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class ActualMarkedCountPoissonRelativeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Estimation/TimeArrow/ActualMarkedCountPoissonRelative.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native marked departure counts and their relative Poisson comparison.",
        H("Native One and Two Row Relative Poisson Transfer"),
        Blocks(Describe.Lean(
            DescribeId.Create("native-marked-count-relative"),
            DeclarationHandle.Create(Module + "actual_marked_count_poisson_relative"),
            H("Uniform native relative count estimate"),
            StatementSource.FromAuthor(RelativeFormula()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The constants A, Mzero and etazero depend only on kappa and Czero. "
                    + "There are k = 1 or k = 2 distinct marked positive states m(j). "
                    + "S is a native support of cardinality q. The native compensation is "
                    + "c = rq/(M-q), with natural difference in the denominator. "
                    + "The experiment e ranges over the native pair and uniform-start path experiments.")),
                Paragraph(Text(
                    "In the displayed formula P is the sum of native history masses over all "
                    + "histories of T = 2M lambda transitions for which every marked positive "
                    + "and negative destination-parity count equals the prescribed natural "
                    + "count. Counts of zero are included. Each pair history has mass equal "
                    + "to the product of (2M)^(-1) transition(x,y); a path history has mass "
                    + "(2M)^(-1) times the product of its consecutive transition factors. "
                    + "The transition is (1+b(x) chi(y))/(2M), where chi is the destination parity.")),
                Paragraph(Text(
                    "Q is the product, over marked states and both destination parities, "
                    + "of exp(-mu) mu^n/n!. The means are muplus(j) = lambda(1+b(m(j)))/2 "
                    + "and muminus(j) = lambda(1-b(m(j)))/2. The profile b is r on the "
                    + "positive support, -c on its positive complement, and zero on negative states. "
                    + "P and Q use the same support and marked rows; no independent path-row model is used.")),
                Paragraph(Text(
                    "Positive radii (n+1)/mu extract both native and Poisson count coefficients "
                    + "from their generating functions on a product torus. The pair and path "
                    + "exponential estimates bound the integrated coefficient difference. "
                    + "A factorial estimate, including n = 0, gives the relative normalization."))),
            DescribeRole.Theorem))));

    private static Formula Pow(Formula x, Formula n) => Seq(Grp(x), Caret, Grp(n));
    private static Formula Sub(Formula x, Formula n) => Seq(Grp(x), Underscore, Grp(n));
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

    private static Formula RelativeFormula()
    {
        Formula kap = F.Id("kappa"), cz = F.Id("Czero"), a = F.Id("A");
        Formula mz = F.Id("Mzero"), ez = F.Id("etazero"), m = F.Id("M");
        Formula q = F.Id("q"), lam = F.Id("lambda"), k = F.Id("k"), r = F.Id("r");
        Formula s = F.Id("S"), mark = F.Id("m"), e = F.Id("e"), j = F.Id("j");
        Formula np = Pow(F.Id("n"), Plus), nm = Pow(F.Id("n"), Minus);
        Formula p = Call("P", m, q, lam, r, s, mark, np, nm, e);
        Formula pois = Call("Q", m, q, lam, r, s, mark, np, nm);
        return Disp(Seq(
            Forall, Sp, kap, Comma, cz, Colon, F.Id("Real"), Comma, Sp,
            D(0), Lt, kap, Lt, D(1), Sp, Land, Sp, D(1), Leq, Sp, cz, Sp, Rightarrow, Sp,
            Exists, Sp, a, Colon, F.Id("Real"), Comma, Sp,
            Exists, Sp, mz, Colon, F.Id("Nat"), Comma, Sp,
            Exists, Sp, ez, Colon, F.Id("Real"), Comma, Sp,
            D(0), Lt, a, Sp, Land, Sp, D(1), Leq, Sp, mz, Sp, Land, Sp,
            D(0), Lt, ez, Sp, Land, Sp,
            Forall, Sp, m, Comma, q, Comma, lam, Comma, k, Colon, F.Id("Nat"), Comma, Sp,
            Forall, Sp, r, Colon, F.Id("Real"), Comma, Sp,
            mz, Leq, Sp, m, Sp, Land, Sp, D(1), Leq, Sp, q, Lt, m, Sp, Land, Sp,
            D(0), Lt, r, Leq, Sp, D(1), Minus, kap, Sp, Land, Sp,
            Call("compensation", m, q, r), Leq, Sp, D(1), Minus, kap, Sp, Land, Sp,
            D(1), Leq, Sp, lam, Sp, Land, Sp, Frac, Grp(lam), Grp(m), Leq, Sp, ez, Sp, Land, Sp,
            Open, k, Eq, D(1), Sp, Lor, Sp, k, Eq, D(2), Close, Sp, Rightarrow, Sp,
            Forall, Sp, s, Colon, Call("Support", m, q), Comma, Sp,
            Forall, Sp, mark, Colon, Call("Fin", k), To, Call("Fin", m), Comma, Sp,
            Call("injective", mark), Sp, Rightarrow, Sp,
            Forall, Sp, np, Comma, nm, Colon, Call("Fin", k), To, Sp, F.Id("Nat"), Comma, Sp,
            Open, Forall, Sp, j, Colon, Call("Fin", k), Comma, Sp,
            Sub(np, j), Leq, Sp, cz, lam, Sp, Land, Sp,
            Sub(nm, j), Leq, Sp, cz, lam, Close, Sp, Rightarrow, Sp,
            Forall, Sp, e, Colon, Call("Experiment"), Comma, Sp,
            Lvert, Sp, Frac, Grp(p), Grp(pois), Minus, D(1), Sp, Rvert, Leq, Sp,
            Frac, Grp(a, Pow(lam, Seq(k, Plus, D(1)))), Grp(m)));
    }
}
