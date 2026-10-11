using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class FiniteStateProbabilityResponseGapDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S3/Observer/ProbabilisticClosure/FiniteStateProbabilityResponseGap.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Global probability constraints separate fixed-degree rational responses from an analytic target with a negative continuation.",
        H("Finite-state probability response gaps"),
        Blocks(
            Describe.Lean(DescribeId.Create("bounded-degree-probability-response-gap"),
                DeclarationHandle.Create(Root + "bounded_degree_probability_response_gap"),
                H("A positive gap for each fixed degree"),
                StatementSource.FromAuthor(GapStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix real endpoints l ≤ a < b ≤ r and an analytic function f on (l,r) that is negative somewhere. "
                    + "The positive constant is uniform over all real polynomial pairs of degree at most d whose denominator "
                    + "has no zero on (l,r) and whose ratio remains between zero and one throughout that interval.")),
                    Paragraph(Text(
                    "Normalize the joint coefficient vector and take a convergent subsequence. Both probability inequalities "
                    + "pass to the same limit. A zero denominator would force the numerator to vanish, contradicting the "
                    + "unit norm. A vanishing residual on (a,b) extends analytically and contradicts the negative target "
                    + "and the limiting sign constraint. Bounded evaluation on a compact interval converts the residual gap "
                    + "to a ratio gap. This argument applies to integer as well as noninteger target exponents."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "A finite common-coin table has continuation matrix (1−t)Qzero+tQone and an analogous terminal-event column. "
                + "Its finite-horizon absorption probabilities start at zero and iterate v ↦ r+Qv. Their increasing limit "
                + "lies in the unit interval and solves the absorption equations. Positive support is independent of the "
                + "interior coin rate. Termination from every retained configuration at one interior rate supplies a finite "
                + "positive-probability exit from every state at every interior rate. The maximum principle then makes I−Q nonsingular.")),
            Paragraph(Text(
                "Cramer determinants give one common denominator and numerator, each of degree at most the number of retained "
                + "nonterminal configurations. Initial terminal mass contributes a constant multiple of the same denominator. "
                + "The private transition probabilities may be arbitrary real numbers. For two source coins restricted to "
                + "the diagonal p=q=t, the branch weights a+bzero(1−t)+bone t+czero(1−t)+cone t combine into the two endpoint tables.")),
            Paragraph(Text(
                "The finite-state rationality argument is the necessary-direction construction of Mossel and Peres, "
                + "New Coins from Old: Computing with Unknown Bias, Proposition 2.3, adapted to fixed real transition weights. "
                + "The compact coefficient and negative-continuation argument is the repository derivation. No optimal rate "
                + "of decay of the gap with the state count is asserted.")))));

    private static Formula GapStatement()
    {
        var d = F.Id("d"); var l = F.Id("l"); var a = F.Id("a");
        var b = F.Id("b"); var r = F.Id("r"); var f = F.Id("f");
        var p = F.Id("P"); var q = F.Id("D"); var x = F.Id("x");
        var c = F.Id("c"); var e = F.Id("epsilon");
        Formula interval(Formula u, Formula v) => Call("Ioo", u, v);
        Formula all(Formula v, Formula type, Formula body) => Seq(Forall, Sp, v, Colon, Sp, type, Comma, Sp, body);
        Formula at(Formula u) => Call("eval", u, x);
        Formula ratio = Frac(at(p), at(q));
        Formula valid = Seq(
            Call("natDegree", p), Sp, Le, Sp, d, Sp, Land, Sp,
            Call("natDegree", q), Sp, Le, Sp, d, Sp, Land, Sp,
            all(x, interval(l, r), Seq(at(q), Sp, Neq, Sp, D(0), Sp, Land, Sp,
                D(0), Sp, Le, Sp, ratio, Sp, Le, Sp, D(1))));
        Formula separation = Seq(Exists, Sp, x, Sp, In, Sp, interval(a, b), Comma, Sp,
            e, Sp, Le, Sp, Lvert, ratio, Minus, Call("apply", f, x), Rvert);
        Formula body = Seq(l, Sp, Le, Sp, a, Sp, Land, Sp, a, Sp, Lt, Sp, b, Sp, Land, Sp,
            b, Sp, Le, Sp, r, Sp, Land, Sp, Call("AnalyticOnNhd", Real, f, interval(l, r)), Sp, Land, Sp,
            Grp(Exists, Sp, c, Sp, In, Sp, interval(l, r), Comma, Sp, Call("apply", f, c), Sp, Lt, Sp, D(0)),
            Sp, Rightarrow, Sp, Exists, Sp, e, Colon, Sp, Real, Comma, Sp, D(0), Sp, Lt, Sp, e, Sp, Land, Sp,
            all(p, Call("Polynomial", Real), all(q, Call("Polynomial", Real),
                Seq(valid, Sp, Rightarrow, Sp, separation))));
        return Disp(all(d, Nat, all(l, Real, all(a, Real, all(b, Real, all(r, Real,
            all(f, Seq(Real, Sp, To, Sp, Real), body)))))));
    }
}
