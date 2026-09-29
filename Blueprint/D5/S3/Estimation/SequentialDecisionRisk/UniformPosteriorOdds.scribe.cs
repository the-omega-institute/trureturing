using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.SequentialDecisionRisk;

internal sealed class UniformPosteriorOddsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A balanced auxiliary Bernoulli array gives a uniform finite approximation to actual posterior log odds.",
        H("Uniform Posterior Log Odds"),
        Blocks(Describe.Lean(
            DescribeId.Create("uniform-posterior-odds"),
            DeclarationHandle.Create("D5/S3/Estimation/SequentialDecisionRisk/UniformPosteriorOdds.result"),
            H("Universal finite posterior log-odds bound"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("There are universal positive real constants C and V0, chosen before every model parameter, observation, tilt and coordinate. Both constants may be taken to be four. Let M, q and s be natural numbers with 1<=q<M, let 0<r<1, and assume the compensation a=rq/(M-q) is less than one. The experiment e is either the compensated independent-pair experiment or the compensated consecutive-path experiment, and o is any complete observation of that experiment.")),
                Paragraph(Text("For any positive real t, put B0=(M-q)/q and p(i)=t w(i)/(B0+t w(i)), where w(i) is the actual positive likelihood weight. Write U for the sum of p(i) and V for the sum of p(i)(1-p(i)). If U=q and V>=V0, every actual posterior inclusion probability pi(i) is strictly between zero and one. Its log odds differ from score(i)-log(B0)+log(t) in absolute value by at most C/V, simultaneously for all coordinates.")),
                Paragraph(Text("The coefficient estimate uses arbitrary positive Bernoulli odds. If their sum mean lies between consecutive integers k and k+1 and their sum variance is W>=2, the logarithm of the ratio of the corresponding adjacent elementary symmetric coefficients has absolute value at most 2/W. Multiply every odds by the ratio of those coefficients. The new coefficients are equal. Coefficient deletion, the first-moment identity and Newton's inequality place the new mean between k and k+1. The rational change in the mean bounds the odds multiplier and its logarithm in terms of W.")),
                Paragraph(Text("For a deleted coordinate, the mean is q-p(i) and the variance is V-p(i)(1-p(i)), at least V-1/4. The auxiliary coefficient estimate therefore applies. The common tilt cancels in every fixed-cardinality support probability; the actual Bayes formula identifies the posterior odds with the tilted single-coordinate odds times the deleted coefficient ratio. Taking logarithms gives the stated bound without a union bound over coordinates.")),
                Paragraph(Text("This is a deterministic finite statement conditional on the realized observation and the displayed mean and variance conditions. It does not assert their probability under the actual data law, a sparse-cardinality asymptotic, or a risk expansion."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        var m = F.Id("M");
        var q = F.Id("q");
        var s = F.Id("s");
        var r = F.Id("r");
        var e = F.Id("e");
        var o = F.Id("o");
        var t = F.Id("t");
        var i = F.Id("i");
        var c = F.Id("C");
        var v0 = F.Id("V0");
        var v = F.Id("V");
        var pi = Call("inclusion", q, r, e, o, i);
        var logOdds = Call("log", Seq(Frac, Grp(pi), Grp(Seq(Num(1), Minus, pi))));
        var centeredScore = Seq(Call("score", q, r, e, o, i), Minus,
            Call("log", F.Id("B0")), Plus, Call("log", t));
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Exists, Sp, c, Gt, Num(0), Comma, Sp, Exists, Sp, v0, Gt, Num(0), Comma,
            RowBreak, Grp(),
            Forall, Sp, m, Comma, q, Comma, s, Colon, F.Id("Nat"), Comma, Sp,
            r, Colon, F.Id("Real"), Comma, Sp, e, Colon, F.Id("Experiment"), Comma, Sp,
            o, Colon, Call("Obs", m, s, e), Comma, Sp, t, Colon, F.Id("Real"), Comma,
            RowBreak, Grp(),
            Num(1), Leq, Sp, q, Lt, m, Sp, Land, Sp, Num(0), Lt, r, Lt, Num(1), Sp, Land, Sp,
            Call("compensation", m, q, r), Lt, Num(1), Sp, Land, Sp,
            Num(0), Lt, t, Sp, Land, Sp, F.Id("U"), Eq, q, Sp, Land, Sp, v0, Leq, Sp, v,
            Sp, Rightarrow, RowBreak, Grp(),
            Forall, Sp, i, Colon, Call("Fin", m), Comma, Sp,
            Num(0), Lt, pi, Lt, Num(1), Sp, Land, Sp,
            Call("abs", Seq(logOdds, Minus, Open, centeredScore, Close)), Leq, Seq(Frac, Grp(c), Grp(v)),
            End, Grp(F.Id("gathered"))));
    }
}
