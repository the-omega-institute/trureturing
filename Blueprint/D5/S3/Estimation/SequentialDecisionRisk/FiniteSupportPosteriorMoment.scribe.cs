using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.SequentialDecisionRisk;

internal sealed class FiniteSupportPosteriorMomentDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Dynamics/borcea2009negative");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exponential moments of the actual finite fixed-support posterior.",
        H("Finite posterior exponential moments"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-support-posterior-moment"),
            DeclarationHandle.Create("D5/S3/Estimation/SequentialDecisionRisk/FiniteSupportPosteriorMoment.finite_support_posterior_moment"),
            H("The two finite moment bounds"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text("Let M, q and s be natural numbers with 1<=q<M, let 0<r<1, and suppose the compensation rq/(M-q) is less than one. Its nonnegativity follows from these conditions. The experiment e is either the compensated independent-pair experiment or the consecutive-path experiment. Fix any complete observation o, any subset I of Fin M, and any real t>=0.")),
                Paragraph(Text("The support S has exactly q elements. The functions posterior and inclusion are those of FiniteSupportSelectionBayes, with the same r, experiment and complete observation throughout. The expectation here is the finite sum against that actual posterior. Its positive likelihood weights identify it with the normalized product-weight q-slice. An independent tie priority may choose I after conditioning; the bound applies to every resulting fixed I and does not allow selection using the hidden support.")),
                Paragraph(Text("Write e_k(U) for the sum of weight products over k-element subsets of U, including e_0(U)=1 and e_k(U)=0 when k exceeds the size of U. For distinct coordinates i and j, expansion over their membership and Newton's coefficient inequality give e_n(U)e_(n-2)(U without i,j)<=e_(n-1)(U without i)e_(n-1)(U without j). Every feasible forced-success condition leaves a positive product-weight slice on the remaining labels. Thus adding another forced success decreases every remaining inclusion probability. Induction on the number of required labels gives a joint inclusion probability at most the product of the original marginals.")),
                Paragraph(Text("Expanding the finite product with x=exp(t)-1>=0 turns the moment into a sum of nonnegative coefficients times joint inclusion probabilities. Apply the joint bound term by term and factor the resulting sum. Applying 1+y<=exp(y) to every factor gives the second bound. Empty I and t=0 give equality. Oversized required-label sets have zero inclusion mass; no conditional law is obtained by dividing by that zero mass.")),
                Paragraph(Text("The finite product-weight moment inequality is a classical consequence of negative dependence. This formulation applies it to the existing actual posterior and does not assert an asymptotic process limit, an unknown-direction posterior, an entropy bound or originality."))),
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
        var m = F.Id("M"); var q = F.Id("q"); var s = F.Id("s");
        var r = F.Id("r"); var e = F.Id("e"); var o = F.Id("o");
        var i = F.Id("i"); var indices = F.Id("I"); var support = F.Id("S");
        var t = F.Id("t");
        var x = Seq(Open, Call("exp", t), Minus, Num(1), Close);
        var pi = Call("inclusion", q, r, e, o, i);
        var product = Seq(new Formula.Subscript(F.Prod,
            Grp(Seq(i, InMacro, Sp, indices))),
            Grp(Seq(Num(1), Plus, x, Sp, pi)));
        var moment = Seq(new Formula.Subscript(Sum,
            Grp(Seq(support, Colon, Call("Support", m, q)))),
            Grp(Seq(Call("posterior", r, e, o, support), Sp,
                Call("exp", Seq(t, Sp, Call("card", Call("inter", indices, support)))))));
        var total = Seq(new Formula.Subscript(Sum,
            Grp(Seq(i, InMacro, Sp, indices))), Grp(pi));
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, m, Comma, q, Comma, s, Colon, F.Id("Nat"), Comma, Sp,
            r, Colon, F.Id("Real"), Comma, Sp, e, Colon, F.Id("Experiment"), Comma, Sp,
            o, Colon, Call("Obs", m, s, e), Comma, Sp,
            indices, Colon, Call("Finset", Call("Fin", m)), Comma, Sp,
            t, Colon, F.Id("Real"), Comma, RowBreak, Grp(),
            Num(1), Leq, Sp, q, Lt, m, Sp, Land, Sp, Num(0), Lt, r, Lt, Num(1), Sp, Land, Sp,
            Call("compensation", m, q, r), Lt, Num(1), Sp, Land, Sp, Num(0), Leq, Sp, t,
            Sp, Rightarrow, RowBreak, Grp(),
            moment, Leq, product, Leq, Call("exp", Seq(x, Sp, total)),
            End, Grp(F.Id("gathered"))));
    }
}
