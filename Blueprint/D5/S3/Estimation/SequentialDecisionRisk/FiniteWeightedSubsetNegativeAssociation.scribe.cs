using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.SequentialDecisionRisk;

internal sealed class FiniteWeightedSubsetNegativeAssociationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Dynamics/borcea2009negative");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Increasing observables on finite slices with fixed positive product weights.",
        H("Finite weighted subset laws"),
        Blocks(Describe.Lean(
            DescribeId.Create("weighted-slice-rank-comparison"),
            DeclarationHandle.Create("D5/S3/Estimation/SequentialDecisionRisk/FiniteWeightedSubsetNegativeAssociation.weighted_slice_rank_comparison"),
            H("Comparison of whole observables across adjacent ranks"),
            StatementSource.FromAuthor(RankFormula()),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text("Let U be any finite set in an arbitrary carrier, and fix one weight function w with w(i)>0 for every i in U. For every natural k<=|U|, write Z_k(U)=sum_{S subset U, |S|=k} product_{i in S} w(i), and E_k(h)=sum_{S subset U, |S|=k} product_{i in S} w(i) h(S) / Z_k(U). Every legal denominator is positive. The zero-rank and full-rank laws are point masses, including the unique empty law when U is empty.")),
                Paragraph(Text("For an arbitrary real-valued f, assume f(S)<=f(T) whenever S subset T subset U. No sign condition is imposed. Then E_k(f)<=E_(k+1)(f) for every k<|U|, with exactly the same weights on both sides. Monotonicity is imposed on the whole Boolean subcube, so it compares configurations in different ranks.")),
                Paragraph(Text("For U obtained by adjoining i to V, decompose each slice according to membership of i. Newton's coefficient inequality makes the probability of including i increase with the rank. Induction compares the two conditional whole observables f(S) and f(S union {i}); their pointwise order compares the overlapping rank. The resulting convex combinations are ordered. The first and last ranks follow directly by averaging f(empty)<=f(S)<=f(U).")),
                Paragraph(Text("For the actual compensated experiment, retain the original support size q0, parameter r, experiment e and complete observation o. Under 1<=q0<M, 0<r<1 and rq0/(M-q0)<1, FiniteSupportSelectionBayes.finite_support_bayes supplies strictly positive weights w(i)=weight(q0,r,e,o,i) and posterior(S)=product_{i in S}w(i)/Z_q0(Fin M). Apply the rank comparison to this one fixed function w. An auxiliary rank k changes only the subset size in E_k; it never changes q0 in the compensation or recomputes weight(k,r,e,o,i).")),
                Paragraph(Text("The actual posterior expectation equals E_q0 for these fixed weights, so its comparison with adjacent auxiliary ranks is an exact finite consequence. Empty and full ranks remain legal for the generic law even though the compensated observation model is asserted only in its original interior parameter domain. Independent tie priorities can fix observables or blocks after conditioning. This application asserts no unknown-direction posterior mixture, process limit, uniform asymptotic estimate or novelty."))),
            DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-slice-negative-association"),
                DeclarationHandle.Create("D5/S3/Estimation/SequentialDecisionRisk/FiniteWeightedSubsetNegativeAssociation.weighted_slice_negative_association"),
                H("Negative association on disjoint Boolean blocks"),
                StatementSource.FromAuthor(NaFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For the same finite U and fixed strictly positive w, let q be any natural number with q<=|U|. Let A and B be disjoint subsets of U. Let f and g be arbitrary signed real functions on subsets, inclusion-increasing on all subsets of A and B respectively. Then E_q(f(S intersect A)g(S intersect B))<=E_q(f(S intersect A))E_q(g(S intersect B)). All three expectations use the identical normalized product-weight q-slice law. No coupling, rank comparison or negative dependence property is assumed. Empty U, empty blocks, q=0, q=|U| and constants are included.")),
                    Paragraph(Text("Split U into A and C=U without A, and condition on k=|S intersect A|. The product weight factors, so the two restrictions have independent weighted slice laws of ranks k and q-k. The conditional mean F(k) of f increases with k by the rank comparison. The conditional mean G(k) of g decreases with k, since B is a subset of C and q-k decreases. Only feasible ranks have positive mass. For every two such ranks, (F(k)-F(l))(G(k)-G(l))<=0. Summing this inequality with the product of their nonnegative masses gives the covariance inequality. This finite argument permits signed observables throughout.")),
                    Paragraph(Text("In the actual compensated experiment retain q0, r, e and o in the positive weight function supplied by finite_support_bayes. At rank q0 its slice law is exactly posterior(r,e,o). Substituting into the three finite expectations therefore gives the same negative-association inequality for the actual posterior and every pair of disjoint blocks fixed after conditioning on the complete observation and any independent tie priority. Auxiliary rank comparisons use weight(q0,r,e,o) throughout. The actual experiment retains 1<=q0<M, 0<r<1 and compensation(M,q0,r)<1. No claim about an unknown-direction posterior mixture or an asymptotic process follows from this finite statement."))),
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

    private static Formula NaFormula()
    {
        var u = F.Id("U"); var w = F.Id("w"); var q = F.Id("q");
        var a = F.Id("A"); var b = F.Id("B"); var f = F.Id("f"); var g = F.Id("g");
        var x = F.Id("X");
        var sets = Call("Finset", x);
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        return Disp(Seq(Begin, Grp(F.Id("gathered")),
            Forall, Sp, x, Colon, Sp, Operatorname, Grp(F.Id("Type")), Star, Comma, Sp,
            OpenBracket, Call("DecidableEq", x), CloseBracket, Comma, Sp,
            u, Comma, a, Comma, b, Colon, sets, Comma, Sp,
            w, Colon, x, To, Sp, reals, Comma, RowBreak, Grp(),
            Forall, Sp, q, Colon, Mathbb, Grp(F.Id("N")), Comma, Sp,
            f, Comma, g, Colon, sets, To, Sp, reals, Comma, Sp,
            Call("positiveOn", w, u), Sp, Land, Sp,
            q, Leq, Call("card", u), Sp, Land, RowBreak, Grp(),
            Call("subset", a, u), Sp, Land, Sp, Call("subset", b, u), Sp, Land, Sp,
            Call("disjoint", a, b), Sp, Land, Sp, Call("increasingOn", f, Call("powerset", a)),
            Sp, Land, Sp, Call("increasingOn", g, Call("powerset", b)), Sp, Rightarrow,
            RowBreak, Grp(), Call("E", u, w, q, Call("blockProduct", f, a, g, b)), Leq,
            Call("E", u, w, q, Call("block", f, a)), Sp,
            Call("E", u, w, q, Call("block", g, b)), End, Grp(F.Id("gathered"))));
    }

    private static Formula RankFormula()
    {
        var u = F.Id("U"); var w = F.Id("w"); var f = F.Id("f");
        var k = F.Id("k"); var s = F.Id("S"); var t = F.Id("T"); var i = F.Id("i");
        var x = F.Id("X");
        var sets = Call("Finset", x);
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        return Disp(Seq(Begin, Grp(F.Id("gathered")),
            Forall, Sp, x, Colon, Sp, Operatorname, Grp(F.Id("Type")), Star, Comma, Sp,
            u, Colon, sets, Comma, Sp, w, Colon, x, To, Sp, reals, Comma, RowBreak, Grp(),
            Forall, Sp, f, Colon, sets, To, Sp, reals, Comma, Sp,
            k, Colon, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Seq(Open, Forall, Sp, i, InMacro, Sp, u, Comma, Num(0), Lt, Call("w", i), Close),
            Sp, Land, Sp, k, Lt, Call("card", u), Sp, Land, RowBreak, Grp(),
            Seq(Open, Forall, Sp, s, Comma, t, Colon, sets, Comma, Sp,
                Call("subset", s, t), Sp, Land, Sp, Call("subset", t, u), Sp, Rightarrow,
                Call("f", s), Leq, Call("f", t), Close),
            Sp, Rightarrow, RowBreak, Grp(),
            Call("E", u, w, k, f), Leq, Call("E", u, w, Seq(k, Plus, Num(1)), f),
            End, Grp(F.Id("gathered"))));
    }
}
