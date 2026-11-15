using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class KBonacciSupportedCoalescenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Supported common-false coalescence of the native conditional prefix coupling.",
        H("Complete outputs of the stopped recursion"),
        Blocks(
            Paragraph(Text(
                "Write W(n) for Fin n to Bool, C(k,n,F,x) for completions, and "
                + "P(s,F,x,y,h,g) for the original prefixCoupling. The histories x and y "
                + "are arbitrary; h and g assert that their full legal completion fibers "
                + "are nonempty. The law tests resetReady before scanning, chooses an "
                + "actual completion representative for reset transport, and retains both "
                + "independent fallback branches for impossible child fibers.")),
            Describe.Lean(
                DescribeId.Create("kbonacci-supported-coalescence"),
                DeclarationHandle.Create(
                    "D5/S1/Words/AdmissibleWords/KBonacciSupportedCoalescence.prefix_coupling_supported_coalescence"),
                H("An emitted common false forces equality at all later scanned positions"),
                StatementSource.FromAuthor(Disp(CoalescenceFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The list s is duplicate-free, strictly increasing in coordinate value, "
                    + "and enumerates exactly the complement of F. FarSame(s,F,x,y) means "
                    + "that x(t)=y(t) whenever i is in s, t is in F and i<t. For any supported "
                    + "complete pair w, a common false at position r implies equality at every "
                    + "position q at or after r. This includes r=q, initially ready resets, "
                    + "equal histories, empty scans, n=0 and empty fixed sets.")),
                    Paragraph(Text(
                    "In a reset branch, map support expresses the complete pair as "
                    + "(u,resetMap(z,y,u)) for the actual chosen reset coordinate z. Every "
                    + "free site lies strictly after z and is therefore equal on both sides. "
                    + "In a recursive branch, bind support retains the same complete output "
                    + "in a supported child. Both refined fibers are then nonempty. Exact "
                    + "native marginals and coupled_fixed recover the sampled head bits. "
                    + "If r is the head, these bits are both false, so the refined histories "
                    + "pass resetReady; its chosen coordinate need not be the head. If r is "
                    + "later, induction applies to the child, including a child already reset. "
                    + "Strict order, complement cover and farther fixed agreement descend "
                    + "with the refined histories."))),
                DescribeRole.Theorem),
            Paragraph(Text("Application to the same native joint law. Retain every hypothesis of "),
                Ref("D5/S1/Words/AdmissibleWords/KBonacciSupportedCoalescence.prefix_coupling_supported_coalescence"),
                Text(" and apply the event estimate from "),
                Ref("D5/S1/Words/AdmissibleWords/KBonacciEmittedTail.prefix_coupling_emitted_tail"),
                Text(" to exactly the same P. Neither supplier declaration individually states the combined inequalities below.")),
            Paragraph(Text(
                "Thus k>0 and n is natural; s is duplicate-free, strictly increasing in coordinate value, "
                + "and enumerates exactly the complement of F. The arbitrary histories x and y have "
                + "nonempty original completion fibers, and x(t)=y(t) whenever i is in s, t is in F, and "
                + "i<t. No legality assumption is imposed on the histories themselves. Put m=length(s) and "
                + "a=1/2 in ENNReal. Keep P=P(s,F,x,y,h,g), including its initial resetReady test, actual "
                + "completion choices and both independent fallback branches.")),
            Paragraph(Text(
                "For q in Fin(m), use the zero-based index q to define D(q,w) as the ENNReal indicator of "
                + "disagreement between w.1(s[q]) and w.2(s[q]). Let H(s,w) be the sum of these indicators, "
                + "namely scanHamming(s,w). Each free site is counted exactly once. This index corresponds "
                + "to position q+1 in a one-based block scan; the index correspondence alone does not "
                + "identify the native law with a paper construction.")),
            new DocumentBlock.DisplayFormula(Disp(ApplicationCostFormula())),
            Paragraph(Text(
                "Define A(j,w) to mean that no coordinate in s.take(j) has both emitted bits false. It "
                + "permits (true,true), so it is not an event of disagreement at every position. For a "
                + "supported complete output w and any r at or before q, a common false at r forces "
                + "agreement at q by supported coalescence. Consequently disagreement at q excludes every "
                + "common false among the first q+1 outputs. Outside support P(w)=0; the weighted "
                + "inequality therefore holds for every complete pair, even if event inclusion fails off "
                + "support.")),
            new DocumentBlock.DisplayFormula(Disp(ApplicationWeightedFormula())),
            Paragraph(Text(
                "Here indicator(A(j)) denotes the ENNReal-valued function of w. Sum the weighted "
                + "inequality over complete pairs and apply the emitted-tail estimate at j=q+1, which is at "
                + "most m because q belongs to Fin(m). This gives both the probability of disagreement at q "
                + "and its mean bound under the unchanged native P.")),
            new DocumentBlock.DisplayFormula(Disp(ApplicationPointwiseFormula())),
            Paragraph(Text(
                "Both W(n) times W(n) and Fin(m) are finite. Expanding mean as its nonnegative sum, using "
                + "tsum_fintype, distributing multiplication across the finite scan sum, and commuting the "
                + "two finite sums yields the mean of H as the sum of the means of D. Apply the pointwise "
                + "bounds term by term under this one P. No independence between disagreement events is "
                + "assumed.")),
            new DocumentBlock.DisplayFormula(Disp(ApplicationMeanFormula())),
            Paragraph(Text(
                "For the geometric identity first work in NNReal with b=1/2. The finite geometric-sum "
                + "identity says that the sum of b^q for 0<=q<m, multiplied by 1-b, equals 1-b^m. Since "
                + "1-b=b, this is the sum of b^(q+1). Coercion from NNReal to ENNReal preserves the finite "
                + "sum and powers, and ENNReal.coe_sub preserves the truncated subtraction. Thus the sum of "
                + "a^(q+1) is 1-a^m in ENNReal as used above. Since b^m<=1 and all quantities are finite, "
                + "no cancellation involving infinity is needed.")),
            Paragraph(Text(
                "For m=0 the pointwise assertion is vacuous, the Hamming sum is zero and 1-a^0=0; n=0 is "
                + "included. If m>0, the last index q=m-1 uses precisely A(m), retaining the full-scan "
                + "endpoint and exponent m. Empty F, equal histories, initial resets and k=1 remain within "
                + "the stated hypotheses. These applications neither exclude degenerate inputs nor replace "
                + "the coupling.")),
            Paragraph(Text(
                "The original native completion-law marginals are already established. What remains for "
                + "the book application is the exact identification of the relevant completion fibers, "
                + "restricted laws and exterior-restored laws with its intended block refresh "
                + "distributions. Simultaneous Fin.rev transport of both outputs, support and events is "
                + "still required for a reflected left block. Equality in law with the paper "
                + "shared-threshold coupling is not asserted and does not follow from these inequalities. "
                + "The complete paper P2E application and any physical Hamiltonian identification retain "
                + "their separate boundaries. This narrative is an application of existing results, with no "
                + "additional Lean declaration or theorem attribution.")))));

    private static Formula ApplicationCostFormula()
    {
        var q = F.Id("q"); var w = F.Id("w"); var s = F.Id("s");
        var bit1 = Call("fst", w, Call("get", s, q));
        var bit2 = Call("snd", w, Call("get", s, q));
        return new Formula.Aligned([
            Rel(Call("D", q, w), Eq, Call("indicator", Rel(bit1, Neq, bit2))),
            Seq(Call("H", s, w), Sp, Eq, Sp, ApplicationSum(Call("D", q, w)),
                Sp, Eq, Sp, Call("scanHamming", s, w))]);
    }

    private static Formula ApplicationWeightedFormula()
    {
        var q = F.Id("q"); var w = F.Id("w");
        var next = Seq(q, Plus, D(1));
        return All(q, Call("Fin", F.Id("m")), All(w, Call("Pair", Word(F.Id("n")), Word(F.Id("n"))),
            Rel(Seq(Call("P", w), Sp, Call("D", q, w)), Leq,
                Seq(Call("P", w), Sp, Call("indicator", Call("A", next, w))))));
    }

    private static Formula ApplicationPointwiseFormula()
    {
        var q = F.Id("q"); var next = Seq(q, Plus, D(1));
        return All(q, Call("Fin", F.Id("m")),
            Seq(Call("mean", F.Id("P"), Call("D", q)), Sp, Leq, Sp,
                Call("mean", F.Id("P"), Call("indicator", Call("A", next))),
                Sp, Leq, Sp, new Formula.Power(F.Id("a"), next)));
    }

    private static Formula ApplicationMeanFormula()
    {
        var q = F.Id("q"); var m = F.Id("m");
        return new Formula.Aligned([
            Rel(Call("mean", F.Id("P"), Call("H", F.Id("s"))), Eq,
                ApplicationSum(Call("mean", F.Id("P"), Call("D", q)))),
            Seq(Call("mean", F.Id("P"), Call("H", F.Id("s"))), Sp, Leq, Sp,
                ApplicationSum(new Formula.Power(F.Id("a"), Seq(q, Plus, D(1)))),
                Sp, Eq, Sp, D(1), Minus, new Formula.Power(F.Id("a"), m))]);
    }

    private static Formula ApplicationSum(Formula term) =>
        Seq(Sum, Underscore, Grp(Seq(F.Id("q"), Sp, InMacro, Sp, Call("Fin", F.Id("m")))), Sp, term);

    private static Formula CoalescenceFormula()
    {
        var k = F.Id("k"); var n = F.Id("n"); var s = F.Id("s"); var f = F.Id("F");
        var x = F.Id("x"); var y = F.Id("y"); var h = F.Id("h"); var g = F.Id("g");
        var i = F.Id("i"); var w = F.Id("w"); var r = F.Id("r"); var q = F.Id("q");
        var free = All(i, Call("Fin", n), Imp(Seq(i, Sp, InMacro, Sp, s),
            Seq(Neg, Sp, Par(Seq(i, Sp, InMacro, Sp, f)))));
        var cover = All(i, Call("Fin", n), Imp(Seq(Neg, Sp, Par(Seq(i, Sp, InMacro, Sp, f))),
            Seq(i, Sp, InMacro, Sp, s)));
        Formula Bit(string side, Formula j) => Call(side, w, Call("get", s, j));
        var eventClaim = All(w, Call("Pair", Word(n), Word(n)),
            Imp(Rel(Call("P", s, f, x, y, h, g, w), Neq, D(0)),
                All(Seq(r, Comma, q), Call("Fin", Call("length", s)),
                    Imp(Rel(r, Leq, q), Imp(Rel(Bit("fst", r), Eq, Op("false")),
                        Imp(Rel(Bit("snd", r), Eq, Op("false")),
                            Rel(Bit("fst", q), Eq, Bit("snd", q))))))));
        var fibers = All(Seq(x, Comma, y), Word(n),
            All(h, Call("Nonempty", Call("C", k, n, f, x)),
                All(g, Call("Nonempty", Call("C", k, n, f, y)),
                    Imp(Call("FarSame", s, f, x, y), eventClaim))));
        return All(Seq(k, Comma, n), Nat, Imp(Rel(D(0), Lt, k),
            All(s, Call("List", Call("Fin", n)), Imp(Call("Nodup", s),
                Imp(Call("StrictlyIncreasing", s), All(f, Call("Finset", Call("Fin", n)),
                    Imp(free, Imp(cover, fibers))))))));
    }

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Word(Formula n) => Seq(Open, Call("Fin", n), Sp, To, Sp, Op("Bool"), Close);
    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Op(name), [.. args]);
    private static Formula Rel(Formula a, Formula r, Formula b) => Seq(a, Sp, r, Sp, b);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula All(Formula v, Formula t, Formula b) => Par(Seq(Forall, Sp, Open, v, Colon, t, Close, Comma, Sp, Par(b)));
    private static Formula Imp(Formula a, Formula b) => Par(Rel(Par(a), Implies, Par(b)));
}
