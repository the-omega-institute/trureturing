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
                DescribeId.Create("kbonacci-reset-ready-after-false"),
                DeclarationHandle.Create(
                    "D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling.reset_ready_after_false"),
                H("A common-false head prepares the reset test"),
                StatementSource.FromAuthor(Disp(ReadyFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let i be the head and t the remaining scan. Every site in t is "
                    + "strictly greater than i, and every coordinate outside insert(i,F) "
                    + "belongs to t. Thus all coordinates through i belong to insert(i,F). "
                    + "If the original histories agree at fixed coordinates beyond i, "
                    + "updating both head bits to false satisfies resetReady. This fact "
                    + "also gives the zero remaining-cost branch of right_scan_hamming."))),
                DescribeRole.Theorem),
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
                    + "with the refined histories. This support implication combines with "
                    + "the separate native emitted-tail estimate at the book's scan interface. "
                    + "Simultaneous Fin.rev transport and the final pointwise and Hamming "
                    + "assembly require additional results."))),
                DescribeRole.Theorem))));

    private static Formula ReadyFormula()
    {
        var n = F.Id("n"); var i = F.Id("i"); var t = F.Id("t"); var f = F.Id("F");
        var x = F.Id("x"); var y = F.Id("y"); var j = F.Id("j");
        var order = All(j, Call("Fin", n), Imp(Seq(j, Sp, InMacro, Sp, t), Rel(i, Lt, j)));
        var cover = All(j, Call("Fin", n), Imp(Seq(Neg, Sp,
            Par(Seq(j, Sp, InMacro, Sp, Call("insert", i, f)))), Seq(j, Sp, InMacro, Sp, t)));
        var far = All(j, Call("Fin", n), Imp(Seq(j, Sp, InMacro, Sp, f),
            Imp(Rel(i, Lt, j), Rel(Call("eval", x, j), Eq, Call("eval", y, j)))));
        var result = Call("resetReady", Call("insert", i, f),
            Call("update", x, i, Op("false")), Call("update", y, i, Op("false")));
        return All(n, Nat, All(i, Call("Fin", n), All(t, Call("List", Call("Fin", n)),
            All(f, Call("Finset", Call("Fin", n)), All(Seq(x, Comma, y), Word(n),
                Imp(order, Imp(cover, Imp(far, result))))))));
    }

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
