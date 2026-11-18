using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class KBonacciRightScanHammingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Right-scan Hamming estimate and common-false reset criterion.",
        H("Increasing scans of the entire free region"),
        Blocks(
            Paragraph(Text("Write W(n) for Fin n to Bool, C(k,n,F,x) for completions, and P(s,F,x,y,h,g) for the original prefixCoupling. The histories are arbitrary; h and g witness nonempty full legal completion fibers. The reset test and independent fallback branches are those of the original law.")),
            Describe.Lean(
                DescribeId.Create("kbonacci-reset-ready-after-false"),
                DeclarationHandle.Create(
                    "D5/S1/Words/AdmissibleWords/KBonacciRightScanHamming.reset_ready_after_false"),
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
                DescribeId.Create("kbonacci-right-scan-hamming"),
                DeclarationHandle.Create(
                    "D5/S1/Words/AdmissibleWords/KBonacciRightScanHamming.right_scan_hamming"),
                H("Expected internal Hamming cost for an increasing scan"),
                StatementSource.FromAuthor(Disp(CostFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "ExpectedHamming(J,s) is the sum over full-word pairs w of J(w)H(s,w). "
                    + "Before(s,i,j) means that i occurs strictly before j in the list s. "
                    + "H(s,w) denotes scanHamming: the sum of the zero-one disagreement "
                    + "indicators at the listed sites. The list is strictly increasing "
                    + "and lists the entire complement of F without repetitions. The "
                    + "fixed histories agree at every fixed site farther right than any "
                    + "scanned site. A supported common-zero branch has zero remaining "
                    + "cost, by screening and the reset law. In every other branch the "
                    + "current indicator is at most one, and the recursive expected "
                    + "remaining cost is at most one. Those branches have total mass "
                    + "at most one half, derived from conditional_step_coupling. "
                    + "Their weighted cost is therefore at most one. This estimate "
                    + "uses the same full-word joint law as the marginal theorem. "
                    + "The theorem covers short words and arbitrary nonempty completion "
                    + "fibers; it does not assert reflection, the geometric survival "
                    + "tail, or the final two-orientation contiguous-block assembly."))),
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

    private static Formula CostFormula()
    {
        var k = F.Id("k"); var n = F.Id("n"); var f = F.Id("F");
        var s = F.Id("s"); var x = F.Id("x"); var y = F.Id("y");
        var h = F.Id("h"); var g = F.Id("g");
        var i = F.Id("i"); var j = F.Id("j");
        var inS = Seq(i, Sp, InMacro, Sp, s);
        var notF = Seq(Neg, Sp, Par(Seq(i, Sp, InMacro, Sp, f)));
        var free = All(i, Call("Fin", n), Imp(inS, notF));
        var cover = All(i, Call("Fin", n), Imp(notF, inS));
        var order = All(i, Call("Fin", n), All(j, Call("Fin", n),
            Imp(Call("Before", s, i, j), Rel(Call("val", i), Lt, Call("val", j)))));
        var far = All(i, Call("Fin", n), All(j, Call("Fin", n), Imp(
            And(inS, Seq(j, Sp, InMacro, Sp, f), Rel(Call("val", i), Lt, Call("val", j))),
            Rel(Call("at", x, j), Eq, Call("at", y, j)))));
        var cost = Rel(Call("ExpectedHamming", Call("P", s, f, x, y, h, g), s), Leq, D(1));
        var fibers = All(Seq(x, Comma, y), Word(n),
            All(h, Call("Nonempty", Call("C", k, n, f, x)),
                All(g, Call("Nonempty", Call("C", k, n, f, y)), Imp(far, cost))));
        var fixedSet = All(f, Call("Finset", Call("Fin", n)), Imp(And(free, cover), fibers));
        var lists = All(s, Call("List", Call("Fin", n)), Imp(And(Call("Nodup", s), order), fixedSet));
        return All(Seq(k, Comma, n), Nat, Imp(Rel(D(0), Lt, k), lists));
    }

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Word(Formula n) => Seq(Open, Call("Fin", n), Sp, To, Sp, Op("Bool"), Close);
    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Op(name), [.. args]);
    private static Formula Rel(Formula a, Formula r, Formula b) => Seq(a, Sp, r, Sp, b);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula All(Formula v, Formula t, Formula b) => Par(Seq(Forall, Sp, Open, v, Colon, t, Close, Comma, Sp, Par(b)));
    private static Formula Imp(Formula a, Formula b) => Par(Rel(Par(a), Implies, Par(b)));
    private static Formula And(params Formula[] parts)
    {
        var result = new System.Collections.Generic.List<Formula>();
        for (var i = 0; i < parts.Length; ++i)
        {
            if (i > 0) result.Add(Seq(Sp, Land, Sp));
            result.Add(Par(parts[i]));
        }
        return Par(Seq([.. result]));
    }
}
