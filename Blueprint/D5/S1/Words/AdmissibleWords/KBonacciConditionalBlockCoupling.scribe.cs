using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class KBonacciConditionalBlockCouplingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditional next-bit couplings and zero screening for forbidden-run words.",
        H("Full exterior and sampled prefix"),
        Blocks(
            Paragraph(Text(
                "Write W(n) for Fin n to Bool and A(k,n,w) for the original "
                + "DBonacciAdmissible scanner. C(k,n,F,x) is the finite set of "
                + "legal full words w satisfying w(i)=x(i) for every i in F. "
                + "The fixed set F can contain the entire exterior of a contiguous "
                + "block and any sampled prefix. Both ends remain fixed. "
                + "L(F,x,h) is completionLaw, the uniform PMF on this fiber, "
                + "where h states that the fiber is nonempty.")),
            Paragraph(Text(
                "For PMFs p and q on Bool, J(p,q) denotes bitCoupling. Set "
                + "a=p(false) and b=q(false). If a is at most b, its masses at "
                + "(false,false), (false,true), (true,false), (true,true) are "
                + "a, zero, b-a, one-b. Otherwise exchange the two coordinates "
                + "of the same construction with a and b interchanged. "
                + "This is the finite shared-threshold next-bit law.")),
            Describe.Lean(
                DescribeId.Create("kbonacci-conditional-step-coupling"),
                DeclarationHandle.Create(
                    "D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling.conditional_step_coupling"),
                H("Exact conditional-bit marginals and a common zero"),
                StatementSource.FromAuthor(Disp(StepFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The laws p and q in the formula are the pushforwards of "
                    + "L(F,x,h) and L(F,y,g) by evaluation at i. Deleting the "
                    + "one at an unfixed coordinate gives an injection from "
                    + "one-completions into zero-completions while preserving "
                    + "all other bits. Thus each actual conditional zero mass "
                    + "is at least one half. The displayed joint law has exact "
                    + "marginals and common-zero mass equal to their minimum. "
                    + "No lower bound on word length relative to k is required."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kbonacci-zero-screening"),
                DeclarationHandle.Create(
                    "D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling.zero_screening"),
                H("A common zero screens the earlier prefix"),
                StatementSource.FromAuthor(Disp(ScreenFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Define S(x,z,t)(i) to be x(i) when i is at most z and "
                    + "t(i) otherwise. A forbidden window is either contained "
                    + "in the legal prefix, contained in the shared later "
                    + "assignment, or crosses z. The last possibility contains "
                    + "the specified zero. Hence replacing the legal prefix "
                    + "preserves the entire suffix-completion condition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kbonacci-reset-law-transport"),
                DeclarationHandle.Create(
                    "D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling.reset_law_transport"),
                H("Uniform suffix laws agree after reset"),
                StatementSource.FromAuthor(Disp(ResetFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "All coordinates through z are fixed. The two legal exterior "
                    + "words have a zero at z and agree at every fixed coordinate "
                    + "strictly after z. Prefix replacement S(y,z,w) is a bijection "
                    + "between their full completion fibers, with inverse S(x,z,w). "
                    + "It therefore transports the uniform conditional laws exactly. "
                    + "R(F,x,y,z) samples w from L(F,x) and returns the pair "
                    + "(w,S(y,z,w)); its two marginal pushforwards are exactly "
                    + "L(F,x) and L(F,y). Every coordinate strictly after z is preserved."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kbonacci-prefix-coupling-marginals"),
                DeclarationHandle.Create(
                    "D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling.prefix_coupling_marginals"),
                H("Stopped conditional recursion has exact full-word marginals"),
                StatementSource.FromAuthor(Disp(PrefixFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "P(s,F,x,y,h,g) denotes prefixCoupling. At each listed site, "
                    + "the finite next-bit joint law is bound to the recursively refined "
                    + "completion law. Its supported bit pairs have nonempty refined "
                    + "fibers. The marginal weight of a bit times its refined uniform "
                    + "completion mass is the original mass on that bit fiber; summing "
                    + "over Bool proves exact disintegration. If the fixed histories "
                    + "already contain a common screening zero and agree at all farther "
                    + "fixed sites, the recursion instead uses resetCoupling, with legal "
                    + "representatives chosen from the actual nonempty fibers. Uniform "
                    + "prefix transport proves both marginals in this stopped branch."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kbonacci-right-scan-hamming"),
                DeclarationHandle.Create(
                    "D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling.right_scan_hamming"),
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

    private static Formula StepFormula()
    {
        var k = F.Id("k"); var n = F.Id("n"); var f = F.Id("F");
        var x = F.Id("x"); var y = F.Id("y"); var i = F.Id("i");
        var h = F.Id("h"); var g = F.Id("g");
        var p = Call("evalLaw", f, x, h, i);
        var q = Call("evalLaw", f, y, g, i);
        var joint = Call("J", p, q);
        var conclusion = And(Rel(Call("mapFst", joint), Eq, p),
            Rel(Call("mapSnd", joint), Eq, q),
            Rel(Seq(D(1), Slash, D(2)), Leq,
                Call("mass", joint, Op("false"), Op("false"))));
        var unfixed = Seq(Neg, Sp, Par(Seq(i, Sp, InMacro, Sp, f)));
        var atSite = All(i, Call("Fin", n), Imp(unfixed, conclusion));
        var fibers = All(h, Call("Nonempty", Call("C", k, n, f, x)),
            All(g, Call("Nonempty", Call("C", k, n, f, y)), atSite));
        return All(Seq(k, Comma, n), Nat,
            Imp(Rel(D(0), Lt, k), All(f, Call("Finset", Call("Fin", n)),
                All(Seq(x, Comma, y), Word(n), fibers))));
    }

    private static Formula ScreenFormula()
    {
        var k = F.Id("k"); var n = F.Id("n");
        var x = F.Id("x"); var y = F.Id("y");
        var z = F.Id("z"); var t = F.Id("t");
        var condition = And(Rel(Call("at", x, z), Eq, Op("false")),
            Rel(Call("at", y, z), Eq, Op("false")));
        var conclusion = All(t, Word(n), Rel(Call("A", k, n, Call("S", x, z, t)),
            Iff, Call("A", k, n, Call("S", y, z, t))));
        var atZero = All(z, Call("Fin", n), Imp(condition, conclusion));
        return All(Seq(k, Comma, n), Nat, Imp(Rel(D(0), Lt, k),
            All(Seq(x, Comma, y), Word(n), Imp(
                And(Call("A", k, n, x), Call("A", k, n, y)), atZero))));
    }

    private static Formula ResetFormula()
    {
        var k = F.Id("k"); var n = F.Id("n"); var f = F.Id("F");
        var x = F.Id("x"); var y = F.Id("y"); var z = F.Id("z");
        var i = F.Id("i"); var w = F.Id("w");
        var fixedLeft = All(i, Call("Fin", n), Imp(Rel(Call("val", i), Leq, Call("val", z)),
            Seq(i, Sp, InMacro, Sp, f)));
        var farSame = All(i, Call("Fin", n), Imp(
            And(Seq(i, Sp, InMacro, Sp, f), Rel(Call("val", z), Lt, Call("val", i))),
            Rel(Call("at", x, i), Eq, Call("at", y, i))));
        var unchanged = All(w, Word(n), All(i, Call("Fin", n),
            Imp(Rel(Call("val", z), Lt, Call("val", i)),
                Rel(Call("at", Call("S", y, z, w), i), Eq, Call("at", w, i)))));
        var marginals = And(
            Rel(Call("mapFst", Call("R", f, x, y, z)), Eq, Call("L", f, x)),
            Rel(Call("mapSnd", Call("R", f, x, y, z)), Eq, Call("L", f, y)));
        var conclusion = And(
            Rel(Call("mapReset", Call("L", f, x), y, z), Eq, Call("L", f, y)),
            unchanged, marginals);
        var assumptions = And(Rel(Call("at", x, z), Eq, Op("false")),
            Rel(Call("at", y, z), Eq, Op("false")), fixedLeft, farSame);
        return All(Seq(k, Comma, n), Nat, Imp(Rel(D(0), Lt, k),
            All(f, Call("Finset", Call("Fin", n)), All(Seq(x, Comma, y), Word(n),
                Imp(And(Call("A", k, n, x), Call("A", k, n, y)),
                    All(z, Call("Fin", n), Imp(assumptions, conclusion)))))));
    }

    private static Formula PrefixFormula()
    {
        var k = F.Id("k"); var n = F.Id("n"); var f = F.Id("F");
        var s = F.Id("s"); var x = F.Id("x"); var y = F.Id("y");
        var h = F.Id("h"); var g = F.Id("g"); var i = F.Id("i");
        var joint = Call("P", s, f, x, y, h, g);
        var free = All(i, Call("Fin", n), Imp(Seq(i, Sp, InMacro, Sp, s),
            Seq(Neg, Sp, Par(Seq(i, Sp, InMacro, Sp, f)))));
        var conclusion = And(Rel(Call("mapFst", joint), Eq, Call("L", f, x, h)),
            Rel(Call("mapSnd", joint), Eq, Call("L", f, y, g)));
        var fibers = All(Seq(x, Comma, y), Word(n),
            All(h, Call("Nonempty", Call("C", k, n, f, x)),
                All(g, Call("Nonempty", Call("C", k, n, f, y)), conclusion)));
        var fixedSet = All(f, Call("Finset", Call("Fin", n)), Imp(free, fibers));
        var lists = All(s, Call("List", Call("Fin", n)), Imp(Call("Nodup", s), fixedSet));
        return All(Seq(k, Comma, n), Nat, Imp(Rel(D(0), Lt, k), lists));
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
