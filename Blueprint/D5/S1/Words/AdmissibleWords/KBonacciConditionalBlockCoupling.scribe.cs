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
                    + "It therefore transports the uniform conditional laws exactly, "
                    + "and every coordinate strictly after z is preserved."))),
                DescribeRole.Theorem))));

    private static Formula StepFormula()
    {
        var k = F.Id("k"); var n = F.Id("n"); var f = F.Id("F");
        var x = F.Id("x"); var y = F.Id("y"); var i = F.Id("i");
        var h = F.Id("h"); var g = F.Id("g");
        var p = Call("evalLaw", f, x, h, i);
        var q = Call("evalLaw", f, y, g, i);
        var joint = Call("J", p, q);
        return All(Seq(k, Comma, n), Nat,
            Imp(Rel(D(0), Lt, k), All(f, Call("Finset", Call("Fin", n)),
                All(Seq(x, Comma, y), Word(n),
                    All(h, Call("Nonempty", Call("C", k, n, f, x)),
                        All(g, Call("Nonempty", Call("C", k, n, f, y)),
                            All(i, Call("Fin", n), Imp(
                                Seq(Neg, Sp, Par(Seq(i, Sp, InMacro, Sp, f))),
                                And(Rel(Call("mapFst", joint), Eq, p),
                                    Rel(Call("mapSnd", joint), Eq, q),
                                    Rel(Seq(D(1), Slash, D(2)), Leq,
                                        Call("mass", joint, Op("false"), Op("false")))))))))));
    }

    private static Formula ScreenFormula()
    {
        var k = F.Id("k"); var n = F.Id("n");
        var x = F.Id("x"); var y = F.Id("y");
        var z = F.Id("z"); var t = F.Id("t");
        return All(Seq(k, Comma, n), Nat, Imp(Rel(D(0), Lt, k),
            All(Seq(x, Comma, y), Word(n), Imp(
                And(Call("A", k, n, x), Call("A", k, n, y)),
                All(z, Call("Fin", n), Imp(
                    And(Rel(Call("at", x, z), Eq, Op("false")),
                        Rel(Call("at", y, z), Eq, Op("false"))),
                    All(t, Word(n), Rel(Call("A", k, n, Call("S", x, z, t)),
                        Iff, Call("A", k, n, Call("S", y, z, t)))))))));
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
        return All(Seq(k, Comma, n), Nat, Imp(Rel(D(0), Lt, k),
            All(f, Call("Finset", Call("Fin", n)), All(Seq(x, Comma, y), Word(n),
                Imp(And(Call("A", k, n, x), Call("A", k, n, y)),
                    All(z, Call("Fin", n), Imp(
                        And(Rel(Call("at", x, z), Eq, Op("false")),
                            Rel(Call("at", y, z), Eq, Op("false")), fixedLeft, farSame),
                        And(Rel(Call("mapReset", Call("L", f, x), y, z), Eq, Call("L", f, y)),
                            All(w, Word(n), All(i, Call("Fin", n),
                                Imp(Rel(Call("val", z), Lt, Call("val", i)),
                                    Rel(Call("at", Call("S", y, z, w), i), Eq,
                                        Call("at", w, i))))))))))));
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
