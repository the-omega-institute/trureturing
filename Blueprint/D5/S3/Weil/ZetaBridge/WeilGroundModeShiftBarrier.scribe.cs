using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilGroundModeShiftBarrierDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/WeilGroundModeShiftBarrier.";
    private static Formula Call(string name, params Formula[] args)
    {
        var result = new System.Collections.Generic.List<Formula>
            { Operatorname, Grp(F.Id(name)), Open };
        for (int i = 0; i < args.Length; i++)
        {
            if (i > 0) { result.Add(Comma); result.Add(Sp); }
            result.Add(args[i]);
        }
        result.Add(Close);
        return Seq(result.ToArray());
    }
    private static Formula Sq(Formula value) => Seq(Grp(value), Caret, Grp(D(2)));
    private static Formula Mass(Formula value) => Call("M", value);
    private static Formula Corr(Formula f, Formula g) => Call("C", f, g);
    private static Formula Energy(Formula f, Formula g) => Call("W", f, g);

    public DocumentDefinition Create()
    {
        Formula f = F.Id("f"), g = F.Id("g"), x = F.Id("x");
        Formula t = F.Id("t"), c = F.Id("c"), mu = F.Id("mu");
        Formula delta = F.Id("delta"), r = F.Id("r");
        Formula bf = Call("B", f), bg = Call("B", g), bbf = Call("B", bf);
        Formula bfx = Seq(bf, Open, x, Close);
        Formula cc = Call("HasCompactSupport", f);
        Formula residual = Seq(Re, Open,
            Energy(f, bbf), Minus, mu, Sp,
            Corr(f, bbf), Open, D(0), Close, Close);
        Formula gap = Seq(Grp(mu, Plus, delta), Sp, Mass(bf), Leq, Sp,
            Re, Open, Energy(bf, bf), Close);
        Formula residualBound = Seq(Sq(residual), Leq, Sp, Sq(r), Sp, Mass(bbf));
        Formula conclusion = Seq(Sq(delta), Sp, Mass(bf), Leq, Sp,
            D(3), Grp(D(2), Plus, Sq(c)), Sp, Sq(r));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Symmetric translations give an exact correlation identity and a necessary "
                + "residual cost for a complement gap of the arithmetic Weil form.",
            H("Weil Ground-Mode Shift Barrier"),
            Blocks(
                Paragraph(Text(
                    "C(f,g) denotes the existing Zeta23.EF.weilTest correlation. "
                    + "W(f,g) denotes Zeta23.EF.literatureRHS applied to C(f,g), "
                    + "including the canonical prime-power, pole-pair and Gamma terms. "
                    + "M(h) is the Lebesgue integral of Complex.normSq(h(x)). "
                    + "B abbreviates symmetricShiftDefect(t,c); t and c are real. "
                    + "Nonzero is the predicate that a function is not identically zero.")),
                Describe.Lean(
                    DescribeId.Create("symmetric-shift-defect"),
                    DeclarationHandle.Create(Owner + "symmetricShiftDefect"),
                    H("The explicit symmetric translation probe"),
                    StatementSource.FromAuthor(Disp(Seq(
                        bfx, Eq, Sp,
                        f, Open, x, Minus, t, Close, Plus,
                        f, Open, x, Plus, t, Close, Minus, c, Sp,
                        f, Open, x, Close))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The input function is arbitrary on the real line with complex values. "
                        + "This probe uses two translations and a real scalar. "
                        + "It makes no reference to an unknown eigenfunction."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("weil-symmetric-shift-transfer"),
                    DeclarationHandle.Create(Owner + "weil_symmetric_shift_transfer"),
                    H("Transfer through the complete correlation function"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("Continuous", f), Land, Sp, Call("Continuous", g), Land, Sp,
                        cc, Sp, Rightarrow, Sp, Corr(bf, g), Eq, Sp, Corr(f, bg)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "This is equality of functions at every correlation displacement. "
                        + "Only f needs compact support. The proof justifies the integral "
                        + "splittings and translates the integration variable. "
                        + "Substitution g=B(f) gives C(B(f),B(f))=C(f,B(B(f))). "
                        + "Applying the existing arithmetic functional transfers every "
                        + "prime sample and both analytic contributions simultaneously."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("symmetric-shift-defect-nonzero"),
                    DeclarationHandle.Create(Owner + "symmetric_shift_defect_ne_zero"),
                    H("The compactly supported probe cannot vanish"),
                    StatementSource.FromAuthor(Disp(Seq(
                        cc, Land, Sp, Call("Nonzero", f), Land, Sp,
                        Call("Positive", t), Sp, Rightarrow, Sp, Call("Nonzero", bf)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Positive(t) means 0<t. No continuity assumption is needed here. "
                        + "If B(f) vanished, the values of f on each arithmetic progression "
                        + "would satisfy a second-order recurrence. Compact support supplies "
                        + "two consecutive terminal zeros, and backward induction gives f=0. "
                        + "For continuous nonzero f, this also implies positive L2 mass of B(f); "
                        + "the public conclusion itself is function nonvanishing."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("weil-symmetric-shift-residual-barrier"),
                    DeclarationHandle.Create(Owner + "weil_symmetric_shift_residual_barrier"),
                    H("A complement gap requires a definite arithmetic residual"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("ContDiff", D(2), f), Land, Sp, cc, Land, Sp,
                        D(0), Leq, delta, Land, Sp, Grp(gap), Land, Sp,
                        Grp(residualBound), Sp, Rightarrow, Sp, conclusion))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "ContDiff(2,f) means ContDiff real 2 f. All five parameters "
                        + "t,c,mu,delta,r are real. The gap premise is tested on the single "
                        + "explicit direction B(f); it is not a theorem establishing a gap "
                        + "for the Weil operator. The residual premise is its squared real "
                        + "directional bound on B(B(f)), written with the exact arithmetic "
                        + "functional and zero-displacement correlation. Cauchy-Schwarz "
                        + "supplies this premise from an operator residual only after domain "
                        + "compatibility has been established. The proof combines the transfer "
                        + "identity with M(B(h)) <= 3(2+c^2)M(h), and treats zero mass separately. "
                        + "For a fixed support window, both translated tests must be admissible. "
                        + "Candidates with nontrivial boundary leakage are outside that interior "
                        + "application. No simplicity, evenness of the lowest mode, all-scale "
                        + "coercivity, or convergence to Xi is asserted."))),
                    DescribeRole.Theorem))));
    }
}
