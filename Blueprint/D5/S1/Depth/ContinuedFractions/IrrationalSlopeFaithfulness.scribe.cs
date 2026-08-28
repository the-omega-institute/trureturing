using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth.ContinuedFractions;

internal sealed class IrrationalSlopeFaithfulnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Irrational slopes faithfully encode integer pairs; the golden encoding also separates distinct labels within a finite horizontal precision budget.",
        H("Irrational Slope Faithfulness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("integer-pair-slope-encoding"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness.slopeEncoding"),
                H("The slope encoding"),
                StatementSource.FromAuthor(EncodingDefinition()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a real slope alpha, the encoding sends the integer label (m,n) to "
                        + "alpha times m plus n. This is the E_alpha used in the theorem; its "
                        + "carrier is the actual product of two integer copies, not a finite "
                        + "enumeration or an abstract replacement."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-precision-gap"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness."
                    + "finitePrecisionGap"),
                H("The effective finite-precision gap"),
                StatementSource.FromAuthor(FinitePrecisionGapDefinition()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At precision P, the visible separation threshold is "
                        + "1/(sqrt(5) P + 1). It decreases as the horizontal budget grows."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-precision-stability"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness."
                    + "FinitePrecisionStable"),
                H("Finite-precision stability observes the encoding"),
                StatementSource.FromAuthor(FinitePrecisionStableDefinition()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At every positive precision P, any two distinct integer-pair labels whose "
                        + "first-coordinate displacement is at most P must have encoded outputs "
                        + "separated by more than the precision-dependent gap. Thus even a "
                        + "nonzero constant encoding fails this property."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("irrational-slope-faithfulness"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness."
                    + "irrational_slope_faithfulness"),
                H("Every irrational slope is faithful"),
                StatementSource.FromAuthor(FaithfulnessStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The four displayed clauses mirror the four statement-level claims. "
                            + "The first gives injectivity at the fixed irrational slope. The "
                            + "second quantifies the same faithfulness over every irrational "
                            + "slope. The third supplies a faithful irrational slope distinct "
                            + "from the golden ratio, so golden faithfulness is not unique. The "
                            + "fourth directly asserts pairwise finite-precision stability of "
                            + "the golden encoding; it contains no additional public Hurwitz "
                            + "assertion.")),
                    Paragraph(Text(
                        "For injectivity, equality of two encoded labels gives alpha times the "
                            + "difference of their first coordinates equal to an integer. A "
                            + "nonzero first-coordinate difference would make that product "
                            + "irrational, a contradiction. The remaining integer coordinates "
                            + "then agree. The golden conjugate is the distinct faithful witness, "
                            + "and the existing golden Hurwitz theorem supplies the arithmetic "
                            + "estimate used internally to prove the pairwise output gap."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S1/Depth/GoldenHurwitzBound")),
        ]));

    private static Formula EncodingDefinition()
    {
        Formula alpha = Alpha;
        Formula m = F.Id("m");
        Formula n = F.Id("n");
        return Disp(Seq(
            Encoding(alpha), Sp, Colon, Sp, Integers(), Caret, Grp(D(2)),
            Sp, To, Sp, Reals(), Comma, Esc,
            Encoding(alpha), Open, m, Comma, n, Close, Sp, Eq, Sp,
            alpha, Sp, Cdot, Sp, m, Sp, Plus, Sp, n));
    }

    private static Formula FinitePrecisionGapDefinition()
    {
        Formula precision = F.Id("P");
        return Disp(Seq(
            PrecisionGap(precision), Sp, Eq, Sp,
            Frac, Grp(D(1)), Grp(
                Sqrt, Grp(D(5)), Sp, precision, Sp, Plus, Sp, D(1))));
    }

    private static Formula FinitePrecisionStableDefinition()
    {
        Formula encoding = F.Id("F");
        Formula precision = F.Id("P");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula leftFirst = Seq(left, Underscore, Grp(D(1)));
        Formula rightFirst = Seq(right, Underscore, Grp(D(1)));
        return Disp(Seq(
            FiniteStable(encoding), Sp, Iff, Sp,
            Forall, Sp, precision, Sp, InMacro, Sp, Naturals(), Comma, Esc,
            D(0), Sp, Lt, Sp, precision, Sp, Rightarrow, Sp,
            Forall, Sp, left, Comma, Sp, right, Sp, InMacro, Sp,
            Integers(), Caret, Grp(D(2)), Comma, Esc,
            Bar, leftFirst, Sp, Minus, Sp, rightFirst, Bar,
            Sp, Leq, Sp, precision, Sp, Rightarrow, Sp,
            left, Sp, Neq, Sp, right, Sp, Rightarrow, Sp,
            PrecisionGap(precision), Sp, Lt, Sp,
            Bar, encoding, Open, left, Close, Sp, Minus, Sp,
            encoding, Open, right, Close, Bar));
    }

    private static Formula FaithfulnessStatement()
    {
        Formula alpha = Alpha;
        Formula beta = Beta;
        return Disp(Seq(
            Forall, Sp, alpha, Sp, InMacro, Sp, Reals(), Comma, Esc,
            Irrational(alpha), Sp, Rightarrow, Sp, Open,
            Injective(alpha), Sp, Land, Sp,
            Open, Forall, Sp, beta, Sp, InMacro, Sp, Reals(), Comma, Esc,
              Irrational(beta), Sp, Rightarrow, Sp, Injective(beta), Close, Sp,
            Land, Sp, Open, Exists, Sp, beta, Sp, InMacro, Sp, Reals(), Comma, Esc,
              beta, Sp, Neq, Sp, Varphi, Sp, Land, Sp,
              Irrational(beta), Sp, Land, Sp, Injective(beta), Close, Sp,
            Land, Sp, FiniteStable(Encoding(Varphi)),
            Close));
    }

    private static Formula Encoding(Formula slope) =>
        Seq(F.Id("E"), Underscore, Grp(slope));

    private static Formula Irrational(Formula value) =>
        Seq(Operatorname, Grp(F.Id("Irrational")), Open, value, Close);

    private static Formula Injective(Formula slope) =>
        Seq(Operatorname, Grp(F.Id("Injective")), Open, Encoding(slope), Close);

    private static Formula PrecisionGap(Formula precision) =>
        Seq(F.Id("g"), Open, precision, Close);

    private static Formula FiniteStable(Formula encoding) =>
        Seq(Operatorname, Grp(F.Id("FinitePrecisionStable")), Open, encoding, Close);

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
