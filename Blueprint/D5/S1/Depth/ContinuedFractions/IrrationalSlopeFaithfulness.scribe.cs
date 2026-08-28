using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth.ContinuedFractions;

internal sealed class IrrationalSlopeFaithfulnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Irrational slopes faithfully encode integer pairs; the golden encoding also separates bounded-denominator labels by an effective finite-precision gap.",
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
                DescribeId.Create("rational-approximation-label"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness."
                    + "rationalApproximationLabel"),
                H("Rational approximations as integer labels"),
                StatementSource.FromAuthor(RationalApproximationLabelDefinition()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A reduced rational q supplies the primitive integer label "
                        + "(den(q), -num(q)). Its golden slope encoding is the unnormalized "
                        + "separation den(q) times (phi - q)."))),
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
                        + "1/(sqrt(5) P + 1). It decreases as the denominator budget grows."))),
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
                    "For every positive precision P and rational q with denominator at most P, "
                        + "the actual encoded primitive label must remain farther from zero than "
                        + "the precision-dependent gap. A constant encoding fails this property."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-finite-precision-stability"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness."
                    + "GoldenFinitePrecisionStability"),
                H("The golden Hurwitz certificate is tied to the golden encoding"),
                StatementSource.FromAuthor(GoldenFinitePrecisionStabilityDefinition()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This package preserves the prior rational Hurwitz bound and also carries "
                        + "its finite-precision interpretation for the actual map E_phi. The "
                        + "second field is the separation bridge absent from the earlier type."))),
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
                            + "fourth is the golden finite-precision package: it preserves the "
                            + "Hurwitz inequality and applies it to encoded labels at every "
                            + "explicit denominator precision.")),
                    Paragraph(Text(
                        "For injectivity, equality of two encoded labels gives alpha times the "
                            + "difference of their first coordinates equal to an integer. A "
                            + "nonzero first-coordinate difference would make that product "
                            + "irrational, a contradiction. The remaining integer coordinates "
                            + "then agree. The golden conjugate is the distinct faithful witness, "
                            + "and the existing golden Hurwitz theorem yields a positive encoded "
                            + "separation after scaling by each rational denominator."))),
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

    private static Formula RationalApproximationLabelDefinition()
    {
        Formula q = F.Id("q");
        return Disp(Seq(
            ApproximationLabel(q), Sp, Eq, Sp, Open,
            Denominator(q), Comma, Sp, Minus, Numerator(q), Close));
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
        Formula q = F.Id("q");
        return Disp(Seq(
            FiniteStable(encoding), Sp, Iff, Sp,
            Forall, Sp, precision, Sp, InMacro, Sp, Naturals(), Comma, Esc,
            D(0), Sp, Lt, Sp, precision, Sp, Rightarrow, Sp,
            Forall, Sp, q, Sp, InMacro, Sp, Rationals(), Comma, Esc,
            Denominator(q), Sp, Leq, Sp, precision, Sp, Rightarrow, Sp,
            PrecisionGap(precision), Sp, Lt, Sp,
            Bar, encoding, Open, ApproximationLabel(q), Close, Bar));
    }

    private static Formula GoldenFinitePrecisionStabilityDefinition()
    {
        Formula q = F.Id("q");
        return Disp(Seq(
            GoldenStability(), Sp, Iff, Sp, Open,
            Open, Forall, Sp, q, Sp, InMacro, Sp, Rationals(), Comma, Esc,
              Frac, Grp(D(1)), Grp(
                Sqrt, Grp(D(5)), Thin, Denominator(q), Caret, Grp(D(2)),
                Sp, Plus, Sp, Denominator(q)),
              Sp, Lt, Sp, Bar, Varphi, Sp, Minus, Sp, q, Bar, Close,
            Sp, Land, Sp, FiniteStable(Encoding(Varphi)), Close));
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
            Land, Sp, GoldenStability(),
            Close));
    }

    private static Formula Encoding(Formula slope) =>
        Seq(F.Id("E"), Underscore, Grp(slope));

    private static Formula Irrational(Formula value) =>
        Seq(Operatorname, Grp(F.Id("Irrational")), Open, value, Close);

    private static Formula Injective(Formula slope) =>
        Seq(Operatorname, Grp(F.Id("Injective")), Open, Encoding(slope), Close);

    private static Formula Denominator(Formula q) =>
        Seq(Operatorname, Grp(F.Id("den")), Open, q, Close);

    private static Formula Numerator(Formula q) =>
        Seq(Operatorname, Grp(F.Id("num")), Open, q, Close);

    private static Formula ApproximationLabel(Formula q) =>
        Seq(F.Id("ell"), Underscore, Grp(q));

    private static Formula PrecisionGap(Formula precision) =>
        Seq(F.Id("g"), Open, precision, Close);

    private static Formula FiniteStable(Formula encoding) =>
        Seq(Operatorname, Grp(F.Id("FinitePrecisionStable")), Open, encoding, Close);

    private static Formula GoldenStability() =>
        Seq(Operatorname, Grp(F.Id("GoldenFinitePrecisionStability")));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));

    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
