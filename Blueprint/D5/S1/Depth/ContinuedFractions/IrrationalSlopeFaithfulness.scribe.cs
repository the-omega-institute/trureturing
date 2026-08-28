using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth.ContinuedFractions;

internal sealed class IrrationalSlopeFaithfulnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Irrational slopes faithfully encode integer pairs, while the golden slope also has an effective finite-precision gap.",
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
                            + "fourth records the effective Hurwitz separation inequality that "
                            + "carries the golden ratio's additional finite-precision stability.")),
                    Paragraph(Text(
                        "For injectivity, equality of two encoded labels gives alpha times the "
                            + "difference of their first coordinates equal to an integer. A "
                            + "nonzero first-coordinate difference would make that product "
                            + "irrational, a contradiction. The remaining integer coordinates "
                            + "then agree. The golden conjugate is the distinct faithful witness, "
                            + "and the final clause is applied directly from the existing golden "
                            + "Hurwitz theorem."))),
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

    private static Formula FaithfulnessStatement()
    {
        Formula alpha = Alpha;
        Formula beta = Beta;
        Formula q = F.Id("q");
        return Disp(Seq(
            Forall, Sp, alpha, Sp, InMacro, Sp, Reals(), Comma, Esc,
            Irrational(alpha), Sp, Rightarrow, Sp, Open,
            Injective(alpha), Sp, Land, Sp,
            Open, Forall, Sp, beta, Sp, InMacro, Sp, Reals(), Comma, Esc,
              Irrational(beta), Sp, Rightarrow, Sp, Injective(beta), Close, Sp,
            Land, Sp, Open, Exists, Sp, beta, Sp, InMacro, Sp, Reals(), Comma, Esc,
              beta, Sp, Neq, Sp, Varphi, Sp, Land, Sp,
              Irrational(beta), Sp, Land, Sp, Injective(beta), Close, Sp,
            Land, Sp, Open, Forall, Sp, q, Sp, InMacro, Sp, Rationals(), Comma, Esc,
              Frac, Grp(D(1)), Grp(
                Sqrt, Grp(D(5)), Thin, Denominator(q), Caret, Grp(D(2)),
                Sp, Plus, Sp, Denominator(q)),
              Sp, Lt, Sp, Bar, Varphi, Sp, Minus, Sp, q, Bar, Close,
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

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));

    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
}
