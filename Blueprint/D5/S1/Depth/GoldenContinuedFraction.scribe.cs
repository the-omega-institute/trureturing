using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth;

internal sealed class GoldenContinuedFractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Depth/GoldenContinuedFraction",
                "The continued fraction of the golden ratio has constant unit coefficients."),
            H("The Golden Continued Fraction"),
            Blocks(
                new DocumentBlock.Describe(
                    DescribeId.Create("golden-ratio-continued-fraction"),
                    DescribeKind.Theorem,
                    H("Every continued-fraction coefficient is one"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Depth/GoldenContinuedFraction.golden_ratio_continued_fraction")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Mathlib's generalized continued fraction of the real golden ratio "
                        + "has head one, and every subsequent numerator-denominator pair is "
                        + "the pair (1, 1)."))),
                    LatexStatement.Create(@"$$\varphi = [\,1;\overline{1}\,]$$")))));
}
