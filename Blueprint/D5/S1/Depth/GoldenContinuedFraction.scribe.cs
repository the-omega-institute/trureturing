using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth;

internal sealed class GoldenContinuedFractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("The continued fraction of the golden ratio has constant unit coefficients.",
        H("The Golden Continued Fraction"),
        Blocks(
            Describe.Lean(DescribeId.Create("golden-ratio-continued-fraction"),
                DeclarationHandle.Create("D5/S1/Depth/GoldenContinuedFraction.golden_ratio_continued_fraction"),
                H("Every continued-fraction coefficient is one"),
                StatementSource.FromAuthor(Disp(Seq(Varphi, Sp, Eq, Sp, OpenBracket, Thin, D(1), Semi, Overline, Grp(D(1)), Thin, CloseBracket))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "Mathlib's generalized continued fraction of the real golden ratio "
                                    + "has head one, and every subsequent numerator-denominator pair is "
                                    + "the pair (1, 1)."))),
                DescribeRole.Theorem))));
}
