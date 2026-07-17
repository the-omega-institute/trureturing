using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Carrier;

internal sealed class GoldenRatioDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/Carrier/GoldenRatio",
            "The real golden ratio satisfies its radical, fixed-point, and conjugate identities."),
        H("Golden Ratio Identities"),
        Blocks(
            new DocumentBlock.Describe(
                DescribeId.Create("radical-fixed-point-and-conjugate-identities"),
                DescribeKind.Theorem,
                H("Radical, fixed-point, and conjugate identities"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S0/Carrier/GoldenRatio.golden_ratio_spec")),
                DescribeProvenance.LiteratureAttested(
                    LibraryNoteRef.Create("D5/L/koshy2001fibonacci")),
                Blocks(Paragraph(Text(
                    "One kernel-checked conjunction records the radical definition, the quadratic fixed point, and the negative-reciprocal conjugate identity.")))))));
}
