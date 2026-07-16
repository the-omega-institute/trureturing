using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class PrimeAxisAdditionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Digit/PrimeAxisAddition",
            "Rowwise W normalization of prime-axis table sums decodes as multiplication."),
        H("Prime-Axis Normalized Addition"),
        Blocks(
            new DocumentBlock.Describe(
                DescribeId.Create("prime-axis-rowwise-normalization-product"),
                DescribeKind.Theorem,
                H("Rowwise normalized addition and decoder multiplication"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S1/Digit/PrimeAxisAddition.prime_axis_addition_spec")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Prime-indexed canonical W rows are equivalent to positive naturals. Adding raw rows and applying the existing local W normalizer preserves exponent sums, so the finite prime-power decoder turns the normalized table sum into multiplication.")))))));
}
