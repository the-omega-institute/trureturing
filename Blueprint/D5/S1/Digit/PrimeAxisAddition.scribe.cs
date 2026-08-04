using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class PrimeAxisAdditionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Digit/PrimeAxisAddition",
            "Rowwise W normalization of prime-axis table sums decodes as multiplication."),
        H("Prime-Axis Normalized Addition"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("prime-axis-rowwise-normalization-product"),
                H("Rowwise normalized addition and decoder multiplication"),
                LeanTheorem(
                    "D5/S1/Digit/PrimeAxisAddition.prime_axis_addition_spec"),
                Disp(Seq(Forall, Sp, F.Id("z"), Comma, F.Id("w"), Sp, InMacro, Sp, Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc, Operatorname, Grp(F.Id("Bijective")), Open, Operatorname, Grp(F.Id("primeAxisEncoding")), Close, Sp, Land, Sp, Operatorname, Grp(F.Id("decodePrimeAxisTable")), Open, Operatorname, Grp(F.Id("normalizedPrimeAxisAdd")), Open, F.Id("z"), Comma, F.Id("w"), Close, Close, Sp, Eq, Sp, Operatorname, Grp(F.Id("decodePrimeAxisTable")), Open, F.Id("z"), Close, Operatorname, Grp(F.Id("decodePrimeAxisTable")), Open, F.Id("w"), Close)),                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Prime-indexed canonical W rows are equivalent to positive naturals. Adding raw rows and applying the existing local W normalizer preserves exponent sums, so the finite prime-power decoder turns the normalized table sum into multiplication.")))
            ))));
}
