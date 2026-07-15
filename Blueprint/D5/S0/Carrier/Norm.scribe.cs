using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Carrier;

internal sealed class NormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/Carrier/Norm",
            "The golden norm is multiplicative and agrees with the scaled mathlib norm."),
        H("Golden Norm"),
        Blocks(
            Paragraph(
                Ref("D5/S0/Carrier/Norm"),
                Text(" defines `N(a+b*phi)=a^2+ab-b^2`. Multiplying an element by its conjugate eliminates the `phi` coordinate and produces this integer, which makes the multiplicativity proof a direct polynomial identity.")),
            Paragraph(
                Text("Under the doubled `Zsqrtd 5` coordinates from the carrier module, the mathlib norm is exactly four times the golden norm. This factor is the expected square of the coordinate scaling.")))));
}
