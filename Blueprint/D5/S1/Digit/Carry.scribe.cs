using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class CarryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeDocument.Create(
            Header(
                "D5/S1/Digit/Carry",
                "Four local Fibonacci carry rules preserve the value of finite raw W digits.",
                AnchorCatalogDefinitions.MathlibZeckendorfModule),
            H("Local Carry Rules"),
            Blocks(
                Paragraph(
                    Ref("D5/S1/Digit/Carry"),
                    Text(" defines the local, value-preserving carry rewrites on raw W-digit strings: adjacent ones merge upward, and doubled coefficients split by the Fibonacci identities for indices zero, one, and the general shifted case. Each rule carries its own value-preservation theorem against `rawValue`.")),
                Paragraph(
                    Text("Termination and the normalization map are deliberately absent here; they live in `D5/S1/Digit/Normalize` with an explicit well-founded measure, so no rule in this file claims more than one local step.")))));
}
