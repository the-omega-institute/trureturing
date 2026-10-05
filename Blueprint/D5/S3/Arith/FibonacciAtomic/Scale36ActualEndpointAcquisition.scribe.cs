using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class Scale36ActualEndpointAcquisitionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal Scale36 family and its conditional routing addresses.",
        H("Scale36 Actual Endpoint Acquisition"),
        Blocks(
            Paragraph(Text("The family has k active slots and one compensation slot. P0 uses C in "
                + "every active slot and KT at the tail. Uj replaces slot j by T and the tail by B; "
                + "Vj replaces slot j by W1 and the tail by A. All brackets are retained.")),
            Paragraph(Text("The public definitions preserve the original preimages and the four "
                + "literal request addresses a, b, q, r. The complete all-source controller "
                + "and exact endpoint theorem are open.")))));
}
