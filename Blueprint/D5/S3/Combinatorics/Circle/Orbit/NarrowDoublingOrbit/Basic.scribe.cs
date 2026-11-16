using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.Orbit.NarrowDoublingOrbit;

internal sealed class NarrowDoublingOrbitBasicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shared original NarrowDoublingOrbit foundation, extracted without changing the mathematical statements.",
        H("Shared NarrowDoublingOrbit foundation"),
        Blocks(Paragraph(Text("The original definitions and proofs are the common dependency of the retained mathematical consumers. Shared originals are exposed directly; no forwarding theorem is introduced. Compilation, axiom closure and exact endpoint scope are checked at the consuming modules."))),
        []));
}
