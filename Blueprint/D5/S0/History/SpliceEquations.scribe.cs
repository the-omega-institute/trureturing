using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History;

internal sealed class SpliceEquationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Marker-history splicing is pinned by its defining recursion, not by a library alias.",
        H("Splice Equations"),
        Blocks(
            Paragraph(
                Text("The marker-history carrier defines splicing through the free-monoid product. That definition is compact, but on its own it leaves a reader unable to check that the operation is the intended one: any product-shaped alias would typecheck equally well.")),
            Paragraph(
                Text("The theorem `splice_recursion_equations` states the two equations that determine splicing on its second argument. The empty history is the right unit, and prefixing a marker to the second argument prefixes the same marker to the result. Together they characterize the operation recursively, so the carrier's definition is verified against the intended recursion rather than assumed to implement it.")),
            Paragraph(
                Ref("D5/S0/History/SpliceEquations"),
                Text(" also carries a computational witness: splicing two one-marker histories yields the two-marker history whose leading marker comes from the second argument. The witness holds by reduction, so it exercises the definition itself rather than a restatement of it.")))));
}
