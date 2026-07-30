using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting;

internal sealed class NewmanDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/Rewriting/Newman",
            "Terminating locally confluent rewrite systems have unique reachable normal forms."),
        H("Newman Normal Forms"),
        Blocks(
            Paragraph(
                Text("For every terminating and locally confluent rewrite relation, each starting history reaches exactly one irreducible normal form through the reflexive transitive closure of the relation.")),
            Paragraph(
                Text("Newman 1942, literature-attested; this repository gives a direct proof because the pinned Mathlib version does not provide this lemma.")))));
}
