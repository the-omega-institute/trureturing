using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.EdgeLabeling;

internal sealed class CubicARGraphEventsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Counts additive collisions on three free edges after fixing labels one and two.",
        H("Free-triple bad events"),
        Blocks(Describe.Lean(
            DescribeId.Create("cubic-ar-free-triple-event"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/EdgeLabeling/CubicARGraphEvents.card_bad_free_triple"),
            H("The free-triple event bound"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Let E be a finite edge type of cardinality m at least six. Fix two "
                + "distinct edges p and q to labels one and two, and choose an injective "
                + "triple of edges disjoint from them. The number of marked bijective "
                + "labelings having an additive collision on this triple is at most "
                + "six times the additive-pair count times (m-5)!. Every collision "
                + "has a unique largest label and a sorted smaller pair. Ordering the "
                + "three edges therefore places its label assignment among the six "
                + "permutations of a sorted additive triple. Each such assignment "
                + "fixes five distinct edge values, so the extension-counting theorem "
                + "gives (m-5)! labelings. The finite union bound completes the count."))),
            DescribeRole.Theorem)),
        []));
}
