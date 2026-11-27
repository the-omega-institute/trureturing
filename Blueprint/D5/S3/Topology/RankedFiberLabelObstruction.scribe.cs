using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class RankedFiberLabelObstructionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/RankedFiberLabelObstruction.";

    private static DocumentBlock Entry(string id, string declaration, string heading, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration),
            H(heading), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rank bounds for lifting simplicial flags",
        H("Rank bounds for lifting simplicial flags"),
        Blocks(
            Entry("rank-capacity-in-one-fibre", "flag_omitted_of_unique_support",
                "A flag is omitted when its witnesses exceed the available ranks",
                "Each required coface contains a vertex whose old support includes a prescribed support. " +
                "Assume there is only one eligible vertex in the enclosing face, projection preserves old support, " +
                "and each coface label contains its projected vertex and stays in the source support. " +
                "All required witnesses then project to the unique eligible vertex, and the ranks available " +
                "in its fibre bound the distinct labels along a source chain."),
            Entry("rank-growth-in-isotone-lift", "card_add_le_of_lifted_flag_chain",
                "An isotone lift adds at least one source vertex per strict flag step",
                "If the initial singleton target flag records the retracted source face, the " +
                "source face starts with at least that cardinality. Along consecutive inclusion-comparable " +
                "source faces, each strict increase in the assigned target flags forces a strict inclusion in the source."))));
}
