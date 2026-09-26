using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagSemantics.DepthFirst;

internal sealed class PostorderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/DagSemantics/DepthFirst/Postorder.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ConceptDynamics/zhao2023algorithm");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "DFS postorder and cycles",
        H("Postorder"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("postorder-return-path"),
                DeclarationHandle.Create(Prefix + "post_spec"),
                H("DFS postorder and cycles"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every DFS forest, postorder is duplicate-free and has exactly the forest support as members. An edge from an earlier to a later output vertex has a return path. No acyclicity is assumed. If no emitted vertex lies on a nonempty full-graph cycle, emitted dependencies precede their sources. With an empty initial visited set, acyclicity of the subgraph induced by emitted vertices suffices."))),
                DescribeRole.Theorem),
            Paragraph(Text("The immutable source mapping, modification notices, full Apache-2.0 license and replacement condition are in Library/ConceptDynamics/zhao2023algorithm.md. These statements concern Lean values and the DFS invariant; they do not establish C# execution, collection or parser correspondence, or physical stack bounds.")))));
}
