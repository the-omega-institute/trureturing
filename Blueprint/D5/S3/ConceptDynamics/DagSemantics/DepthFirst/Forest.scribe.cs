using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagSemantics.DepthFirst;

internal sealed class ForestDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/DagSemantics/DepthFirst/Forest.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ConceptDynamics/zhao2023algorithm");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every root belongs to the forest support",
        H("Forest"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("forest-roots-in-support"),
                DeclarationHandle.Create(Prefix + "roots_subset_support"),
                H("Every root belongs to the forest support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The original structural induction places every forest root in its support."))),
                DescribeRole.Theorem),
            Paragraph(Text("The immutable source mapping, modification notices, full Apache-2.0 license and replacement condition are in Library/ConceptDynamics/zhao2023algorithm.md. These statements concern Lean values and the DFS invariant; they do not establish C# execution, collection or parser correspondence, or physical stack bounds.")))));
}
