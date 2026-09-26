using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagSemantics.DepthFirst;

internal sealed class SearchDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/DagSemantics/DepthFirst/Search.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ConceptDynamics/zhao2023algorithm");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Depth-first forest construction",
        H("Search"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("shared-visited-search"),
                DeclarationHandle.Create(Prefix + "dfsForest"),
                H("Depth-first forest construction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The algorithm marks a fresh vertex before descending, threads the child traversal's visited set into sibling traversal, and returns the original forest and final visited dictionary. The retained original proofs roots_dfsForest'_fst_subset, subset_visited_dfsForest'_snd and isDFSForest_dfsForest' establish its DFS invariant and supplied-root coverage. Their primed names are preserved."))),
                DescribeRole.Definition),
            Paragraph(Text("The immutable source mapping, modification notices, full Apache-2.0 license and replacement condition are in Library/ConceptDynamics/zhao2023algorithm.md. These statements concern Lean values and the DFS invariant; they do not establish C# execution, collection or parser correspondence, or physical stack bounds.")))));
}
