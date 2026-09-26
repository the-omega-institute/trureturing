using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagSemantics.DepthFirst;

internal sealed class ForestInvariantDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/DagSemantics/DepthFirst/ForestInvariant.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ConceptDynamics/zhao2023algorithm");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Final visited set",
        H("ForestInvariant"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("visited-union"),
                DeclarationHandle.Create(Prefix + "union"),
                H("Final visited set"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The final visited set is the union of the initial visited set and forest support."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fresh-forest-support"),
                DeclarationHandle.Create(Prefix + "inter"),
                H("Fresh forest vertices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The initial visited set is disjoint from forest support."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("root-reachability"),
                DeclarationHandle.Create(Prefix + "sound"),
                H("Forest vertices are reachable"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Every forest vertex is reachable from a forest root."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("successors-marked"),
                DeclarationHandle.Create(Prefix + "succSet_support_subset"),
                H("Forest successors are visited"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Every successor of a forest vertex belongs to the final visited set. Generic Mathlib closure preservation extends this to paths when successors of initially visited vertices are also finally visited; no separate completeness wrapper is retained."))),
                DescribeRole.Theorem),
            Paragraph(Text("The immutable source mapping, modification notices, full Apache-2.0 license and replacement condition are in Library/ConceptDynamics/zhao2023algorithm.md. These statements concern Lean values and the DFS invariant; they do not establish C# execution, collection or parser correspondence, or physical stack bounds.")))));
}
