using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LinearForests;

internal sealed class AlternatingUndirectedCompletionLawDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef OrientationMultiplicity =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/greenhilljansonkimwormald2002pseudographs");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The extension event and conditional probability on actual alternating undirected cycles.",
        H("Alternating undirected cycle completions"),
        Blocks(Describe.Lean(
            DescribeId.Create("alternating-undirected-completion-law"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/LinearForests/AlternatingUndirectedCompletionLaw."
                + "alternating_undirected_completion_law"),
            H("Fixed-edge conditioning under the uniform alternating undirected cycle law"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(OrientationMultiplicity),
            Blocks(
                Paragraph(Text(
                    "A finite labelled vertex set has n vertices of each of two colors, "
                    + "with at least four vertices in total. An alternating completed graph "
                    + "is an undirected connected two-regular graph on these vertices whose "
                    + "edges have differently colored endpoints. The ambient carrier has "
                    + "n! (n−1)! / 2 such graphs.")),
                Paragraph(Text(
                    "Let F be any prescribed simple graph on the same vertices. The event "
                    + "that every edge of F is present consists of the alternating completed "
                    + "graphs extending F. Its uniform ambient probability is the number "
                    + "of those completions divided by the ambient count. The event has "
                    + "positive probability exactly when a completion exists. At positive "
                    + "probability, the uniform mass on those completions gives the "
                    + "conditioned law by inclusion into the ambient carrier.")),
                Paragraph(Text(
                    "A full-cycle successor permutation alternates precisely when its "
                    + "undirected shadow has cross-color edges. Restricting the shadow to "
                    + "alternating lifts therefore preserves its two-element fibers. The "
                    + "directed alternating count divided by two gives the ambient count. "
                    + "The inclusion of completed graphs identifies the fixed-edge law "
                    + "with uniform mass on the corresponding subset."))),
            DescribeRole.Theorem))));
}
