using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.SubQuorum;

internal sealed class HeawoodOrderTwoRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/SubQuorum/HeawoodOrderTwoRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/omega2026c4representatives");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A feasible optimal pair in the order-two incidence graph has singletons in both color classes.",
        H("The order-two exception to one-side support"),
        Blocks(
            Describe.Lean(DescribeId.Create("heawood-order-two-claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("One-side support from order two"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "The proposed extension quantifies over every finite simple graph, every proper two-coloring, "
                    + "and every natural order q at least two. The graph must have no four-cycle, have degree q+1 at every vertex, "
                    + "and have q squared plus q plus one vertices in each color class. For every feasible singleton and matching "
                    + "pair of that same objective, the conclusion requires a color class containing all singletons and requires "
                    + "every vertex in that class to be a singleton or a matching endpoint."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("heawood-order-two-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The binary Heawood counterexample"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "Use the source's binary labeling, with point vertices 0 through 6 and line vertices 7 through 13. "
                    + "Each side has the nonzero three-bit labels in increasing numeric order. Opposite-side vertices are "
                    + "incident when their binary dot product is zero. This graph is cubic and two distinct vertices share at "
                    + "most one neighbor, so there is no four-cycle. The six singletons are {1, 2, 3, 11, 12, 13} and "
                    + "the matching is {(0, 8)}. The matching is disjoint from the singletons, and each singleton has at most one "
                    + "neighbor among the occupied vertices, so the pair is feasible. The point side has singletons {1, 2, 3} "
                    + "and the line side has singletons {11, 12, 13}, three on each side. "
                    + "C4RepresentativeBounds.threshold_parameters at degree three and side size seven gives "
                    + "beta(H,2)=psiSq(H)=Omega(H)=7. The pair attains objective seven and refutes the one-side "
                    + "conclusion at q=2."))), DescribeRole.Theorem))));
}
