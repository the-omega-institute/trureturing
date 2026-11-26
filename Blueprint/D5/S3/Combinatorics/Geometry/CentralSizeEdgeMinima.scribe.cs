using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class CentralSizeEdgeMinimaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/CentralSizeEdgeMinima.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Topology/mazhang2026centraledges");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An n-point metric space can have k central values exactly for the feasible pairs, and "
            + "each feasible pair needs at least and at most (k−1)⌈n/2⌉ central edges.",
        H("All feasible center sizes and sharp edge minima"),
        Blocks(
            Describe.Lean(DescribeId.Create("central-size-edge-minima-labels"),
                DeclarationHandle.Create(Prefix + "labO"),
                H("The odd-order packing"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "On the points 0,…,2m of Z/(2m+1), class r consists of the pairs with "
                    + "i+j ≡ r; it misses only the point u with 2u ≡ r. The classes 2m−1 and 2m "
                    + "are reserved; their union is a path from 2m to m. Orienting it towards m, "
                    + "every point except m has one outgoing reserved edge: {u, 2m−1−u} for u<m "
                    + "and {u, 2m−u} for m<u<2m. Class r<2m−1 borrows the outgoing edge of its "
                    + "missing point, so it covers every point with m+1 edges. labO records, for "
                    + "a pair i<j, the class that uses it, and 2m−1 for the one pair {0, 2m} "
                    + "nobody borrows. This is the packing in the proof of Corollary 7 of "
                    + "H. Ma and W. Zhang, who credit Andersen's cover-index criterion as its "
                    + "antecedent."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("central-size-edge-minima-feasible"),
                DeclarationHandle.Create(Prefix + "Feasible"),
                H("Feasible pairs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A pair (n,k) with n ≥ 1 is feasible when k=1 for n=1, k=2 for n=2, and "
                    + "1 ≤ k ≤ n for even n ≥ 4 or 1 ≤ k ≤ n−1 for odd n ≥ 3."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("central-size-edge-minima-result"),
                DeclarationHandle.Create(Prefix + "all_center_sizes"),
                H("Center sizes and edge minima"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For n ≥ 1, an n-point metric space with exactly k central values exists if "
                    + "and only if (n,k) is feasible, and then the least number of central edges "
                    + "is (k−1)⌈n/2⌉. Zero is always central and the central values form a finite "
                    + "set, so k ≥ 1; the edge-cover bound against the n(n−1)/2 pairs gives "
                    + "k ≤ n, and k ≤ n−1 for odd n ≥ 3; on two points the one distance is "
                    + "realized at both points, so k=2. The edge-cover bound is the lower bound "
                    + "on edges. For attainment, an even order 2m+2 takes the band whose first "
                    + "k−1 round-robin classes are central, and an odd order 2m+1 takes the band "
                    + "on the odd-order packing with its first k−1 classes central. Every other "
                    + "pair gets its own non-central distance. Each class r has m+1 edges: the "
                    + "edge at slot 0 and the chords ±t around the point u with 2u ≡ r for "
                    + "1 ≤ t ≤ m. So the central graph has at most (k−1)(m+1)=(k−1)⌈n/2⌉ edges. "
                    + "This is Corollary 7 of H. Ma and W. Zhang."))),
                DescribeRole.Theorem))));
}
