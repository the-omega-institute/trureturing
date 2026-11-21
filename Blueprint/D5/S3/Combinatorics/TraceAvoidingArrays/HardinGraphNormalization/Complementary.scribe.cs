using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization;

internal sealed class ComplementaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization/Complementary.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2013a233170");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal complementary-colour normalization by partition and free signs.",
        H("Arbitrary palettes on finite ordered graphs"),
        Blocks(
            PairNode("complement", "complement", "The literal complementary colour", DescribeRole.Definition,
                "For c in Fin (2p), the complementary colour is 2p−1−c."),
            PairNode("pair-label", "pair", "The lower colour labels the pair", DescribeRole.Definition,
                "The label is min(c,2p−1−c) in Fin p."),
            PairNode("pair-sign", "sign", "The sign of the actual colour", DescribeRole.Definition,
                "The sign is true exactly when p≤c."),
            PairNode("pair-lift", "lift", "The literal lifting map", DescribeRole.Definition,
                "The lower sign gives t and the upper sign gives 2p−1−t."),
            PairNode("colour-equiv", "colourEquiv", "The pair label and sign recover every literal colour", DescribeRole.Definition,
                "The two palette halves give inverse maps Fin (2p) and Fin p × Bool."),
            PairNode("bond-iff", "bond_iff", "Unequal pair labels characterize legal bonds", DescribeRole.Theorem,
                "For every natural p and c,d in Fin (2p), pair c differs from pair d exactly when c differs from d and their natural values do not sum to 2p−1."),
            PairNode("pair-first", "First", "The first vertex of a label class", DescribeRole.Definition,
                "Every strictly earlier vertex has a different label."),
            PairNode("pair-free", "Free", "The vertices with a free sign", DescribeRole.Definition,
                "A free vertex has an earlier vertex with the same pair label."),
            PairNode("pair-normal", "Normal", "The arbitrary-p first-appearance convention", DescribeRole.Definition,
                "The pair word is canonical and every first vertex has the lower sign. Canonicality gives each smaller label an earlier occurrence, so the used labels form an initial segment and the least vertex has literal colour zero."),
            PairNode("pair-legal", "Legal", "Normalized literal graph assignments", DescribeRole.Definition,
                "The assignments have colours in Fin (2p) and obey the actual literal bond at every graph edge."),
            PairNode("at-most-p", "AtMost", "Independent partitions with at most p blocks", DescribeRole.Definition,
                "The blocks are the actual nonempty subsets in a Mathlib graph partition."),
            PairNode("ordered-pair-colouring", "OrderedColoring", "Canonical proper pair words", DescribeRole.Definition,
                "Restricted-growth labels name the occupied classes in the order of their first vertices."),
            PairNode("pair-partition-equiv", "partitionEquiv", "Canonical proper words and their independent partitions", DescribeRole.Definition,
                "IndependentPartitionExpansion.coloringEquiv gives the actual blocks and their injected names. The canonical permutation representative of HardinA233177Canonical.canonical_exists_unique is unique because two injections on the same blocks differ by a palette permutation. The inverse names all blocks of any partition with at most p blocks."),
            PairNode("read-pair-word", "toOrderedColoring", "Read the actual pair word", DescribeRole.Definition,
                "Apply the lower-member label to each literal colour. The bond equivalence makes the resulting word proper."),
            PairNode("pair-fiber-equiv", "fiberEquiv", "Inverse signs over the same canonical proper word", DescribeRole.Definition,
                "Restrict the sign to non-first vertices. The inverse lifts the given word with false at every first vertex and the supplied sign elsewhere. The palette inverse laws recover each endpoint of this equivalence."),
            PairNode("literal-pair-partition-equiv", "literalPartitionEquiv", "Literal assignments by partition and free signs", DescribeRole.Definition,
                "The canonical pair word and its partition determine one another. Together with the sign inverse this decomposes the entire literal assignment type, including partitions that omit some palette labels."),
            PairNode("free-card", "free_card", "Exactly N−k free signs over a k-block partition", DescribeRole.Theorem,
                "For every finite linearly ordered vertex type and each independent partition with k≤p blocks, the free-vertex type of the canonical word reconstructed from the partition has cardinality N−k. Each block has a unique least vertex. Removing these k vertices leaves N−k independent Boolean choices and therefore 2^(N−k) assignments over the partition."),
            PairNode("arbitrary-p-count", "card_eq_sum", "The weighted graphical Stirling sum for the actual palette", DescribeRole.Theorem,
                "For every nonempty finite linearly ordered simple graph and every natural p, the cardinality of Legal G p is the sum of 2^(N−k) S_G(k) over 1≤k≤min(p,N). Here S_G(k) counts the actual unlabelled independent partitions into k blocks. The cardinality is invariant under changing the vertex order, since N and the independent partitions use only the underlying graph."),
            PairNode("three-pair-scanner", "scannerEquiv", "The original six-colour scanner at p=3", DescribeRole.Definition,
                "The equivalence is the identity on the literal word. The fixed scanner characterization normal_iff supplies both directions. The original three-pair count and chromatic reduction apply under this identification."),
            Paragraph(Text("A singleton has literal colour zero and count one for every positive p. For p=1 the unique pair word is constant. Its count is 2^(N−1) on an edgeless nonempty graph and zero on a graph with an edge. The empty carrier has one empty assignment. The sum beginning at k=1 applies to nonempty carriers, and the strip series retain their zero constant-term convention.")))));

    private static DocumentBlock PairNode(string id, string name, string title,
        DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
