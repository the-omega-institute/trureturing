using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Sequenceability;

internal sealed class AdaptiveMergeZeroCrossingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For distinct x,y in A, every fork gives nonempty proper zero-sum subsets C,D with all three Venn regions nonempty and at least one singleton. For M choose C = U union {x}, D = U union V. Their regions are U, {x}, V; C omits y and D omits x. For E choose C = U union {x}, D = V union {x}. The regions are {x}, U, V; both sets omit y. Properness is essential even when A itself has sum zero.",
        H("AdaptiveMergeZeroCrossing"), Blocks(
            Describe.Lean(
                DescribeId.Create("adaptivemergezerocrossing-fork-edge-crossing"),
                DeclarationHandle.Create("D5/S1/Words/Sequenceability/AdaptiveMergeZeroCrossing.fork_edge_crossing"),
                H("Signed forks force proper singleton-region zero-sum crossings"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For distinct x,y in A, every fork gives nonempty proper zero-sum subsets C,D with all three Venn regions nonempty and at least one singleton. For M choose C = U union {x}, D = U union V. Their regions are U, {x}, V; C omits y and D omits x. For E choose C = U union {x}, D = V union {x}. The regions are {x}, U, V; both sets omit y. Properness is essential even when A itself has sum zero.")))),
            Describe.Lean(
                DescribeId.Create("adaptivemergezerocrossing-no-singleton-crossing-fork-empty"),
                DeclarationHandle.Create("D5/S1/Words/Sequenceability/AdaptiveMergeZeroCrossing.no_singleton_crossing_fork_empty"),
                H("An explicit crossing exclusion removes every fork edge"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If no pair of nonempty proper zero-sum subsets has three nonempty Venn regions with one singleton, then ForkEdge A x y is false for every distinct pair x,y in A. This is an extra hypothesis on the actual zero-sum subsets, not an automatic property of arbitrary A.")))),
            Describe.Lean(
                DescribeId.Create("adaptivemergezerocrossing-laminar-no-singleton-crossing"),
                DeclarationHandle.Create("D5/S1/Words/Sequenceability/AdaptiveMergeZeroCrossing.laminar_no_singleton_crossing"),
                H("Laminar proper-zero families exclude the obstruction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Laminar A quantifies only nonempty proper zero-sum subsets C,D of A and requires containment in one direction or disjointness. Each alternative empties one Venn region, so a singleton-region crossing is impossible. No hypothesis about the full set being nonzero is added.")))),
            Describe.Lean(
                DescribeId.Create("adaptivemergezerocrossing-partition-blocks-no-singleton-crossing"),
                DeclarationHandle.Create("D5/S1/Words/Sequenceability/AdaptiveMergeZeroCrossing.partition_blocks_no_singleton_crossing"),
                H("Unions of partition blocks cannot have a singleton Venn region"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("PartitionBlocks A P means that the pairwise disjoint blocks cover A and every block has cardinality at least two. ProperZeroBlockUnions requires each nonempty proper zero-sum subset to be a union of selected blocks. For two such subsets, their intersection and both differences are saturated by the same blocks. A nonempty region therefore contains a whole block and has at least two elements. This sufficient condition need not make the proper-zero family laminar. Both the common partition and the zero-set representation are visible additional hypotheses.")))),
            Paragraph(Text("The unrestricted adaptive principle and original arbitrary-subset parent remain OPEN. Under H and existence of a legal pair for an arbitrary finite nonzero alphabet of size at least three, it remains OPEN whether some actual Good compressed order has a Good adjacent expansion; a complete checked counterexample would refute that principle. Static legal-edge inclusion in ForkEdge does not decide it. The published IntegerStrongOrdering theorem is reused in a transient exact-telescope check; no new integer ordering theorem is retained and concrete ZMod Good is not generalized. No literature novelty claim follows from repository search. Four-slot Reg registration is unfinished; see https://github.com/the-omega-institute/trureturing/issues/21061 for exact targets and missing source-binding evidence.")))));
}
