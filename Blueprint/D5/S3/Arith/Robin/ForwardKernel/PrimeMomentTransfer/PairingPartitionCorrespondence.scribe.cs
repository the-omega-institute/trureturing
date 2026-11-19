using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class PairingPartitionCorrespondenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionCorrespondence.";

    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The bijection between retained singleton/free pair partitions and unordered partial pairings.",
        H("Pairing partition correspondence"),
        Blocks(
            Paragraph(Text(
                "For any natural k, a partition of the positions Fin k is a Mathlib Setoid, and its blocks are quotient classes. "
                + "The block sizes use the existing multiplicity function mult from ArithmeticTransferDefs. "
                + "The degree-zero collision shape consists of retained singleton blocks and unretained two-element blocks. "
                + "No ordering of the blocks or of their labels is chosen.")),
            Entry("partition-label-block", "partitionLabelBlock", "Labels of a quotient block",
                "For a setoid sigma on Fin k and a quotient block B, partitionLabelBlock(sigma,B) is the finite set of positions i "
                + "whose quotient class equals B. Its cardinality is definitionally mult(Quotient.mk(sigma),B).", DescribeRole.Definition),
            Entry("partition-label-block-injective", "partitionLabelBlock_injective", "Distinct blocks have distinct fibers",
                "For every natural k and setoid sigma on Fin k, the map B to partitionLabelBlock(sigma,B) is injective. "
                + "Each block contains its quotient representative; equality of fibers forces equality of the quotient classes.", DescribeRole.Theorem),
            Entry("pairing-partition-data", "PairingPartitionData", "Retained singleton/free pair data",
                "PairingPartitionData(k) consists of a setoid sigma on Fin k, a finite set S of its retained quotient blocks, "
                + "and the laws mult(Quotient.mk(sigma),B)=1 for B in S and =2 for B outside S.", DescribeRole.Definition),
            Entry("pairing-partition-pairs", "pairingPartitionPairs", "The free blocks as pairs",
                "For degree-zero partition data D, pairingPartitionPairs(D) is the image of the complement of its retained set "
                + "under the label-fiber map. It is a finite set of unordered two-element label sets.", DescribeRole.Definition),
            Entry("pairing-partition-pairs-is-partial", "pairingPartitionPairs_isPartial", "The resulting collection is a partial pairing",
                "For every natural k and D in PairingPartitionData(k), pairingPartitionPairs(D) satisfies IsPartialPairing on all positions Fin k. "
                + "Every unretained fiber has size two and distinct quotient fibers are disjoint.", DescribeRole.Theorem),
            Entry("pairing-partition-pairs-support", "pairingPartitionPairs_support", "Covered and retained labels",
                "For every natural k and degree-zero partition data D, the support of pairingPartitionPairs(D) equals the positions i "
                + "whose quotient block is not retained. Thus its uncovered labels are exactly the labels in retained singleton blocks.", DescribeRole.Theorem),
            Entry("pairing-partition-pairs-bijective", "pairingPartitionPairs_bijective", "Cardinality-preserving bijection with partial pairings",
                "For every natural k, the map from PairingPartitionData(k) to the subtype of partial pairings of Fin k, "
                + "sending D to pairingPartitionPairs(D) together with its partial-pairing proof, is bijective. "
                + "For every D, the number of resulting pairs equals the number of unretained quotient blocks. "
                + "The original partition relation is recovered by saying that two labels are equal or lie together in one of the free pairs. "
                + "The retained blocks are then determined by their singleton sizes, proving injectivity. "
                + "Conversely, for any partial pairing P, use this equality-or-common-edge relation as a setoid. "
                + "Disjointness of the edges proves transitivity. A covered label has its edge as quotient fiber; an uncovered label has a singleton fiber. "
                + "Retaining exactly the singleton fibers constructs inverse partition data whose free pairs are precisely P. "
                + "The construction also includes the empty label type and the empty partial pairing.", DescribeRole.Theorem))));
}
