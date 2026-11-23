using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeightedBond;

internal sealed class WeightedBondFiniteOrderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeightedBond/FiniteOrder.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/gonzalezdeleonwachs2026weighted");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Connected colored blocks and literal lower intervals.",
        H("Connected colored blocks and literal lower intervals"),
        Blocks(
            Node("MultiweightedBond",
                "Each block induces a connected graph and has a weak composition of its size minus one across Fin(r). Every weight outside the partition blocks is zero.", DescribeRole.Definition),
            Node("ext_weights",
                "Two elements with the same partition agree if their weights agree on its blocks in every color.", DescribeRole.Theorem),
            Node("childSum",
                "For a given vertex set and color, sum the weights of the partition blocks contained in that set.", DescribeRole.Definition),
            Node("Refines",
                "The partition refines the upper partition and each upper weight dominates the sum of the finer weights in that color.", DescribeRole.Definition),
            Node("singletonZero",
                "The bottom consists of singleton blocks with all weights zero.", DescribeRole.Definition),
            Node("complete_block_connected",
                "Every nonempty block of a partition in the complete graph induces a connected graph.", DescribeRole.Theorem),
            Node("weight_eq_zero_of_card_one",
                "A singleton block has zero weight in every color.", DescribeRole.Theorem),
            Node("total_weight_eq_rank",
                "Summing the block weights over every color gives the vertex count minus the number of blocks.", DescribeRole.Theorem),
            Node("CompleteBond",
                "The finite colored bond poset of the complete graph on Fin(n).", DescribeRole.Definition),
            Node("psiComplete",
                "Sum the integer incidence Möbius coefficients from the singleton bottom, each multiplied by X to the number of vertices minus the number of blocks.", DescribeRole.Definition),
            Node("restrictBlock",
                "Restrict the finer partition and its weights to an upper block, using the induced graph on its vertex subtype.", DescribeRole.Definition),
            Node("oneBlock",
                "The weighted partition of an upper block into itself, with the upper block's original color weights.", DescribeRole.Definition),
            Node("oneBlock_parts",
                "The one-block partition has just the full vertex set of the block.", DescribeRole.Theorem),
            Node("oneBlock_weight",
                "The weight of its full vertex set equals the weight of the corresponding upper block in every color.", DescribeRole.Theorem),
            Node("recombineBlocks",
                "Glue the block partitions in their disjoint ambient sets and transport each coordinate of their weights back to the original graph.", DescribeRole.Definition),
            Node("restrictBlock_recombineBlocks",
                "Restriction to any upper block recovers that block's input after recombination.", DescribeRole.Theorem),
            Node("recombineBlocks_restrictBlock",
                "Recombining all restrictions recovers the original partition and all its weights.", DescribeRole.Theorem),
            Node("lowerIntervalOrderIso",
                "The lower interval of an upper weighted partition is order-isomorphic to the dependent product of the lower intervals below its one-block restrictions in the induced graphs.", DescribeRole.Definition),
            Node("rank_eq_sum_block_ranks",
                "For each finer element in the lower interval, the ambient rank is the sum of the local ranks of its restrictions.", DescribeRole.Theorem),
            Node("mu_bot_iic",
                "Restricting to a lower interval leaves every Möbius coefficient from the bottom unchanged.", DescribeRole.Theorem),
            Node("mu_bot_orderIso",
                "An order isomorphism of locally finite orders with bottoms preserves the bottom Möbius function.", DescribeRole.Theorem),
            Node("mu_bot_eq_prod_blocks",
                "The Möbius value from bottom to an upper weighted partition is the product of the corresponding bottom-to-one-block values on its blocks.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string name, string prose, DescribeRole role, Formula? formula = null,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant().Replace('_', '-')), DeclarationHandle.Create(Prefix + name),
            H(name), formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role, resolution);
}
