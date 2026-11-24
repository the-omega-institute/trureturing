using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeightedBond;

internal sealed class WeightedBondPartitionExpansionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeightedBond/PartitionExpansion.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/gonzalezdeleonwachs2026weighted");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Labeled partitions and one-block extension counts.",
        H("Labeled partitions and one-block extension counts"),
        Blocks(
            Node("Bonds",
                "The connected-block poset on a finite vertex set with the complete graph.", DescribeRole.Definition),
            Node("Weights",
                "The type of weak r-compositions of a natural number.", DescribeRole.Definition),
            Node("weights_card",
                "For r positive the number of weak r-compositions of d is the binomial coefficient choosing r minus one from d plus r minus one.", DescribeRole.Theorem),
            Node("Partitions",
                "The finite partitions of the complete vertex set.", DescribeRole.Definition),
            Node("Decoration",
                "Each block of a partition independently carries a weak r-composition of its size minus one.", DescribeRole.Definition),
            Node("decorate",
                "Equip the blocks of a partition with their chosen weight vectors.", DescribeRole.Definition),
            Node("decorationsEquiv",
                "A weighted partition of the complete graph is equivalent to an ordinary partition together with its block weight vectors.", DescribeRole.Definition),
            Node("topPartition",
                "On a nonempty vertex set the indiscrete partition has the full vertex set as its only block.", DescribeRole.Definition),
            Node("topBond",
                "On a nonempty vertex set, put the specified weight vector on its one-block partition.", DescribeRole.Definition),
            Node("globalWeight",
                "The total of the weights in one specified color.", DescribeRole.Definition),
            Node("sum_globalWeight",
                "The sum of the global coordinates equals the vertex count minus the block count.", DescribeRole.Theorem),
            Node("le_topBond_iff",
                "Refining the specified one-block element is equivalent to its weight dominating the global weights in every coordinate.", DescribeRole.Theorem),
            Node("parts_pos",
                "A partition of a nonempty vertex set has a positive block count.", DescribeRole.Theorem),
            Node("topExtensions",
                "The one-block elements above a k-block element correspond to weak r-compositions of k minus one, by subtracting the global weights from the upper vector.", DescribeRole.Definition),
            Node("relabelPartition",
                "Image every block under a bijection of vertex sets.", DescribeRole.Definition),
            Node("relabel",
                "Relabel the partition and preserve the weight of each relabeled block.", DescribeRole.Definition),
            Node("relabelOrderIso",
                "Relabeling along a bijection gives an order isomorphism of the complete-graph weighted bond posets.", DescribeRole.Definition),
            Node("muComplete",
                "For a positive vertex count, sum the actual bottom Möbius values over the one-block elements of the complete graph. The zero-vertex input returns zero.", DescribeRole.Definition),
            Node("partitionProduct",
                "Multiply the sums of one-block Möbius values evaluated at the individual block sizes.", DescribeRole.Definition),
            Node("sum_mu_grouped",
                "For any ring-valued function of the underlying partition, grouping the Möbius-weighted sum gives the partition sum weighted by the one-block products.", DescribeRole.Theorem),
            Node("psiComplete_partition",
                "For every n and r the rank polynomial sums the one-block products over labeled partitions, each times X to the vertex count minus the block count.", DescribeRole.Theorem),
            Node("partition_inverse_recurrence",
                "For positive n and positive r, sum the one-block Möbius products over labeled partitions, multiplied by the number of one-block extensions. The result is one at n = 1 and zero at larger n.", DescribeRole.Theorem),
            Node("reversePsi",
                "Sum the same Möbius values over finite-color complete-graph elements, marking a partition with k blocks by X to the power k minus one.", DescribeRole.Definition),
            Node("reversePsi_eq_reflect",
                "For n positive and any r, the printed convention equals the reflection of the literal rank polynomial in degree n minus one.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string name, string prose, DescribeRole role, Formula? formula = null,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant().Replace('_', '-')), DeclarationHandle.Create(Prefix + name),
            H(name), formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role, resolution);
}
