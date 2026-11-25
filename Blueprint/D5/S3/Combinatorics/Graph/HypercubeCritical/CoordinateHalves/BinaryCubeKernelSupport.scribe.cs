using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves;

internal sealed class BinaryCubeKernelSupportDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeKernelSupport";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The minimum-support classification and weight divisibility transfer to the Boolean-coordinate cube.",
        H("Support and minimum weight of binary cube words"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binary-sites"),
                DeclarationHandle.Create(Module + ".binarySites"),
                H("Support of a binary word"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("On a finite type, the support is the set of sites where the binary word is nonzero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("support-cardinality-of-a-sum"),
                DeclarationHandle.Create(Module + ".add_sites_card_add_twice_inter"),
                H("Shared sites cancel in a binary sum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The support of a sum is the symmetric difference of the two supports. Its size plus twice " +
                        "the size of their intersection equals the sum of the two original support sizes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("minimum-kernel-support"),
                DeclarationHandle.Create(Module + ".minimum_kernel_support"),
                H("A minimum support in Boolean coordinates is a neighbor shell"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In even dimension n at least six, a nonzero binary adjacency-kernel word with support size " +
                        "at most n has support size exactly n, and its support is the set of all single-coordinate " +
                        "flips of a center.")),
                    Paragraph(Text("Taking the set of true coordinates turns each Boolean flip into symmetric difference with a " +
                        "singleton. The kernel equation gives even selected neighbor counts. The lower bound in " +
                        "BinaryKernelCrossing forces equality, and BinaryKernelMinimum.minimum_support_iff identifies " +
                        "the support in the coordinate-subset model. Pulling back by the same equivalence gives the " +
                        "Boolean-coordinate shell."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kernel-support-divisible-by-four"),
                DeclarationHandle.Create(Module + ".four_dvd_binarySites_card"),
                H("Kernel support sizes are divisible by four"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("On a cube of dimension 4m with m positive, every binary adjacency-kernel word has support " +
                        "size divisible by four. The coordinate-subset equivalence preserves binary adjacency and " +
                        "transports the weight congruence from BinaryAdjacencyWeight."))),
                DescribeRole.Theorem)),
        []));
}
