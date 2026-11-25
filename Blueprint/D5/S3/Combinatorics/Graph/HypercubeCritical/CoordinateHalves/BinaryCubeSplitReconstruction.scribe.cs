using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves;

internal sealed class BinaryCubeSplitReconstructionDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSplitReconstruction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two opposite pairs determine adjacent six-cube centers and recover the full eight-cube word.",
        H("Reconstructing the two shells of a sharp split"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("neighborhood"),
                DeclarationHandle.Create(Module + ".neighborhood"),
                H("Open neighborhood of a cube vertex"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The neighborhood of p consists of all vertices reached from p by a single " +
                        "coordinate flip."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("delta"),
                DeclarationHandle.Create(Module + ".delta"),
                H("Point indicator"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The word δₚ is one at p and zero elsewhere."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("adjacency-delta"),
                DeclarationHandle.Create(Module + ".adjacency_delta"),
                H("Adjacency of a point indicator gives its neighbor shell"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The adjacency sum of δₚ at x is one precisely when x is a neighbor of p. " +
                        "A neighbor reaches p by a unique coordinate flip, so that flip is the sole nonzero " +
                        "summand."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sharp-split-reconstruction"),
                DeclarationHandle.Create(Module + ".sharp_split_reconstruction"),
                H("Each opposite pair splits its shell into one and five sites"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Suppose a Q8 binary kernel word has weight at most twelve and both opposite-section sums are " +
                        "nonzero. Its weight is twelve and the sums are the shells of two adjacent centers p and q " +
                        "in Q6. The equal-bit sections partition the shell at p into the " +
                        "singleton q and its five-site complement in that shell. The unequal-bit sections partition " +
                        "the shell at q into the singleton p and its five-site complement. Either orientation of each " +
                        "partition is allowed.")),
                    Paragraph(Text("The adjacency of either section is the opposite sum from the other pair. Its image thus has " +
                        "six sites. The partial-shell count s(6 − s) plus the residue of s modulo two forces s to be " +
                        "one or five. The image of a singleton is its entire shell, and the shell in Q6 identifies " +
                        "its center, so each singleton is the other shell's center."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sharp-split-two-shells"),
                DeclarationHandle.Create(Module + ".sharp_split_two_shells"),
                H("A sharp split lifts to two shells with centers at distance two"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Under the same hypotheses, the weight is twelve and the full word is the adjacency of the " +
                        "sum of two point indicators on Q8. Write s,s for the leading bits of the section containing " +
                        "only q and t,¬t for those of the section containing only p. The lifted centers have tails p " +
                        "and q and leading bits ¬s,¬s and ¬t,t, respectively.")),
                    Paragraph(Text("The lifted centers differ in one leading bit and one tail bit. Taking the four sections of " +
                        "the adjacency of their sum gives the singleton and shell-complement words from the " +
                        "reconstruction, so the full word agrees in every section."))),
                DescribeRole.Theorem)),
        []));
}
