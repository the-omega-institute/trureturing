using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves;

internal sealed class BinaryCubeRadialSmallKernelDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeRadialSmallKernel";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The no-split star hypothesis reduces a small kernel word to one eight-point Hamming layer.",
        H("Small radial binary kernel words on the eight-cube"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("true-coordinates"),
                DeclarationHandle.Create(Module + ".trueCoords"),
                H("Set of true coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Select the coordinate indices at which the vertex has bit true."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hamming-weight"),
                DeclarationHandle.Create(Module + ".hammingWeight"),
                H("Hamming weight of a cube vertex"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Count the true coordinates, equivalently the Hamming distance from the all-false vertex."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("support-weight"),
                DeclarationHandle.Create(Module + ".supportWeight"),
                H("Weight of a binary cube word"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Count the vertices where the word is nonzero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("true-coordinates-equivalence"),
                DeclarationHandle.Create(Module + ".trueCoordsEquiv"),
                H("Equivalence with subsets of coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Take the set of true coordinates. The inverse sends a set of indices to the vertex " +
                        "whose bits are their membership indicators. This identifies a Hamming layer with the " +
                        "sets of the corresponding size."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("radial-kernel-even-profile"),
                DeclarationHandle.Create(Module + ".radial_kernel_even_profile"),
                H("A radial kernel profile is constant on the even layers"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let a be the layer profile of a binary kernel word on Q8. At a vertex of radius k, the " +
                        "adjacency sum receives k terms from radius k − 1 and 8 − k terms from radius k + 1. At k " +
                        "equal to 1, 3, 5 or 7, both multiplicities are odd, so the two neighboring profile values " +
                        "coincide. This gives equality of the values at radii 0, 2, 4, 6 and 8."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("radial-small-kernel-one-shell"),
                DeclarationHandle.Create(Module + ".radial_small_kernel_one_shell"),
                H("A nonzero small radial kernel word occupies one shell"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Suppose a Q8 binary kernel word is constant on each Hamming layer and has positive weight at " +
                        "most twelve. Layers 2, 3 and 5 each exceed the weight budget. The even-layer equations then " +
                        "force every even layer to vanish. The two remaining layers have radii 1 and 7 and size eight " +
                        "each, so exactly one is occupied and the word has weight eight."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("no-split-small-kernel-one-shell"),
                DeclarationHandle.Create(Module + ".no_split_small_kernel_one_shell"),
                H("A small kernel word with no split on the star is a translated shell"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix a coordinate r of Q8. For each j distinct from r, assume the double flip preserves the " +
                        "word on all unequal-bit vertices or on all equal-bit vertices for r and j. If the word lies " +
                        "in the kernel and has positive weight at most twelve, there is a translation with r bit " +
                        "false whose pullback has support exactly the radius-one or radius-seven layer. The original " +
                        "word has weight eight.")),
                    Paragraph(Text("The star swaps give constancy by Hamming layer after translation. Translation commutes with " +
                        "each coordinate flip and is a bijection, so it preserves the kernel equation and support " +
                        "size. The radius-seven layer is the open neighbor shell of the antipode of the all-false " +
                        "vertex."))),
                DescribeRole.Theorem)),
        []));
}
