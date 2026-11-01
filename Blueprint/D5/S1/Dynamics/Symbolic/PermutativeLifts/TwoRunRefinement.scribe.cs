using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class TwoRunRefinementDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical refinement of two-run word tilings.",
        H("Physical refinement of two-run word tilings"),
        Blocks(
            Describe.Lean(DescribeId.Create("construction"), DeclarationHandle.Create(Owner + "word"),
                H("Two positive runs"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let W assign a nonempty binary word to each Boolean type, and let l and r assign positive integers to each parent type a. The upper word of type a is l(a) literal copies of W(false), followed by r(a) literal copies of W(true). At physical offset p, the cut is l(a) times the length of W(false). Before that cut the child type is false and its offset is p modulo the length of W(false); after it the child type is true and its offset is p minus the cut, modulo the length of W(true). Neither equality nor inequality of the two lower word lengths is required."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("state-morphism"), DeclarationHandle.Create(Owner + "refineState_next"),
                H("Preservation of actual edges"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every actual upper TileNext edge maps to a lower TileNext edge. Within a parent, the upper types agree, so their cuts agree. The transition across the cut is the end of a false child followed by the start of a true child. Across a parent boundary, positivity places the old state in its true run and the new state in its false run, even when the two parents have different cuts. Thus pointwise refinement gives an actual map of bi-infinite marked tiling spaces."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("parent-boundaries"), DeclarationHandle.Create(Owner + "refineTiling_boundary_iff"),
                H("Parent boundary detection"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At every integer coordinate i of every actual upper marked tiling, its parent offset is zero if and only if the refined child type at i minus one is true and the refined child type at i is false. This identifies the parent boundaries from lower types; it does not assume or assert unique decoding from the visible binary configuration."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("visible-read"), DeclarationHandle.Create(Owner + "readTiling_refineTiling"),
                H("Preservation of physical symbols"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reading the refined marked tiling gives exactly the same binary configuration at every physical coordinate. The proof reads literal repeated words at the remainder of the physical offset. In particular every upper tiled configuration admits a lower tiling of the same visible symbols."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("aligned-origin"), DeclarationHandle.Create(Owner + "refineTiling_aligned_zero"),
                H("Preservation of an aligned origin"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the parent offset at physical coordinate zero is zero, the refined child offset there is also zero. This permits compatible constraints on the origin when forming nested spaces of aligned configurations. For a positive integer N, the construction applies to l(false) = 2N, l(true) = N, r(false) = N and r(true) = 2N. Unique decoding from visible binary symbols requires an additional recognizability argument."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nested-tiling-spaces"), DeclarationHandle.Create(Owner + "tiledSubshift_subset"),
                H("Nested tiling spaces"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The tiled subshift for the upper words is a subset of the tiled subshift for W: refine a witnessing marked tiling and use equality of the physical readouts."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("aligned-configurations"), DeclarationHandle.Create(Owner + "alignedConfigurations"),
                H("Configurations with an aligned origin"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The aligned configuration set consists of readouts of actual marked tilings whose offset at coordinate zero is zero. It is defined by an image, without assuming a unique marked representation."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("compact-aligned-image"), DeclarationHandle.Create(Owner + "alignedConfigurations_compact_nonempty"),
                H("A nonempty compact aligned image"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For nonempty words, the aligned configuration set is compact and nonempty. The zero-offset condition is closed in the compact marked tiling space, and the readout is continuous. A periodic tiling by W(false), started at its boundary, supplies a point."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nested-aligned-images"), DeclarationHandle.Create(Owner + "alignedConfigurations_subset"),
                H("Nested aligned images"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The aligned configuration set of the upper words is contained in the aligned configuration set of W. Refinement preserves both the visible readout and the zero offset at the physical origin. Consequently successive refinements supply the nesting needed for a compact intersection with a common aligned origin."))), DescribeRole.Theorem)),
            [ DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialRefinement")) ]));
}
