using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class BipermutativeLiftDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The entire bipermutative lift as a finite skew product.",
        H("The entire bipermutative lift as a finite skew product"),
        Blocks(
            Describe.Lean(DescribeId.Create("shared-reconstruction"), DeclarationHandle.Create(Owner + "equivOfPrefixPerm"),
                H("Reconstruction from prefix permutations"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an arbitrary alphabet, suppose a family of prefix permutations agrees pointwise with the native prefix step. The skew product shifts the entire output by one and applies the corresponding permutation to the literal prefix. Its signed integer iterates define overlapping prefixes and hence one physical source sequence. This construction is shared by the finite-alphabet equivalence and by arbitrary-alphabet recovery after the prefix permutations have been constructed."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("reconstruction-right-inverse"), DeclarationHandle.Create(Owner + "coordinates_reconstruct_of_prefix_perm"),
                H("Reconstruction realizes the prescribed coordinates"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If every supplied prefix permutation agrees with the native prefix step, reconstructing an output-prefix pair and then taking its native coordinates returns that pair. Prefix overlap identifies each reconstructed physical window; the right-end equation gives its output letter."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reconstruction-left-inverse"), DeclarationHandle.Create(Owner + "reconstruct_coordinates_of_prefix_perm"),
                H("Reconstruction recovers every source"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the same prefix permutations, reconstructing the native coordinates of an existing source returns the source. The coordinate map intertwines both forward and backward source shifts with the skew product, so every reconstructed prefix is the corresponding physical prefix."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("code-shift"), DeclarationHandle.Create(Owner + "code_shift"),
                H("Sliding codes commute with integer shifts"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual finite-window block code commutes with every signed integer shift."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("integer-lift-action"), DeclarationHandle.Create(Owner + "integerShift"),
                H("The full integer lift action"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The entire inverse image of any subshift carries the inherited integer shift. Subshift invariance and the public code-shift law supply membership without a new reconstruction proof."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("construction"), DeclarationHandle.Create(Owner + "fullLiftHomeomorph"),
                H("Construction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a code of length k+2 over any finite discrete alphabet, the fibre is exactly the set Fin(k+1) to A of actual prefixes. Bijectivity in both endpoints makes the prefix update a permutation. Integer iterates reconstruct every two-sided preimage in both directions. Coordinates consisting of the coded image and the prefix give a homeomorphism of the entire inverse image to the base times that prefix fibre, conjugating the shift to the actual prefix permutation cocycle."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("main-result"), DeclarationHandle.Create(Owner + "full_lift_conjugacy"),
                H("Result"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a code of length k+2 over any finite discrete alphabet, the fibre is exactly the set Fin(k+1) to A of actual prefixes. Bijectivity in both endpoints makes the prefix update a permutation. Integer iterates reconstruct every two-sided preimage in both directions. Coordinates consisting of the coded image and the prefix give a homeomorphism of the entire inverse image to the base times that prefix fibre, conjugating the shift to the actual prefix permutation cocycle."))), DescribeRole.Theorem))));
}
