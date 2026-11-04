using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class BipermutativeLiftDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The entire bipermutative lift as a finite skew product.",
        H("The entire bipermutative lift as a finite skew product"),
        Blocks(
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
