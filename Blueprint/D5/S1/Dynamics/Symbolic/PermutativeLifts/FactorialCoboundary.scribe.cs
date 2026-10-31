using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class FactorialCoboundaryDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialCoboundary.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous transfers for every finite action.",
        H("Continuous transfers for every finite action"),
        Blocks(
            Describe.Lean(DescribeId.Create("construction"), DeclarationHandle.Create(Owner + "transfer"),
                H("Construction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At a level where both block holonomies are identity, the prefix product from the recognizable block boundary gives a continuous transfer. Advancing inside a block adds the current letter permutation on the left. At a boundary, identity holonomy supplies the same equation. The finite set Q remains the actual action fibre; it is not replaced by a regular group action."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("main-result"), DeclarationHandle.Create(Owner + "exists_continuous_permutation_transfer"),
                H("Result"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At a level where both block holonomies are identity, the prefix product from the recognizable block boundary gives a continuous transfer. Advancing inside a block adds the current letter permutation on the left. At a boundary, identity holonomy supplies the same equation. The finite set Q remains the actual action fibre; it is not replaced by a regular group action."))), DescribeRole.Theorem)),
            [ DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialSubshift")) ]));
}
