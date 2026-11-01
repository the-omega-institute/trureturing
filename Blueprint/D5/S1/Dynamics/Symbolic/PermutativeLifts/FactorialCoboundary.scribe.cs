using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class FactorialCoboundaryDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialCoboundary.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous transfers for every finite action.",
        H("Continuous transfers for every finite action"),
        Blocks(
            Describe.Lean(DescribeId.Create("prefix-holonomy-step"), DeclarationHandle.Create(Owner + "holonomy_take_succ"),
                H("One-symbol prefix extension"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Appending the next symbol to a taken prefix multiplies its holonomy on the left. This original generic monoid lemma is public for reuse by recognizable towers."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tile-state-transfer"), DeclarationHandle.Create(Owner + "stateTransfer"),
                H("Generic tile-state transfer"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The prefix product is defined for arbitrary binary tile words and a monoid. It is reused by both factorial and balanced towers."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("tile-state-transition"), DeclarationHandle.Create(Owner + "stateTransfer_next"),
                H("Generic tile-state transition"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If both complete tile words have identity holonomy, every legal marked-tile step multiplies the prefix product by its visible symbol on the left."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("construction"), DeclarationHandle.Create(Owner + "transfer"),
                H("Construction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At a level where both block holonomies are identity, the prefix product from the recognizable block boundary gives a continuous transfer. Advancing inside a block adds the current letter permutation on the left. At a boundary, identity holonomy supplies the same equation. The finite set Q remains the actual action fibre; it is not replaced by a regular group action."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("main-result"), DeclarationHandle.Create(Owner + "transfer_shift"),
                H("Result"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At a level where both block holonomies are identity, the prefix product from the recognizable block boundary gives a continuous transfer. Advancing inside a block adds the current letter permutation on the left. At a boundary, identity holonomy supplies the same equation. The finite set Q remains the actual action fibre; it is not replaced by a regular group action."))), DescribeRole.Theorem)),
            [ DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialSubshift")) ]));
}
