using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class FactorialSubshiftDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialSubshift.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous decoding and aperiodicity.",
        H("Continuous decoding and aperiodicity"),
        Blocks(
            Describe.Lean(DescribeId.Create("construction"), DeclarationHandle.Create(Owner + "decode"),
                H("Construction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compact tiling reader is injective, so its inverse on the factorial subshift is continuous. A positive period would preserve every recognizable boundary set. Choosing a level whose shortest block exceeds that period translates a boundary into a strict block interior, a contradiction. The natural-number orbit is injective, so the base is infinite."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("main-result"), DeclarationHandle.Create(Owner + "factorial_no_positive_period"),
                H("Result"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compact tiling reader is injective, so its inverse on the factorial subshift is continuous. A positive period would preserve every recognizable boundary set. Choosing a level whose shortest block exceeds that period translates a boundary into a strict block interior, a contradiction. The natural-number orbit is injective, so the base is infinite."))), DescribeRole.Theorem)),
            [ DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialRefinement")) ]));
}
