using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class BalancedCoboundaryDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedCoboundary.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous finite-action transfers for the balanced subshift.", H("Continuous finite-action transfers for the balanced subshift"),
        Blocks(
            Describe.Lean(DescribeId.Create("result-0"), DeclarationHandle.Create(Owner + "transfer"),
                H("transfer"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Read the prefix holonomy at zero in the unique actual balanced marked tiling."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result-1"), DeclarationHandle.Create(Owner + "transfer_shift"),
                H("transfer_shift"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The public generic tile-state transition law supplies the coboundary equation whenever both tile holonomies are neutral."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result-2"), DeclarationHandle.Create(Owner + "permutationTransfer_shift"),
                H("permutationTransfer_shift"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite permutation action, the symbolic cardinal bound selects a neutral level of the same fixed balanced base."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result-3"), DeclarationHandle.Create(Owner + "trivializing_conjugacy"),
                H("trivializing_conjugacy"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The generic fibre change conjugates the balanced skew step to the balanced base shift with the original fibre fixed."))), DescribeRole.Theorem)),
            [ DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialCoboundary")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/FiniteActionTrivialization")) ]));
}
