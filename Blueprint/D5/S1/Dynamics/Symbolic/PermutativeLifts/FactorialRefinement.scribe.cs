using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class FactorialRefinementDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialRefinement.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Refinement and recognizability of factorial tilings.",
        H("Refinement and recognizability of factorial tilings"),
        Blocks(
            Describe.Lean(DescribeId.Create("construction"), DeclarationHandle.Create(Owner + "factorialSubshift"),
                H("Construction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each upper block is refined into its actual repeated lower blocks. On the lower block types, the marker 10 occurs exactly at the upper boundaries. Induction from the one-letter level gives unique marked decoding at every level. The descending compact tiling subshifts have a nonempty intersection; this actual closed shift-invariant intersection defines the base."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("main-result"), DeclarationHandle.Create(Owner + "readTiling_injective"),
                H("Result"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each upper block is refined into its actual repeated lower blocks. On the lower block types, the marker 10 occurs exactly at the upper boundaries. Induction from the one-letter level gives unique marked decoding at every level. The descending compact tiling subshifts have a nonempty intersection; this actual closed shift-invariant intersection defines the base."))), DescribeRole.Theorem)),
            [ DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialWords")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/MarkedTiling")) ]));
}
