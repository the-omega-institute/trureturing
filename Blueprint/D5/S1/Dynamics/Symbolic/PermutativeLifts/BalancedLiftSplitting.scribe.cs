using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class BalancedLiftSplittingDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftSplitting.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full binary lifts over the balanced base.", H("Full binary lifts over the balanced base"),
        Blocks(
            Describe.Lean(DescribeId.Create("result-0"), DeclarationHandle.Create(Owner + "splitting"),
                H("splitting"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every k and every bipermutative binary block code of length k+2, the full inverse image of the same fixed balancedSubshift is homeomorphic to BalancedPoint times the literal prefix set Fin(k+1) to Bool. The whole inverse image and every prefix are retained. For a source x with coded image y, the transformed prefix label β(y)^(-1)(sourcePrefix x) is valued in that original prefix set."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result-1"), DeclarationHandle.Create(Owner + "splitting_conjugacy"),
                H("splitting_conjugacy"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The homeomorphism conjugates the actual lift shift to the balanced base shift and fixes the transformed prefix label β(y)^(-1)(sourcePrefix x), valued in the original prefix set."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result-2"), DeclarationHandle.Create(Owner + "splitting_fibre_invariant"),
                H("splitting_fibre_invariant"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every signed integer iterate preserves the transformed prefix label β(y)^(-1)(sourcePrefix x), valued in the original prefix set."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result-3"), DeclarationHandle.Create(Owner + "splitting_fibre_clopen"),
                H("splitting_fibre_clopen"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each actual fibre is clopen, by continuity and discreteness of the prefix set."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result-4"), DeclarationHandle.Create(Owner + "full_lift_not_minimal"),
                H("full_lift_not_minimal"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two distinct constant prefixes yield distinct nonempty closed invariant fibres, so the entire inverse image is nonminimal. Exact minimal component count is not asserted here."))), DescribeRole.Theorem)),
            [ DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedCoboundary")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift")) ]));
}
