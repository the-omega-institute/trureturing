using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class BalancedLiftComponentsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftComponents.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minimal actual prefix fibres of the balanced full lift.", H("Minimal actual prefix fibres"),
        Blocks(
            Describe.Lean(DescribeId.Create("orbit-closure-fibre"), DeclarationHandle.Create(Owner + "orbit_closure_eq_fibre"),
                H("Every orbit closure"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The orbit closure of every point in the entire inverse image is exactly the clopen minimal fibre selected by the transformed prefix label β(y)^(-1)(sourcePrefix x), valued in the original prefix set."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exact-orbit-closure-count"), DeclarationHandle.Create(Owner + "orbit_closure_family_card"),
                H("Exact number of distinct orbit closures"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Distinct original prefixes give distinct nonempty fibres. The range of the orbit-closure map is exactly this fibre family, whose cardinal is the binary prefix cardinal 2^(k+1)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("all-integer-conjugacy"), DeclarationHandle.Create(Owner + "splitting_integer_conjugacy"),
                H("All integer shifts"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The full product splitting intertwines every signed integer shift with the balanced base shift and fixes the transformed prefix label β(y)^(-1)(sourcePrefix x), valued in the original prefix set."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fibre-homeomorphism"), DeclarationHandle.Create(Owner + "componentHomeomorph"),
                H("Actual fibre homeomorphism"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each value of the transformed prefix label in the original binary prefix set, its nonempty clopen fibre in the full inverse image is homeomorphic to the balanced base. The inverse is the full splitting inverse with that label fixed."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("minimal-fibres"), DeclarationHandle.Create(Owner + "componentMinimal"),
                H("Minimal fibres"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The fibre homeomorphism intertwines the inherited integer shift and the already proved minimal balanced action. Its image of every fibre orbit is a dense balanced orbit. Thus each fibre is minimal."))), DescribeRole.Theorem)),
            [ DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftSplitting")) ]));
}
