using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class UniversalLiftSplittingDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/UniversalLiftSplitting.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform splitting of all complete binary lifts.",
        H("Uniform splitting of all complete binary lifts"),
        Blocks(
            Describe.Lean(DescribeId.Create("construction"), DeclarationHandle.Create(Owner + "splitting"),
                H("Construction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every k and every bipermutative binary code of length k+2, the entire inverse image over the same factorial base is homeomorphic to the base times its actual binary prefix set. The continuous transfer conjugates the shift to the base shift times the identity. Distinct constant prefixes give a nonempty proper closed invariant fibre, contradicting minimality. No component is substituted for the entire inverse image."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("main-result"), DeclarationHandle.Create(Owner + "full_lift_not_minimal"),
                H("Result"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every k and every bipermutative binary code of length k+2, the entire inverse image over the same factorial base is homeomorphic to the base times its actual binary prefix set. The continuous transfer conjugates the shift to the base shift times the identity. Distinct constant prefixes give a nonempty proper closed invariant fibre, contradicting minimality. No component is substituted for the entire inverse image."))), DescribeRole.Theorem)),
            [ DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialCoboundary")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialMinimal")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/FiniteActionTrivialization")) ]));
}
