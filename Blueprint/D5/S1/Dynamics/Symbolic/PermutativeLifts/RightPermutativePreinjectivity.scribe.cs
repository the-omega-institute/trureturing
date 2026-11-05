using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class RightPermutativePreinjectivityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/RightPermutativePreinjectivity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-difference preinjectivity from a single endpoint permutation.",
        H("Right-permutative finite-difference preinjectivity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("right-permutative-rule"),
                DeclarationHandle.Create(Owner + "RightPermutative"),
                H("Right-permutative local rule"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A local rule is right-permutative when, after fixing the left-hand prefix, its output is injective in the right endpoint."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("right-preinjective-code"),
                DeclarationHandle.Create(Owner + "right_preinjective_code"),
                H("Right-permutative codes are preinjective"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite disagreement set has a least integer coordinate. The windows ending there agree in their left prefix, so right-endpoint injectivity forces agreement at that least coordinate, a contradiction."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/LeftPermutativePreinjectivity"))]));
}
