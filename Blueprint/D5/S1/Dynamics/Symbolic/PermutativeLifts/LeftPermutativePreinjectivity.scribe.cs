using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class LeftPermutativePreinjectivityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/LeftPermutativePreinjectivity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-difference preinjectivity from a single endpoint permutation.",
        H("Left-permutative finite-difference preinjectivity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("left-permutative-rule"),
                DeclarationHandle.Create(Owner + "LeftPermutative"),
                H("Left-permutative local rule"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A local rule is left-permutative when, after fixing the right-hand tail, its output is injective in the left endpoint."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("left-preinjective-code"),
                DeclarationHandle.Create(Owner + "left_preinjective_code"),
                H("Left-permutative codes are preinjective"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite disagreement set has a greatest integer coordinate. The windows to its right agree, so left-endpoint injectivity forces agreement at that greatest coordinate, a contradiction."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativePreinjectivity"))]));
}
