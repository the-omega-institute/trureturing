using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class FiniteDifferencePropagationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/FiniteDifferencePropagation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-difference propagation under local codes.",
        H("Finite-difference propagation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-difference-code"),
                DeclarationHandle.Create(Owner + "finite_difference_code"),
                H("Finite-window codes preserve finite disagreement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If two source configurations disagree on a finite set, an output can disagree only when one of the finitely many coordinates in its local window disagrees. The output disagreement set is contained in a finite union of translates of the source disagreement set."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("code-iterate"),
                DeclarationHandle.Create(Owner + "codeIter"),
                H("Iterated local code"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("codeIter h n applies the same finite-window code n times, with the zero iterate equal to the identity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-difference-code-iterate"),
                DeclarationHandle.Create(Owner + "finite_difference_code_iterate"),
                H("Finite disagreement survives every finite iterate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Induction on the iterate depth reuses finite-window propagation at each step, transporting finite-difference classes through repeated local-code evolution."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativePreinjectivity"))]));
}
