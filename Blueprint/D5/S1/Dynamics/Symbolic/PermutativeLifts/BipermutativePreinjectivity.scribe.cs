using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class BipermutativePreinjectivityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativePreinjectivity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-difference preinjectivity for bipermutative two-sided codes.",
        H("Finite-difference preinjectivity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-difference"),
                DeclarationHandle.Create(Owner + "FiniteDifference"),
                H("Finite-difference relation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two integer configurations are finitely different when their disagreement set is finite."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("preinjective-predicate"),
                DeclarationHandle.Create(Owner + "Preinjective"),
                H("Finite-difference preinjectivity predicate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The predicate requires equal code outputs to force equal source configurations whenever the sources differ on only finitely many coordinates."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("preinjective-code"),
                DeclarationHandle.Create(Owner + "preinjective_code"),
                H("Bipermutative codes are preinjective"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a bipermutative local rule, a finite disagreement has a greatest coordinate. The right tail of the corresponding windows agrees, so injectivity in the left endpoint forces agreement at the greatest coordinate, a contradiction."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift"))]));
}
