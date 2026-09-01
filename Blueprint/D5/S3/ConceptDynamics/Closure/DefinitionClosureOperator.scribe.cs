using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Closure;

internal sealed class DefinitionClosureOperatorDocument : IScribeDocumentDefinition
{
    private const string Declaration = "D5/S3/ConceptDynamics/Closure/DefinitionClosureOperator.isClosed_definitionClosureOperator_iff";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The existing semantic closure of readout families is exposed through Mathlib's canonical closure-operator interface.",
        H("Definition Closure as an Upstream Closure Operator"),
        Blocks(Describe.Lean(
            DescribeId.Create("definition-closure-operator"),
            DeclarationHandle.Create(Declaration),
            H("Upstream closed families are exactly semantically closed families"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The repository already proves that DefinitionClosure is extensive, monotone, and literally idempotent on same-codomain readout families.")),
                Paragraph(Text(
                    "Those laws are bundled as Mathlib ClosureOperator without introducing a second closure operation. Its closed-element carrier is therefore available to standard order-theoretic APIs.")),
                Paragraph(Text(
                    "A family is closed exactly when it contains every readout constant on the family's common observational kernel."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/DefinitionEscape/DefinitionKernelGalois")),
        ]));
}