using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class ImplicationRegistrationTemplatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact implication registration programs over finite object states.",
        H("ImplicationRegistrationTemplates"),
        Blocks(
            Node("implicationSignature", "Two CUT slots retain finite Boolean functions for the antecedent and consequent independently.", DescribeRole.Definition),
            Node("implicationRealization", "Each predicate is evaluated at the current arena state and finite index, then reflected by decide; no source theorem is used.", DescribeRole.Definition),
            Node("implicationArena", "At every state and index, the fixed law requires the consequent whenever the antecedent holds. No arbitrary law is accepted.", DescribeRole.Definition),
            Node("implicationLegacy", "Boolean reflection preserves every state and both predicates of the complete implication.", DescribeRole.Theorem),
            Node("implication_sensitivity", "When the arena and index are inhabited, switching either Boolean-function readout alone changes the law while the other slot remains fixed.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/ImplicationRegistrationTemplates." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
