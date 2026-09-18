using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class EscapeRecordDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Escape records close a statement onto an arena law in one direction and certify where information continues to escape.",
        H("EscapeRecord"),
        Blocks(
            Node("EscapePrimitiveRealization", "A forward bridge proves that the statement implies the law of the declared realization; equivalence is not claimed, so the unresolved part is recorded separately.", DescribeRole.Definition),
            Node("EscapePrimitiveRealization.ofLegacy", "An equivalence bridge yields a forward bridge by its forward direction.", DescribeRole.Definition),
            Node("EscapeResidualWitness", "A residual witness is a pair of arena states that the finest listed kernel of a chain leaves unresolved; it names where the closed information keeps escaping.", DescribeRole.Definition),
            Node("EscapeResidualEmpty", "The closure leaves no residual when the finest listed kernel separates every pair.", DescribeRole.Definition),
            Node("escapeResidualEmpty_iff", "No residual holds exactly when the unresolved pair set is empty.", DescribeRole.Theorem),
            Node("escapeResidualEmpty_no_witness", "A chain without residual admits no residual witness.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').Replace('.', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/EscapeRecord." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
