using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class GuardedEqualityRegistrationTemplatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Guarded equality registration programs over complete finite object arenas.",
        H("GuardedEqualityRegistrationTemplates"),
        Blocks(
            Node("guardedEqSignature", "One Boolean ADMIT guard and two typed CUT terms preserve all states.", DescribeRole.Definition),
            Node("guardedEqRealization", "The supplied guard and equality expressions remain independent readouts.", DescribeRole.Definition),
            Node("guardedEqArena", "The fixed law equates the CUT terms whenever the varying guard is true.", DescribeRole.Definition),
            Node("guardedEqLegacy", "The full conditional equation is definitionally the generated law.", DescribeRole.Theorem),
            Node("guardedEq_sensitivity", "An inhabited arena and two distinct values witness each guard and equality slot independently.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrationTemplates." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
