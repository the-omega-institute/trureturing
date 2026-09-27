using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class GuardedEqualityRegistrationTemplatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Guarded equality registration programs over complete finite object arenas.",
        H("GuardedEqualityRegistrationTemplates"),
        Blocks(
            Node("guardSlot", "The shared constructor-written zero label in Fin 3 identifies the guard slot.", DescribeRole.Definition),
            Node("leftSlot", "The shared constructor-written one label in Fin 3 identifies the left equality slot.", DescribeRole.Definition),
            Node("isGuardSlot", "Pinned finite equality decides whether a slot label is guardSlot.", DescribeRole.Definition),
            Node("isLeftSlot", "Pinned finite equality decides whether a slot label is leftSlot.", DescribeRole.Definition),
            Node("guardedEqSignature", "Fin 3 retains three slot labels. Bool.rec selects the output type, its equality dictionary and its role: one Boolean ADMIT guard and two typed CUT terms. The anchor index is empty and every state is retained.", DescribeRole.Definition),
            Node("guardedEqRealization", "Dependent Boolean dispatch selects the guard or a typed value; a second Bool.rec selects the left or right equality term. Fin labels are compared as data, with no Fin or Nat recursor dispatch, and all three readouts remain independent.", DescribeRole.Definition),
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
