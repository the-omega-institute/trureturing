using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class ExistentialWitnessRegistrationTemplatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact existential registration over complete finite witness assignments.",
        H("ExistentialWitnessRegistrationTemplates"),
        Blocks(
            Node("existentialWitnessSignature", "A complete witness assignment is the state and its acceptance is the sole ADMIT slot.", DescribeRole.Definition),
            Node("existentialWitnessRealization", "The supplied predicate is evaluated at each witness state without replacing it by a proved existential.", DescribeRole.Definition),
            Node("existentialWitnessArena", "The fixed law requires an accepted state; no raw law or predicate is passed to the arena constructor.", DescribeRole.Definition),
            Node("existentialWitnessLegacy", "Boolean reflection identifies existence of an accepted state with the full existential predicate.", DescribeRole.Theorem),
            Node("existentialWitness_sensitivity", "On any inhabited arena, all-accepted and all-rejected realizations witness sensitivity of the single slot.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrationTemplates." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
