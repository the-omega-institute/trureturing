using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class ExistentialWitnessRegistrationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact existential registration over complete finite witness assignments.",
        H("ExistentialWitnessRegistrations"),
        Blocks(
            Node("capturedArena", "All eight twist and listing assignments form the witness arena.", DescribeRole.Definition),
            Node("capturedRealization", "Acceptance retains the negated IsEscaped predicate at each twist and listing.", DescribeRole.Definition),
            Node("captured_bridge", "The original two existential binders are bundled into a pair using only product existential equivalence and Boolean reflection.", DescribeRole.Theorem),
            Node("captured_lawSensitive", "The frozen captured-listing theorem validates the original realization; rejecting every assignment falsifies the law.", DescribeRole.Theorem),
            Node("captured_slotSensitive", "The generic witness-template sensitivity theorem certifies the ADMIT slot.", DescribeRole.Theorem),
            Node("recognitionArena", "All 64 concept and value assignments form the witness arena.", DescribeRole.Definition),
            Node("recognitionRealization", "Acceptance retains both concept inequality and the original mutual-recognition predicate.", DescribeRole.Definition),
            Node("recognition_bridge", "All four existential binders and both conjuncts are preserved by product bundling and Boolean reflection.", DescribeRole.Theorem),
            Node("recognition_lawSensitive", "The frozen unequal-concepts theorem validates acceptance; the all-rejected realization falsifies the law.", DescribeRole.Theorem),
            Node("recognition_slotSensitive", "The single ADMIT slot has a checked generic sensitivity witness.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrations." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
