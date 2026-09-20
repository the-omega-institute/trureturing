using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics;

internal sealed class RegistrationWitnessesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/RegistrationWitnesses.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Law variation and exact slot sensitivity over a single primitive signature.",
        H("Primitive Law Witness Predicates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("law-variation"),
                DeclarationHandle.Create(Prefix + "FiniteLawVariation"),
                H("Law variation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two realizations of the same signature satisfy and violate the law."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("slot-sensitivity"),
                DeclarationHandle.Create(Prefix + "FiniteSlotSensitivity"),
                H("Exact slot sensitivity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each readout or anchor can change the law while every other coordinate is held fixed."))),
                DescribeRole.Definition))));
}
