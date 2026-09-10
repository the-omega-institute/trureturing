using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class TaggedPresentationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite HF Event Presentations.",
        H("Finite HF Event Presentations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("taggedpresentation-eventequiv"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/TaggedPresentation.eventEquiv"),
                H("A finite presentation has an exact HF event equivalence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An injective HF code realizes the actual finite archive. Its inverse recovers every "
                    + "typed event, and archive attributes and order are transported through this same "
                    + "equivalence."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("taggedpresentation-charge-map"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/TaggedPresentation.charge_map"),
                H("Signed charge respects the event equivalence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The sum over the actual HF event subtype reindexes to the finite presentation. This "
                    + "proves the readout bridge used by the concrete operations; no arithmetic law is assumed "
                    + "as a field."))),
                DescribeRole.Theorem))));
}
