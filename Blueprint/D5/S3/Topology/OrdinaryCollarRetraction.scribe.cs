using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class OrdinaryCollarRetractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Support of the ordinary collar retraction",
        H("Support of the ordinary collar retraction"),
        Blocks(Describe.Lean(
            DescribeId.Create("ordinarycollarretraction-result"),
            DeclarationHandle.Create("D5/S3/Topology/OrdinaryCollarRetraction.retract_support"),
            H("Support of the ordinary collar retraction"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text("The old support of the retracted nested flag is the intersection of its original support with the selected colour."))),
            DescribeRole.Theorem))));
}
