using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class BarycentricRealizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Realization of finite barycentric subdivisions",
        H("Realization of finite barycentric subdivisions"),
        Blocks(Describe.Lean(
            DescribeId.Create("barycentric-realization-homeomorphism"),
            DeclarationHandle.Create("D5/S3/Topology/BarycentricRealization.realizationHomeomorph"),
            H("The realization homeomorphism"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(
                Paragraph(Text("Replacing each vertex of an ordinary subdivision by the barycentre of its old face induces a homeomorphism of the two finite coordinate realizations.")),
                Paragraph(Text("The greatest face of a positive flag is recovered as the old support. Its coefficient is determined by the least positive coordinate. Subtracting that contribution and repeating gives existence and uniqueness of the flag coordinates. The same support statement identifies the homeomorphism on every subcomplex."))),
            DescribeRole.Theorem))));
}
