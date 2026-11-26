using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class MatchedFaceIncidenceForestDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The incidence forest of a collapse sequence",
        H("The incidence forest of a collapse sequence"),
        Blocks(Describe.Lean(
            DescribeId.Create("matched-face-incidence-forest"),
            DeclarationHandle.Create(
                "D5/S3/Geometry/MatchedFaceIncidenceForest.incidenceGraph_isAcyclic_of_sequence"),
            H("A coface bound prevents cycles among deleted faces"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Geometry/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text(
                "A fixed-dimensional collapse sequence orders the matched faces. " +
                "Each lower face has at most one other original upper coface, which precedes its match. " +
                "The maximum-rank vertex on a hypothetical incidence cycle would have two distinct predecessors."))),
            DescribeRole.Theorem))));
}
