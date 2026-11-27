using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.ClosedNeighborhoodCorona;

internal sealed class RegularIntertwinerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Regular adjacency-cospectral graphs admit an orthogonal intertwiner fixing the constant vector.",
        H("Orthogonal intertwining of regular adjacency matrices"),
        Blocks(
            Describe.Lean(DescribeId.Create("regular-adjacency-orthogonal-intertwiner"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/RegularIntertwiner"
                    + ".exists_orthogonal_adjacency_intertwiner"),
                H("An intertwiner fixing the all-ones vector"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For two separately regular graphs on the same finite vertex type, "
                    + "equality of the real adjacency characteristic polynomials gives a spectral "
                    + "conjugacy. On a nonempty carrier the regular degrees agree. A reflection "
                    + "in the common row-sum eigenspace corrects the conjugacy to fix the all-ones "
                    + "vector. On the empty carrier the identity already satisfies the equations."))),
                DescribeRole.Theorem))));
}
