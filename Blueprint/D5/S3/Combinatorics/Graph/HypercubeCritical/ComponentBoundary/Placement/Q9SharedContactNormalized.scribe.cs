using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9SharedContactNormalizedDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9SharedContactNormalized.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A cube translation and axis permutation preserve the local conditions of shared contacts.",
        H("Normalize a shared distance-three contact"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-normalized-shared-contact"),
                DeclarationHandle.Create(Owner + "exists_normalized_shared_contact"),
                H("Transport to the canonical contact"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Translate the second endpoint to zero and order the coordinates by the axis "
                    + "permutation. Hamming distances and occupied degrees are preserved. A coordinate flip "
                    + "conjugates to the corresponding flip in the new coordinates, preserving exterior "
                    + "evenness and the exclusion of occupied squares. The normalized vertices and occupied "
                    + "triples match one of the three shared cases."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9SharedContactAxisOrbits"))
        ]));
}
