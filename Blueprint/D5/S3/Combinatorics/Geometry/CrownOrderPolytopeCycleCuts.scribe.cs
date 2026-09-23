using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class CrownOrderPolytopeCycleCutsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/lundstrom2025crown");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Connected cycle partitions are encoded by their boundary cuts.",
        H("Boundary cuts of a cycle partition"),
        Blocks(
            Paragraph(Text("The cut-set construction makes explicit the partition/edge-deletion correspondence used in the proof of source Lemma 3.5. No new enumerative formula is claimed here.")),
            Describe.Lean(
                DescribeId.Create("cycle-boundary-cuts-eq-empty-iff"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCycleCuts.cycleBoundaryCuts_eq_empty_iff"),
                H("No boundary cuts exactly for the one-block partition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For a nonzero cycle size at least three, a connected partition has no boundary cuts if and only if every two vertices are equivalent."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("connected-cycle-partition-cuts-equiv"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCycleCuts.connectedCyclePartitionCutsEquiv"),
                H("The boundary-cut equivalence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For a nonzero cycle size at least three, connected partitions with at least two boundary cuts are explicitly equivalent to cut sets with at least two elements. The inverse uses the connected components after deleting the selected successor edges. The one-block case is excluded from this equivalence and handled separately by the empty-boundary characterization."))),
                DescribeRole.Definition)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEnumeration"))
        ]));
}
