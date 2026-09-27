using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class CrownOrderPolytopeOddBlocksDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/lundstrom2025crown");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Parity imbalance determines extremality of each odd block.",
        H("Geometry of odd crown blocks"),
        Blocks(
            Paragraph(Text("The parity-majority orientation is the odd-block argument in the proof of source Lemma 3.2 and the endpoint selection in Proposition 3.3.")),
            Describe.Lean(
                DescribeId.Create("crown-odd-block-geometry"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeOddBlocks.crownOddBlock_geometry"),
                H("Odd blocks have a unique parity majority"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For n at least two, every odd block of a connected cycle partition has even-vertex and odd-vertex counts differing by one. An even majority excludes incoming crown edges from other blocks; an odd majority excludes outgoing edges to other blocks. These orientations are conclusions derived from the actual block geometry."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCyclePartitions"))
        ]));
}
