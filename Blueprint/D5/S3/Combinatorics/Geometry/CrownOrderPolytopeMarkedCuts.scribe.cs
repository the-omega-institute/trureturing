using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class CrownOrderPolytopeMarkedCutsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/lundstrom2025crown");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Marked cycle partitions yield exact parity-profile cardinalities.",
        H("Marked cuts and parity profiles"),
        Blocks(
            Paragraph(Text("The first count agrees with the denominator-cleared form of source Lemma 3.5 on its stated range. The formal proof also covers m equals zero and all vanishing support cases. The other statements justify the actual block and parity bookkeeping.")),
            Describe.Lean(
                DescribeId.Create("card-prescribed-odd-connected-cycle-partition-identity"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeMarkedCuts.card_prescribedOddConnectedCyclePartition_identity"),
                H("The marked parity-profile count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For n at least two and i at least two, multiplying the number of connected partitions of the 2n-cycle into i blocks with 2m odd blocks by i gives 2n times choose(i,2m) times choose(n+m-1,i-1). The factor i counts markings; all natural support cases are included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-odd-cycle-blocks-card-even"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeMarkedCuts.actualOddCycleBlocks_card_even"),
                H("The number of odd blocks is even"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("In every connected partition of a nonzero cycle of even size, the number of actual odd-cardinality blocks is even. This is the parity constraint needed to index profiles by 2m."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quotient-card-eq-boundary-cuts-card"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeMarkedCuts.quotient_card_eq_boundaryCuts_card"),
                H("Cuts count the actual quotient blocks"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For a cycle of size at least three with at least two boundary cuts, the actual quotient cardinality equals the cardinality of the boundary-cut set."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCyclePartitions"))
        ]));
}
