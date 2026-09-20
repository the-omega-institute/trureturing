using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class CrownOrderPolytopeSelectionCountsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/lundstrom2025crown");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Profile counts and the one-block edge give the full selection count.",
        H("Counting selected odd blocks"),
        Blocks(
            Paragraph(Text("These counts implement source Lemma 3.4 together with the marked count in Lemma 3.5. All support conditions and the one-block contribution are explicit.")),
            Describe.Lean(
                DescribeId.Create("crown-odd-block-selection-profile-card"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeSelectionCounts.crownOddBlockSelection_profile_card"),
                H("Count for a fixed odd-block profile"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For n at least two, i at least two and m positive, the selections with i boundary cuts and 2m odd blocks that yield d+2 augmented blocks have the exact marked cardinality stated in Lean. The binomial factor choosing i-d selected odd blocks is zero when d exceeds i; that support condition is explicit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("crown-odd-block-selection-one-block-card"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeSelectionCounts.crownOddBlockSelection_oneBlock_card"),
                H("The unique one-block contribution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every positive n, selections whose underlying cycle partition has one block contribute exactly one when d equals one and zero otherwise. The single even block permits only the empty odd-block selection."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("crown-odd-block-selection-card"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeSelectionCounts.crownOddBlockSelection_card"),
                H("Sum of all selection profiles"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For n at least two, the cardinality of all selections producing d+2 augmented blocks equals the one-block correction plus the finite sum of the exact profile counts. Division by the number of markings is justified within the count."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeMarkedCuts")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEndpointRecovery"))
        ]));
}
