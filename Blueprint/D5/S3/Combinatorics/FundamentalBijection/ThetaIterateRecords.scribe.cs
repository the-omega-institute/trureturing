using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaIterateRecordsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaIterateRecords.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Consecutive record values and the ordering of record-block tails characterize 132-avoidance.",
        H("Record-Block Characterization of 132-Avoidance"),
        Blocks(
            Node("fundamental-bijection-thetaiteraterecords-adjacent-record-values", "Consecutive record values", "adjacent_record_values",
                "Two consecutive left-to-right maxima of a 132-avoiding permutation differ in value by exactly one.", DescribeRole.Theorem),
            Node("fundamental-bijection-thetaiteraterecords-earlier-entry-gt-later-tail", "Earlier letters dominate a later block tail", "earlier_entry_gt_later_tail",
                "In a 132-avoiding permutation, an entry before a record position exceeds every later entry in that record block.", DescribeRole.Theorem),
            Node("fundamental-bijection-thetaiteraterecords-avoids132-iff-record-blocks", "The record-block criterion", "avoids132_iff_record_blocks",
                "A permutation avoids 132 exactly when consecutive record values differ by one, each tail after a record and before the next record avoids 132 internally, and every earlier entry exceeds every entry in a later record-block tail.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
