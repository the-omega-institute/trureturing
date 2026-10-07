using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PatternMatchings;

internal sealed class TripleAvoidingMatchingsScanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsScan.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/biswas2026matchingtriples");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pattern avoidance is equivalent to closing the oldest or second-oldest open arc with a conditional constraint on the next closure.",
        H("An ordered scan characterizes pattern avoidance"),
        Blocks(
            Node("bss-scan-scanrules", "The oldest-or-second-oldest rule", "ScanRules",
                "Scan the vertices from left to right, ordering the open arcs by their left endpoints. Each closure must select the oldest or second-oldest open arc. If a second-oldest arc closes while a younger open arc is present, the next closure must select the oldest arc. Any number of openings may intervene. When exactly two arcs are open, either closure is allowed without this constraint.", DescribeRole.Definition),
            Node("bss-scan-scan-characterization", "Equivalence of avoidance and the scan rule", "scan_characterization",
                "For every perfect matching on 2n ordered vertices, avoidance of 123, 132 and 213 is equivalent to the oldest-or-second-oldest scan rule and its conditional constraint on the next closure. The condition at height two and arbitrary intervening openings are included.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
