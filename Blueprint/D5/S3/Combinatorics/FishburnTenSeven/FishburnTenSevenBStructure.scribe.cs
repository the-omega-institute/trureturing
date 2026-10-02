using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FishburnTenSeven;

internal sealed class FishburnTenSevenBStructureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenBStructure.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Permutations in the second triple-avoidance class have one of two interval forms.",
        H("FishburnTenSevenBStructure"),
        Blocks(
            Node("fishburntensevenbstructure-b-interval-normalform-theorem", "Interval forms for the second class", "B_interval_normalForm",
                "For positive n, every Fishburn permutation of length n avoiding 1324, 2143 and 3124 has an m between one and n and one of two forms. The first is the decreasing interval from n through m plus one followed by a Fishburn permutation of length m avoiding 213 and starting with one. The second has two at most d, d at most h, and h less than m, and consists of the decreasing interval from n through m plus one, the decreasing interval from h through d, one, the increasing interval from h plus one through m minus one, m, and a Fishburn permutation of length d minus two avoiding 213 with each entry increased by one.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
