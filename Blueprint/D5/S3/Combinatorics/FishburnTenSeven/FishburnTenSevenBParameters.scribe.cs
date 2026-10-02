using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FishburnTenSeven;

internal sealed class FishburnTenSevenBParametersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenBParameters.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The second triple-avoidance class has parameters describing initial-one tails and interval forms.",
        H("FishburnTenSevenBParameters"),
        Blocks(
            Node("fishburntensevenbparameters-hstart-definition", "Permutations starting with one", "HStart",
                "For a nonnegative size, this set consists of the Fishburn permutations of that length avoiding 213 whose first entry is one.", DescribeRole.Definition),
            Node("fishburntensevenbparameters-bparameters-definition", "Parameters for the second class", "BParameters",
                "Choose a maximum between one and the size. Its parameters are the disjoint union of Fishburn permutations of length maximum avoiding 213 and starting with one, and triples consisting of a low between two and maximum minus one, a high between low and maximum minus one, and a Fishburn permutation of length low minus two avoiding 213.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
