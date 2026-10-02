using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Fishburn;

internal sealed class FishburnTenTenAAddressesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Fishburn/FishburnTenTenAAddresses.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fishburn permutations and classical permutations avoiding specified patterns are classified by their forms and permitted insertion positions.",
        H("FishburnTenTenAAddresses"),
        Blocks(
            Node("fishburntentenaaddresses-a-live-addresses-theorem", "Unique parameters for positive insertion positions", "a_live_addresses", "For n at least two, consider the increasing permutation, the permutations formed by reversing a consecutive interval from low plus one through high with low plus two at most high and high at most n, and the permutations formed by a decreasing block from peak through bottom plus one, then one, then an increasing block from peak plus one through n, then a decreasing block from bottom through two, where two is at most bottom and bottom is less than peak and peak is at most n. The map from these three disjoint parameter sets to permutations is injective. Its image consists exactly of the Fishburn permutations avoiding 2143, 1423 and 3124 that have a positive insertion position for the next maximum preserving this avoidance.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
