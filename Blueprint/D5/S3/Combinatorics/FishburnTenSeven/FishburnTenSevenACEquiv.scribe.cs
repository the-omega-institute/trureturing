using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FishburnTenSeven;

internal sealed class FishburnTenSevenACEquivDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenACEquiv.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first and third triple-avoidance classes are parametrized by three-letter words.",
        H("FishburnTenSevenACEquiv"),
        Blocks(
            Node("fishburntensevenacequiv-acparameters-definition", "Parameters for the first and third classes", "ACParameters",
                "For a nonnegative size and a Boolean selecting the third class, the parameter set is the disjoint union of a singleton and pairs consisting of a peak between two and the size and a word of length peak minus two. The word belongs to language C when the Boolean is true and to language A when it is false.", DescribeRole.Definition),
            Node("fishburntensevenacequiv-ac-equivalence-theorem", "Word parametrization of two avoidance classes", "ac_equivalence",
                "For every positive size, the Fishburn permutations avoiding 1324, 2143 and 1423 are in bijection with the parameters using language A, and those avoiding 1324, 1423 and 3124 are in bijection with the parameters using language C. The singleton corresponds to the decreasing permutation. A peak and word correspond to the permutation obtained by reconstruction at the given size, with the word assigning the entries from two through peak minus one to the three blocks.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
