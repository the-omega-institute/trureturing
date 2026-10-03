using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PermutationSquare;

internal sealed class PermutationSquareStructureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PermutationSquare/PermutationSquareStructure.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Dynamics/archer2026pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonempty permutation avoiding 312 and 54321 whose square avoids 132 consists of an indecomposable first component followed by decreasing components of length at most four.",
        H("The first component and the layered tail"),
        Blocks(
            Node("permutationsquarestructure-component-ends-one-theorem", "The last entry of an indecomposable component", "component_ends_one", "Every nonempty permutation of one through its length that avoids 312 and is indecomposable under direct sum ends in one. Direct-sum indecomposability means that at every proper nonempty prefix there is an entry in the remaining suffix no greater than some entry of the prefix.", DescribeRole.Theorem),
            Node("permutationsquarestructure-square-tail-identity-theorem", "Squaring a direct sum and its tail", "square_tail_identity", "Let left and right be permutations of one through m and one through n, respectively, with m positive. Their direct sum is left followed by right with m added to every entry. Its square is the direct sum of their squares. If the square of the direct sum avoids 132, the square of right is the increasing permutation of one through n, so right is an involution.", DescribeRole.Theorem),
            Node("permutationsquarestructure-component-involution-decreasing-theorem", "Indecomposable 312-avoiding involutions are decreasing", "component_involution_decreasing", "If a nonempty permutation of one through its length avoids 312, is indecomposable under direct sum, and has square equal to the increasing permutation, then it is the decreasing permutation of that length.", DescribeRole.Theorem),
            Node("permutationsquarestructure-avoider-layered-tail-theorem", "Decomposition of a square-avoider", "avoider_layered_tail", "For every positive n, each permutation p of one through n avoiding 312 and 54321 whose square avoids 132 is a direct sum of a nonempty indecomposable first component and a list of decreasing blocks. The first component belongs to the same square-avoidance class at its own length. Every block of the tail is nonempty, consists of its length down to one, and has length at most four. The tail is assembled by repeated direct sums and may be empty.", DescribeRole.Theorem),
            Node("permutationsquarestructure-admissible-layered-tail-theorem", "Appending decreasing blocks preserves square avoidance", "admissible_layered_tail", "Let first be a nonempty permutation avoiding 312 and 54321 whose square avoids 132. Let tail be any list of nonempty decreasing permutations, each of length at most four. The direct sum of first with the repeated direct sum of tail again avoids 312 and 54321 and has square avoiding 132. The first permutation need not be indecomposable.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
