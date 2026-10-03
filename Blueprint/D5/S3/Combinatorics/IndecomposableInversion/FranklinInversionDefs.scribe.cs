using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.IndecomposableInversion;

internal sealed class FranklinInversionDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/franklin2024inversions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Indecomposable permutations avoiding 321 and 1342 are grouped by their number of inversions.",
        H("FranklinInversionDefs"),
        Blocks(
            Node("franklininversiondefs-inv-definition", "Number of inversions", "inv", "For a list of natural numbers, the inversion number is the number of pairs of positions i and j such that i is less than j and the entry at i is greater than the entry at j. Positions are numbered from zero and both positions are less than the length of the list.", DescribeRole.Definition),
            Node("franklininversiondefs-indecomposable-definition", "Indecomposability", "Indecomposable", "A list is indecomposable if, for every positive i strictly less than its length, its prefix of length i is not a permutation of one through i. For a permutation, this excludes a decomposition as the direct sum of two nonempty permutations.", DescribeRole.Definition),
            Node("franklininversiondefs-avoiders-definition", "Indecomposable avoiders with a fixed inversion number", "avoiders", "For a nonnegative integer k, I_k(321, 1342) consists of all nonempty permutations of one through n, with n allowed to vary, that are indecomposable, have exactly k inversions and avoid the classical patterns 321 and 1342.", DescribeRole.Definition),
            Node("franklininversiondefs-claim-definition", "The conjectured count", "claim", "The conjecture states that, for every nonnegative integer k, the number of permutations in I_k(321, 1342) equals k(k + 1)/2 + 1.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
