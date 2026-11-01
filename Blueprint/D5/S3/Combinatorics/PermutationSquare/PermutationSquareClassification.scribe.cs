using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PermutationSquare;

internal sealed class PermutationSquareClassificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PermutationSquare/PermutationSquareClassification.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Dynamics/archer2026pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tail structure, middle-segment pattern avoidance, classification for first entry four across all lengths at least four, and the full seven-family classification for lengths at least nine.",
        H("First entry four and complete classification"),
        Blocks(
            Node("permutationsquareclassification-first-entry-four-structure-theorem", "Tail types and middle-segment structure when the first entry is four", "first_entry_four_structure", "For every natural number n at least four and every p in indecomposableAvoiders(n) with first entry four, the last four entries of the square of p form a permutation of one, two, three, four ending in four, and the three entries of p immediately preceding its final entry one form the set consisting of n together with the one-based positions of two and three in p. When n is at least five, the second entry of p equals three and those three penultimate entries form one of the triples (n, n minus one, two), (n minus one, n, two), or (n minus two, two, n). When n is at least seven, the middle subword M of length n minus six starting at the third entry of p avoids both 312 and 321; its set of entries equals five through n minus two in the first two tail cases, while in the third tail case its set of entries equals five through n minus three together with n minus one and the entry immediately before the triple equals n minus one.", DescribeRole.Theorem),
            Node("permutationsquareclassification-first-entry-four-classification-theorem", "Classification and count for first entry four", "first_entry_four_classification", "For every natural number n at least four, a list p belongs to indecomposableAvoiders(n) and has first entry four if and only if p equals familyC(n), or n is at least six and p equals familyA(n), or n is at least seven and p equals familyB(n), or n is at least nine and p equals familyD(n). Consequently, the number of indecomposable square-avoiders of length n with first entry four equals one for n equal to four or five, two for n equal to six, three for n equal to seven or eight, and four for every n at least nine.", DescribeRole.Theorem),
            Node("permutationsquareclassification-indecomposable-classification-ge-nine-theorem", "Complete classification of indecomposable square-avoiders for length at least nine", "indecomposable_classification_ge_nine", "For every natural number n at least nine, a list p belongs to indecomposableAvoiders(n) if and only if p equals familyI(n), familyJ(n), familyK(n, j) for some j at most floor((n minus six) / 2), familyA(n), familyD(n), familyB(n), or familyC(n).", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
