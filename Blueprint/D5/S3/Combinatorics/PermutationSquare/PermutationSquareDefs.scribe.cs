using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PermutationSquare;

internal sealed class PermutationSquareDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PermutationSquare/PermutationSquareDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Dynamics/archer2026pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Permutations avoiding 312 and 54321 whose squares avoid 132 define the counting sequence in the Archer-Bourne recurrence conjecture.",
        H("Permutation squares and the conjectured recurrence"),
        Blocks(
            Node("permutationsquaredefs-square-definition", "The square in one-line notation", "square", "For a list p of natural numbers, replace each entry x by the entry of p at zero-based position x minus one, with zero as the default value when that position is absent. Subtraction is in the natural numbers. For a permutation of one through n, this gives its square under composition: the entry at position i is the value of p at position p(i).", DescribeRole.Definition),
            Node("permutationsquaredefs-avoiders-definition", "The square-avoidance class", "avoiders", "For every nonnegative n, the set consists of the lists that permute one through n, avoid the classical patterns 312 and 54321, and have squares avoiding the classical pattern 132. Classical occurrence means a subsequence with the same relative order as the pattern.", DescribeRole.Definition),
            Node("permutationsquaredefs-a-definition", "The counting sequence", "a", "For every nonnegative n, a(n) is the cardinality of the set of permutations of one through n that avoid 312 and 54321 and whose squares avoid 132.", DescribeRole.Definition),
            Node("permutationsquaredefs-claim-definition", "The Archer-Bourne recurrence conjecture", "claim", "The conjecture in Section 5 of Archer and Bourne's Pattern avoidance in compositions and powers of permutations states that, for every natural number n at least six, a(n) equals a(n minus one) plus a(n minus two) plus a(n minus three) plus a(n minus four) plus n minus one. Here a(n) counts permutations avoiding 312 and 54321 whose squares avoid 132.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
