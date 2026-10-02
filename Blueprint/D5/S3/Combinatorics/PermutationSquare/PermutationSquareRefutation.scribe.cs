using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PermutationSquare;

internal sealed class PermutationSquareRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PermutationSquare/PermutationSquareRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Dynamics/archer2026pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "There are nine indecomposable permutations of length eleven avoiding 312 and 54321 whose squares avoid 132, which refutes the Archer-Bourne recurrence conjecture.",
        H("The Archer-Bourne square recurrence fails at eleven"),
        Blocks(
            Node("permutationsquarerefutation-componentcandidates-definition", "Candidates obtained by inserting successive maxima", "componentCandidates", "At parameter zero the candidate list contains only the permutation consisting of one. To obtain the candidates at parameter size plus one, take each candidate at parameter size and insert size plus two immediately before a decreasing suffix of length one, two or three. A suffix length is permitted only when it does not exceed the length of the candidate and the suffix is strictly decreasing. Candidates at parameter size have length size plus one.", DescribeRole.Definition),
            Node("permutationsquarerefutation-component-candidates-complete-theorem", "Completeness of maximum insertion", "component_candidates_complete", "For every nonnegative size, every permutation of one through size plus one that ends in one and avoids 312 and 54321 occurs in the candidate list at parameter size. Removing its maximum leaves a permutation with the same conditions; the entries following that maximum form a nonempty decreasing suffix of length at most three.", DescribeRole.Theorem),
            Node("permutationsquarerefutation-result-theorem", "Refutation at length eleven", "result", "The Archer-Bourne conjecture that a(n) equals the sum of the four preceding terms plus n minus one for every n at least six is false. At length eleven, the number of indecomposable permutations avoiding 312 and 54321 whose squares avoid 132 is nine. The corrected recurrence therefore gives a(11) equal to a(10) plus a(9) plus a(8) plus a(7) plus nine, whereas the conjectured recurrence requires the same four terms plus ten.", DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("archer-bourne-square-tetranacci-refutation"), ResolutionKind.Refuted))
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
