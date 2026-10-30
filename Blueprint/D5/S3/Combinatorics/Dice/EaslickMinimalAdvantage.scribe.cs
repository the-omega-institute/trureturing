using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Dice;

internal sealed class EaslickMinimalAdvantageDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/easlick2026minimaldice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sorted dice and exact unconditional probabilities describe minimal-advantage simple cycles.",
        H("Minimal winning advantage for fair dice"),
        Blocks(
            Node("easlick-isdie","Valid sorted dice","IsDie","For every natural n and list d of natural labels, IsDie(n,d) means that d has length n, is pairwise nondecreasing, and each face x occurring in d satisfies 1 ≤ x ≤ n. Repeated labels and the standard tuple are permitted.", DescribeRole.Definition),
            Node("easlick-wincount","Strict winning ordered outcomes","winCount","For any two lists d and e of natural labels, winCount(d,e) is the sum over occurrences x in d and y in e of the indicator of y < x. Repeated labels retain their multiplicities and ties contribute zero.", DescribeRole.Definition),
            Node("easlick-indexwincount","Strict wins on the independent index product","indexWinCount","For all lists d,e, indexWinCount(d,e) is the sum over i in Fin(length(d)) and j in Fin(length(e)) of the indicator of e[j] < d[i]. Both indices vary over their whole finite domains independently.", DescribeRole.Definition),
            Node("easlick-winprobability","Unconditional uniform strict-win probability","winProbability","For all lists d,e, winProbability(d,e) is the rational indexWinCount(d,e) divided by length(d) times length(e). For nonempty dice this gives every ordered independent pair of face indices the same probability and leaves ties in the denominator.", DescribeRole.Definition),
            Node("easlick-threshold","The least integer above half the outcome count","threshold","For every natural n, threshold(n) = floor(n²/2) + 1. This is an integer score; its attainability by valid dice is a separate assertion.", DescribeRole.Definition),
            Node("easlick-isminimum","The true attained minimum","IsMinimum","For every natural n and rational p, IsMinimum(n,p) requires valid n-face dice d,e with winProbability(d,e)=p, requires p>1/2, and requires p≤winProbability(a,b) for every valid ordered pair a,b with winProbability(a,b)>1/2.", DescribeRole.Definition),
            Node("easlick-edge","Minimum-advantage directed edges","Edge","For natural n and lists d,e, Edge(n,d,e) requires that both are valid n-face dice and that their actual unconditional strict-win probability is an attained minimum among all probabilities above one half.", DescribeRole.Definition),
            Node("easlick-hascycle","Simple cycles with their closing edge","HasCycle","For natural n,k, HasCycle(n,k) means there is a nonempty list c of exactly k pairwise distinct dice such that c followed by its first entry is a chain for Edge(n). The last-to-first edge is included and no vertex can be reused.", DescribeRole.Definition),
            Node("easlick-s","An exact global maximum","S","For every natural n, S(n) means HasCycle(n,n) and, for every natural k>n, the negation of HasCycle(n,k). Thus the bound concerns all simple cycles in the entire graph.", DescribeRole.Definition),
            Node("easlick-conjectureone","The complete conjecture","ConjectureOne","ConjectureOne is the proposition S(6) and, for every natural n≥7, not S(n). It imposes no condition at three, four or five, and it does not assume the existence of longer cycles.", DescribeRole.Definition),
            Node("easlick-wincount-eq-indexwincount","The occurrence-to-index counting bridge","winCount_eq_indexWinCount","For all lists d and e of natural labels, winCount(d,e)=indexWinCount(d,e). Each occurrence in a list is recovered from its face index, so multiplicities are preserved in the equality.", DescribeRole.Theorem),
            Node("easlick-threshold-attained","Attainment for every n at least three","threshold_attained","For every natural n≥3 there exist valid sorted n-face dice d,e whose strict-win count is threshold(n). For n=2k the dice are 1 repeated k−1 times, then 2, then 3 repeated k times, against 1 followed by 2 repeated 2k−1 times. For n=2k+1 they are 1 repeated k times, then 2, then 3 repeated k times, against 1 repeated k+1 times followed by 2 repeated k times.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
