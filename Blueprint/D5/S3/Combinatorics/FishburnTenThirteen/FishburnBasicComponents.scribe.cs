using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FishburnTenThirteen;

internal sealed class FishburnBasicComponentsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicComponents.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The unique direct-sum decomposition of a permutation yields counting recurrences for Fishburn avoidance classes.",
        H("Unique Direct-Sum Components"),
        Blocks(
            Node("fishburnbasiccomponents-assemble", "Iterated direct sum", "assemble",
                "The assembly of an empty list of words is the empty word. The assembly of a first block followed by further blocks is the first block followed by the assembly of the remaining blocks with every entry increased by the length of the first block.", DescribeRole.Definition),
            Node("fishburnbasiccomponents-unique-sum-components", "Decomposition and component recurrences", "unique_sum_components",
                "Let p be a permutation of one through n, and let B consist of nonempty sum-indecomposable patterns with positive entries containing every rank from one through their maximum entry. There is a unique list of nonempty sum-indecomposable permutations whose iterated direct sum is p. The permutation p is Fishburn and avoids B exactly when every component is Fishburn and avoids B; the same equivalence holds for any list of such components. Write a(s) for the number of Fishburn permutations of length s avoiding B and i(s) for the number of their sum-indecomposable members. Then a(0) is one and a(s + 1) is the sum of i(j + 1) times a(s - j) over j from zero through s. Write b(s, r) for the number of component lists of total length s with r components, all Fishburn and avoiding B. Then b(0, 0) is one, b(s, 0) is zero for positive s, and b(s + 1, r + 1) is the sum of i(j + 1) times b(s - j, r) over j from zero through s. Both recurrences arise from bijections taking a first component and a remaining permutation or component list to their assembly or concatenation, respectively. For any rational-polynomial weight on component lists, the sum of the weights over lists of length s + 1 with r + 1 components equals the corresponding sum over these first-component and remaining-list pairs.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
