using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Fishburn;

internal sealed class FishburnTenTenBTreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Fishburn/FishburnTenTenBTree.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fishburn permutations and classical permutations avoiding specified patterns are classified by their forms and permitted insertion positions.",
        H("FishburnTenTenBTree"),
        Blocks(
            Node("fishburntentenbtree-btype-definition", "Four types of insertion-position labels", "BType", "For length n, the labels consist of an increasing type, an adjacent type with a parameter from zero through n minus two, a persistent type with a parameter from zero through n minus three, and a terminal type with a parameter from zero through n minus two. The adjacent and terminal parameter sets are empty for n less than two, and the persistent parameter set is empty for n less than three.", DescribeRole.Definition),
            Node("fishburntentenbtree-bspec-definition", "Specifications of the four classical types", "BSpec", "The increasing type is the increasing permutation with every position permitted for insertion of the next maximum. An adjacent type with parameter c permits exactly positions c plus one and c plus two; if c plus two equals n, the prefix before c plus one and the suffix beginning there are increasing and the two entries across the cut form a descent. A persistent type with parameter c has these same increasing pieces and descent at c plus one, and permits exactly positions c plus one and n. A terminal type with parameter c permits only position c plus one. Permitted insertion positions preserve avoidance of 321, 2143 and 3124.", DescribeRole.Definition),
            Node("fishburntentenbtree-b-classification-theorem", "Classification of the first classical class", "b_classification", "Every permutation of length n avoiding 321, 2143 and 3124 satisfies the specification of at least one of the increasing, adjacent, persistent or terminal types. The specification records its permitted positions for insertion of the next maximum and the required increasing pieces.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
