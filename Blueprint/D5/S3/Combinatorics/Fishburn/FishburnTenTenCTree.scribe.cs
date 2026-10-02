using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Fishburn;

internal sealed class FishburnTenTenCTreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Fishburn/FishburnTenTenCTree.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fishburn permutations and classical permutations avoiding specified patterns are classified by their forms and permitted insertion positions.",
        H("FishburnTenTenCTree"),
        Blocks(
            Node("fishburntentenctree-ctype-definition", "Four labels for the second classical class", "CType", "For length n, the labels consist of an increasing type, a persistent type with a cut from zero through n minus two, a delayed type with a cut from zero through n minus three, and a terminal type with a cut from zero through n minus one. Persistent labels require n at least two, delayed labels require n at least three, and terminal labels require positive n.", DescribeRole.Definition),
            Node("fishburntentenctree-cspec-definition", "Specifications of insertion positions and increasing prefixes", "CSpec", "The increasing type is the increasing permutation with every position permitted for insertion of the next maximum. A persistent type with cut c is not increasing, has a strictly increasing prefix before c, and permits exactly positions c and n. A delayed type with cut c is not increasing and permits exactly positions c and n minus one. A terminal type with cut c permits only position c. Permitted insertion positions preserve avoidance of 231, 4132 and 2134.", DescribeRole.Definition),
            Node("fishburntentenctree-c-classification-theorem", "Unique classification of the second classical class", "c_classification", "Every permutation of length n avoiding 231, 4132 and 2134 satisfies the specification of exactly one increasing, persistent, delayed or terminal label, including its cut parameter when present.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
