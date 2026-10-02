using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Fishburn;

internal sealed class FishburnBasicPrependDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Fishburn/FishburnBasicPrepend.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fishburn permutations and classical permutations avoiding specified patterns are classified by their forms and permitted insertion positions.",
        H("FishburnBasicPrepend"),
        Blocks(
            Node("fishburnbasicprepend-prepend-inherited-sites-theorem", "Insertion positions after prepending the maximum", "prepend_inherited_sites", "Let p be a Fishburn permutation of positive length n, and let every forbidden pattern belong to the set consisting of 1324, 2143, 1423 and 3124. Prepend n plus one to p. Inserting n plus two at position s plus one in this word, for s from zero through n inclusive, produces an avoiding Fishburn permutation exactly when s is positive, inserting n plus one at position s in p produces an avoiding Fishburn permutation, and, if 3124 is forbidden, every pair of entries in the prefix before s is strictly decreasing.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
