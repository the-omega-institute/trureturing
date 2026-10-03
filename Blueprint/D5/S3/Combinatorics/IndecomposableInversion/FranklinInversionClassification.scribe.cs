using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.IndecomposableInversion;

internal sealed class FranklinInversionClassificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionClassification.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/franklin2024inversions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positions of entries exceeding a later entry determine the star and five-block classification of indecomposable 321- and 1342-avoiders.",
        H("FranklinInversionClassification"),
        Blocks(
            Node("franklininversionclassification-tall-definition", "Entries exceeding a later entry", "Tall", "A position in a list is tall if there exists a later position within the list whose entry is smaller than the entry at the given position. Positions are numbered from zero.", DescribeRole.Definition),
            Node("franklininversionclassification-tall-ltrmax-theorem", "Tall entries are left-to-right maxima", "tall_ltrMax", "In a list with distinct entries avoiding 321, every tall position within the list is a left-to-right maximum: its entry exceeds every preceding entry.", DescribeRole.Theorem),
            Node("franklininversionclassification-tall-block-structure-theorem", "Positions of tall entries", "tall_block_structure", "Let p be an indecomposable permutation of one through n, where n is positive, avoiding 321 and 1342, and suppose its first entry is not n. There exist positions r, m and later with one at most r, r at most m, m less than the length of p, and m less than later less than the length of p, such that the entry at m is n and the entry at later is smaller than the first entry. A position within p is tall exactly when it is less than r or equal to m.", DescribeRole.Theorem),
            Node("franklininversionclassification-classification-theorem", "Classification of indecomposable avoiders", "classification", "For every nonnegative integer k and every permutation p in I_k(321, 1342), either p is the star permutation with first entry k plus one followed by one through k, or p is a five-block permutation with natural parameters r, t, d and h satisfying r, t and d positive, d at most t, and rt plus d plus h equal to k.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
