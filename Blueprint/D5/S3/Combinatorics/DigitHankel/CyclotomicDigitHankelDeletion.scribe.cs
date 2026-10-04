using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.DigitHankel;

internal sealed class CyclotomicDigitHankelDeletionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelDeletion.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/sobolewski2026hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted Deletion for Binary Carry Blocks",
        H("Weighted Deletion for Binary Carry Blocks"),
        Blocks(
            Node("cyclotomic-digit-hankel-deletion-weighted", "Weighted determinant deletion", "weighted_deletion", "Let f over a field of characteristic zero satisfy the two binary carry recurrences with weights w and x, with k at least two and n in the stated middle range. Replacing f above the threshold 2 to the k by the correction x divided by two minus w gives a shorter sequence g. The Hankel determinant H at n and its bordered difference determinant E then equal the displayed powers of 2, x minus 2w, and the smaller determinants H prime and E prime at n minus 2 to the k.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
