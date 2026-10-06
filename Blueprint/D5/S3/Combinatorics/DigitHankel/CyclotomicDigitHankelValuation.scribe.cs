using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.DigitHankel;

internal sealed class CyclotomicDigitHankelValuationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelValuation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/sobolewski2026hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Valuation Bounds and Recursive Noncancellation",
        H("Valuation Bounds and Recursive Noncancellation"),
        Blocks(
            Node("cyclotomic-digit-hankel-valuation-torsion", "Torsion root difference valuation", "torsion_root_difference", "For a valuation in which the value of 2 is below one, a nontrivial n-th root of unity has difference from one of valuation at least the value of 2, with equality exactly for the root minus one.", DescribeRole.Theorem),
            Node("cyclotomic-digit-hankel-valuation-recursive", "Recursive noncancellation", "recursive_noncancellation", "Assume base bounds through size four, equality information at valuation one, and a recursive determinant step whose correction term has strictly smaller valuation. Then every nonzero bordered determinant forces the corresponding Hankel determinant to be nonzero and preserves the valuation lower bound.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
