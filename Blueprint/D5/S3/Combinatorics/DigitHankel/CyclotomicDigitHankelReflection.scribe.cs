using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.DigitHankel;

internal sealed class CyclotomicDigitHankelReflectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelReflection.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/sobolewski2026hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reflection and Block Conjugation",
        H("Reflection and Block Conjugation"),
        Blocks(
            Node("cyclotomic-digit-hankel-reflection-block", "Determinant-one block conjugation", "block_conjugation", "For a sequence over a commutative ring satisfying the two binary carry relations, with 2 to the k below n at most twice that power, there is a determinant-one matrix whose conjugation transforms the Hankel matrix into the stated binary block form with weights w and x minus 2w.", DescribeRole.Theorem),
            Node("cyclotomic-digit-hankel-reflection-weighted", "Weighted reflection recurrence", "weighted_reflection", "Under the carry relations, k at least one, and n in the reflection range, the Hankel determinant H at n and bordered determinant E at n reduce to the corresponding determinants at 2 to the k plus reflected index, with the explicit powers and signs in the recurrence.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
