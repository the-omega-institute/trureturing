using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.DigitHankel;

internal sealed class CyclotomicDigitHankelDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/sobolewski2026hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary Digit Sums and Their Cyclotomic Hankel Zero Set",
        H("Binary Digit Sums and Their Cyclotomic Hankel Zero Set"),
        Blocks(
            Node("cyclotomic-digit-hankel-defs-digit-sum", "Binary digit sum", "digitSum", "For a natural number u and a complex parameter t, digitSum is the sum of the binary digits of u, read from the least significant position, each multiplied by the corresponding power of t.", DescribeRole.Definition),
            Node("cyclotomic-digit-hankel-defs-hankel", "Binary digit Hankel determinant", "hankel", "For a natural number n and a complex parameter t, hankel is the determinant of the n by n matrix whose entry at indices i and j is digitSum of i plus j at t.", DescribeRole.Definition),
            Node("cyclotomic-digit-hankel-defs-z-bound", "Cyclotomic interval radius", "zBound", "For an order d and a length l, zBound uses the remainder of l minus one modulo d and its quotient by d to form the integer radius in the binary zero intervals.", DescribeRole.Definition),
            Node("cyclotomic-digit-hankel-defs-in-zero-set", "Cyclotomic zero interval membership", "InZeroSet", "A positive natural number n belongs to InZeroSet d when some l at least d plus one and some odd s place n in the half-open interval centered at 2 to the l times s with radius zBound d l plus one.", DescribeRole.Definition),
            Node("cyclotomic-digit-hankel-defs-claim", "Cyclotomic Hankel zero characterization", "claim", "For every d at least two, every primitive d-th root of unity zeta, and every n at least two, the binary digit Hankel determinant at 2 times zeta vanishes exactly when n belongs to InZeroSet d.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
