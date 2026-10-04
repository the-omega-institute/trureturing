using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.DigitHankel;

internal sealed class CyclotomicDigitHankelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankel.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/sobolewski2026hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cyclotomic Binary Digit Hankel Zeros",
        H("Cyclotomic Binary Digit Hankel Zeros"),
        Blocks(
            Node("cyclotomic-digit-hankel-result", "Cyclotomic Hankel zero characterization", "result", "For every d at least two, every primitive d-th root of unity zeta, and every n at least two, the binary digit Hankel determinant at 2 times zeta is zero if and only if n lies in the cyclotomic zero intervals described by InZeroSet.", DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("sobolewski-ulas-cyclotomic-hankel-zeros"), ResolutionKind.Proved))
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
