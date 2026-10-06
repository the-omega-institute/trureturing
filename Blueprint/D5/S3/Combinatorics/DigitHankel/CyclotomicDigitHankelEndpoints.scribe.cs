using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.DigitHankel;

internal sealed class CyclotomicDigitHankelEndpointsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelEndpoints.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/sobolewski2026hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Phase Power Auxiliary Determinant",
        H("Phase Power Auxiliary Determinant"),
        Blocks(
            Node("cyclotomic-digit-hankel-endpoints-phase", "Phase power endpoint criterion", "phase_power_auxiliary", "For d at least two and a d-th primitive root zeta, define the phase sequence F and its bordered determinant E. At every k at least one and every a, E at k minus one and size 2 to the k is nonzero exactly when no integer from zero through k minus one added to a is divisible by d.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
