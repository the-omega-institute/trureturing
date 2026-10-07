using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hypermatrix;

internal sealed class SoutheastFactorizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Hypermatrix/SoutheastFactorization.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/koprowski2026enumeration");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Constructive southeast Bruhat factors", H("Constructive southeast Bruhat factors"),
        Blocks(
            Describe.Lean(DescribeId.Create("southeast-factorization"),
                DeclarationHandle.Create(Prefix + "southeast_factorization"), H("Constructive southeast Bruhat factors"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Over every field F, a matrix in GL(n plus one,F) has an upper triangular factor and a residual matrix whose first column has a single pivot one at p; deleting that row and first column gives a matrix in GL(n,F). The pivot is the largest row with a nonzero original first-column entry. Every G in GL(n,F) can be written U B, where U is upper triangular and B has southeast shape for a permutation sigma. If A and C have southeast shapes for sigma and tau and A=U C with U upper triangular, then sigma=tau, A=C and U=1. The proof constructs pivots and inducts on n; uniqueness follows by descending through the row pivots. The zero-dimensional case is retained."))), DescribeRole.Theorem)
        ), []));
}
