using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MetallicHankel;

internal sealed class MetallicHankelUnboundedStripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedStrip.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/han2025hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exponential coefficient growth and bounded determinant rows at two shifts give a bound independent of determinant size at every intermediate shift.",
        H("Bounded Strips of Shifted Hankel Determinants"),
        Blocks(
            Node("metallic-hankel-unbounded-strip-bounded-strip", "A uniform bound between two bounded rows", "bounded_strip",
                "Let Phi be an integral formal power series, let a, b and B be nonnegative integers with a at most b, and let M be a positive integer. Suppose that the absolute value of [q^m]Phi is at most B^m for every nonnegative integer m, and that the absolute values of both Delta_j^{(a)} and Delta_j^{(b)} are at most M for every nonnegative integer j. Then for every integer ell between a and b and every nonnegative integer j, the absolute value of Delta_j^{(ell)} is strictly less than 2^{floor(log_2 M)+2(ell-a)(b-ell)+1}. Here Delta_j^{(ell)} is the shifted Hankel determinant of Phi, with empty determinant one. The bound is independent of j and B; B is used only in the coefficient-growth hypothesis. In particular, two bounded rows force all intervening rows to be bounded.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
