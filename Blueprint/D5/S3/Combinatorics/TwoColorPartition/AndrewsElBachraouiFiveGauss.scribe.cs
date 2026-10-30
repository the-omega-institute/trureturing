using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TwoColorPartition;

internal sealed class AndrewsElBachraouiFiveGaussDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveGauss.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/andrews2025positive");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp parity-sensitive Gauss coefficient upper bound.",
        H("Sharp parity-sensitive Gauss coefficient upper bound"),
        Blocks(
            Node("andrews-el-bachraoui-fivegauss-gauss-coefficient-upper", "Sharp leading upper bound", "gauss_coefficient_upper", "For every natural n, the real coefficient of productTrunc 2 n is at most pi over four times n, plus five quarters times the square root of twice n plus one half, plus pi over sixteen and three eighths. The proof keeps the parity-compatible triangular rows, bounds their square-root sums by a quarter-circle integral, and applies the existing exact Gauss coefficient count. This upper bound is sufficient for the full eventual result.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
