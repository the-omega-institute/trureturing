using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaIterateCycleScanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaIterateCycleScan.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Avoidance in a parameter, its successor word, and its cycle word controls the terminal value and low suffix.",
        H("Bounds from the Parameter Cycle"),
        Blocks(
            Node("fundamental-bijection-thetaiteratecyclescan-terminal-value-at-least-half", "A lower bound for the terminal value", "terminal_value_at_least_half",
                "Let r and q be permutations of the same size h at least four, with q beginning at h and its cyclic successor map equal to the permutation map of r. If r starts with h, h minus one, has penultimate value one and terminal value v at least two, and r, b(r), and q all avoid 132, then h is at most twice v.", DescribeRole.Theorem),
            Node("fundamental-bijection-thetaiteratecyclescan-low-suffix-descending", "The decreasing low suffix", "low_suffix_descending",
                "Under the same cycle and avoidance conditions, if v is below h minus two, then the entry of r at each position i from v through h minus three is h minus one minus i.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
