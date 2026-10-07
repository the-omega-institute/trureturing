using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Apwenian;

internal sealed class GuoHanBlocksDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Apwenian/GuoHanBlocks.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/guo2025apwenian");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal letters determine equal iterated substitution blocks, and the apwenian recursion identifies parity once every even position is one.",
        H("Substitution Blocks and Parity Identification"),
        Blocks(
            Node("guo-han-blocks-equal-blocks", "Equal letters have equal iterated blocks", "equal_blocks",
                "Let p be a positive integer, let sigma assign a word of length p of nonnegative integers to each nonnegative integer, and let a satisfy a(np + r) = sigma(a(n), r) for every nonnegative n and every r from zero through p minus one. If a(n) = a(m), then for every nonnegative integer t and every j from zero through p^t minus one, a(n p^t + j) = a(m p^t + j). The equality is between actual letters, without passing to parity.", DescribeRole.Theorem),
            Node("guo-han-blocks-identify-parity", "Even positions determine period doubling", "identify_parity",
                "Let b be a sequence in the integers modulo two satisfying b(n) = b(2n + 1) + b(2n + 2) for every nonnegative integer n. If b(2n) = 1 for every nonnegative n, then b(n) equals the image of P(n) modulo two for every nonnegative n, where P is the period-doubling sequence. The recursion gives b(2n + 1) = 1 - b(n), so induction determines every entry.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
