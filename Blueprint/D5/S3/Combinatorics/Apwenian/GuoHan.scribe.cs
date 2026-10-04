using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Apwenian;

internal sealed class GuoHanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Apwenian/GuoHan.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/guo2025apwenian");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Purely automatic sequences over a finite alphabet whose only odd letter is one are apwenian exactly when their parity is period doubling.",
        H("Guo and Han's Classification of Automatic Apwenian Sequences"),
        Blocks(
            Node("guo-han-power-two-even", "Power-of-two blocks force every even position to be one", "power_two_even",
                "Let b be a sequence in the integers modulo two satisfying b(n) = b(2n + 1) + b(2n + 2) for all nonnegative n, with b(0) = b(2) = 1. Let p = 2^v for a positive integer v. Suppose that for all nonnegative t and n with b(n) = 1, and every j from zero through p^t minus one, b(n p^t + j) = b(j). Then b(2n) = 1 for every nonnegative n. Contracting copied blocks gives b(n) = 1 implying both b(2n) = 1 and b(4n + 2) = 1; descent rules out a least even position with value zero.", DescribeRole.Theorem),
            Node("guo-han-result", "The automatic apwenian classification", "result", "For every finite alphabet Sigma of nonnegative integers whose only odd letter is one, every integer p at least two, every p-uniform substitution sigma on Sigma, and every fixed point a over Sigma satisfying a(np + r) = sigma(a(n), r) for all nonnegative n and all r from zero through p minus one, a is apwenian if and only if a(n) modulo two equals P(n) for every nonnegative n. Here apwenian means a(0) = 1 and a(n) congruent to a(2n + 1) + a(2n + 2) modulo two, and P is the period-doubling sequence defined by P(2n) = 1 and P(2n + 1) = 1 - P(n). This proves Conjecture 2 of Guo and Han's paper. Equal letters yield equal iterated blocks, finiteness forces initial parity 101, and dyadic contraction excludes every odd factor greater than one in p. For p a power of two, descent forces every even parity to be one and the recursion determines the odd parities. The characterization allows distinct even letters and concerns equality of parity sequences.", DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("guo-han-automatic-apwenian-one-odd-letter"), ResolutionKind.Proved))
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
