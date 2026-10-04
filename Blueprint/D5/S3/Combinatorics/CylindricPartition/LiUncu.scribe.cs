using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CylindricPartition;

internal sealed class LiUncuDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CylindricPartition/LiUncu.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/li2025macmahon");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Li and Uncu's finite Andrews-Gordon companion identity holds for every k at least five.",
        H("The Finite Andrews-Gordon Companion Identity"),
        Blocks(
            Node("li-uncu-result", "The companion identity", "result",
                "For every nonnegative integer n, every integer k at least five, and every integer i with 1 at most i and i less than k, the finite multiple sum equals the finite alternating Gaussian sum of equation (1.5). The multiple sum runs over n_1 at least n_2 at least the successive entries through n_(k-1) at least n_k = 0, with entries at most n. Its exponent is the sum of n_j squared for 1 at most j and j less than k, plus the sum of n_j for i at most j and j less than k. Its jth primed Gaussian factor has upper index 2n - 2 times the sum of n_l for l less than j, minus n_j, n_(j+1), and 2 max(j-i+1,0), and lower index n_j - n_(j+1). The alternating sum has sign (-1)^r, exponent r((2k+1)r+2k-2i+1)/2, and Gaussian upper index 2n and lower index n-(2k+1)r/2+(2k-2i+1)((-1)^r-1)/4. Its nonzero terms have r between -(n+1) and n+1. The Gaussian polynomial vanishes outside zero through its upper index; its primed version is one at lower index zero even for a negative upper index. Weighted peak deletion gives the multiple sum, and the four image families give the alternating sum.", DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("li-uncu-finite-andrews-gordon-companion"), ResolutionKind.Proved))
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
