using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MetallicHankel;

internal sealed class MetallicHankelUnboundedTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedTransfer.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/han2025hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The metallic reversed-denominator recurrence over integer dual numbers has an explicit linear monodromy at each complete cycle.",
        H("Dual-Number Transfer Along the Metallic Cycle"),
        Blocks(
            Node("metallic-hankel-unbounded-transfer-jet-word", "The cyclic dual-number coefficients", "jetWord",
                "Work in the integer dual numbers, written a + b epsilon with epsilon squared equal to zero. For n equal to one, the coefficient word is [(1+epsilon,-1), (1+epsilon,1), (-1+epsilon,-1)]. For every other nonnegative integer n, take the metallic cycle in its given order. At each state with fraction data (k,v,D), the corresponding pair is ([q^{k+1}]D + [q^k]D epsilon, v). Thus the word retains the denominator coefficients at degrees k+1 and k together with the sign of each fraction term.", DescribeRole.Definition),
            Node("metallic-hankel-unbounded-transfer-jet-step", "One reversed-denominator step", "jetStep",
                "For a state (z_1,z_2) of two integer dual numbers and a coefficient pair (a,v) consisting of a dual number and an integer, the next state is (a z_1 - v z_2, z_1). Integers act as dual numbers with zero epsilon coefficient.", DescribeRole.Definition),
            Node("metallic-hankel-unbounded-transfer-cycle-transfer", "The state after complete cycles", "cycle_transfer",
                "Let n be a positive integer, let W be its cyclic dual-number coefficient word, and let a sequence of states start at (1,0) and follow the step (z_1,z_2) to (a z_1 - v z_2,z_1), using the coefficient W at the current index modulo its length. Put lambda = 1 for n = 1 and lambda = 2n+1 otherwise. After k complete cycles, for every nonnegative integer k, the state is (1 - k lambda epsilon, 2k lambda epsilon). This includes the separate three-term golden word and the metallic words for every n at least two.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
