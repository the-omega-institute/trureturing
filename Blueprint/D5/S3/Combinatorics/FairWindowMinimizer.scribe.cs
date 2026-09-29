using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class FairWindowMinimizerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FairWindowMinimizer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Offline word orderings and labels have an exact average defect on every context without repeated words.",
        H("Deterministic Word-Minimum Window Tables"),
        Blocks(
            Node("word", "Candidate word types", "word",
                "For natural m and k, a binary block v of length m+k has k+1 candidate "
                + "words of length m. Candidate i reads v(i+j) for every j less than m.",
                DescribeRole.Definition),
            Node("select", "Leftmost minimum", "select",
                "For every natural n and every natural-valued rank function on positions "
                + "zero through n, select is the least position among those attaining the "
                + "minimum rank.", DescribeRole.Definition),
            Node("rank", "Ordering all word types", "rank",
                "For each natural m, a permutation rho of all binary m-words followed by "
                + "their fixed finite enumeration assigns distinct natural ranks to word types. "
                + "Each permutation represents one complete strict ordering.", DescribeRole.Definition),
            Node("table", "A fixed strict-window table", "table",
                "For natural m and k, fix one word permutation rho and one binary label "
                + "function beta on all m-words. On a binary window v of length m+k, choose "
                + "the leftmost candidate a of minimum rank. Multiply the sign of beta at "
                + "the chosen word by the relation signs at positions a+m through m+k-1. "
                + "The output is one if this product is one, and zero otherwise. A zero "
                + "bit has sign minus one and a one bit has sign one. The chosen tables "
                + "are fixed across all contexts and times; the rule reads only this window.",
                DescribeRole.Definition),
            Node("good-context-average", "Exact defect on a context with distinct words",
                "good_context_average",
                "For every natural m greater than zero, every natural k, and every binary "
                + "context v of length m+k+1, suppose its k+2 consecutive m-words are pairwise "
                + "distinct. Uniformly average over all complete word permutations rho and, "
                + "independently, all complete binary label functions beta. The average of "
                + "the actual defect of table(m,k,rho,beta) on v is exactly 1/(k+2). "
                + "Swapping word identities makes every candidate equally likely to have "
                + "the least rank in the union of the two windows. The chosen position "
                + "changes exactly when that minimum is at one of the two outer endpoints, "
                + "giving frequency 2/(k+2). A common chosen position gives exact transport. "
                + "For two distinct chosen words, flipping the label at the new word pairs "
                + "defect zero with defect one, giving label average one half. This also "
                + "includes k equal to zero, when the two candidate sets are disjoint.",
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/FairWindowDefect"))]));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
