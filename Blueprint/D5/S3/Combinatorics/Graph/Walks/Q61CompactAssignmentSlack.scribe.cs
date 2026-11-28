using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class Q61CompactAssignmentSlackDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/Walks/Q61CompactAssignmentSlack.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compact positive assignment slack and finite-block losses for min-plus walks.",
        H("Compact positive assignment slack"),
        Blocks(
            Paragraph(Text("In the complete-Bob model of Meyerovitch–Young Question 6.1, each Alice edge has a real cost matrix on a finite nonempty set of m Bob states. Rows are sources and columns are destinations. For a fixed legal Alice walk, Bob minimizes the sum of the paired costs with both endpoints free. Zero initial scores give every starting state the same initial cost, and the least terminal score is the payoff. https://arxiv.org/html/2603.21449v1#S4.E6")),
            Paragraph(Text("Fix a per-state rate r and an Alice vertex potential H in total-score units. The chosen permutation on an edge has assignment cost at most m times r plus the source potential minus the target potential. When this bound is supplied for the cheapest assignment in per-state units, choose a minimizing permutation on each edge and multiply the bound and potential by m.")),
            Describe.Lean(
                DescribeId.Create("compact-projective-box"),
                DeclarationHandle.Create(Prefix + "isCompact_projectiveBox"),
                H("Compactness of the anchored score box"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Subtracting the score at an anchor o gives a representative with coordinate o equal to zero. The projective box consists of these anchored vectors with every ordered coordinate difference at most B. It is a closed subset of the product of the intervals from −B to B and includes its boundary."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normalized-endpoint-scores-in-box"),
                DeclarationHandle.Create(Prefix + "normalize_endpointScores_mem"),
                H("The box contains the normalized scores after every prefix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Suppose all ordered differences between entries in the same row of each edge matrix are at most B. To bound the difference of two output scores, use a source attaining the minimum for the second destination as a candidate for the first. Its input score cancels, leaving the within-row bound. An input whose normalization is in the box therefore stays in the box after normalization at every prefix."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("assignment-slack-spec"),
                DeclarationHandle.Create(Prefix + "assignmentSlack_spec"),
                H("Slack vanishes exactly on tight walks"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a legal n-edge walk from s to t, the assignment slack is n times m times r plus H(s) minus H(t), minus the gain in the sum of Bob's scores. The assignment certificate makes this slack nonnegative. It is zero exactly when every chosen assignment saturates the edge cap and all its column guards hold at the actual prefix scores from the given input. The guards allow ties."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("assignment-slack-append"),
                DeclarationHandle.Create(Prefix + "assignmentSlack_append"),
                H("Exact addition of block losses"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a split at an intermediate vertex, the slack of the concatenated word equals the first block's slack plus the second block's slack evaluated at the actual scores after the first block. The intervening potential and sum of scores cancel. A common translation of the input translates every later score by the same constant, so the slack can also be evaluated at the normalized input to each block."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compact-block-assignment-slack"),
                DeclarationHandle.Create(Prefix + "compact_block_assignment_slack"),
                H("An attained positive minimum for blocks of fixed length"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Take a finite Alice graph and fix a block length N. For each legal word of length N with specified endpoints, slack is continuous in the input because each update takes a finite minimum of affine functions. There are finitely many word and endpoint choices, so their slack images of the projective box form a compact union.")),
                    Paragraph(Text("If every legal N-edge walk fails tightness from every input in the box, every slack in the union is strictly positive. When the union is nonempty, its least element δ is positive and realized by some legal block and input. An empty union permits any positive lower bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compact-block-payoff-bound"),
                DeclarationHandle.Create(Prefix + "compact_block_payoff_bound"),
                H("A finite-horizon payoff deficit for every complete block"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume N is positive, B is nonnegative, and the same-row bounds hold on every edge. If no legal N-edge walk is tight from any input in the box, take δ from the compact block minimum. Zero initial scores are in the box. Every complete block contributes at least δ at its own prefix scores and the remaining suffix contributes nonnegative slack.")),
                    Paragraph(Text("For any legal n-edge walk from s to t, m times its zero-start, free-terminal payoff plus ⌊n/N⌋δ is at most n times m times r plus H(s) minus H(t). The least terminal score is at most the average terminal score, which converts the total-score bound to the payoff bound."))),
                DescribeRole.Theorem))));
}
