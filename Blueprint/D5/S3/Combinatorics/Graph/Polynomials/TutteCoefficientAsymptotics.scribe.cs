using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Polynomials;

internal sealed class TutteCoefficientAsymptoticsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Polynomials/TutteCoefficientAsymptotics.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For each forward-degree bound D and coefficient index k, the signed rank-state polynomial of every connected simple graph with that ordered degree bound differs from the negative-binomial comparison coefficient by at most C(D,k)(e+1)^(k−1). The constant is independent of the graph and carrier size. No forest equality, cyclic-state count, or term estimate is assumed: the proof consumes the graph-derived fixed-rank count and term bounds in CyclicRankEstimate.",
        H("Uniform signed graph coefficient estimate"),
        Blocks(
            Paragraph(Text("The graph polynomial is the finite sum over actual edge subsets S of (−1)^|S| z^q(S) (1+z)^(v−1+|S|−2q(S)), with q(S)=v−c(S) counting all connected components, including isolated vertices. Its exponents are proved nonnegative. The cyclomatic number is the natural number e+1−v; connectedness and v>0 justify its integer interpretation, including trees and the one-vertex graph.")),
            Paragraph(Text("The proof uses the integer-binomial comparison term (−1)^s choose(v−1−s,k−s) for s≤k. Summing it over all edge subsets gives choose(−b,k) by the powerset insertion identity and Pascal recurrence. On forests this term equals the actual coefficient. Consequently the forest error is exactly minus the comparison sum over cyclic states. This error generally does not vanish: the triangle has forest polynomial 1−z+z² and cubic coefficient zero, whereas choose(−1,3)=−1. Integer binomial coefficients keep negative comparison exponents intact, so small vertex sets require no asymptotic restriction.")),
            Paragraph(Text("Grouping cyclic states by their actual graph rank j≤k, the finite support-pattern injection gives O(D,j)((e+1)^(j−1)) states. Each actual state term and each comparison term has growth O(k)((e+1)^(k−j)). Their products therefore have the common exponent k−1. Cyclic graph rank is at least two, giving the exact first coefficient −b. States above rank k vanish. This establishes both the approximate forest contribution and the full uniform estimate.")),
            Node("cyclic-constant", "cyclicErrorConstant", "Finite cyclic-error constant", "Sum the proved rank-specific pattern constants from j=0 through k. It depends only on D and k.", DescribeRole.Definition),
            Node("cyclic-estimate", "graph_cyclic_coefficient_estimate", "Actual cyclic contribution", "The absolute cyclic coefficient is bounded by 2^k times the cyclic-error constant times (e+1)^(k−1). The proof uses actual graph ranks, the finite-injection count, and derived state-term growth.", DescribeRole.Theorem),
            Node("forest-estimate", "graph_forest_coefficient_estimate", "Approximate forest contribution", "The forest coefficient differs from choose(−b,k) by at most (2k+3)^k times the cyclic-error constant times (e+1)^(k−1). Forest equality is neither assumed nor claimed.", DescribeRole.Theorem),
            Node("uniform-constant", "uniformCoefficientConstant", "Uniform coefficient constant", "The constant is (2^k+(2k+3)^k) times the cyclic-error constant; it is independent of e, v and the graph.", DescribeRole.Definition),
            Node("signed-estimate", "signed_tutte_coefficient_estimate", "Uniform coefficient theorem", "For every connected simple graph on Fin v with v>0 and forward degree at most D, and every k≥1, the absolute difference between the kth signed state coefficient and (−1)^k choose(b+k−1,k) is at most C(D,k)(e+1)^(k−1). The statement includes small graphs and trees. This is a theorem about the explicit rank-state polynomial, not a geometric Jones identification or a resolution of the weaving conjecture.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create("tutte-coefficient-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
