using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Polynomials;

internal sealed class CyclicRankEstimateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed rank-state polynomial has an exact finite coefficient decomposition. Forest states supply the negative-binomial coefficient, while a bounded cyclic-state count and a uniform term bound give the coefficient error estimate. The graph wrapper records the actual SimpleGraph rank state used by the eventual weaving application; its bounded-degeneracy counting and Jones/geometric identification remain later obligations.",
        H("Signed rank-state coefficient estimate"),
        Blocks(
            Node("state-exponent", "stateExponent", "State exponent", "The finite polynomial uses the Nat conversion of the integer exponent only after an explicit nonnegativity proof has been supplied.", DescribeRole.Definition),
            Node("state-exponent-integer", "stateExponentInteger", "Integer rank-state exponent", "The exponent is first formed in Z as v − 1 + s − 2q, before any conversion to a polynomial Nat exponent.", DescribeRole.Definition),
            Node("state-exponent-cast", "stateExponent_cast_eq_integer", "No-truncation exponent bridge", "Under the explicit integer nonnegativity hypothesis, the Nat exponent used by the polynomial casts back to the original integer rank-state exponent.", DescribeRole.Theorem),
            Node("state-term", "stateTerm", "Signed rank-state term", "Each subset state contributes its sign, rank power and (1+z) exponent to the integer polynomial.", DescribeRole.Definition),
            Node("state-polynomial", "statePolynomial", "Signed rank-state polynomial", "The polynomial is the finite sum over all edge-indexed subset states.", DescribeRole.Definition),
            Node("forest-states", "forestStates", "Forest states", "States with q(S)=|S| are selected as the forest part of the finite subset sum.", DescribeRole.Definition),
            Node("cyclic-states", "cyclicStates", "Cyclic states", "States with q(S)<|S| are selected as the cyclic part.", DescribeRole.Definition),
            Node("term-coefficient", "termCoefficient", "Coefficient of one state", "The coefficient of z^k in one state term is the signed binomial contribution when q(S)≤k and is zero otherwise.", DescribeRole.Definition),
            Node("ideal-coefficient", "idealCoefficient", "Ideal forest coefficient", "The comparison coefficient is Ring.choose (−b) k over the integers.", DescribeRole.Definition),
            Node("ideal-coefficient-formula", "idealCoefficient_formula", "Negative-binomial coefficient formula", "The ideal coefficient equals (−1)^k choose(b+k−1,k), including the b=k=0 boundary case.", DescribeRole.Theorem),
            Node("coeff-state-term", "coeff_stateTerm", "Exact state coefficient", "Polynomial coefficient extraction agrees with termCoefficient for every finite subset state.", DescribeRole.Theorem),
            Node("coeff-state-polynomial", "coeff_statePolynomial", "Exact finite coefficient sum", "The coefficient of the full state polynomial is the finite sum of the state coefficients.", DescribeRole.Theorem),
            Node("forest-coefficient", "forestCoefficient", "Forest coefficient", "The forest contribution is the sum of termCoefficient over forestStates.", DescribeRole.Definition),
            Node("cyclic-coefficient", "cyclicCoefficient", "Cyclic coefficient", "The cyclic contribution is the sum of termCoefficient over cyclicStates.", DescribeRole.Definition),
            Node("coeff-split", "coeff_split", "Forest/cyclic coefficient split", "Under the rank upper bound, every state belongs to exactly one of the forest and cyclic filters, so the full coefficient splits into the two contributions.", DescribeRole.Theorem),
            Node("cyclic-abs-bound", "natAbs_cyclicCoefficient_le", "Cyclic absolute coefficient bound", "A uniform per-state NatAbs bound B implies the cyclic coefficient is bounded by the cyclic-state cardinality times B.", DescribeRole.Theorem),
            Node("signed-estimate", "signed_tutte_coefficient_estimate", "Signed coefficient estimate", "The theorem consumes coeff_split and the cyclic absolute bound: if the forest coefficient is the ideal coefficient, the coefficient error is bounded by the cyclic count times the per-state bound, with the stated uniform growth envelope.", DescribeRole.Theorem),
            Node("graph-edge-predicate", "graphEdgePredicate", "Actual simple-graph edge predicate", "The graph wrapper lifts SimpleGraph adjacency to the unordered edge type Sym2(Fin n).", DescribeRole.Definition),
            Node("graph-edge", "graphEdge", "Actual graph edge type", "The graph wrapper restricts the finite edge index type to the actual adjacency predicate, so nonedges are not duplicated in the subset state sum.", DescribeRole.Definition),
            Node("graph-rank", "graphRank", "Actual graph rank state", "The graph wrapper computes rank from the connected-component count of the image of the actual edge subset, including isolated vertices.", DescribeRole.Definition),
            Node("graph-state-polynomial", "graphStatePolynomial", "Actual graph state polynomial", "The graph wrapper instantiates the signed state polynomial with graphRank; it is the consumer interface for the later bounded-degeneracy and weaving layer.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create("cyclic-rank-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
