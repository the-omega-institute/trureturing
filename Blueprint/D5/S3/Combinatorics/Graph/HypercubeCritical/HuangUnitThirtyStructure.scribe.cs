using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class HuangUnitThirtyStructureDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/HuangUnitThirtyStructure.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A unit negative-three Huang eigenvector of support thirty has actual support degrees three or five and a nonempty matching of opposite edges.",
        H("Structure at unit support thirty"),
        Blocks(
            Paragraph(Text(
                "Hong–Wu–Xia, arXiv:2610.09483v1, §7 Problem 2 "
                    + "(https://arxiv.org/html/2610.09483v1#Thmproblem2), asks whether "
                    + "f₂(Q₉)=3 or 4 (the 258-vertex question). The original external "
                    + "problem remains unresolved here; literature novelty is unconfirmed. "
                    + "Throughout, intA and intCoeff retain the original FALSE-prefix "
                    + "signed Huang integer operator and coefficients from HuangIntegralNormGap.")),
            Describe.Lean(
                DescribeId.Create("structure-of-unit-negative-three-support-thirty"),
                DeclarationHandle.Create(Prefix + "structure_of_unit_negative_three_support_thirty"),
                H("Actual degrees three or five and a nonempty opposite-edge matching"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For r : Q9 → ℤ, assume heig: intA r = −3r, "
                            + "hu: every r(x) is 0, 1, or −1, and hcard: "
                            + "S = {x : r(x) ≠ 0} has cardinality thirty. "
                            + "Then every x ∈ S has actual induced support "
                            + "degree three or five; at most one actual neighbor "
                            + "y ∈ S satisfies intCoeff(x,y) r(x) r(y) = +1; "
                            + "and at least one such actual edge exists. This "
                            + "is the conclusion of "
                            + "structure_of_unit_negative_three_support_thirty(r, heig, hu, hcard). "
                            + "These opposite edges form a nonempty matching. "
                            + "The conclusion asserts neither connectedness nor "
                            + "regular degree three of the full support.")),
                    Paragraph(Text(
                        "Unit values identify squared norm with support size. "
                            + "parity_norms gives squared norm fifteen on each "
                            + "parity part, and parts_eigen makes every original "
                            + "Huang row of each part divisible by three. For "
                            + "a support vertex y, take the part q of parity "
                            + "opposite y and eps = −r(y), so intA q y = 3 eps. "
                            + "Let k = |supp(q) ∩ N(y)|, and reduce "
                            + "q(x) − eps intCoeff(x,y) modulo three to its "
                            + "centered representative c(x) ∈ {0, ±1}. The "
                            + "reduced vector stays in one parity and its rows "
                            + "remain divisible by three. Summing the local "
                            + "identities gives 2|supp(c)| + 3k = 45 and "
                            + "2|supp(c) ∩ N(y)| + k = 15.")),
                    Paragraph(Text(
                        "The row equation gives 3 ≤ k ≤ 9, and the second "
                            + "identity makes k odd. If k ≥ 7, the reduced "
                            + "support is nonempty and has size at most twelve. "
                            + "No singleton rows and its single parity allow "
                            + "CubeTwelveSupport.eq_neighbors_of_card_le_twelve "
                            + "to identify it with a full nine-neighbor star "
                            + "N(z). The identities then force k = 9 and "
                            + "|N(z) ∩ N(y)| = 3. Cube neighborhoods intersect "
                            + "in nine points when z = y and in at most two "
                            + "otherwise, a contradiction. Hence k is three "
                            + "or five, which is also y's actual degree in S.")),
                    Paragraph(Text(
                        "For each x ∈ S, summing the original signed row "
                            + "equation after multiplication by r(x) gives "
                            + "2 opposite_count(x) + 3 = degree_S(x). Thus "
                            + "every vertex has at most one opposite neighbor. "
                            + "If there were no opposite edge, all degrees "
                            + "would be three. The original parity switch "
                            + "sigma(x) = (if cubeParity(x) then −1 else 1) r(x), "
                            + "viewed over ℝ, would witness IsBalanced S. "
                            + "BalancedCubeLowerBound.forty_eight_le_card applies "
                            + "to this nonempty balanced regular degree-three "
                            + "support and gives 48 ≤ 30, a contradiction."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/HuangUnitNormThirty")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/HuangEnergyFiveResidual")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeLowerBound"))
        ]));
}
