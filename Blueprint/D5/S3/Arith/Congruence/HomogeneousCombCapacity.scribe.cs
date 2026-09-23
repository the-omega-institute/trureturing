using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class HomogeneousCombCapacityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual homogeneous prefix-tree capacity flow is bounded below by the comb recursion when each depth has at most one forbidden node.",
        H("Homogeneous Capacity and Forbidden-Prefix Combs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("homogeneous-comb-actual-prefix-flow"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Congruence/HomogeneousCombCapacity.comb_le_actual_prefix_flow"),
                H("Actual prefix-tree flow is bounded below by the comb recursion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let p >= 2 and H >= 0 be arbitrary integers. Give every node "
                        + "of the full p-ary tree at depth d the same nonnegative "
                        + "capacity beta(d) in any linearly ordered field, with no "
                        + "monotonicity requirement. Rationals and reals are both "
                        + "direct specializations. An "
                        + "arbitrary Boolean predicate on finite words over Fin p "
                        + "marks forbidden nodes. The root is allowed, and at each "
                        + "positive depth through H at most one word is forbidden. "
                        + "The count includes redundant forbidden descendants.")),
                    Paragraph(Text(
                        "The actual prefixFlow recursion returns zero at a forbidden "
                        + "node. At an allowed leaf it returns that depth's capacity; "
                        + "at an allowed internal node it returns the minimum of "
                        + "the node capacity and the sum of its actual child flows. "
                        + "For an unobstructed subtree the corresponding fullFlow "
                        + "recursion has p equal children. The combFlow recursion "
                        + "has one blocked child, p-2 full children, and one "
                        + "continuing comb child. The theorem proves combFlow <= "
                        + "prefixFlow at the root for every actual obstacle predicate.")),
                    Paragraph(Text(
                        "The proof constructs a depth-count loss envelope. Its "
                        + "positive-part recursion subtracts each layer's unused "
                        + "full-tree capacity. Induction proves this envelope "
                        + "monotone and superadditive for nonnegative count "
                        + "profiles. Counts from the actual child prefix trees "
                        + "sum exactly to the next global level count, so the "
                        + "tree induction derives the loss bound without assuming "
                        + "a partition inequality or assuming the desired flow "
                        + "comparison. The all-one count envelope equals the "
                        + "difference between full and comb flow.")),
                    Paragraph(Text(
                        "The formal statement compares explicit finite-tree "
                        + "min/sum recursions. The ordinary interpretation of "
                        + "that recursion as an attained maximum of supported "
                        + "leaf flows requires the usual recursive splitting "
                        + "of a parent mass among its children; that realization "
                        + "is not a separate conclusion of this Lean theorem. "
                        + "In the prime-power application, distinct pure powers "
                        + "supply one possible forbidden prefix per depth. "
                        + "Node-dependent capacities, several forbidden nodes "
                        + "at one depth, and optimal second-moment claims are "
                        + "outside the theorem's hypotheses and conclusion."))),
                DescribeRole.Theorem))));
}
