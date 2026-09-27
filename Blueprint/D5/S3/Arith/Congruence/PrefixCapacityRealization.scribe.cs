using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class PrefixCapacityRealizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual forbidden-prefix trees admit supported probability laws with capacities normalized by their positive comb-flow lower bound.",
        H("Supported Probability Laws from Prefix Capacities"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-prefix-capacity-probability-law"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Congruence/PrefixCapacityRealization.exists_comb_capped_probability"),
                H("Every actual prefix tree realizes the comb-normalized capacities"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix any alphabet size p >= 2, finite height H, and "
                        + "nonnegative capacity beta(d) in any linearly ordered "
                        + "field at each depth. "
                        + "An arbitrary Boolean predicate on actual finite words "
                        + "marks forbidden prefixes. The root is allowed and "
                        + "there is at most one forbidden word at every positive "
                        + "depth through H, including redundant descendants. "
                        + "Assume the existing combFlow recursion is positive.")),
                    Paragraph(Text(
                        "The theorem constructs nonnegative weights on all "
                        + "height-H words whose sum is one. The function "
                        + "prefixMass is the actual marginal: fix every symbol "
                        + "of the given prefix, then sum the remaining leaf "
                        + "coordinates. Every forbidden prefix has marginal "
                        + "zero. Every depth-d prefix has marginal at most "
                        + "beta(d) divided by combFlow(p,H,beta).")),
                    Paragraph(Text(
                        "The proof first constructs an unnormalized leaf "
                        + "measure of total mass exactly prefixFlow. Inductively, "
                        + "each child has a supported measure realizing its "
                        + "flow. If their total mass is zero, the parent measure "
                        + "is zero. Otherwise multiply every child measure by "
                        + "the minimum of the parent capacity and total child "
                        + "mass, divided by that total. This factor is between "
                        + "zero and one, so it preserves all descendant capacity "
                        + "bounds and forbidden-prefix zero masses. This "
                        + "construction works for arbitrary forbidden predicates.")),
                    Paragraph(Text(
                        "The existing comb comparison then bounds the actual "
                        + "root mass below by the positive comb flow. Dividing "
                        + "the constructed measure by its actual root mass "
                        + "gives the stated probability law. No monotonicity of "
                        + "the depth capacities is assumed. The formal result "
                        + "supplies finite leaf weights and their marginal caps "
                        + "over the chosen field. At rational scalars, the "
                        + "weights, nonnegativity and unit-sum fields directly "
                        + "construct the imported FiniteLaw structure; no "
                        + "approximation or rationalization step is required. "
                        + "Transport to the physical prime-power coordinates "
                        + "and the subsequent conditional-kernel application "
                        + "remain separate proof obligations."))),
                DescribeRole.Theorem))));
}
