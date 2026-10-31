using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SetFamily;

internal sealed class CrossIntersectingLayerGapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SetFamily/CrossIntersectingLayerGap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonnegative rank weights and cross-intersection force a gap between the coatom and singleton layers.",
        H("A Weighted Cross-Intersection Layer Gap"),
        Blocks(
            Describe.Lean(DescribeId.Create("cross-intersection-weighted-mass"),
                DeclarationHandle.Create(Prefix + "weightedMass"), H("Rank-weighted mass"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an arbitrary finite carrier alpha and a finite family C of its subsets, "
                    + "weightedMass(omega,C) is the sum of omega(card(A)) over all A in C. "
                    + "The function omega assigns one real weight to each natural rank; "
                    + "the definition itself imposes no sign or monotonicity condition."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("weighted-cross-intersecting-layer-gap"),
                DeclarationHandle.Create(Prefix + "weighted_cross_intersecting_layer_gap"),
                H("The coatom layer exceeds the singleton layer by at least two"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let alpha be any finite type with decidable equality, and put d=card(alpha). "
                        + "Assume d is at least four. Let omega be an arbitrary function from natural ranks to real numbers "
                        + "such that every weight is nonnegative. Zero weights are allowed, and no relation between "
                        + "weights at different ranks is required. Let C and D be finite families of subsets of alpha. "
                        + "Both families are upward closed under inclusion, and every member of C has nonempty "
                        + "intersection with every member of D. Suppose each family's weighted mass is strictly greater "
                        + "than omega(d-1)+omega(d). Then card(C.slice(1))+2 is at most card(C.slice(d-1)). "
                        + "Here slice(r) keeps exactly the members of cardinality r. "
                        + "The nonnegative weights and strict mass bounds also imply that both families are nonempty.")),
                    Paragraph(Text("For a finite set J in a larger ambient type, take alpha to be the subtype of elements "
                        + "of J. Its finite subsets are exactly subsets of J through the canonical inclusion. "
                        + "This identifies the statement for every finite J, with d=card(J), without choosing an ordering "
                        + "or restricting the original carrier to a particular labelled set.")),
                    Paragraph(Text("If every member of a family contains a fixed coatom, its only possible members "
                        + "are that coatom and the full carrier. Nonnegativity bounds its mass by the sum of the "
                        + "coatom and top weights. Thus an upward family above this threshold has at least two "
                        + "coatoms: with at most one missing-point index, every member would contain the corresponding coatom.")),
                    Paragraph(Text("Let t be the number of singletons in C. Cross-intersection forces every member "
                        + "of D to contain all t selected points. If t were at least d-1, every member of D would "
                        + "contain a fixed coatom, contradicting its strict mass bound. Hence t+2 is at most d. "
                        + "If t=0, the two-coatom bound proves the result. If t=1, upward closure includes at least "
                        + "d-1 coatoms, giving a gap of at least d-2, which is at least two. If t is at least two, "
                        + "every coatom contains a selected singleton, so all d coatoms belong to C and the result follows. "
                        + "The upward-closure hypothesis on D is retained in the statement, although this argument "
                        + "uses only its mass and cross-intersection.")),
                    Paragraph(Text("This theorem concerns arbitrary weighted families of finite subsets. "
                        + "Applying it to polygon completions requires a separate encoding of those completions, "
                        + "a proof that the resulting families satisfy these hypotheses, and any required compression "
                        + "or identification of families. Those constructions are outside this theorem."))),
                DescribeRole.Theorem)), []));
}
