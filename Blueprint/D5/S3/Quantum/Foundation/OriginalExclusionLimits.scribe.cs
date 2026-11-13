using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class OriginalExclusionLimitsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/OriginalExclusionLimits.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Whole-P discontinuity witnesses and Baire regularity", H("Whole-P discontinuity witnesses and Baire regularity"), Blocks(
            Paragraph(Text("V is an arbitrary finite dimensional real normed space, C its entire original pointed cone, and u the original linear unit. Assume C is closed and generating and u is strictly positive on nonzero C. K is the entire normalized base, P its entire extreme locus, and the effects and confirmers are the full original families, including u. EB3 parametrizes every whole exclusion, and PR exchanges only pure endpoints. All label neighborhoods use all P. No mixed PR, weakPair, RegularAnchor, global UF, prescribed saturation or matrix specialization is assumed.")),
            Describe.Lean(DescribeId.Create("original-discontinuity-collapse"),
                DeclarationHandle.Create(Owner + "original_discontinuity_collapse"), H("Every discontinuity supplies an actual whole-ball collapse"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Under the full original EB3 and pure PR hypotheses, at each Hausdorff discontinuity p there is a sequence pn of original pure labels tending to p and an actual pure q in D(p) such that the entire D(pn) tends to {q}. The proof directly consumes the frozen ReciprocalExclusionLimits.exclusion_limit_dichotomy, including its actual parameter extraction and exact whole-ball equality. If no such singleton subsequence exists, compactness of the entire family inside K makes every subsequence admit a further subsequence tending to the old whole D(p), proving continuity. This is not a conditional row premise. The stronger frozen ReciprocalPureCompactness.reciprocal_pure_compact supplies pure compactness without EB or nontriviality; no duplicate pure-compactness declaration is retained."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-diameter-upper-semicontinuous"),
                DeclarationHandle.Create(Owner + "original_diameter_upperSemicontinuous"), H("Actual whole diameters on all P"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The function p -> diam(D(p)) is upper semicontinuous on all original pure labels. Each diameter upper layer is sequentially closed. Compactness in the hyperspace supplies an actual whole-set limit; the exact frozen dichotomy places that limit inside D(p). The diameter is Lipschitz with constant two on the nonempty compact hyperspace, so the threshold survives the limit."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-baire-regular-region"),
                DeclarationHandle.Create(Owner + "original_baire_regular_region"), H("Open dense regular region and closed nowhere dense residual"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Define S(j) by 1/(j+1)<=diam(D(p)), with j ranging over all natural numbers, and R as the union of their interiors in all P. Every S(j) is closed, and positive dimension makes every full diameter positive, so these layers cover P. Frozen pure compactness makes P a compact Baire space. Hence R is open and dense, and Sigma=P\\R is closed and nowhere dense. This does not remove either residual collapse branch."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-regular-iff-continuous"),
                DeclarationHandle.Create(Owner + "original_regular_iff_continuous"), H("Exact whole-ball continuity set"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every original pure p, p belongs to R if and only if the actual whole-exclusion map is Hausdorff continuous at p. On an interior diameter layer an actual singleton collapse would contradict the positive lower bound and continuity of diameter. Conversely continuity at a nondegenerate old ball gives a positive diameter bound in an open neighborhood in all P. OriginalComparisonTopology.original_common_continuity_sets identifies this same R with both actual scalar continuity sets, and its two semicontinuity theorems cover all P."))), DescribeRole.Theorem))));
}
