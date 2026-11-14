using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class OriginalExclusionLimitsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/OriginalExclusionLimits.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original whole-exclusion limits and regular region",
        H("Original whole-exclusion limits and regular region"), Blocks(
            Paragraph(Text("For every natural j set S(j)={p in P : 1/(j+1)<=diam(D(p))}, and define R as the union of the interiors of S(j), all taken in P. Upper semicontinuity makes every S(j) closed. The original positive-dimensional whole-ball exclusions have strictly positive full diameter, so exists_nat_one_div_lt shows that the S(j) cover all P. ReciprocalPureCompactness.reciprocal_pure_compact, under the same closedness, strict positivity, generation and pure PR assumptions, makes P compact; Mathlib.Topology.Baire.LocallyCompactRegular supplies its Baire structure. The dense_iUnion_interior_of_closed theorem from Mathlib.Topology.Baire.Lemmas applies to this countable closed cover. Consequently IsOpen R and Dense R both hold. With Sigma=P\\R, IsClosed Sigma follows from openness, and interior(closure Sigma) is empty because closure Sigma=Sigma and density of R gives empty interior of its complement. These are full consequences of the compactness, dichotomy, diameter and generic Baire results. The original_regular_iff_continuous theorem below identifies exactly this R with the Hausdorff continuity set of the entire D map; neither residual collapse branch is removed.")),
            Describe.Lean(DescribeId.Create("original-discontinuity-collapse"),
                DeclarationHandle.Create(Owner + "original_discontinuity_collapse"), H("Every discontinuity supplies an actual whole-ball collapse"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Under the full original EB3 and pure PR hypotheses, at each Hausdorff discontinuity p there is a sequence pn of original pure labels tending to p and an actual pure q in D(p) such that the entire D(pn) tends to {q}. The proof directly consumes the frozen ReciprocalExclusionLimits.exclusion_limit_dichotomy, including its actual parameter extraction and exact whole-ball equality. If no such singleton subsequence exists, compactness of the entire family inside K makes every subsequence admit a further subsequence tending to the old whole D(p), proving continuity. This is not a conditional row premise. The stronger frozen ReciprocalPureCompactness.reciprocal_pure_compact supplies pure compactness without EB or nontriviality; no duplicate pure-compactness declaration is retained."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-regular-iff-continuous"),
                DeclarationHandle.Create(Owner + "original_regular_iff_continuous"), H("Exact whole-ball continuity set"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every original pure p, p belongs to R if and only if the actual whole-exclusion map is Hausdorff continuous at p. On an interior diameter layer an actual singleton collapse would contradict the positive lower bound and continuity of diameter. Conversely continuity at a nondegenerate old ball gives a positive diameter bound in an open neighborhood in all P. OriginalComparisonTopology.original_common_continuity_sets identifies this same R with both actual scalar continuity sets, and the scalar applications below establish both semicontinuities on all P."))), DescribeRole.Theorem))));
}
