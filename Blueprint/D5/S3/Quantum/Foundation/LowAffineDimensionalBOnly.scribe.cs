using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class LowAffineDimensionalBOnlyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Whole-base balls and the Radon segment-face branch supply original proper antipodal effects.",
        H("Whole-base and segment-face branches of VII98.7"),
        Blocks(
            Paragraph(Text("For the original finite-dimensional closed pointed generating cone and its original strictly positive unit, an entire pair ball equal to the whole normalized base yields a genuine linear proper effect separating every unit antipodal chart pair.")),
            Describe.Lean(DescribeId.Create("ball-chart-antipodal-effect"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/LowAffineDimensionalBOnly.ball_chart_antipodal_effect"),
                H("A whole-base chart gives a proper antipodal effect"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The chart coordinate functional is extended from the chart direction to the entire original carrier. Properness is checked on every cone element by normalization into the whole base."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("all-antipodes-of-full-pair-balls"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/LowAffineDimensionalBOnly.allAntipodes_of_full_pair_balls"),
                H("Consumer: the original allAntipodes predicate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When every distinct pure pair has a chart whose pair base is the whole base, the preceding effect supplies allAntipodes on the original carrier."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("segment-faces-lowdim-antipodes"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/LowAffineDimensionalBOnly.segment_faces_lowdim_antipodes"),
                H("Radon reduction of the entire segment-face branch"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Start with the entire original pure set, with no finiteness or closedness hypothesis on it. Assume affine dimension at most three and that every distinct pure pair has its entire native pair base equal to its segment. Radon's theorem partitions any dependent family of at most five pure points into two intersecting convex hulls. One side has at most two points; its hull is an extreme singleton or a native segment face. Every pure point on the other side lies outside that face, and the complement of an extreme set in the original convex base is convex. Thus the hulls cannot intersect. Five distinct original pure points would be dependent by affine dimension, so the whole pure set is finite. The same argument gives its affine independence, and compact convex generation identifies the whole base with its simplex. The frozen zero-kernel coordinate-effect theorem then supplies genuine proper linear effects on the original carrier. Its coordinate values distinguish every distinct pure pair, including both endpoints of every actual admitted ball-chart antipode."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("affine-dimension-at-most-one-antipodes"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/LowAffineDimensionalBOnly.affine_dimension_at_most_one_antipodes"),
                H("The zero- and one-dimensional branches"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The direction of a chart's whole ball is the range of its injective linear part. If the chart dimension reaches the affine dimension of the original base, these direction spaces coincide. Every original base point then has an ambient chart coordinate. Pairing that coordinate with a sufficiently small negative multiple puts the chart center strictly between the original point and a point of the pair face. The native face property forces the original point into the pair face. In affine dimension at most one, every positive-dimensional chart therefore fills the original base. The original B supplies a chart for every distinct pure pair, so allAntipodes_of_full_pair_balls applies on its live proof path. This includes the empty distinct-pair quantifier in dimension zero."))), DescribeRole.Theorem),
            Paragraph(Text("The dimension is the finrank of the affine direction vectorSpan of the original base, not the linear span of that normalized base. The result also bounds the full pure-set cardinality by affine dimension plus one.")),
            Paragraph(Text("These are proved branches of source VII98.7, not the complete B-implies-A theorem. The remaining work is the global full-ball case from a single full-dimensional pair face, reduction of one-dimensional pair balls to native segments, and the m=3 spherical-facet branch from VII98.6. In particular no general positive-dimensional-facet exclusion or m-at-least-four failure conclusion is asserted. The source atom remains open and uncovered.")))));
}
