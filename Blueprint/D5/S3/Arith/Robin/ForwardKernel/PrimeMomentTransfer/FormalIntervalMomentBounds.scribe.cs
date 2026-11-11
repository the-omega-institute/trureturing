using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class FormalIntervalMomentBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform interval correlation estimates bound the formal cubic and fourth values.",
        H("Formal interval moment bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("interval-weight"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.intervalWeight"),
                H("interval weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a real scale H, a finite set S of natural numbers and real endpoints a,b, the interval weight on S is one exactly at natural shifts d satisfying floor(aH) < d <= floor(bH), with both floors taken in the natural numbers, and zero elsewhere."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("is-interval-weight"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.IsIntervalWeight"),
                H("is interval weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A coefficient function on a finite shift set is an interval weight in [0,M] at scale H when it equals intervalWeight for some 0 <= a <= b <= M. Membership uses natural floors; for nonnegative H this agrees with the indicator of (aH,bH]."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("is-interval-weight-mul"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.mul"),
                H("is interval weight mul"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For nonnegative H, the product of two interval weights in [0,M] is again such an interval weight. The intersection uses lower endpoint max(a,c) and upper endpoint max(max(a,c),min(b,d)), so disjoint intervals give the empty interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("interval-points-subset"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.interval_points_subset"),
                H("interval points subset"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For nonnegative H and b <= M, every positive integer shift in (aH,bH] is at most floor(MH)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("distinct-interval-weight-moment"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.distinct_interval_weight_moment"),
                H("distinct interval weight moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For nonnegative H and ordered interval endpoints in [0,M], the formal distinct moment of their interval weights on the natural shifts at most floor(MH), with singular-series data transported along inclusion, equals their distinct centered interval correlation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("interval-weight-family"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.interval_weight_family"),
                H("interval weight family"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite family of interval weights in [0,M] at scale H can be represented by two endpoint functions a,b, with 0 <= a_i <= b_i <= M for every index."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("index-interval-weight-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds.index_interval_weight_bound"),
                H("index interval weight bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For nonnegative H, the absolute sum of an interval weight in [0,M] over the natural shifts at most floor(MH) is at most M H."))),
                DescribeRole.Theorem),

            Describe.Lean(DescribeId.Create("geom-product-error"), DeclarationHandle.Create(Prefix + "geom_product_error"), H("Covariance product error"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("If two factors have errors bounded by D H and their leading terms are bounded by M H L, with L at least one, their product error is at most (2 M D plus D squared) H squared L."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("geom-points-card-le"),
                DeclarationHandle.Create(Prefix + "geom_points_card_le"),
                H("Cardinality bound for a scaled interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For nonnegative H and endpoints 0 <= a <= b <= M, the number of positive integer shifts in (aH,bH] is at most M times H."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sigma-bound"),
                DeclarationHandle.Create(Prefix + "sigma_bound"),
                H("Bounds for an overlap length"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If M is nonnegative, a and c are nonnegative, and b is at most M, the nonnegative overlap length max(0,min(b,d)-max(a,c)) is at most M."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("formal-interval-second-bound"),
                DeclarationHandle.Create(Prefix + "formal_interval_second_bound"),
                H("Uniform second formal values"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive alpha, beta below one, M at least one, singular-series values one on empty sets and singletons, and the interval correlation input, there is a nonnegative C such that eventually |Phi(SS,H,s,a,b,a,b)| is at most C H log N for every N^alpha<=H<=N^beta, log N<=s<=log N+log 2 and 0<=a<=b<=M. The estimate uses the second correlation bound and the diagonal overlap count."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The finite signed-cube realization identifies Phi with the formal coefficient moment. "
                + "Products of interval indicators are again interval indicators, including when their intersection is empty. "
                + "The number of lattice points in an overlap differs from H times its length by at most two. "
                + "Consequently the second formal moment differs from H(s-log H) times the overlap length by O(H). "
                + "The cubic identity and the full fourth pairing-defect identity then control every repeated-index term. "
                + "On the polynomial length band, (log N)^2 is eventually at most H, so H(log N)^3 is at most H^2 log N. "
                + "The fourth main term is the sum of the three products of overlap lengths, multiplied by H^2(s-log H)^2.")),
            Describe.Lean(
                DescribeId.Create("formal-interval-moment-bounds"),
                DeclarationHandle.Create(Prefix + "formal_interval_moment_bounds"),
                H("Uniform cubic and fourth formal values"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let 0<alpha<beta<1, let the singular series equal one on the empty set and every singleton, "
                    + "and assume the uniform interval correlation estimates. For every M at least one there is a nonnegative constant C "
                    + "and a nonnegative modulus eta, antitone on [2,infinity) and tending to zero, such that eventually for all "
                    + "N^alpha<=H<=N^beta and log N<=s<=log N+log 2, writing L=log N, the absolute cubic formal value is at most "
                    + "C[eta(H)(HL)^(3/2)+HL^2]. The absolute difference of the fourth formal value from "
                    + "H^2(s-log H)^2 W4 is at most C[eta(H)H^2 L^2+H^2 L]. Both estimates hold uniformly over all ordered "
                    + "interval endpoints in [0,M], allowing empty intervals and arbitrary overlaps."))),
                DescribeRole.Theorem))));
}
