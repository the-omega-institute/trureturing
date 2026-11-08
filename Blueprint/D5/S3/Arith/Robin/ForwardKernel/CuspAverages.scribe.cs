using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class CuspAveragesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/CuspAverages.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Averaged clipped logarithmic cusps and comparison of averaging lengths.",
        H("Cusp averages"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cusp-jump-interval-integrable"),
                DeclarationHandle.Create(Prefix + "jump_integrable"),
                H("Integrability of a cusp increment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 0<h<k and arbitrary real q and y, the forward cusp increment as a function of the averaging parameter is integrable on every compact real interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("clipped-log-monotone-positive-axis"),
                DeclarationHandle.Create(Prefix + "clip_mono"),
                H("Monotonicity on the positive axis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 0<h<k and 0<=x<=z, the clipped logarithm at x is at most its value at z."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("clipped-log-range"),
                DeclarationHandle.Create(Prefix + "clip_range"),
                H("Range of the clipped logarithm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 0<h<k and every real x, the clipped logarithm lies between log(h/k) and zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cusp-average-bounds"),
                DeclarationHandle.Create(Prefix + "cuspAverage_bounds"),
                H("Depth bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive h<k, nonnegative length q and nonnegative base y, the average is between zero and log(k/h). These bounds control the lower clipped region in the cross-energy estimate and in moving-length transport."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cusp-average-short-bound"),
                DeclarationHandle.Create(Prefix + "cuspAverage_short_bound"),
                H("The lower clipped region"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 0<=y<=h and 0<=q<=2h, the cusp average is at most log(3). This bounds the contribution of the lower clipped region to the cross energy and to moving-length transport."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cusp-average-length-comparison"),
                DeclarationHandle.Create(Prefix + "cuspAverage_length_comparison"),
                H("Comparison of lengths"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For y>=h and 0<r<=q, the averages satisfy B_r(y)<=B_q(y)<=(q/r)B_r(y). The clipped logarithm is increasing and concave above h. This comparison controls moving lengths in CuspMovingLengths."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cusp-average-continuous"),
                DeclarationHandle.Create(Prefix + "cuspAverage_continuous"),
                H("Continuity of the averages"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive h<k and fixed length q, the average is continuous in its base point. The cross-energy integrals use this continuity for compact interval integrability."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cusp-average-le-half-ratio"),
                DeclarationHandle.Create(Prefix + "cuspAverage_le_half_ratio"),
                H("A short-length upper bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For y>=h and q>=0, the average is at most q/(2y). The inequality log(1+t)<=t and integration of s over the unit interval give this bound, used at the upper endpoint of the cross-energy integral."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cusp-average-inner-approx"),
                DeclarationHandle.Create(Prefix + "cuspAverage_inner_approx"),
                H("The short average expansion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When 2h<=k and h<=y<=k-h, the absolute difference between B_h(y) and h/(2y) is at most h^2/y^2. The one-sided inequality 2t/(t+2)<=log(1+t) applies also at h/y=1. The estimate is consumed by the middle interval of the cross-energy proof."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cusp-average-le-log-ratio"),
                DeclarationHandle.Create(Prefix + "cuspAverage_le_log_ratio"),
                H("Remaining depth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For h<=y<=k and every length q, the average is at most log(k/y). This controls outer averages in the cross-energy calculation and in moving-length transport."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cusp-average-outer-eq"),
                DeclarationHandle.Create(Prefix + "cuspAverage_outer_eq"),
                H("The outer average"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For h<=y<=k, the outer average equals log(k/y)-1+(y/k)(1+log(k/y)). Splitting the affine integral at k and integrating the logarithm gives this formula. It supplies the exact outer integral in CuspCrossEnergy."))),
                DescribeRole.Theorem))));
}
