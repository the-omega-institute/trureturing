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
