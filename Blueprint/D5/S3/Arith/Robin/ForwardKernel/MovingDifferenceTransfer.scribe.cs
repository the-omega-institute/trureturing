using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class MovingDifferenceTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/MovingDifferenceTransfer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An expanding moving substitution transfers a difference onto a smooth test function and two endpoint strips.",
        H("Transfer of moving differences"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("endpoint-strips"),
                DeclarationHandle.Create(Prefix + "endpointStrips"),
                H("Endpoint strips"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a moving shift with exponent theta and profile parameter s, endpointStrips(theta,s,l,r) is the union of the intervals from l to its shifted endpoint and from r to its shifted endpoint."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("square-comp-le"),
                DeclarationHandle.Create(Prefix + "square_comp_le"),
                H("Square integrals under an expanding map"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If a differentiable map on [l,r] has derivative at least one and maps into [L,R], the square integral of a measurable square-integrable function composed with that map is at most its square integral on [L,R]. The composed square is integrable. The change of variables formula and the positive derivative lower bound give the result."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("moving-shift-nonneg-gap"),
                DeclarationHandle.Create(Prefix + "moving_shift_nonneg_gap"),
                H("Nonnegative displacement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a positive exponent theta, a nonnegative x, and s in [0,1], the moving point x+s*x^theta lies to the right of x."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("moving-shift-gap-le"),
                DeclarationHandle.Create(Prefix + "moving_shift_gap_le"),
                H("Uniform displacement on a dyadic interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If 0<theta<1, X>=1, x is in [X,2X], and s is in [0,1], the displacement s*x^theta is at most 2*X^theta."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("endpoint-strips-subset"),
                DeclarationHandle.Create(Prefix + "endpointStrips_subset"),
                H("The endpoint strips lie in the working interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 0<theta<1, X>=1, s in [0,1], and X<=l<=r<=2X, both endpoint strips lie in [X/2,4X]. The displacement bound and X^theta<=X give the upper endpoint bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sliding-primitive-l2-le"),
                DeclarationHandle.Create(Prefix + "sliding_primitive_l2_le"),
                H("Square norm of a sliding primitive"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let u be measurable and square integrable on [L,R]. Suppose [l,r] lies inside [L,R], phi is continuous, and 0<=phi(x)-x<=H on [l,r], with phi(x)<=R. The square norm of the integral of u from x to phi(x), viewed as a function of x in [l,r], is at most H times the square norm of u on [L,R]. Cauchy–Schwarz bounds each moving interval integral; after interchanging the integrals, each point belongs to a set of starting points of length at most H."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("moving-difference-transfer-bound"),
                DeclarationHandle.Create(Prefix + "moving_difference_transfer_bound"),
                H("Transfer onto a smooth test function"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix 0<a<1. There is C>0 such that, for all sufficiently large X, uniformly for s in [0,1] and [l,r] contained in [X,2X], the absolute integral of (u(x+s*x^a)-u(x))*v(x) is at most C times the sum of X^a*||u||2*||v'||2, (X^a/X)*||u||2*||v||2, and V times the integral of |u| over the union of [l,l+s*l^a] and [r,r+s*r^a]. Here u is measurable and square integrable on [X/2,4X], v is continuously differentiable there, |v|<=V, and all square norms are on that enlarged interval. The proof uses the sliding primitive of u, forward change of variables, and integration by parts for absolutely continuous primitives."))),
                DescribeRole.Theorem))));
}
