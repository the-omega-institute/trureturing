// Exposition of the original response-adjoint energy lower bound.
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class OriginalResidualResponseAdjointEnergyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/OriginalResidualResponseAdjointEnergy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The unchanged original response adjoint has a quantitative positive weighted-square energy, using the original pointwise affine defect and original weights.",
        H("Lower Energy of the Original Response Adjoint"),
        Blocks(
            Paragraph(Text(
                "All logarithms are natural. For natural N>=3 put S(N)={m in N:N<=m<2N} "
                + "and delta=1-log(2)/log(N)>0. This lowercase logarithmic gap is distinct "
                + "from the original Gram determinant Delta(N). Use the exact original "
                + "Mobius floor response R, w(m)=1/[m(m+1)], full original weighted Gram G, "
                + "q=G^(-1)*sum_(m in S(N)) w(m)*R(N,m)*v(N,m), and "
                + "E(N,m)=R(N,m)-q0-q1*m/N from OriginalResidualResponseAdjoint. "
                + "The coordinates are the same (1,m/N); no norm or energy carrier is redefined.")),
            Describe.Lean(
                DescribeId.Create("original-response-adjoint-energy-lower-bound"),
                DeclarationHandle.Create(Prefix + "responseAdjoint_energy_lower_bound"),
                H("Explicit lower bound delta squared over a collision-aware quadratic"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural N>=3, "
                        + "(1-log(2)/log(N))^2/(24*N^2-36*N+14) "
                        + "<= sum_(m in S(N)) w(m)*E(N,m)^2. "
                        + "The only mathematical hypothesis is N>=3. The bound assumes "
                        + "neither a separate affine defect, distinct witness indices, a spectral "
                        + "gap, an interval sign, nor a change of response or cutoff.")),
                    Paragraph(Text(
                        "The original prime/composite four-point gap annihilates every affine vector, "
                        + "including the actual Gram coordinates. Aggregate repeated slots before "
                        + "squaring: adjacent rows have coefficients -1,2,-1 or 1,-2,1. Their "
                        + "inverse-weight cost is at most K=24*N^2-36*N+14. The nonadjacent case "
                        + "has smaller cost. Finite weighted Cauchy gives delta^2<=K*sum w*E^2. "
                        + "All original block rows and collision cases are included. The positive "
                        + "lower bound does not determine the sign at a prescribed interval."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The coefficient-energy upper result concerns a different "
                + "quantity: for N>=3 and real N<=a<=b, it bounds "
                + "sum_(m in S(N)) A(N,a,b,m)^2/w(m) by (1+1/log(N))^2/(8*N). "
                + "That result retains its full scope, original proof and exposition. "
                + "The present lower result concerns w*E^2 for the "
                + "response adjoint and does not convert that upper bound into a signed pairing.")),
            Paragraph(Text(
                "The lower-energy proof uses response_four_point_gap, the positive logarithmic "
                + "gap and the original Gram response-residual definitions. These finite energies provide no prescribed "
                + "endpoint lower bound, actual interval sign, cofinal selection, infinite "
                + "compensation, strict Robin inequality above 5040, or RH. "
                + "Classical suppliers and the existing ended proofs are reused with no "
                + "novelty claim.")))));
}
