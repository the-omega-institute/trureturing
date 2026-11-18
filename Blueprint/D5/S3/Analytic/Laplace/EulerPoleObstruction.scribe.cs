using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace;

internal sealed class EulerPoleObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full complex Euler double-pole coefficient bounds every eventual signed tail envelope.",
        H("Signed Euler pole obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("lone-source-finite-head-entire"),
                DeclarationHandle.Create("D5/S3/Analytic/Laplace/EulerPoleObstruction.finiteHead_entire"),
                H("Entire finite heads"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let g be a real function integrable on the finite interval (U,V]. The function P(z)=integral over (U,V] of exp(-zu)g(u) is differentiable at every complex z, hence entire. No pointwise bound on g or global measurability assumption is required. The hypotheses are for the restricted Lebesgue measure.")),
                    Paragraph(Text("On a compact complex neighborhood times the compact real interval, the derivative multiplier -u exp(-zu) has a uniform bound K. The integrable dominating function is K norm(g(u)). Differentiation under the integral therefore applies to arbitrary integrable sources, including unbounded ones. This is the usual dominated parameter integral argument; no originality is claimed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lone-source-tail-analytic"),
                DeclarationHandle.Create("D5/S3/Analytic/Laplace/EulerPoleObstruction.tail_analytic"),
                H("Positive half-plane analyticity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("If g is integrable on (U,infinity) and U>=0, its actual Laplace integral is AnalyticOnNhd on Re z>0. At a given z, derivatives are dominated by exp(-1)/(Re z/2) times norm(g(u)), since u exp(-bu)<=exp(-1)/b for b>0. No convergence on a negative half-plane is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lone-source-tail-cutoff"),
                DeclarationHandle.Create("D5/S3/Analytic/Laplace/EulerPoleObstruction.tail_cutoff"),
                H("Exact cutoff correction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For U>=0, V>=U, g integrable on (U,infinity), and Re z>0, the actual tail at V equals the actual tail at U minus finiteHead g U V z. The disjoint partition is (U,V] union (V,infinity)=(U,infinity). Both integrals converge absolutely on this positive half-plane."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("euler-pole-pointwise-coefficient"),
                DeclarationHandle.Create("D5/S3/Analytic/Laplace/EulerPoleObstruction.coefficient_le_of_pointwise_envelope"),
                H("The positive-gap moment estimate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let g be real and integrable on (U,infinity), U>0, and d<sigma<0. Let Phi be meromorphic on Re z>d and analytic at every real x with sigma<=x<=0. Write L(z) for the actual integral of exp(-zu)g(u) over u>U and E(L)(z)=z L''(z)+2 L'(z). Assume E(L)=Phi only on Re z>0. At a nonreal point a with Re a=sigma assume the full complex punctured limit (z-a)^2 Phi(z) tends to a nonzero Lambda. For real s with s^2=1 and c>=0, the bound s g(u)<=c exp(sigma u)/u for every u>U implies norm(Lambda)<=norm(a)c.")),
                    Paragraph(Text("The nonnegative gap c exp(sigma u)/u-s g(u) is an actual integrable density, giving a finite positive measure. Its comparison transform has explicit first and second derivatives. PositiveEulerContinuation.integrable_and_analytic_of_euler_corridor forces exponential integrability throughout Re z>sigma. The proof includes the finite-measure dominated convergence limit when its genuine convergence cut is zero and uses the full complex zero extension there.")),
                    Paragraph(Text("At the real point sigma the signed solution extends across a disk by EulerLocalContinuation. The normalized first positive moment tends to zero and the normalized second moment tends to c. At a, the comparison Euler expression is analytic. Combining the original full complex pole limit with the Euler identity gives the signed coefficient on a rightward ray. Norm bounds for the actual positive moment integrals yield the entire coefficient estimate; neither moments nor negative-half-plane convergence are assumptions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("euler-pole-eventual-coefficient"),
                DeclarationHandle.Create("D5/S3/Analytic/Laplace/EulerPoleObstruction.coefficient_le_of_envelope"),
                H("An eventual envelope at the original cutoff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Keep exactly the same g,U,d,sigma,Phi,a,Lambda,s,c and the same hypotheses, but assume only eventually at real infinity that s g(u)<=c exp(sigma u)/u. The same conclusion norm(Lambda)<=norm(a)c follows. Choose V>U beyond the eventual bound. The removed finite head P is entire by finiteHead_entire, with domination proportional to norm(g), even when g is unbounded.")),
                    Paragraph(Text("The later actual tail is L-P on Re z>0. Its forcing is Phi-E(P), meromorphic on the same half-plane and regular on the same real corridor. Subtracting the entire Euler expression preserves the full complex punctured coefficient Lambda, including its nonzero value. Apply the pointwise positive-gap estimate at V. This establishes the eventual statement for the original U and original Phi."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("euler-pole-signed-peaks"),
                DeclarationHandle.Create("D5/S3/Analytic/Laplace/EulerPoleObstruction.signed_peaks"),
                H("Arbitrarily late peaks of both signs"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Under the same actual integrability, positive cutoff, forcing equation, corridor regularity and full nonzero pole hypotheses, for every real s with s^2=1, every 0<=c<norm(Lambda)/norm(a), and every real T, some u>max(T,U) satisfies c<u exp(-sigma u)(s g(u)). If all such values were at most c, division by the positive normalization would give the forbidden eventual envelope.")),
                    Paragraph(Text("Only forcing data at the original cutoff are needed: the finite-head correction supplies later cutoffs. In particular, an EulerTail family with actual g integrable at U0>0 and forcing, equation, real regularity and the same a,Lambda at every U>=U0 satisfies the complete all-cutoff conclusion by its data at U0. No additional family or signed-theta theorem is required.")),
                    Paragraph(Text("The argument is a reusable form of the classical positive Laplace and local pole comparison method. It asserts no zeta zero, RH truth value, arithmetic error rate, effective peak location, or endpoint coefficient equality, and makes no literature originality claim."))),
                DescribeRole.Theorem))));
}
