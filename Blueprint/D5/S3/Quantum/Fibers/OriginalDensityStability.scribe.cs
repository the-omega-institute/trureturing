using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class OriginalDensityStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strong derivative error and a separate terminal phase certificate control the full original output.",
        H("Loss density stability on the original clock"), Blocks(
            Paragraph(Text("Let c<1/2, 0<a<c and eta>0. Both (k,chi) and (l,psi) are original controls at the same base (c,c,1-2c) and horizon T>=0, with k(0)=l(0)=a. Both heights stay in [eta,c-eta]. For every t in [0,T], assume |k(t)-l(t)|<=delta. All integrals are Lebesgue integrals on (0,T], with their norm taken before integration. The original regularity alternatives imply absolute continuity and integrability of the derivatives; no common partition or derivative supremum bound is assumed.")),
            Paragraph(Text("Write e=derivativeError(T,k,l)=integral |k prime-l prime|, M=variation(T,l)=integral |l prime|, and D=variation(T,k)=integral |k prime|. Absolute continuity identifies these variations with total variation. Define budget(eta,delta,e,M)=B=e/eta+M delta/eta^2. The five original probabilities have slopes sigma=(1,-1,0,-1,1), in mode order 0,1,2,3,13. Every mode remains in the loss output, including constant-probability mode 2 and mode 13 at index four.")),
            Entry("hazard-pointwise", "hazard_pointwise_error", "Pointwise hazard error",
                Seq(C("absHazardDifference"), Leq, C("velocityErrorOverMargin"), Plus, C("heightReciprocalError")),
                "For any two differentiable-value functions k,l and any real t at which both heights lie in [eta,c-eta], |hazard_k(t)-hazard_l(t)|<=|k prime(t)-l prime(t)|/eta+|l prime(t)| |k(t)-l(t)|/eta^2. The assertion is pointwise for totalized derivatives. The velocity dependence is continuous piecewise linear, and changing a reciprocal height costs at most the height error divided by eta squared."),
            Entry("hazard-integral", "hazard_integral_error", "Accumulated hazard error",
                Seq(C("integralAbsHazardDifference"), Leq, C("B")),
                "Under the common margin and height-error hypotheses, integral_0^T |hazard_k-hazard_l|<=B. The proof integrates the pointwise bound using the actual L1 derivative difference and the variation of l."),
            Entry("survival-integral", "survival_integral_error", "Every survival prefix uses the full hazard error",
                Seq(C("absSurvivalDifference", C("t")), Leq, C("integralAbsHazardDifference")),
                "For any two original controls and every t in [0,T], |S_k(t)-S_l(t)|<=integral_0^T |hazard_k-hazard_l|. No margin hypothesis is needed for this intermediate assertion. The hazard primitives are nonnegative; exp(-x) is one-Lipschitz for x>=0."),
            Entry("survival-budget", "survival_error", "Uniform survival error",
                Seq(C("absSurvivalDifference", C("t")), Leq, C("B")),
                "The accumulated hazard estimate therefore gives |S_k(t)-S_l(t)|<=B for every t in [0,T] under the common margin and height-error assumptions."),
            Entry("loss-density", "loss_density_error", "The exact loss-density estimate IS.28",
                Seq(C("integralAbsLossDensityDifference", C("i")), Leq,
                    Open, D(1), Plus, C("M"), Slash, C("eta"), Plus, C("D"), Close,
                    C("B"), Plus, C("delta"), Plus, C("e")),
                "For every original mode i, integral_0^T |lossDensity_i(k)-lossDensity_i(l)|<=(1+M/eta+D)B+delta+e. lossDensity_i is the original unnormalized source-family density, modeCoefficient_i p_i(a); OriginalReferenceOutputMeasure.source_coefficient identifies it with the source failureDensity, and native_coefficient_deriv identifies it almost everywhere with minus the derivative of S p_i(k). No common initial-height equality is needed for this scalar estimate itself."),
            Paragraph(Text("Product differentiation gives the four differences -(S_k prime-S_l prime)p_i(k), -S_l prime(p_i(k)-p_i(l)), -(S_k-S_l)sigma_i k prime, and -S_l sigma_i(k prime-l prime). Their integrated absolute values are bounded by (1+M/eta)B, delta, DB and e. Here integral |S_k prime-S_l prime|<=(1+M/eta)B follows from S prime=-hazard S and integral hazard_l<=M/eta. Monotone survival gives integral |S_l prime|=1-S_l(T)<=1. Each p_i is at most one, each probability coordinate is one-Lipschitz, and |sigma_i|<=1. This proves the displayed constants for all five modes.")),
            Entry("variation-bound", "variation_le", "No additional speed hypothesis is required",
                Seq(C("D"), Leq, C("M"), Plus, C("e")),
                "For every two original controls on the same horizon, D<=M+e follows by integrating |k prime|<=|l prime|+|k prime-l prime|. The variations are the integrals of the derivatives of the actual absolutely continuous heights."),
            Entry("combined-bound", "complete_error_bound", "The full complete-output estimate",
                Seq(C("dOp"), Leq, C("rootBudget"), Plus, C("phaseError"), Plus, C("densityBudget")),
                "Put d_min=initialFloor(c,a)=min(a,c-a,1-2c)>0 and C=(1+M/eta+D)B+delta+e. For the actual complete operational distance of OriginalCompleteOutputStability, d_op<=sqrt((B+delta)/d_min)+phaseError+C/(2 d_min). phaseError=max_i |character_i(k,chi,T)-character_i(l,psi,T)| is a separate terminal character certificate. The result combines the complete joint-output estimate IS.27, the loss-density estimate IS.28 and the terminal Kraus estimate IS.29, on the same common data."),
            Entry("height-from-derivatives", "height_error_le_derivativeError", "A common initial height gives uniform height control",
                Seq(C("absHeightDifference", C("t")), Leq, C("e")),
                "For any two original controls with k(0)=l(0), and every t in [0,T], |k(t)-l(t)|<=derivativeError(T,k,l). The fundamental theorem for absolutely continuous functions writes the difference as the integral of k prime-l prime on (0,t], which is bounded by the full L1 difference."),
            Entry("complete-convergence", "complete_output_convergence", "Convergence of the complete operational output",
                Seq(C("dOp", C("n")), To, D(0)),
                "Fix c,a,T,eta and a real bound M. Let (k_n,chi_n) and (l_n,psi_n) be two sequences of original controls on the common base and horizon, with both initial heights a and both heights in [eta,c-eta] for every n. Assume variation(T,l_n)<=M for every n, derivativeError(T,k_n,l_n) tends to zero, and phaseError(c,T,k_n,chi_n,l_n,psi_n) separately tends to zero. Then their completeOperationalDistance tends to zero, uniformly over all normalized positive joint trace-class inputs and unchanged Hilbert references in any fixed universe."),
            Paragraph(Text("For convergence take delta_n=e_n, use D_n<=M+e_n and B_n=e_n/eta+M e_n/eta^2. The common initial probability floor is strictly positive. Continuity of the square root and the rational polynomial upper bound makes every term in the combined estimate tend to zero. Nonnegativity of the actual operational distance completes the squeeze argument. This proves a sufficient condition; it asserts neither necessity of derivative convergence nor acquisition of the phase certificate.")),
            Paragraph(Text("The actual output is the successful tensor Kraus congruence together with five Bochner failure-density measures on the same reference and physical time records. The result does not infer terminal phase control from height control, recover an intermediate phase waveform, grant access to old programme fields, construct an acquisition service, authorize a post-failure restart or establish physical realization.")))));

    private static DocumentBlock Entry(string id, string declaration, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalDensityStability." + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    private static Formula C(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
