using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Fourier;

internal sealed class JointFourierSynthesisDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Fourier/JointFourierSynthesis.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted Fourier synthesis of grade n+2 is jointly real C^n in coefficients and position.",
        H("Joint Fourier Synthesis"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("joint-fourier-synthesis-joint-contdiff-fourier-synthesis"),
                DeclarationHandle.Create(Prefix + "joint_contdiff_fourier_synthesis"),
                H("Joint differentiability of weighted Fourier synthesis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let K be the full lattice Z x Z and V be EuclideanSpace C (Fin 2), the complex two-dimensional vector space with its Euclidean norm. The coefficient space H is lp (fun _ : K => V) 2, with arbitrary square-summable vector coefficients. The spatial space X is Fin 2 -> R with its usual supremum norm. Differentiation is over R on the product H x X, so it includes every real coefficient direction as well as every spatial direction.")),
                    Paragraph(Text("For each natural number n, set rho(k) = k_1^2 + k_2^2 and w(k) = ((1 + rho(k))^((n+2)/2))^(-1), using real powers. Decode a coefficient sequence by dec(a,k) = w(k) a(k), and put character(k,x) = exp(i (k_1 x_0 + k_2 x_1)). The theorem states that (a,x) maps to the unordered sum over all k in K of character(k,x) dec(a,k) as a real C^n map. The grade is exactly n+2, and n=0 is included.")),
                    Paragraph(Text("For a finite set F of frequencies, form the continuous real-linear operator T_F(x) from H to V by summing character(k,x) w(k) times coefficient evaluation at k. The derivatives of the exponential phase are bounded by (|k_1| + |k_2|)^j. Cauchy-Schwarz applied to the finite coefficient energy gives the operator estimate ||D^j T_F(x)|| <= b sqrt(card F) whenever (|k_1| + |k_2|)^j w(k) <= b on F. This bound is uniform over x and over coefficient vectors of norm at most one.")),
                    Paragraph(Text("Partition the nonzero lattice by the dyadic shells A_m = {k : 2^m <= max(|k_1|,|k_2|) < 2^(m+1)}. Their cardinalities satisfy sqrt(card A_m) <= 5 * 2^m. For every j <= n, the weighted phase bound on A_m is at most 4^n / (2^m)^2, hence ||D^j T_{A_m}(x)|| <= 5 * 4^n * (1/2)^m. The summable geometric bound proves that the shell series is C^n as a function into the space of continuous real-linear operators H -> V. The zero frequency is included separately as a smooth finite term.")),
                    Paragraph(Text("The squared weights are summable on K: they are bounded by the product of the one-dimensional summable sequences (1 + k_1^2)^(-1) and (1 + k_2^2)^(-1). Together with a in H, Cauchy-Schwarz proves absolute convergence of the original vector-valued Fourier series. Every nonzero lattice point lies in exactly one dyadic shell, so absolute regrouping identifies the operator series, including its zero term, with the original full unordered sum.")),
                    Paragraph(Text("Finally, evaluating the C^n operator-valued sum at the variable coefficient vector a is jointly C^n in (a,x). The absolute regrouping identity transfers this conclusion to the literal Fourier synthesis map."))),
                DescribeRole.Theorem))));
}
