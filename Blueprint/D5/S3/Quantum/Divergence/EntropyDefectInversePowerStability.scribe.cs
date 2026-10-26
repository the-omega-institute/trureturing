using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class EntropyDefectInversePowerStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual entropy loss controls supported inverse fractional powers with the sharp cap-energy constant.",
        H("Entropy defect and fractional modular stability"), Blocks(
            Describe.Lean(
                DescribeId.Create("entropy-defect-inverse-power-stability"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/EntropyDefectInversePowerStability.entropy_defect_inverse_power_stability"),
                H("A quantitative family on the actual supported modular model"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let Phi be an arbitrary channel between finite nonempty systems, and let "
                    + "rho and sigma be density states with support of rho contained in support of sigma. Form the existing "
                    + "canonical supported relative-modular model M=(A,B,V,xi,eta). For any 0<alpha<1 and "
                    + "m>0 with mI<=A and mI<=B, set d_alpha=A^(-alpha)xi-V B^(-alpha)eta, using real "
                    + "continuous functional calculus on the positive supported carriers. Its Euclidean L2 "
                    + "norm is at most (sin(pi alpha)/pi) K_alpha (2/m)^alpha Delta^((1-alpha)/2), where "
                    + "K_alpha=(1-alpha)^(-1)((alpha+1)/(2alpha))^((alpha+1)/2), and Delta is the actual "
                    + "finite trace-log entropy deficit of rho,sigma and their channel images.")),
                    Paragraph(Text("The generalized implementation in EntropyDefectInverseSqrtStability "
                    + "evaluates the scalar normalizer by t=x/(1-x), the Beta integral and Gamma reflection. "
                    + "Finite positive spectral sums prove actual Bochner integrability and the identity "
                    + "d_alpha=(sin(pi alpha)/pi) integral t^(-alpha) w(t) dt on the full positive axis. "
                    + "Continuous linear maps transport the identity through V and WithLp 2. The existing "
                    + "coercivity and contraction bounds give norm(w(t))<=2/m, and the full resolvent "
                    + "energy integral is bounded by Delta. CapWeightedEnergy supplies the sharp abstract "
                    + "inequality, including zero cap and zero budget. The energy budget also proves "
                    + "Delta>=0; no integrability premise is replaced by a default-zero integral.")),
                    Paragraph(Text("The constant is optimal for the abstract cap and weighted-energy "
                    + "constraints. Optimality within actual channel resolvent differences is not established. "
                    + "The square-root member has coefficient 6^(3/4)/pi before m^(-1/2) Delta^(1/4). "
                    + "This is a repository derivation using existing canonical-model suppliers and pinned "
                    + "Mathlib analysis, with no claim of literature novelty. The theorem concerns supported "
                    + "modular intertwining; a general fractional trace-recovery interpretation requires "
                    + "additional physical coordinate and Schwarz arguments."))),
                DescribeRole.Theorem))));
}
