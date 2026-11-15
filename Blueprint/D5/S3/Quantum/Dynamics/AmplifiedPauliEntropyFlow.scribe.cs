using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class AmplifiedPauliEntropyFlowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual amplified Pauli channels connect noncommuting trace entropy to dissipative dynamics.",
        H("Pauli flow with arbitrary finite quantum memory"), Blocks(
            Paragraph(Text("All matrix traces are ordinary unnormalized traces, and derivatives use the L2 operator norm. The faithful-memory derivative is a local milestone. The all-state arbitrary-memory two-axis inequality, its angular comparison, singular endpoint passage, amplified Pythagoras identity and sharpness remain separate mathematical obligations. No external open-problem resolution or literature novelty is asserted.")),
            Describe.Lean(
                DescribeId.Create("amplified-pauli-spinlift"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.spinLift"),
                H("Spin matrices with quantum memory"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a real three-vector v, spinLift(v) is spin(v) tensor I_R on Fin 2 times an arbitrary finite memory R. A unit vector is specified by v dot v = 1. The existing Pauli Hermiticity and square identities make this lift a Hermitian unitary."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("amplified-pauli-pinching"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.pinching"),
                H("The actual Pauli pinching"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real linear map E_v sends X to (X+U_v X U_v-adjoint)/2 on every complex matrix. For a unit vector v this is the two-Kraus pinching channel. Its definition retains the actual matrix action."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("amplified-pauli-equilibrium"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.equilibrium"),
                H("The memory reference expectation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("E0(X) is (I_2/2) tensor partialTraceLeft(X). The partial trace is taken on the input matrix itself. It is not supplied as a separate marginal or as an assumed invariant."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("amplified-pauli-pinching-comp-eq-equilibrium"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.pinching_comp_eq_equilibrium"),
                H("Orthogonal pinchings compose to complete qubit erasure"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let a and b be real three-vectors with a dot a = b dot b = 1 and a dot b = 0. For every complex matrix X on Fin 2 times R, E_a(E_b(X)) = E_b(E_a(X)) = E0(X). The proof first uses the original spin triple-product identity on arbitrary qubit blocks, and then applies it to all memory matrix entries. No state, trace, or Hermiticity condition is needed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("amplified-pauli-partialtraceleft-pinching"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.partialTraceLeft_pinching"),
                H("The actual memory marginal is preserved"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every unit real three-vector v and every complex matrix X on the joint system, partialTraceLeft(E_v(X)) = partialTraceLeft(X). This follows by taking the qubit trace of the actual conjugation in each memory block."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("amplified-pauli-equilibrium-posdef"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.equilibrium_posDef"),
                H("A faithful memory gives a faithful reference"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If partialTraceLeft(X) is positive definite, then E0(X) is positive definite. The statement requires faithfulness only of the actual marginal, not of the joint input X."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("amplified-pauli-flow"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.flow"),
                H("A matrix curve on the whole real line"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For s=exp(-t), T_t(X)=s^2 X+s(1-s)(E_a(X)+E_b(X))+(1-s)^2 E0(X). This formula defines a matrix for every real t. State and channel conclusions are restricted to t>=0; the all-real formula supplies the domain for ordinary two-sided differentiation at positive times."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("amplified-pauli-generator"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.generator"),
                H("The sign of the dissipative generator"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("L(X)=2X-E_a(X)-E_b(X). The evolution equation uses minus this generator: T-prime=-L(T). Entropy production is paired with L, so the entropy derivative is minus that pairing."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("amplified-pauli-partialtraceleft-flow"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.partialTraceLeft_flow"),
                H("Marginal preservation along the matrix curve"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For unit a and b, partialTraceLeft(T_t(X)) = partialTraceLeft(X) for every complex X and every real t. Orthogonality is not required for this preservation law. Taking the full trace also proves trace preservation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("amplified-pauli-flow-lower-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.flow_lower_bound"),
                H("A concrete lower bound at nonnegative times"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive semidefinite X and t>=0, T_t(X)>=(1-exp(-t))^2 E0(X) in Loewner order. The remaining terms are positive semidefinite with nonnegative coefficients. This bound does not assume a spectral gap or a dissipation identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("amplified-pauli-flow-posdef"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.flow_posDef"),
                H("Faithfulness at positive times"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If X is positive semidefinite and its actual memory marginal is positive definite, then T_t(X) is positive definite for every t>0. The input joint matrix is allowed to be singular. The lower bound by a positive multiple of E0(X) gives the conclusion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("amplified-pauli-hasderivat-flow"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.hasDerivAt_flow"),
                H("The negative-generator equation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For orthonormal real axes a and b, every complex input X, and every real t, the raw matrix curve has real derivative -L(T_t(X)) in the L2 operator norm. The proof differentiates its explicit exponential coefficients and uses the actual pinching composition and fixed-reference identities."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("amplified-pauli-generator-log-equilibrium-pairing"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.generator_log_equilibrium_pairing"),
                H("The fixed logarithmic reference cancels"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For unit axes a,b and arbitrary complex X,Y, Tr(L(Y) log E0(X))=0. The local spin lifts commute with the actual tensor reference, and CFC preserves this commutation for its logarithm. Cyclicity of trace and the unitary square identities then remove each pinching from the pairing. Orthogonality, positivity and commutation of X with Y are not hypotheses."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("amplified-pauli-relativeentropycurve"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.relativeEntropyCurve"),
                H("The raw relative entropy observable"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real observable F(t)=Re Tr(T_t(X)(log T_t(X)-log E0(X))) is defined on the whole real line using the total CFC logarithm. At positive times under faithful memory it agrees with supported canonical relative entropy."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("amplified-pauli-flow-quantumchannel"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.flow_quantumChannel"),
                H("The four-unitary channel realization"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For orthonormal a,b and t>=0, a canonical all-amplification QuantumChannel has matrix action T_t on every complex input. With p=(1+s)/2 and q=(1-s)/2, its unitary weights are p^2,pq,pq,q^2 on I,U_a,U_b,U_a U_b. Their square roots give an actual complete Kraus family; the existing finite-Kraus constructor supplies complete positivity and trace preservation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("amplified-pauli-flowstate"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.flowState"),
                H("Canonical states from the channel"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a joint DensityState rho and t>=0, flowState is the image under the actual four-unitary QuantumChannel. Its matrix is T_t applied to the matrix of rho. The channel realization therefore enters the entropy statement through the state itself."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("amplified-pauli-equilibriumstate"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.equilibriumState"),
                H("The canonical reference state"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The reference DensityState has matrix (I_2/2) tensor the actual memory marginal of rho. Positivity and unit trace follow from the partial-trace suppliers and the explicit reference map."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("amplified-pauli-supported-relativeentropy-flow-derivative"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow.supported_relativeEntropy_flow_derivative"),
                H("Entropy dissipation for arbitrary finite quantum memory"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let R be any nonempty finite memory type, a,b real orthonormal axes, and rho any joint DensityState whose actual memory marginal is positive definite. For each t>0 the raw observable has a genuine two-sided real derivative -Re Tr(L(T_t)(log T_t-log tau)), equal to -Re Tr(L(T_t) log T_t), where tau=E0(rho). The flow preserves the actual memory marginal and has trace one. At that time flowState is supported in equilibriumState, its finiteTraceLogRelativeEntropy equals F(t), and its extendedQuantumRelativeEntropy is the finite value F(t) in WithTop Real. The proof applies the noncommuting trace-entropy chain rule with V=-L(T_t), uses zero generator trace to remove the identity correction, and proves the fixed-reference pairing cancellation from the actual maps. The hypotheses allow singular rho; they do not yet allow a singular memory marginal."))),
                DescribeRole.Theorem))));
}
