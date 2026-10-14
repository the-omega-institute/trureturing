using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class OriginalQTransferredTermComputationTransientDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/OriginalQTransferredTermComputationTransient.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The native original-Q finite correction has degree-raising support at every power.",
        H("Native Fixed-Energy Correction Support"),
        Blocks(
            Paragraph(Text("The carrier is the existing complex finite-support lattice oscillator tensor "
                + "the full exterior bc Fock space. Both inverse-Gram equations and both inverse-frame "
                + "equations are retained. The null direction, its adapted partner, the nonzero chosenP, "
                + "distinct longitudinal axes, and the two exact dual-row equations are explicit assumptions. "
                + "No real-frame, rank26, positive-signature, occupation-cutoff or mass-shell assumption is added.")),
            Describe.Lean(
                DescribeId.Create("original-projected-correction-power-support"),
                DeclarationHandle.Create(Prefix + "original_projected_correction_pow_mem_filtration"),
                H("Every signed correction power retains its native support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a charge-beta state with actual total-zero eigenvalue "
                    + "chosenH(beta)+level-1, every natural k satisfies (-S*(Q-delta))^k(P(state)) "
                    + "in signedEnergyFiltration(level,k). The filtration is exactly the span of nativeWord "
                    + "with nativeLevel=level and nativeDegree at least k, not an alternate carrier or norm. "
                    + "Degree means matter auxiliary degree plus ghost number minus one. The proof reuses "
                    + "the existing local finite-power induction: P gives lower0, Q-delta raises by one or two, "
                    + "S preserves degree, and negation preserves the submodule. The exposed helper is actually "
                    + "consumed by original_transferred_tail_vanishes; refactoring it is not new mathematics."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-transferred-nonconstant-tail-vanishes"),
                DeclarationHandle.Create(Prefix + "original_transferred_tail_vanishes"),
                H("The surviving transferred differential is its constant term"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original finite inverse uses all signed powers k in "
                    + "range(2*level.toNat+2). After Q-delta, every nonconstant power lies in lower k+1, "
                    + "so the original projector kills it at lower2. This statement preserves the original "
                    + "fixed-energy cutoff for every integer level, including negative and zero levels. "
                    + "It computes the transferred differential; it does not say the inclusion tail is zero. "
                    + "The classical provenance is the finite geometric-series homological perturbation "
                    + "argument on a statewise fixed-energy sector, not a global inverse."))),
                DescribeRole.Theorem),
            Paragraph(Text("Exact applications to energyReducedInclusion use its actual domain "
                + "LinearMap.range(energyProjector) and its originalEnergySector codomain. Their nonconstant "
                + "readout is the sum over range(2*level.toNat+2).erase(0) of (-ES*(EQ-ED))^k(u0). "
                + "These bind-only applications are transient compilation evidence, not new named endpoints. "
                + "No tensor pairing, C0 selection, isometry, physical norm, positivity or no-ghost theorem "
                + "follows from support alone; both pairing slots require their own released form correspondence.")))));
}
