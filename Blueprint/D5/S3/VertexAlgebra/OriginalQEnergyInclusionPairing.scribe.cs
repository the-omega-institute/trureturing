using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class OriginalQEnergyInclusionPairingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/OriginalQEnergyInclusionPairing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original finite inclusion preserves the literal rotated right-C0 pairing on its native projector range.",
        H("Native Finite Inclusion Pairing"),
        Blocks(
            Paragraph(Text("The states are the full finite-support lattice oscillator carrier tensor the full exterior bc Fock space over the complex numbers. Each slot belongs to the actual range of energyProjector in originalEnergySector, with its own charge and arbitrary integer level. The two slots use the same Gram inverse and frame. Both Gram inverse equations and both frame inverse equations remain explicit. The common longitudinal null direction is the exact x row. Each charge has nonzero chosenP and its actual adapted partner is the exact y row. The axes are distinct; the two longitudinal rows are star-fixed and satisfy both exact dual-row identities. No critical rank, mass shell, positive signature or positive-definite hypothesis is needed.")),
            Describe.Lean(
                DescribeId.Create("original-energy-inclusion-c0-pairing"),
                DeclarationHandle.Create(Prefix + "energyReducedInclusion_c0_pairing"),
                H("Actual inclusion preserves the inserted form"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The map is the original energyReducedInclusion, not a replacement tail map. Its original energyCorrectionInverse is the sum of signed powers of energyNormalizer times energyOriginalQ minus energyLeading, with cutoff 2*level.toNat+2. Native projector idempotence fixes every range input. The existing original_projected_correction_pow_mem_filtration places the k-th signed power in lower k. The zero-th power gives the lower-zero base; summing the actual range with zero erased gives the lower-one tail. Splitting this same finite inverse proves inclusion=input+tail in each actual energy sector. The actual F_c0_two_slot_cancellation then kills all three correction terms, including tail-tail. This is a native application of the finite perturbation support and actual rotated two-slot selection laws, not independent mathematical novelty."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-energy-transverse-down-input"),
                DeclarationHandle.Create(Prefix + "energyTransverseDownInput"),
                H("Genuine native transverse down inputs"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite matter monomial with zero occupation on both longitudinal axes and an empty polarized ghost word defines an actual energy-projector range input at its own nativeLevel. nativeWord_sector and nativeWord_T0 prove the original charge and total-zero equations; P_native and kappa_zero_iff prove the actual projector fixes it. energyTransverseDownCombination extends these actual inputs to arbitrary finite complex coefficient families on TransverseDownIndex. The full-State value of the resulting native range input is proved to be exactly its coordinate-substituted matter polynomial tensor down, without an assumed compatibility interface or occupation cutoff."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("original-energy-inclusion-transverse-down-normalization"),
                DeclarationHandle.Create(Prefix + "energyReducedInclusion_transverse_down_normalization"),
                H("Negative native transverse down normalization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary finite coefficient families in both transverse down sectors, the inclusion readout equals the negative charge-diagonal actual oscillator Fock form of their transverseDownOscillator polynomials. Different charges give zero; matching charges retain the negative actual Fock form. The sign is inherited from the original down=j, c(0)down=k and Hplus(j,k)=-1; Hplus and the actual ghost rotation are unchanged. The pairing identity applies to arbitrary full finite native states in the range, not merely to an occupation table. Neither pairing preservation nor this negative normalization establishes positivity, a radical, a no-ghost theorem, full quotient C0 descent or an unrestricted relative-to-absolute injection."))),
                DescribeRole.Theorem))));
}
