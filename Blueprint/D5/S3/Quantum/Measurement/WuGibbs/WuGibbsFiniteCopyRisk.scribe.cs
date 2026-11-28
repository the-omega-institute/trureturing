using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.WuGibbs;

internal sealed class WuGibbsFiniteCopyRiskDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Measurement/WuGibbs/WuGibbsFiniteCopyRisk.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The physical one-mode Wu deficit bounds the probability gap of every collective binary effect at every finite copy count.",
        H("Finite-copy testing against Wu’s Gibbs state"),
        Blocks(
            Entry("trace-distance-from-affinity", "traceNorm_sub_half_le_sqrt_one_sub_affinity_sq",
                "Trace distance from ordinary square-root affinity", AssessedProvenance.FromRepo(),
                "For complex positive semidefinite matrices ρ and σ of ordinary trace one on the same finite index set, " +
                "put A = Re Tr(√ρ √σ), using the positive matrix square roots. Then ‖ρ − σ‖₁/2 ≤ √(1 − A²), " +
                "where ‖·‖₁ is the trace norm. The bound includes singular states. The sum and difference of the " +
                "two roots give a symmetrized product for ρ − σ, and the Hilbert–Schmidt product bound controls its trace norm."),
            Entry("collective-effect-gap", "collective_effect_gap_le",
                "Collective binary probability gap from the one-mode deficit", AssessedProvenance.FromRepo(Wu),
                "Let h = β/2 ≥ 0 and let σₕ = gibbs(h) be the one-mode Gibbs density in the normalization of " +
                "Wu, arXiv:2610.33686v1, §3.1. For every complex positive semidefinite trace-one qubit ρ, " +
                "put A = Re Tr(√ρ √σₕ), δ = energy(h,ρ) − sharpCoefficient(h) × entropy(h,ρ), " +
                "c = exactAffinityCoefficient(h), and L = max(0, 1 − √(δ/c)). The physical affinity bound gives L ≤ A. " +
                "For every natural n, put D = ρ⊗ⁿ − σₕ⊗ⁿ using the actual tensor powers. The theorem " +
                "`D5.S3.Quantum.Measurement.WuGibbsFiniteCopyRisk.collective_effect_gap_le` gives, " +
                "for every effect E on these copies with E and I − E positive semidefinite, " +
                "|Re Tr(ED)| ≤ ‖D‖₁/2 ≤ √(1 − (Aⁿ)²) ≤ √(1 − (Lⁿ)²). " +
                "The square-root affinity of the two tensor powers is Aⁿ. Either outcome of the binary measurement " +
                "{E, I − E} has this absolute probability gap. With equal priors, half the bound controls the " +
                "success advantage over random guessing. At n = 0 the tensor powers coincide and the bounds are zero."))));

    private static DocumentBlock Entry(string id, string declaration, string title,
        AssessedProvenance provenance, string claim) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration),
            H(title), StatementSource.WithoutFormula(), provenance,
            Blocks(Paragraph(Text(claim))), DescribeRole.Theorem);
}
