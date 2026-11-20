using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSUniformHardCoreMarginalWitnessDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreMarginalWitness";
    private static LibraryNoteRef Lesanovsky =>
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/lesanovsky2012constrainedspinchain");
    private static LibraryNoteRef CritchMorton =>
        LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One adjacent marginal determines the cyclic independent-set witness",
        H("Recovery of the equal-weight independent-set state"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodic-hard-core-observed-support"),
                DeclarationHandle.Create(Module + ".support_of_pairGram_corner_zero"),
                H("The observed 11 entry forces hard-core support"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a cyclic amplitude at length n ≥ 7, the 11,11 entry of the first adjacent Gram matrix is the sum of squared moduli over words starting with 11. A zero sum forces each such amplitude to vanish. Rotating any adjacent occupied pair into the observed position then forces its word amplitude to vanish, including when the pair straddles the seam."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodic-hard-core-observed-energy"),
                DeclarationHandle.Create(Module + ".shiftedEnergy_eq_observed"),
                H("The adjacent Gram matrix determines the shifted energy"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Lesanovsky),
                Blocks(Paragraph(Text("For n ≥ 7, assume cyclicity and independent-set support. On supported words, the projected flip, half-weight hop and number terms have the compressed move weights. Cyclicity makes every edge expectation equal to the first one. The shifted energy is n times the squared amplitude mass plus n times that first-edge expectation. The Gram trace gives the mass, while its entries give the flip, hop and number contributions."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodic-hard-core-cyclic-marginal-recovery"),
                DeclarationHandle.Create(Module + ".eq_constant_same_norm_of_pairGram_eq_indicator"),
                H("The fixed witness is determined among cyclic amplitudes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Lesanovsky, CritchMorton),
                Blocks(
                    Paragraph(Text("At each length n ≥ 7, let the target amplitude be a on the independent sets of the cycle and zero on the other words. Any cyclic complex amplitude with the same raw adjacent two-site Gram matrix is constant on the independent sets and zero elsewhere. Its constant c satisfies |c|² = |a|², giving recovery up to unit phase for every nonzero a and forcing the zero competitor when a = 0.")),
                    Paragraph(Text("The observed 11,11 entry first gives support. The target has zero shifted Dirichlet energy. The shared Gram matrix transfers that energy value to the competitor, so deletion connectivity forces its supported amplitudes to equal its empty-word amplitude. The common Gram trace then fixes the modulus.")),
                    Paragraph(Text("Lesanovsky, arXiv:1110.1815v1, equations (1)–(2) and pages 2–3, gives the unique ground state of the periodic constrained parent and its equal weights at z = 1. The adjacent-marginal determination uses the hop term and the observation identity above. Critch and Morton give the broader generic periodic reconstruction question, which remains open across all lengths."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodic-hard-core-raw-two-witness-recovery"),
                DeclarationHandle.Create(Module + ".traceWord_eq_unit_of_rawTwo_eq_witness"),
                H("Recovery in the periodic bond-two trace image"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(CritchMorton),
                Blocks(Paragraph(Text("A periodic binary bond-two trace tensor is cyclic by the trace identity. The two explicit rank-one cores realize the independent-set indicator, and the periodic raw two-site matrix is its adjacent Gram matrix. At every n ≥ 7, any periodic core with that same raw matrix therefore has full amplitudes equal to the witness amplitudes times a single scalar of squared modulus one."))),
                DescribeRole.Theorem))));
}
