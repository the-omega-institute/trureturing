using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof;

internal sealed class NoisyGhzExactRoofMatrixAveragesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/MatrixAverages.";
    private static readonly LibraryNoteRef Antecedent =
        LibraryNoteRef.Create("D5/L/Divergence/xuzhouzhaohu2023gme");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual all-cut noisy-GHZ bounds, finite matrix ensembles and the original witness conjugate.",
        H("Noisy GHZ: MatrixAverages"),
        Blocks(
            Paragraph(Text("Scientific source credit: Haobo Ma, then Wenlin Zhang; CC BY 4.0. This formalization follows the approved noisy-GHZ note in the original scientific capsule SHA256 4c31bee2cd31b1109b3940fd7121dd512ac560b04f69c2cf5fa99ed0b44a5cb5. Xu et al., arXiv:2211.05563v1, supply the witness and defining conjugate, as recorded in the existing library note. The scalar expression is credited to Wei and Goldbart, Physical Review A 68, 042307 (2003), Section IV.C, Eq. (54), doi:10.1103/PhysRevA.68.042307. The multiple-observable Legendre method is credited to Gühne, Reimpell and Werner, Physical Review Letters 98, 110502 (2007), Eqs. (1)-(6), doi:10.1103/PhysRevLett.98.110502, and Physical Review A 77, 052317 (2008), Section II, arXiv:0802.1734, doi:10.1103/PhysRevA.77.052317. Earlier qubit results of Buchholz, Moroder and Gühne (2016), Observation 3, and Cianciaruso, Bromley and Adesso (2016), Eq. (6) and Table 4, remain outside the higher-dimensional roof claim. No priority or novelty claim is made.")),
            Paragraph(Text("Objects are the existing NoisyGhzWitnessBoundGap complex matrices, normalized word amplitudes, arbitrary-cut IsBiseparable predicate, actual overlap supremum, finite normalized matrix ensembles and their infimum. DensityState supplies positive semidefinite trace-one matrices. Observable expectations are real traces. twoMeanOptimum includes the zero region; the older twoMeanValue denotes the radical branch only.")),
            Paragraph(Text("Source uncertainty retained: the released scalar-difference wording modulo three is not used. Characters are functions on the independent phase-coordinate group. The literal all-real-slope displayed antecedent formula is not a universal supplier; witness_optimum is proved against the actual hatE definition. These observations do not amend an upstream text.")),
            Paragraph(Text("The all-parameter roof uses explicit finite matrix ensembles in two closed regimes: the source basis/cut-phase/Q ensemble below p_W and an actual biseparable threshold/computational ensemble above p_W. Equality is derived from full matrix reconstruction, finite-ensemble upper bounds and the universal two-mean lower bound. The d=2 statement is only the preserved operator boundary. Graph-witness improvement, broad noise robustness, general unfaithfulness and singlet-witness conjectures are outside this result.")),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-two-mean-optimum-max"),
                DeclarationHandle.Create(Prefix + "twoMeanOptimum_max"),
                H("The complete truncated radical"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("On the closed triangle zero at most f at most y, the piecewise optimum equals the squared positive part of sqrt((d-1)f)-sqrt(y-f), divided by d."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-support-projector-decomposition"),
                DeclarationHandle.Create(Prefix + "support_projector_decomposition"),
                H("The actual disjoint support-matrix decomposition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("The original complex matrix P equals the constant-word projector C plus the sum of the off-constant projectors for all anchored bipartitions. This is a full matrix equality, not only a dimension count."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-basis-average-matrix"),
                DeclarationHandle.Create(Prefix + "basis_average_matrix"),
                H("The full finite basis-average matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("The d actual chi projectors average to F*G+(1-F)/(d-1)*(C-G), with exact arbitrary-d coefficients and endpoint domains."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-phase-average-matrix"),
                DeclarationHandle.Create(Prefix + "phase_average_matrix"),
                H("The full finite phase-average matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("For each nonempty proper cut, the 3^d actual cutState projectors average to F*G+(1-F)/(d*(d-1))*T_A. All unwanted matrix entries cancel by independent-coordinate character orthogonality, for arbitrary d."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-helper-matrixaverages-noisy-density-matrix"),
                DeclarationHandle.Create(Prefix + "noisyDensity_matrix"),
                H("noisyDensity matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-helper-matrixaverages-diagonal-projector-sum"),
                DeclarationHandle.Create(Prefix + "diagonal_projector_sum"),
                H("diagonal projector sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split."))),
                DescribeRole.Theorem))));
}
