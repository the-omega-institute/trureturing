using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof;

internal sealed class NoisyGhzExactRoofNoisyEnsemblesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles.";
    private static readonly LibraryNoteRef Antecedent =
        LibraryNoteRef.Create("D5/L/Divergence/xuzhouzhaohu2023gme");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual all-cut noisy-GHZ bounds, finite matrix ensembles and the original witness conjugate.",
        H("Noisy GHZ: NoisyEnsembles"),
        Blocks(
            Paragraph(Text("Scientific source credit: Haobo Ma, then Wenlin Zhang; CC BY 4.0. This formalization follows the approved noisy-GHZ note in the original scientific capsule SHA256 4c31bee2cd31b1109b3940fd7121dd512ac560b04f69c2cf5fa99ed0b44a5cb5. Xu et al., arXiv:2211.05563v1, supply the witness and defining conjugate, as recorded in the existing library note. The scalar expression is credited to Wei and Goldbart, Physical Review A 68, 042307 (2003), Section IV.C, Eq. (54), doi:10.1103/PhysRevA.68.042307. The multiple-observable Legendre method is credited to Gühne, Reimpell and Werner, Physical Review Letters 98, 110502 (2007), Eqs. (1)-(6), doi:10.1103/PhysRevLett.98.110502, and Physical Review A 77, 052317 (2008), Section II, arXiv:0802.1734, doi:10.1103/PhysRevA.77.052317. Earlier qubit results of Buchholz, Moroder and Gühne (2016), Observation 3, and Cianciaruso, Bromley and Adesso (2016), Eq. (6) and Table 4, remain outside the higher-dimensional roof claim. No priority or novelty claim is made.")),
            Paragraph(Text("Objects are the existing NoisyGhzWitnessBoundGap complex matrices, normalized word amplitudes, arbitrary-cut IsBiseparable predicate, actual overlap supremum, finite normalized matrix ensembles and their infimum. DensityState supplies positive semidefinite trace-one matrices. Observable expectations are real traces. twoMeanOptimum includes the zero region; the older twoMeanValue denotes the radical branch only.")),
            Paragraph(Text("Source uncertainty retained: the released scalar-difference wording modulo three is not used. Characters are functions on the independent phase-coordinate group. The literal all-real-slope displayed antecedent formula is not a universal supplier; witness_optimum is proved against the actual hatE definition. These observations do not amend an upstream text.")),
            Paragraph(Text("The all-parameter roof uses explicit finite matrix ensembles in two closed regimes: the source basis/cut-phase/Q ensemble below p_W and an actual biseparable threshold/computational ensemble above p_W. Equality is derived from full matrix reconstruction, finite-ensemble upper bounds and the universal two-mean lower bound. The d=2 statement is only the preserved operator boundary. Graph-witness improvement, broad noise robustness, general unfaithfulness and singlet-witness conjectures are outside this result.")),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-noisy-means"),
                DeclarationHandle.Create(Prefix + "noisy_means"),
                H("Exact noisy-matrix means"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("The actual complex-matrix real traces are f=1-p+p/M and y=1-p+p*R/M."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-witness-value-affine"),
                DeclarationHandle.Create(Prefix + "witness_value_affine"),
                H("The affine noisy witness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("The original witnessValue is exactly -(d-1)/d+k*p, with the defined source slope."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-noisy-witness-optimum"),
                DeclarationHandle.Create(Prefix + "noisy_witness_optimum"),
                H("The original noisy single-witness optimum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("For every physical p the original epsilonO equals the full feasible-interval optimum at the actual witness trace. It is bridged through the defining hatE, without the disputed all-real-slope antecedent formula."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-two-mean-strict-witness-gap"),
                DeclarationHandle.Create(Prefix + "two_mean_strict_witness_gap"),
                H("Strict two-observable advantage"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("On the full means triangle, y<1 and negative witness imply strict improvement over the complete original single-witness conjugate. The proof compares radicals with their sign conditions and uses no singular endpoint metric."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-source-average-matrix"),
                DeclarationHandle.Create(Prefix + "source_average_matrix"),
                H("The complete supported source average"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("The finite combination S_F of J_F and all anchored H_A,F equals F*G+(1-F)/(R-1)*(P-G), as a full matrix identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-low-noise-reconstruction"),
                DeclarationHandle.Create(Prefix + "low_noise_reconstruction"),
                H("The complete low-noise matrix reconstruction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("For 0<=p<=p_W, lowNoiseWeights and lowNoiseStates reconstruct every entry of rho(p). Their index consists of d basis vectors, K*3^d cut-phase vectors, and the actual computational Q sector."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-low-noise-attainment"),
                DeclarationHandle.Create(Prefix + "low_noise_attainment"),
                H("An actual attaining low-noise ensemble"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("The displayed weights are nonnegative and sum to one, every constituent is unit, their projectors reconstruct the actual noisy matrix, and their mean pure measure equals the two-mean value and the actual finite convex roof. The p=0 and p=p_W endpoints are included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-threshold-constituents-biseparable"),
                DeclarationHandle.Create(Prefix + "threshold_constituents_biseparable"),
                H("Actual cut products at the threshold"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("At p_W the optimal amplitudes are alpha=1 and beta=0. Every constituent genuinely factorizes across its displayed nonempty proper cut or is a computational product; zero roof is not used to infer factorization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-high-noise-reconstruction"),
                DeclarationHandle.Create(Prefix + "high_noise_reconstruction"),
                H("Full high-noise matrix reconstruction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("For p_W<=p<=1 the explicit finite highNoiseWeights and highNoiseStates mix the threshold ensemble with the computational I/M ensemble, with lambda=(1-p)/(1-p_W)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-high-noise-attainment"),
                DeclarationHandle.Create(Prefix + "high_noise_attainment"),
                H("A finite biseparable high-noise ensemble"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("All high-noise weights are nonnegative and normalized, all actual constituents are biseparable, and the complete matrix is reconstructed. Its original convex roof is zero, including p=1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-helper-noisyensembles-noisy-parameter-data"),
                DeclarationHandle.Create(Prefix + "noisy_parameter_data"),
                H("noisy parameter data"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-helper-noisyensembles-noisy-triangle"),
                DeclarationHandle.Create(Prefix + "noisy_triangle"),
                H("noisy triangle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-helper-noisyensembles-noisy-witness-means"),
                DeclarationHandle.Create(Prefix + "noisy_witness_means"),
                H("noisy witness means"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-helper-noisyensembles-two-mean-optimum-pos"),
                DeclarationHandle.Create(Prefix + "twoMeanOptimum_pos"),
                H("twoMeanOptimum pos"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-helper-noisyensembles-q-index-card"),
                DeclarationHandle.Create(Prefix + "qIndex_card"),
                H("qIndex card"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-helper-noisyensembles-noisy-optimum-zero"),
                DeclarationHandle.Create(Prefix + "noisy_optimum_zero"),
                H("noisy optimum zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split."))),
                DescribeRole.Theorem))));
}
