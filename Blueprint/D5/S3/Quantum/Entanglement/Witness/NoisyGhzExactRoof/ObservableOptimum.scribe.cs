using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof;

internal sealed class NoisyGhzExactRoofObservableOptimumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum.";
    private static readonly LibraryNoteRef Antecedent =
        LibraryNoteRef.Create("D5/L/Divergence/xuzhouzhaohu2023gme");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual all-cut noisy-GHZ bounds, finite matrix ensembles and the original witness conjugate.",
        H("Noisy GHZ: ObservableOptimum"),
        Blocks(
            Paragraph(Text("Scientific source credit: Haobo Ma, then Wenlin Zhang; CC BY 4.0. This formalization follows the approved noisy-GHZ note in the original scientific capsule SHA256 4c31bee2cd31b1109b3940fd7121dd512ac560b04f69c2cf5fa99ed0b44a5cb5. Xu et al., arXiv:2211.05563v1, supply the witness and defining conjugate, as recorded in the existing library note. The scalar expression is credited to Wei and Goldbart, Physical Review A 68, 042307 (2003), Section IV.C, Eq. (54), doi:10.1103/PhysRevA.68.042307. The multiple-observable Legendre method is credited to Gühne, Reimpell and Werner, Physical Review Letters 98, 110502 (2007), Eqs. (1)-(6), doi:10.1103/PhysRevLett.98.110502, and Physical Review A 77, 052317 (2008), Section II, arXiv:0802.1734, doi:10.1103/PhysRevA.77.052317. Earlier qubit results of Buchholz, Moroder and Gühne (2016), Observation 3, and Cianciaruso, Bromley and Adesso (2016), Eq. (6) and Table 4, remain outside the higher-dimensional roof claim. No priority or novelty claim is made.")),
            Paragraph(Text("Objects are the existing NoisyGhzWitnessBoundGap complex matrices, normalized word amplitudes, arbitrary-cut IsBiseparable predicate, actual overlap supremum, finite normalized matrix ensembles and their infimum. DensityState supplies positive semidefinite trace-one matrices. Observable expectations are real traces. twoMeanOptimum includes the zero region; the older twoMeanValue denotes the radical branch only.")),
            Paragraph(Text("Source uncertainty retained: the released scalar-difference wording modulo three is not used. Characters are functions on the independent phase-coordinate group. The literal all-real-slope displayed antecedent formula is not a universal supplier; witness_optimum is proved against the actual hatE definition. These observations do not amend an upstream text.")),
            Paragraph(Text("The all-parameter roof uses explicit finite matrix ensembles in two closed regimes: the source basis/cut-phase/Q ensemble below p_W and an actual biseparable threshold/computational ensemble above p_W. Equality is derived from full matrix reconstruction, finite-ensemble upper bounds and the universal two-mean lower bound. The d=2 statement is only the preserved operator boundary. Graph-witness improvement, broad noise robustness, general unfaithfulness and singlet-witness conjectures are outside this result.")),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-chi-attainment"),
                DeclarationHandle.Create(Prefix + "chi_attainment"),
                H("The source constant-sector pure optimizer"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("The actual chi vector has one optimalAlpha amplitude and d-1 optimalBeta amplitudes. Its norm is one, its P and G means are one and F, and its all-cut pure measure equals the complete optimum, including F=1/d and F=1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-observable-correspondence"),
                DeclarationHandle.Create(Prefix + "observable_correspondence"),
                H("The measured means W,Q"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("For every density state, y=1-q and f=(1-q)/d-w. Thus the two G,P means encode exactly the two W,Q measurements."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-two-mean-attainment"),
                DeclarationHandle.Create(Prefix + "two_mean_attainment"),
                H("Attained all-state two-mean minimum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("Every feasible pair has an actual density operator and the explicit three-component normalized ensemble twoMeanWeights/twoMeanStates. Their matrix sum, both means, average entanglement and exact roof are proved. The zero branch uses computational products, including qWord=|0,1,2,0,...>; the positive branch mixes chi with qWord. This optimizer is not asserted to be the noisy matrix."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-witness-optimum"),
                DeclarationHandle.Create(Prefix + "witness_optimum"),
                H("The complete original single-witness optimum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("On the full interval -(d-1)/d through 1/d, epsilonWitness equals twoMeanOptimum d (1/d-w) 1. epsilonWitness uses the original hatE two-vector supremum, and epsilonO is its exact specialization at witnessValue. The proof covers both spectral endpoints and the nonnegative-w zero interval using actual finite optimizers and finite supporting slopes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-helper-observableoptimum-constant-vector-apply"),
                DeclarationHandle.Create(Prefix + "constantVector_apply"),
                H("constantVector apply"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-helper-observableoptimum-constant-vector-off"),
                DeclarationHandle.Create(Prefix + "constantVector_off"),
                H("constantVector off"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-helper-observableoptimum-optimal-amplitudes"),
                DeclarationHandle.Create(Prefix + "optimal_amplitudes"),
                H("optimal amplitudes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-helper-observableoptimum-epsilon-o-bridge"),
                DeclarationHandle.Create(Prefix + "epsilonO_bridge"),
                H("epsilonO bridge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-helper-observableoptimum-q-word-outside"),
                DeclarationHandle.Create(Prefix + "qWord_outside"),
                H("qWord outside"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-helper-observableoptimum-two-mean-scaling"),
                DeclarationHandle.Create(Prefix + "twoMean_scaling"),
                H("twoMean scaling"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split."))),
                DescribeRole.Theorem))));
}
