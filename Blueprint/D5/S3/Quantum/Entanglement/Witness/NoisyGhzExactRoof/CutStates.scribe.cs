using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof;

internal sealed class NoisyGhzExactRoofCutStatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates.";
    private static readonly LibraryNoteRef Antecedent =
        LibraryNoteRef.Create("D5/L/Divergence/xuzhouzhaohu2023gme");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual all-cut noisy-GHZ bounds, finite matrix ensembles and the original witness conjugate.",
        H("Noisy GHZ: CutStates"),
        Blocks(
            Paragraph(Text("Scientific source credit: Haobo Ma, then Wenlin Zhang; CC BY 4.0. This formalization follows the approved noisy-GHZ note in the original scientific capsule SHA256 4c31bee2cd31b1109b3940fd7121dd512ac560b04f69c2cf5fa99ed0b44a5cb5. Xu et al., arXiv:2211.05563v1, supply the witness and defining conjugate, as recorded in the existing library note. The scalar expression is credited to Wei and Goldbart, Physical Review A 68, 042307 (2003), Section IV.C, Eq. (54), doi:10.1103/PhysRevA.68.042307. The multiple-observable Legendre method is credited to Gühne, Reimpell and Werner, Physical Review Letters 98, 110502 (2007), Eqs. (1)-(6), doi:10.1103/PhysRevLett.98.110502, and Physical Review A 77, 052317 (2008), Section II, arXiv:0802.1734, doi:10.1103/PhysRevA.77.052317. Earlier qubit results of Buchholz, Moroder and Gühne (2016), Observation 3, and Cianciaruso, Bromley and Adesso (2016), Eq. (6) and Table 4, remain outside the higher-dimensional roof claim. No priority or novelty claim is made.")),
            Paragraph(Text("Objects are the existing NoisyGhzWitnessBoundGap complex matrices, normalized word amplitudes, arbitrary-cut IsBiseparable predicate, actual overlap supremum, finite normalized matrix ensembles and their infimum. DensityState supplies positive semidefinite trace-one matrices. Observable expectations are real traces. twoMeanOptimum includes the zero region; the older twoMeanValue denotes the radical branch only.")),
            Paragraph(Text("Source uncertainty retained: the released scalar-difference wording modulo three is not used. Characters are functions on the independent phase-coordinate group. The literal all-real-slope displayed antecedent formula is not a universal supplier; witness_optimum is proved against the actual hatE definition. These observations do not amend an upstream text.")),
            Paragraph(Text("The all-parameter roof uses explicit finite matrix ensembles in two closed regimes: the source basis/cut-phase/Q ensemble below p_W and an actual biseparable threshold/computational ensemble above p_W. Equality is derived from full matrix reconstruction, finite-ensemble upper bounds and the universal two-mean lower bound. The d=2 statement is only the preserved operator boundary. Graph-witness improvement, broad noise robustness, general unfaithfulness and singlet-witness conjectures are outside this result.")),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-cut-product-biseparable"),
                DeclarationHandle.Create(Prefix + "cutProduct_biseparable"),
                H("Actual cut product vectors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("For every nonempty proper cut and every unit local vector u, cutProduct embeds u tensor conjugate(u) into the original computational word space and satisfies the original IsBiseparable factorization predicate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-cut-state-unit"),
                DeclarationHandle.Create(Prefix + "cutState_unit"),
                H("Normalization of the source cut constituents"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("Every source cutState has norm one whenever alpha squared plus (d-1) beta squared is one, for every unit local u and every nonempty proper cut."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-cut-state-attainment"),
                DeclarationHandle.Create(Prefix + "cutState_attainment"),
                H("Genuine all-cut entanglement of each constituent"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("For the source optimal amplitudes and every unit u, the actual cutState has means (F,1), norm one and genuine all-cut pure entanglement twoMeanOptimum d F 1. A product across the specified cut attains overlap alpha; the universal all-cut bound gives the reverse inequality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-support-trace"),
                DeclarationHandle.Create(Prefix + "support_trace"),
                H("Actual support-projector trace"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("The real rank formula is the trace of the original complex-matrix supportProjector, for arbitrary positive party count."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-helper-cutstates-sum-on-embedding"),
                DeclarationHandle.Create(Prefix + "sum_on_embedding"),
                H("sum on embedding"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-helper-cutstates-push-vector-apply"),
                DeclarationHandle.Create(Prefix + "pushVector_apply"),
                H("pushVector apply"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-helper-cutstates-push-vector-off"),
                DeclarationHandle.Create(Prefix + "pushVector_off"),
                H("pushVector off"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-helper-cutstates-phase-vector-unit"),
                DeclarationHandle.Create(Prefix + "phaseVector_unit"),
                H("phaseVector unit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-helper-cutstates-phase-vector-pair"),
                DeclarationHandle.Create(Prefix + "phaseVector_pair"),
                H("phaseVector pair"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-helper-cutstates-basis-projector-sum"),
                DeclarationHandle.Create(Prefix + "basis_projector_sum"),
                H("basis projector sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("Consumed proof helper for the full actual-object noisy-GHZ result. The statement and its hypotheses are taken from the checked Lean declaration; this helper is exported to support the source module split."))),
                DescribeRole.Theorem))));
}
