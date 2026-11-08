using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Witness;

internal sealed class NoisyGhzExactRoofDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.";
    private static readonly LibraryNoteRef Antecedent =
        LibraryNoteRef.Create("D5/L/Divergence/xuzhouzhaohu2023gme");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual all-cut noisy-GHZ bounds, finite matrix ensembles and the original witness conjugate.",
        H("Noisy GHZ: exact roof and strict gaps"),
        Blocks(
            Paragraph(Text("Scientific source credit: Haobo Ma, then Wenlin Zhang; CC BY 4.0. This formalization follows the approved noisy-GHZ note in the original scientific capsule SHA256 4c31bee2cd31b1109b3940fd7121dd512ac560b04f69c2cf5fa99ed0b44a5cb5. Xu et al., arXiv:2211.05563v1, supply the witness and defining conjugate, as recorded in the existing library note. The scalar expression is credited to Wei and Goldbart, Physical Review A 68, 042307 (2003), Section IV.C, Eq. (54), doi:10.1103/PhysRevA.68.042307. The multiple-observable Legendre method is credited to Gühne, Reimpell and Werner, Physical Review Letters 98, 110502 (2007), Eqs. (1)-(6), doi:10.1103/PhysRevLett.98.110502, and Physical Review A 77, 052317 (2008), Section II, arXiv:0802.1734, doi:10.1103/PhysRevA.77.052317. Earlier qubit results of Buchholz, Moroder and Gühne (2016), Observation 3, and Cianciaruso, Bromley and Adesso (2016), Eq. (6) and Table 4, remain outside the higher-dimensional roof claim. No priority or novelty claim is made.")),
            Paragraph(Text("Objects are the existing NoisyGhzWitnessBoundGap complex matrices, normalized word amplitudes, arbitrary-cut IsBiseparable predicate, actual overlap supremum, finite normalized matrix ensembles and their infimum. DensityState supplies positive semidefinite trace-one matrices. Observable expectations are real traces. twoMeanOptimum includes the zero region; the older twoMeanValue denotes the radical branch only.")),
            Paragraph(Text("Source uncertainty retained: the released scalar-difference wording modulo three is not used. Characters are functions on the independent phase-coordinate group. The literal all-real-slope displayed antecedent formula is not a universal supplier; witness_optimum is proved against the actual hatE definition. These observations do not amend an upstream text.")),
            Paragraph(Text("The all-parameter roof uses explicit finite matrix ensembles in two closed regimes: the source basis/cut-phase/Q ensemble below p_W and an actual biseparable threshold/computational ensemble above p_W. Equality is derived from full matrix reconstruction, finite-ensemble upper bounds and the universal two-mean lower bound. The d=2 statement is only the preserved operator boundary. Graph-witness improvement, broad noise robustness, general unfaithfulness and singlet-witness conjectures are outside this result.")),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-noisy-exact-roof"),
                DeclarationHandle.Create(Prefix + "noisy_exact_roof"),
                H("The entire noisy-GHZ exact convex roof"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("For every n,d>=3 and 0<=p<=1, the actual finite-ensemble convex roof is twoMeanOptimum d f y and equals the truncated-radical source formula. Both finite constructions supply genuine attainment, rather than only matching two means."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-witness-threshold-formula"),
                DeclarationHandle.Create(Prefix + "witness_threshold_formula"),
                H("The exact physical threshold"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("The source threshold is M*(d-1)/(M*(d-1)+R-d), strictly between zero and one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-star-single-witness"),
                DeclarationHandle.Create(Prefix + "star_single_witness"),
                H("The exact interior single-witness value"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("At p_star=(d-2)^2/(T*k), the probability lies strictly between zero and p_W, the witness is w_star, and the original epsilonO is e_star=1/((d-1)^3+1)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-noisy-strict-gap"),
                DeclarationHandle.Create(Prefix + "noisy_strict_gap"),
                H("The entire strict noisy interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("For every 0<p<p_W the complete original epsilonO is strictly less than the two-mean optimum, which equals the actual noisy roof."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-noisy-gap-endpoints"),
                DeclarationHandle.Create(Prefix + "noisy_gap_endpoints"),
                H("Equality and the common zero region"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("The witness optimum equals the actual roof at p=0. Both are zero throughout p_W<=p<=1; the finite biseparable ensemble is supplied by high_noise_attainment."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-star-certificate-gap"),
                DeclarationHandle.Create(Prefix + "star_certificate_gap"),
                H("A strictly stronger universal certificate at p_star"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("The actual affine certificate gives e_star+h*p_star*(1-R/M) as a roof lower bound, and this is strictly greater than e_star. Positivity uses the genuine support rank R<M."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-qutrit-exact-ensemble"),
                DeclarationHandle.Create(Prefix + "qutrit_exact_ensemble"),
                H("The exact 90-component qutrit roof"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("At n=d=3 and p=3/8, the universal ensemble specializes to three basis components of weight 11/360, 81 cut-phase components of weight 11/1080 and six Q components of weight 1/72. Complete amplitudes are lowNoiseStates at F=23/33. Their full matrix is I/72+5*G/8, their average and actual roof equal (14-sqrt(115))/27, strictly greater than 13/108, which is greater than epsilonO=1/9."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-support-rank-binomial"),
                DeclarationHandle.Create(Prefix + "support_rank_binomial"),
                H("The manuscript support-rank formula"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("The actual two-symbol support rank is also d+choose(d,2)*(2^n-2), with exact natural-number arithmetic."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-ghz-left-endpoint"),
                DeclarationHandle.Create(Prefix + "ghz_left_endpoint"),
                H("Attainment at the left spectral endpoint"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("The actual normalized GHZ vector has all-cut pure measure (d-1)/d, witness expectation -(d-1)/d, and the original conjugate has the same endpoint value."))),
                DescribeRole.Theorem))));
}
