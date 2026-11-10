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
            Paragraph(Text("The complete qutrit application of the generic construction has n=d=3 and p=3/8. The parameter functions give M=wordCount(3,3)=27, K=cutCount(3)=3, R=supportRank(3,3)=21, k=witnessSlope(3,3)=8/9 and p_W=witnessZeroProbability(3,3)=3/4. The actual noisy-state means are f=noisyF(3,3,3/8)=23/36 and y=noisyY(3,3,3/8)=11/12, hence F=f/y=23/33. These parameters lie in the closed low-noise regime and the feasible two-mean triangle.")),
            Paragraph(Text("Write alpha=(sqrt(23/33)+sqrt(20/33))/sqrt(3) and beta=(sqrt(23/33)-sqrt(20/33)/2)/sqrt(3). These are exactly optimalAlpha(3,F) and optimalBeta(3,F), with alpha^2+2*beta^2=1. The first three constituents, indexed by j in Fin 3, are chiVector: amplitude alpha on the constant word jjj, beta on the other two constant words, and zero on every nonconstant word.")),
            Paragraph(Text("The next 81 constituents are indexed by (s,theta), where s is one of {1}, {2}, {1,2} in SourceCut 3 and theta is any of the 27 functions Fin 3 -> ZMod 3. Put a=complement(s), u_i=stdAddChar(theta_i)/sqrt(3). On the word equal to i throughout a and j throughout s, the amplitude is beta*delta_ij+(alpha-beta)*u_i*conjugate(u_j); it is zero outside this cut embedding. This is the actual cutState in lowNoiseStates, with independent cubic phase coordinates, not a scalar-difference phase prescription. The last six constituents are computational unit vectors indexed by QIndex 3 3: precisely the six permutations of the word 012. Thus the complete indexed family contains 3+3*27+6=90 unit states, retaining all phase indices even when rays coincide.")),
            Paragraph(Text("Each of the first three weights is 11/360, each cut-phase weight is 11/1080, and each Q weight is 1/72. The block totals are respectively 11/120, 33/40 and 1/12; all weights are nonnegative and their sum is one. Every constituent is normalized. The generic suppliers are Foundations.sourceCut_card, NoisyEnsembles.qIndex_card and NoisyEnsembles.low_noise_attainment, with the explicit lowNoiseWeights/lowNoiseStates definitions, ObservableOptimum.chi_attainment, CutStates.cutState_attainment and phaseVector_unit. Module-qualified supplier names here refer to the owning NoisyGhzExactRoof source modules.")),
            Paragraph(Text("The weighted sum of all 90 rank-one complex density matrices is the entire matrix rho=I/72+5*G/8, where G=rankOneDensity(ghz 3 3). In every pair of computational words x,z, rho(x,z)=delta_xz/72+5/24 when both words are constant, with the second term zero otherwise. This entrywise identity follows from Foundations.pair_cross_phase_sum, MatrixAverages.phase_average_matrix and basis_average_matrix, and NoisyEnsembles.source_average_matrix and low_noise_reconstruction. Matching only the two observable means would not establish this matrix identity.")),
            Paragraph(Text("The first 84 pure-state measures are 1-alpha^2=4*(14-sqrt(115))/99; the six Q measures are zero. Their weighted average is (11/12)*(1-alpha^2)=(14-sqrt(115))/27. NoisyEnsembles.low_noise_attainment supplies both this actual ensemble average and its equality with the original finite-ensemble convex roof; the universal lower bound and the reconstructed finite upper competitor are both used. Equivalently NoisyGhzExactRoof.noisy_exact_roof specializes to the same value. The scalar evaluation uses sqrt(2*(23/36)*(11/12-23/36))=sqrt(115)/18, and does not infer a matrix roof from scalar arithmetic alone.")),
            Paragraph(Text("For the strict comparison, sqrt(115)>=0 and sqrt(115)^2=115<(43/4)^2 imply sqrt(115)<43/4. Consequently the exact roof is strictly greater than 13/108, which is strictly greater than 1/9 since 13>12. NoisyGhzExactRoof.star_single_witness at n=d=3 gives p_star=3/8 and the original epsilonO(3,3,3/8)=1/9. This epsilonO retains its original hatE supremum over unit states and optimization over every real slope, through ObservableOptimum.witness_optimum and epsilonO_bridge and NoisyEnsembles.noisy_witness_optimum. The strict radical bound, all 90 normalized constituents, and the full matrix reconstruction are parts of this application, in addition to the generic strict-gap conclusion.")),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-support-rank-binomial"),
                DeclarationHandle.Create(Prefix + "support_rank_binomial"),
                H("The manuscript support-rank formula"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Antecedent),
                Blocks(Paragraph(Text("The trace of the actual two-symbol supportProjector is d+choose(d,2)*(2^n-2). The proof uses support_trace and its disjoint supportIndexEquiv enumeration, then converts d+K*d*(d-1) to the binomial form by exact natural-number arithmetic."))),
                DescribeRole.Theorem),
            Paragraph(Text("For every n,d>=3 the actual normalized GHZ vector satisfies all three endpoint equalities: geometricMeasurePure(ghz n d)=(d-1)/d; readout(witnessOp n d,ghz n d)=-(d-1)/d; epsilonWitness n d (-(d-1)/d)=(d-1)/d. To derive them, use ObservableOptimum.chi_attainment at F=1 and any j in Fin d. Both optimal amplitudes equal 1/sqrt(d), so the actual chiVector equals ghz on every constant word and vanishes on every other word. Its support mean is 1 and its GHZ mean is 1; twoMeanOptimum d 1 1=(d-1)/d gives its pure measure and witness readout. ObservableOptimum.witness_optimum at the left spectral endpoint gives the third equality against the original defining conjugate. All three statements hold for every n,d>=3, without a fixed-dimensional restriction.")),
            Paragraph(Text("The preserved local-dimension-two boundary follows directly in the same complex-matrix representation. For any natural n and computational word x: Fin n -> Fin 2, the image of x is a subset of Fin 2, so its cardinality is at most two. Therefore every diagonal entry of supportProjector n 2 is one and every off-diagonal entry is zero: P=I entrywise. Unfolding witnessOp then gives W=(1/2)I-rankOneDensity(ghz n 2). Consequently the witness and fidelity observables, and hence bounds defined from that identical observable, agree for n>=3. This operator identity neither invokes nor extends the d>=3 attained-roof theorem to qubits.")))));
}
