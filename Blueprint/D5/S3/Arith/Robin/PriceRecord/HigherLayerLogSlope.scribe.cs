using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class HigherLayerLogSlopeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform logarithmic slope of the actual higher-layer marginal.",
        H("Uniform logarithmic slope of the actual higher-layer marginal"),
        Blocks(
            Paragraph(Text("SOURCE ONLY: UNCOMPILED_UNACCEPTED. No Lean elaboration, kernel/axiom closure, native report, Scribe compilation, official acceptance, or four-slot Reg validation was run. Full Lean bodies are candidate proof attempts. The ordinary Pro derivation and the independent ordinary audit are fallible inputs, not axioms; this context already includes the repository and prior source candidates. No sterile-context or model-diversity claim is made. Native checking may expose elaboration or proof gaps. Root owns both pre-existing native queues and later integration.")),
            Paragraph(Text("For every natural j>=2 and real u>=2, S_j is the finite sum u+...+u^j, beta_j=log(1+1/S_j)/log(u). The source differentiates log(beta_j), proves S_j<=2u^j and uS_j prime>=j u^j, and bounds the reciprocal logarithm factor below by 4/5. It obtains logarithmicSlope>=j/3, integrates that inequality on the closed lower boundary, proves strict antitonicity, and constructs a finite decay endpoint. beta_nat reconciles the real formula with the existing goldenLayerMarginal at every prime and every positive layer. This is a repository-derived implementation of the supplied audited elementary calculation, not a novelty claim or a substitute spectrum.")),
            Paragraph(Text("Owning Lean source SHA256: d6166af0cedc0d7657e22f349aef072978b3408e6d2df772ee1c9e4f3871c111. The complete new-declaration signatures, source line locations, import closure and dependency patches are exposed in source-manifest.json and dependency-boundary.json.")),
            Paragraph(Text("Four-slot Reg is not supplied. Missing evidence after the compiled telescope is an actual full-law variation/realization for this literal prime-power inventory, an exact specialization/control witness on its valid arithmetic domain, the corresponding realization/equivalence proofs, and the residual/open-slot statement accepted by the current Reg contract. Abstract invented spectra, weakened prime support or assumed final inequalities would not be faithful. Root must attach that precise missing-evidence statement to its existing issue workflow after native compilation; no issue or fake declared_validated status is created in this source-only packet.")),
            Describe.Lean(
                DescribeId.Create("higherlayerlogslope-powersum-succ"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.powerSum_succ"),
                H("powerSum succ"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem powerSum_succ (j : ℕ) (u : ℝ) :\n    powerSum (j + 1) u = powerSum j u + u ^ (j + 1)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerlogslope-powersum-nonneg"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.powerSum_nonneg"),
                H("powerSum nonneg"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem powerSum_nonneg {u : ℝ} (hu : 0 ≤ u) (j : ℕ) : 0 ≤ powerSum j u"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerlogslope-last-power-le-sum"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.last_power_le_sum"),
                H("last power le sum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem last_power_le_sum {u : ℝ} (hu : 0 ≤ u) {j : ℕ} (hj : 1 ≤ j) :\n    u ^ j ≤ powerSum j u"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerlogslope-powersum-pos"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.powerSum_pos"),
                H("powerSum pos"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem powerSum_pos {u : ℝ} (hu : 0 < u) {j : ℕ} (hj : 1 ≤ j) :\n    0 < powerSum j u"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerlogslope-powersum-geometric"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.powerSum_geometric"),
                H("powerSum geometric"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem powerSum_geometric (j : ℕ) (u : ℝ) :\n    (u - 1) * powerSum j u = u * (u ^ j - 1)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerlogslope-powersum-le-twice"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.powerSum_le_twice"),
                H("powerSum le twice"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem powerSum_le_twice {u : ℝ} (hu : 2 ≤ u) (j : ℕ) :\n    powerSum j u ≤ 2 * u ^ j"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerlogslope-powersum-hasderivat"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.powerSum_hasDerivAt"),
                H("powerSum hasDerivAt"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem powerSum_hasDerivAt (j : ℕ) (u : ℝ) :\n    HasDerivAt (powerSum j) (powerSumDerivative j u) u"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerlogslope-weighted-last-le"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.weighted_last_le"),
                H("weighted last le"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem weighted_last_le {u : ℝ} (hu : 0 ≤ u) {j : ℕ} (hj : 1 ≤ j) :\n    (j : ℝ) * u ^ j ≤ u * powerSumDerivative j u"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerlogslope-gain-pos"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.gain_pos"),
                H("gain pos"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem gain_pos {u : ℝ} (hu : 0 < u) {j : ℕ} (hj : 1 ≤ j) :\n    0 < gain j u"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerlogslope-gain-le-inv-pow"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.gain_le_inv_pow"),
                H("gain le inv pow"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem gain_le_inv_pow {u : ℝ} (hu : 0 < u) {j : ℕ} (hj : 1 ≤ j) :\n    gain j u ≤ 1 / u ^ j"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerlogslope-beta-pos"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.beta_pos"),
                H("beta pos"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem beta_pos {u : ℝ} (hu : 2 ≤ u) {j : ℕ} (hj : 1 ≤ j) :\n    0 < beta j u"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerlogslope-beta-le-inv-pow-log"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.beta_le_inv_pow_log"),
                H("beta le inv pow log"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem beta_le_inv_pow_log {u : ℝ} (hu : 2 ≤ u) {j : ℕ} (hj : 1 ≤ j) :\n    beta j u ≤ 1 / (u ^ j * log u)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerlogslope-beta-nat"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.beta_nat"),
                H("beta nat"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem beta_nat {p j : ℕ} (hp : p.Prime) (hj : 1 ≤ j) :\n    beta j (p : ℝ) = goldenLayerMarginal p j"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerlogslope-log-beta-hasderivat"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.log_beta_hasDerivAt"),
                H("log beta hasDerivAt"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem log_beta_hasDerivAt {u : ℝ} (hu : 2 ≤ u) {j : ℕ} (hj : 1 ≤ j) :\n    HasDerivAt (fun v => log (beta j v)) (-logarithmicSlope j u / u) u"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerlogslope-logarithmicslope-ge"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.logarithmicSlope_ge"),
                H("logarithmicSlope ge"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem logarithmicSlope_ge {u : ℝ} (hu : 2 ≤ u) {j : ℕ} (hj : 2 ≤ j) :\n    (j : ℝ) / 3 ≤ logarithmicSlope j u"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerlogslope-beta-continuouson"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.beta_continuousOn"),
                H("beta continuousOn"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem beta_continuousOn {j : ℕ} (hj : 1 ≤ j) :\n    ContinuousOn (beta j) (Set.Ici 2)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerlogslope-log-beta-drop"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.log_beta_drop"),
                H("log beta drop"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem log_beta_drop {j : ℕ} (hj : 2 ≤ j) {u v : ℝ}\n    (hu : 2 ≤ u) (huv : u ≤ v) :\n    (j : ℝ) / 3 * log (v / u) ≤ log (beta j u / beta j v)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerlogslope-beta-strictantion"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.beta_strictAntiOn"),
                H("beta strictAntiOn"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem beta_strictAntiOn {j : ℕ} (hj : 2 ≤ j) :\n    StrictAntiOn (beta j) (Set.Ici 2)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerlogslope-beta-small-endpoint"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope.beta_small_endpoint"),
                H("beta small endpoint"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem beta_small_endpoint {j : ℕ} (hj : 1 ≤ j) {η : ℝ} (hη : 0 < η) :\n    ∃ v : ℝ, 2 ≤ v ∧ beta j v < η"))),
                DescribeRole.Theorem)
        )));
}
