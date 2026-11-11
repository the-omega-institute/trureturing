using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class CompleteHigherInventoryDualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All actual higher coordinates and exact complete loss.",
        H("All actual higher coordinates and exact complete loss"),
        Blocks(
            Paragraph(Text("SOURCE ONLY: UNCOMPILED_UNACCEPTED. No Lean elaboration, kernel/axiom closure, native report, Scribe compilation, official acceptance, or four-slot Reg validation was run. Full Lean bodies are candidate proof attempts. The ordinary Pro derivation and the independent ordinary audit are fallible inputs, not axioms; this context already includes the repository and prior source candidates. No sterile-context or model-diversity claim is made. Native checking may expose elaboration or proof gaps. Root owns both pre-existing native queues and later integration.")),
            Paragraph(Text("higherMass(n) is the sum over every actual prime factor of (v_p(n)-1 : Nat)*log(p). coordinates(n) contains exactly the prime pairs with 2<=j<=v_p(n), and its weight sum equals that mass. Canonical membership is reused from strict_layer_iff; equal prices are excluded. The literal completeSecondLayerLoss+completeHigherLayerLoss is converted to the union of all canonical and actual coordinates. Exposing the existing finite decomposition then proves R=potential(lambda)-inventoryGain(n)+lambda*higherMass(n) on any finite superset of that union. Finite convex duality proves both signs using coordinatewise maximization and positive parts. This finite set never truncates n; even arbitrarily large actual negative-margin coordinates enter its actual inventory and loss.")),
            Paragraph(Text("Owning Lean source SHA256: c558a6f48fee969cc77571312483ad3390c0fbfe6d4a255b673c3e0d0d895efe. The complete new-declaration signatures, source line locations, import closure and dependency patches are exposed in source-manifest.json and dependency-boundary.json.")),
            Paragraph(Text("Four-slot Reg is not supplied. Missing evidence after the compiled telescope is an actual full-law variation/realization for this literal prime-power inventory, an exact specialization/control witness on its valid arithmetic domain, the corresponding realization/equivalence proofs, and the residual/open-slot statement accepted by the current Reg contract. Abstract invented spectra, weakened prime support or assumed final inequalities would not be faithful. Root must attach that precise missing-evidence statement to its existing issue workflow after native compilation; no issue or fake declared_validated status is created in this source-only packet.")),
            Describe.Lean(
                DescribeId.Create("completehigherinventoryduality-mem-coordinates"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.mem_coordinates"),
                H("mem coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem mem_coordinates {n p j : ℕ} :\n    (p, j) ∈ coordinates n ↔ p.Prime ∧ 2 ≤ j ∧ j ≤ n.factorization p"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("completehigherinventoryduality-sum-coordinates"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.sum_coordinates"),
                H("sum coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem sum_coordinates (n : ℕ) (f : ℕ × ℕ → ℝ) :\n    ∑ c ∈ coordinates n, f c =\n      ∑ p ∈ n.primeFactors, ∑ j ∈ Icc 2 (n.factorization p), f (p, j)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("completehigherinventoryduality-highermass-eq-coordinate-sum"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.higherMass_eq_coordinate_sum"),
                H("higherMass eq coordinate sum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem higherMass_eq_coordinate_sum (n : ℕ) :\n    higherMass n = ∑ c ∈ coordinates n, log (c.1 : ℝ)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("completehigherinventoryduality-highermass-nonneg"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.higherMass_nonneg"),
                H("higherMass nonneg"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem higherMass_nonneg (n : ℕ) : 0 ≤ higherMass n"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("completehigherinventoryduality-canonical-mem"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.canonical_mem"),
                H("canonical mem"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem canonical_mem {η : ℝ} (hη : 0 < η) {p j : ℕ} :\n    (p, j) ∈ coordinates (strictInteger η) ↔\n      p.Prime ∧ 2 ≤ j ∧ η < goldenLayerMarginal p j"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("completehigherinventoryduality-canonical-coordinates-antitone"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.canonical_coordinates_antitone"),
                H("canonical coordinates antitone"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem canonical_coordinates_antitone {η ζ : ℝ} (hη : 0 < η) (hζ : 0 < ζ)\n    (hηζ : η ≤ ζ) : coordinates (strictInteger ζ) ⊆ coordinates (strictInteger η)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("completehigherinventoryduality-positive-coordinate"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.positive_coordinate"),
                H("positive coordinate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem positive_coordinate {η : ℝ} {p j : ℕ} (hp : p.Prime) :\n    0 < coordinateGain (p, j) - η * coordinateWeight (p, j) ↔\n      η < goldenLayerMarginal p j"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("completehigherinventoryduality-strictmass-eq"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.strictMass_eq"),
                H("strictMass eq"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem strictMass_eq {η : ℝ} (hη : 0 < η) {S : Finset (ℕ × ℕ)}\n    (hprime : ∀ c ∈ S, c.1.Prime ∧ 2 ≤ c.2)\n    (hsub : coordinates (strictInteger η) ⊆ S) :\n    strictMass S η = higherMass (strictInteger η)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("completehigherinventoryduality-complete-loss-coordinates"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.complete_loss_coordinates"),
                H("complete loss coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem complete_loss_coordinates {X : ℝ} (hX : 1 < X) (n : ℕ) :\n    (∑ c ∈ coordinates (strictInteger (referencePrice X)) ∪ coordinates n,\n      layerLoss X n c.1 c.2) = completeSecondLayerLoss X n + completeHigherLayerLoss X n"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("completehigherinventoryduality-literal-loss-identity"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.literal_loss_identity"),
                H("literal loss identity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem literal_loss_identity {X : ℝ} (hX : 1 < X) {n : ℕ} (hn : 1 ≤ n)\n    (S : Finset (ℕ × ℕ)) (hprime : ∀ c ∈ S, c.1.Prime ∧ 2 ≤ c.2)\n    (hsub : coordinates (strictInteger (referencePrice X)) ∪ coordinates n ⊆ S) :\n    actualDefect X n - completeFirstLayerLoss X n =\n      potential S (referencePrice X) - inventoryGain n + referencePrice X * higherMass n"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("completehigherinventoryduality-finite-dual-abs"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.finite_dual_abs"),
                H("finite dual abs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem finite_dual_abs {ι : Type*} (S : Finset ι) (b w : ι → ℝ) (i : ι → Bool)\n    (hw : ∀ c ∈ S, 0 ≤ w c) {λ t : ℝ} (ht : 0 < t) :\n    let F := fun η => ∑ c ∈ S, max (b c - η * w c) 0\n    let h := fun η => ∑ c ∈ S, if 0 < b c - η * w c then w c else 0\n    let H := ∑ c ∈ S, if i c then w c else 0\n    let B := ∑ c ∈ S, if i c then b c else 0\n    let R := F λ - B + λ * H\n    |H - h λ| ≤ R / t + h (λ - t) - h (λ + t)"))),
                DescribeRole.Theorem)
        )));
}
