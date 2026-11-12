using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class CompleteHigherInventoryDualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All actual higher coordinates and exact complete loss.",
        H("All actual higher coordinates and exact complete loss"),
        Blocks(
            Paragraph(Text("higherMass(n) is the sum over every actual prime factor of (v_p(n)-1 : Nat)*log(p). coordinates(n) contains exactly the prime pairs with 2<=j<=v_p(n), and its weight sum equals that mass. Canonical membership is reused from strict_layer_iff; equal prices are excluded. The literal completeSecondLayerLoss+completeHigherLayerLoss is converted to the union of all canonical and actual coordinates. The finite decomposition gives R=potential(«λ»bda)-inventoryGain(n)+«λ»bda*higherMass(n) on any finite superset of that union. Finite convex duality proves both signs using coordinatewise maximization and positive parts. This finite set never truncates n; even arbitrarily large actual negative-margin coordinates enter its actual inventory and loss.")),
            Describe.Lean(
                DescribeId.Create("completehigherinventoryduality-mem-coordinates"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.mem_coordinates"),
                H("mem coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean statement: theorem mem_coordinates {n p j : ℕ} : (p, j) ∈ coordinates n ↔ p.Prime ∧ 2 ≤ j ∧ j ≤ n.factorization p"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("completehigherinventoryduality-sum-coordinates"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.sum_coordinates"),
                H("sum coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean statement: theorem sum_coordinates (n : ℕ) (f : ℕ × ℕ → ℝ) : ∑ c ∈ coordinates n, f c = ∑ p ∈ n.primeFactors, ∑ j ∈ Icc 2 (n.factorization p), f (p, j)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("completehigherinventoryduality-highermass-eq-coordinate-sum"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.higherMass_eq_coordinate_sum"),
                H("higherMass eq coordinate sum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean statement: theorem higherMass_eq_coordinate_sum (n : ℕ) : higherMass n = ∑ c ∈ coordinates n, log (c.1 : ℝ)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("completehigherinventoryduality-canonical-mem"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.canonical_mem"),
                H("canonical mem"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean statement: theorem canonical_mem {η : ℝ} (hη : 0 < η) {p j : ℕ} : (p, j) ∈ coordinates (strictInteger η) ↔ p.Prime ∧ 2 ≤ j ∧ η < goldenLayerMarginal p j"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("completehigherinventoryduality-canonical-coordinates-antitone"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.canonical_coordinates_antitone"),
                H("canonical coordinates antitone"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean statement: theorem canonical_coordinates_antitone {η ζ : ℝ} (hη : 0 < η) (hζ : 0 < ζ) (hηζ : η ≤ ζ) : coordinates (strictInteger ζ) ⊆ coordinates (strictInteger η)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("completehigherinventoryduality-positive-coordinate"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.positive_coordinate"),
                H("positive coordinate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean statement: theorem positive_coordinate {η : ℝ} {p j : ℕ} (hp : p.Prime) : 0 < coordinateGain (p, j) - η * coordinateWeight (p, j) ↔ η < goldenLayerMarginal p j"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("completehigherinventoryduality-strictmass-eq"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.strictMass_eq"),
                H("strictMass eq"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean statement: theorem strictMass_eq {η : ℝ} (hη : 0 < η) {S : Finset (ℕ × ℕ)} (hprime : ∀ c ∈ S, c.1.Prime ∧ 2 ≤ c.2) (hsub : coordinates (strictInteger η) ⊆ S) : strictMass S η = higherMass (strictInteger η)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("completehigherinventoryduality-complete-loss-coordinates"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.complete_loss_coordinates"),
                H("complete loss coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean statement: theorem complete_loss_coordinates {X : ℝ} (hX : 1 < X) (n : ℕ) : (∑ c ∈ coordinates (strictInteger (referencePrice X)) ∪ coordinates n, layerLoss X n c.1 c.2) = completeSecondLayerLoss X n + completeHigherLayerLoss X n"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("completehigherinventoryduality-literal-loss-identity"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.literal_loss_identity"),
                H("literal loss identity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean statement: theorem literal_loss_identity {X : ℝ} (hX : 1 < X) {n : ℕ} (hn : 1 ≤ n) (S : Finset (ℕ × ℕ)) (hprime : ∀ c ∈ S, c.1.Prime ∧ 2 ≤ c.2) (hsub : coordinates (strictInteger (referencePrice X)) ∪ coordinates n ⊆ S) : actualDefect X n - completeFirstLayerLoss X n = potential S (referencePrice X) - inventoryGain n + referencePrice X * higherMass n"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("completehigherinventoryduality-finite-dual-abs"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality.finite_dual_abs"),
                H("finite dual abs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean statement: theorem finite_dual_abs {ι : Type*} (S : Finset ι) (b w : ι → ℝ) (i : ι → Bool) (hw : ∀ c ∈ S, 0 ≤ w c) {«λ» t : ℝ} (ht : 0 < t) : let F := fun η => ∑ c ∈ S, max (b c - η * w c) 0 let h := fun η => ∑ c ∈ S, if 0 < b c - η * w c then w c else 0 let H := ∑ c ∈ S, if i c then w c else 0 let B := ∑ c ∈ S, if i c then b c else 0 let R := F «λ» - B + «λ» * H |H - h «λ»| ≤ R / t + h («λ» - t) - h («λ» + t)"))),
                DescribeRole.Theorem)
        )));
}
