/- GID: D5/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/CompleteHigherInventoryDuality
   mirror-E: none(waiver:finite-quantitative-analysis)
   anchors: []
   utility: none
   digest: Exact all-support higher loss and both finite convex dual signs. -/
import D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
import D5.S3.Arith.Robin.ActualTwoPriceDefect
import Mathlib.Tactic

/-! The finite set used in duality includes the arbitrary actual inventory. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.CompleteHigherInventoryDuality
open Finset Real
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual

/-- Literal higher logarithmic mass, over every actual prime factor. -/
def higherMass (n : ℕ) : ℝ :=
  ∑ p ∈ n.primeFactors, ((n.factorization p - 1 : ℕ) : ℝ) * log p

def coordinates (n : ℕ) : Finset (ℕ × ℕ) :=
  n.primeFactors.biUnion fun p => (Icc 2 (n.factorization p)).image fun j => (p, j)

theorem mem_coordinates {n p j : ℕ} :
    (p, j) ∈ coordinates n ↔ p.Prime ∧ 2 ≤ j ∧ j ≤ n.factorization p := by
  classical
  simp only [coordinates, mem_biUnion, mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨q, hq, k, hk, rfl, rfl⟩
    exact ⟨Nat.prime_of_mem_primeFactors hq, (mem_Icc.mp hk).1, (mem_Icc.mp hk).2⟩
  · rintro ⟨hp, hj, hv⟩
    have hs : p ∈ n.primeFactors := by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]
      omega
    exact ⟨p, hs, j, mem_Icc.mpr ⟨hj, hv⟩, rfl, rfl⟩

theorem sum_coordinates (n : ℕ) (f : ℕ × ℕ → ℝ) :
    ∑ c ∈ coordinates n, f c =
      ∑ p ∈ n.primeFactors, ∑ j ∈ Icc 2 (n.factorization p), f (p, j) := by
  classical
  rw [coordinates, sum_biUnion]
  · apply sum_congr rfl
    intro p _
    exact sum_image (fun _ _ _ _ h => (Prod.mk.inj h).2)
  · intro p _ q _ hpq
    apply disjoint_left.mpr
    intro c hp hq
    obtain ⟨i, _, hi⟩ := mem_image.mp hp
    obtain ⟨j, _, hj⟩ := mem_image.mp hq
    exact hpq (Prod.mk.inj (hi.trans hj.symm)).1

theorem higherMass_eq_coordinate_sum (n : ℕ) :
    higherMass n = ∑ c ∈ coordinates n, log (c.1 : ℝ) := by
  rw [sum_coordinates]
  apply sum_congr rfl
  intro p _
  simp only [sum_const, Nat.card_Icc, nsmul_eq_mul]
  congr 1

theorem canonical_mem {η : ℝ} (hη : 0 < η) {p j : ℕ} :
    (p, j) ∈ coordinates (strictInteger η) ↔
      p.Prime ∧ 2 ≤ j ∧ η < goldenLayerMarginal p j := by
  rw [mem_coordinates]
  constructor
  · rintro ⟨hp, hj, hv⟩
    exact ⟨hp, hj, (strict_layer_iff hη hp (by omega)).mp hv⟩
  · rintro ⟨hp, hj, hv⟩
    exact ⟨hp, hj, (strict_layer_iff hη hp (by omega)).mpr hv⟩

theorem canonical_coordinates_antitone {η ζ : ℝ} (hη : 0 < η) (hζ : 0 < ζ)
    (hηζ : η ≤ ζ) : coordinates (strictInteger ζ) ⊆ coordinates (strictInteger η) := by
  intro c hc
  obtain ⟨hp, hj, hg⟩ := (canonical_mem hζ).mp hc
  exact (canonical_mem hη).mpr ⟨hp, hj, hηζ.trans_lt hg⟩

def coordinateGain (c : ℕ × ℕ) : ℝ := log c.1 * goldenLayerMarginal c.1 c.2
def coordinateWeight (c : ℕ × ℕ) : ℝ := log c.1

def potential (S : Finset (ℕ × ℕ)) (η : ℝ) : ℝ :=
  ∑ c ∈ S, max (coordinateGain c - η * coordinateWeight c) 0

def strictMass (S : Finset (ℕ × ℕ)) (η : ℝ) : ℝ :=
  ∑ c ∈ S, if 0 < coordinateGain c - η * coordinateWeight c then coordinateWeight c else 0

def inventoryGain (n : ℕ) : ℝ := ∑ c ∈ coordinates n, coordinateGain c

theorem positive_coordinate {η : ℝ} {p j : ℕ} (hp : p.Prime) :
    0 < coordinateGain (p, j) - η * coordinateWeight (p, j) ↔
      η < goldenLayerMarginal p j := by
  have he : coordinateGain (p, j) - η * coordinateWeight (p, j) =
      log p * (goldenLayerMarginal p j - η) := by
    dsimp [coordinateGain, coordinateWeight]; ring
  rw [he, mul_pos_iff_of_pos_left hp.log_pos, sub_pos]

theorem strictMass_eq {η : ℝ} (hη : 0 < η) {S : Finset (ℕ × ℕ)}
    (hprime : ∀ c ∈ S, c.1.Prime ∧ 2 ≤ c.2)
    (hsub : coordinates (strictInteger η) ⊆ S) :
    strictMass S η = higherMass (strictInteger η) := by
  classical
  rw [higherMass_eq_coordinate_sum, strictMass, ← sum_filter]
  have hset : S.filter (fun c => 0 < coordinateGain c - η * coordinateWeight c) =
      coordinates (strictInteger η) := by
    ext c
    constructor
    · intro hc
      obtain ⟨hcS, hpos⟩ := mem_filter.mp hc
      obtain ⟨hp, hj⟩ := hprime c hcS
      exact (canonical_mem hη).mpr ⟨hp, hj, (positive_coordinate hp).mp hpos⟩
    · intro hc
      obtain ⟨hp, hj, hg⟩ := (canonical_mem hη).mp hc
      exact mem_filter.mpr ⟨hsub hc, (positive_coordinate hp).mpr hg⟩
  rw [hset]
  rfl

private theorem second_higher_sum {X : ℝ} (hX : 1 < X) (n : ℕ) {p : ℕ}
    (hp : p.Prime) :
    (∑ j ∈ Icc 2 (layerCutoff X n p), layerLoss X n p j) =
      layerLoss X n p 2 + ∑ j ∈ Icc 3 (layerCutoff X n p), layerLoss X n p j := by
  classical
  by_cases hM : 2 ≤ layerCutoff X n p
  · have hset : Icc 2 (layerCutoff X n p) = insert 2 (Icc 3 (layerCutoff X n p)) := by
      ext j
      simp only [mem_Icc, mem_insert]
      omega
    rw [hset, sum_insert (by simp)]
  · have h2 := loss_above_cutoff hX n hp (by norm_num : 1 ≤ (2 : ℕ)) (by omega)
    have hset2 : Icc 2 (layerCutoff X n p) = ∅ := Icc_eq_empty (by omega)
    have hset3 : Icc 3 (layerCutoff X n p) = ∅ := Icc_eq_empty (by omega)
    simp [hset2, hset3, h2]

theorem complete_loss_coordinates {X : ℝ} (hX : 1 < X) (n : ℕ) :
    (∑ c ∈ coordinates (strictInteger (referencePrice X)) ∪ coordinates n,
      layerLoss X n c.1 c.2) = completeSecondLayerLoss X n + completeHigherLayerLoss X n := by
  classical
  have hη : 0 < referencePrice X := one_div_pos.mpr (mul_pos (by linarith) (log_pos hX))
  let S := lossPrimes X n
  let f := fun p => (Icc 2 (layerCutoff X n p)).image fun j => (p, j)
  have hset : coordinates (strictInteger (referencePrice X)) ∪ coordinates n = S.biUnion f := by
    ext c
    rcases c with ⟨p, j⟩
    simp only [mem_union, mem_coordinates, mem_biUnion, f, mem_image, Prod.mk.injEq]
    constructor
    · intro hc
      have hp : p.Prime := hc.elim (fun h => h.1) (fun h => h.1)
      have hj : 2 ≤ j := hc.elim (fun h => h.2.1) (fun h => h.2.1)
      have hmem (a : ℕ) (ha : j ≤ a.factorization p) : p ∈ a.primeFactors := by
        rw [← Nat.support_factorization, Finsupp.mem_support_iff]
        omega
      have hpS : p ∈ S := by
        dsimp [S, lossPrimes]
        rcases hc with hc | hc
        · exact mem_union_left _ (hmem _ hc.2.2)
        · exact mem_union_right _ (hmem _ hc.2.2)
      refine ⟨p, hpS, j, mem_Icc.mpr ⟨hj, ?_⟩, rfl, rfl⟩
      dsimp [layerCutoff]
      rw [← strictInteger_counts hη]
      rcases hc with hc | hc <;> omega
    · rintro ⟨q, hq, k, hk, hqp, hkj⟩
      subst q
      subst k
      have hp : p.Prime := by
        rcases mem_union.mp hq with h | h <;> exact Nat.prime_of_mem_primeFactors h
      obtain ⟨hj, hv⟩ := mem_Icc.mp hk
      dsimp [layerCutoff] at hv
      rw [← strictInteger_counts hη] at hv
      rcases le_max_iff.mp hv with hv | hv
      · exact Or.inl ⟨hp, hj, hv⟩
      · exact Or.inr ⟨hp, hj, hv⟩
  rw [hset, sum_biUnion]
  · simp only [completeSecondLayerLoss, completeHigherLayerLoss, S]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    rw [sum_image (fun _ _ _ _ h => (Prod.mk.inj h).2)]
    exact second_higher_sum hX n (by
      rcases mem_union.mp hp with h | h <;> exact Nat.prime_of_mem_primeFactors h)
  · intro p _ q _ hpq
    apply disjoint_left.mpr
    intro c hc hd
    obtain ⟨i, _, hi⟩ := mem_image.mp hc
    obtain ⟨j, _, hj⟩ := mem_image.mp hd
    exact hpq (Prod.mk.inj (hi.trans hj.symm)).1

/-- Exact positive-part identity on ANY finite superset of all canonical and
actual coordinates. In particular, the superset is never an exponent cap on n. -/
theorem literal_loss_identity {X : ℝ} (hX : 1 < X) {n : ℕ} (hn : 1 ≤ n)
    (S : Finset (ℕ × ℕ)) (hprime : ∀ c ∈ S, c.1.Prime ∧ 2 ≤ c.2)
    (hsub : coordinates (strictInteger (referencePrice X)) ∪ coordinates n ⊆ S) :
    actualDefect X n - completeFirstLayerLoss X n =
      potential S (referencePrice X) - inventoryGain n + referencePrice X * higherMass n := by
  classical
  let U := coordinates (strictInteger (referencePrice X)) ∪ coordinates n
  have hdecomp := actual_defect_decomposition hX hn
  have hzero (c : ℕ × ℕ) (hc : c ∈ S) (hcU : c ∉ U) : layerLoss X n c.1 c.2 = 0 := by
    obtain ⟨hp, hj⟩ := hprime c hc
    have hnmem : c ∉ coordinates n := fun h => hcU (mem_union_right _ h)
    have hnval : ¬ c.2 ≤ n.factorization c.1 := fun h =>
      hnmem (mem_coordinates.mpr ⟨hp, hj, h⟩)
    have hNmem : c ∉ coordinates (strictInteger (referencePrice X)) :=
      fun h => hcU (mem_union_left _ h)
    have hraw : rawLayerMargin X c.1 c.2 ≤ 0 := by
      apply le_of_not_gt
      intro h
      have hv := (margin_active_iff hX hp (by omega)).mp h
      rw [← strictInteger_counts (reference_price_pos hX)] at hv
      exact hNmem (mem_coordinates.mpr ⟨hp, hj, hv⟩)
    simp [layerLoss, hnval, max_eq_right hraw]
  have hsum : ∑ c ∈ S, layerLoss X n c.1 c.2 =
      actualDefect X n - completeFirstLayerLoss X n := by
    rw [← sum_subset hsub hzero, complete_loss_coordinates hX n]
    linarith
  have hoccupied : (∑ c ∈ S, if c.2 ≤ n.factorization c.1 then
      coordinateGain c - referencePrice X * coordinateWeight c else 0) =
      inventoryGain n - referencePrice X * higherMass n := by
    rw [← sum_filter]
    have hfilter : S.filter (fun c => c.2 ≤ n.factorization c.1) = coordinates n := by
      ext c
      constructor
      · intro hc
        obtain ⟨hcS, hv⟩ := mem_filter.mp hc
        exact mem_coordinates.mpr ⟨(hprime c hcS).1, (hprime c hcS).2, hv⟩
      · intro hc
        exact mem_filter.mpr ⟨hsub (mem_union_right _ hc), (mem_coordinates.mp hc).2.2⟩
    rw [hfilter, sum_sub_distrib, ← mul_sum, higherMass_eq_coordinate_sum]
    rfl
  have hraw (c : ℕ × ℕ) : rawLayerMargin X c.1 c.2 =
      coordinateGain c - referencePrice X * coordinateWeight c := by
    dsimp [rawLayerMargin, coordinateGain, coordinateWeight]
    ring
  rw [← hsum]
  simp_rw [layerLoss, hraw]
  rw [sum_sub_distrib]
  change potential S (referencePrice X) - _ = _
  rw [hoccupied]
  ring

/-- Finite convex duality. Zero margins are excluded from the strict mass;
actual occupancies at zero margins still enter the loss identity. -/
theorem finite_dual_abs {ι : Type*} (S : Finset ι) (b w : ι → ℝ) (i : ι → Bool)
    (hw : ∀ c ∈ S, 0 ≤ w c) {«λ» t : ℝ} (ht : 0 < t) :
    let F := fun η => ∑ c ∈ S, max (b c - η * w c) 0
    let h := fun η => ∑ c ∈ S, if 0 < b c - η * w c then w c else 0
    let H := ∑ c ∈ S, if i c then w c else 0
    let B := ∑ c ∈ S, if i c then b c else 0
    let R := F «λ» - B + «λ» * H
    |H - h «λ»| ≤ R / t + h («λ» - t) - h («λ» + t) := by
  classical
  dsimp only
  let F := fun η => ∑ c ∈ S, max (b c - η * w c) 0
  let h := fun η => ∑ c ∈ S, if 0 < b c - η * w c then w c else 0
  let H := ∑ c ∈ S, if i c then w c else 0
  let B := ∑ c ∈ S, if i c then b c else 0
  let R := F «λ» - B + «λ» * H
  change |H - h «λ»| ≤ R / t + h («λ» - t) - h («λ» + t)
  have hRdef : R = F «λ» - B + «λ» * H := rfl
  have hopt (η : ℝ) : B - η * H ≤ F η := by
    dsimp [B, H, F]
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_le_sum
    intro c _
    cases hi : i c <;> simp only [hi, Bool.false_eq_true, if_false, if_true,
      mul_zero, sub_self, zero_sub, sub_zero]
    · exact le_max_right _ _
    · exact le_max_left _ _
  have hlower : F («λ» - t) - F «λ» ≤ t * h («λ» - t) := by
    dsimp [F, h]
    rw [← sum_sub_distrib, mul_sum]
    apply sum_le_sum
    intro c hc
    have hwc := hw c hc
    by_cases hlo : 0 < b c - («λ» - t) * w c
    · rw [if_pos hlo, max_eq_left hlo.le]
      have hm := le_max_left (b c - «λ» * w c) 0
      nlinarith
    · have hbase : b c - «λ» * w c ≤ 0 := by nlinarith [mul_nonneg ht.le hwc]
      simp [hlo, max_eq_right (le_of_not_gt hlo), max_eq_right hbase]
  have hupper : t * h («λ» + t) ≤ F «λ» - F («λ» + t) := by
    dsimp [F, h]
    rw [← sum_sub_distrib, mul_sum]
    apply sum_le_sum
    intro c hc
    have hwc := hw c hc
    by_cases hhi : 0 < b c - («λ» + t) * w c
    · have hbase : 0 ≤ b c - «λ» * w c := by nlinarith [mul_nonneg ht.le hwc]
      rw [if_pos hhi, max_eq_left hhi.le, max_eq_left hbase]
      ring_nf
      exact le_rfl
    · rw [if_neg hhi, max_eq_right (le_of_not_gt hhi)]
      simpa using le_max_right (b c - «λ» * w c) 0
  have hmono (η ζ : ℝ) (hηζ : η ≤ ζ) : h ζ ≤ h η := by
    apply sum_le_sum
    intro c hc
    have hwc := hw c hc
    split_ifs with hζ hη
    · exact le_rfl
    · exfalso
      apply hη
      have hm := mul_nonneg (sub_nonneg.mpr hηζ) hwc
      nlinarith
    · exact hwc
    · exact le_rfl
  have hlow := hmono («λ» - t) «λ» (by linarith)
  have hhigh := hmono «λ» («λ» + t) (by linarith)
  have hleft := hopt («λ» - t)
  have hright := hopt («λ» + t)
  have hleft_mul : (H - h («λ» - t)) * t ≤ R := by
    rw [hRdef]
    nlinarith only [hleft, hlower]
  have hright_mul : (h («λ» + t) - H) * t ≤ R := by
    rw [hRdef]
    nlinarith only [hright, hupper]
  have hleft_div := (le_div_iff₀ ht).mpr hleft_mul
  have hright_div := (le_div_iff₀ ht).mpr hright_mul
  exact abs_le.mpr ⟨by linarith only [hright_div, hlow], by linarith only [hleft_div, hhigh]⟩

end D5.S3.Arith.Robin.PriceRecord.CompleteHigherInventoryDuality
