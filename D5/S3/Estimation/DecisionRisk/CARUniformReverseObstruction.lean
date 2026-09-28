/- GID: D5/S3/Estimation/DecisionRisk/CARUniformReverseObstruction
   generality: G
   mirror-B: D5/B/S3/Estimation/DecisionRisk/CARUniformReverseObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset, mathlib/module/Mathlib.Data.Nat.Choose.Cast]
   utility: none
   digest: Uniform asymmetric CAR deficiencies and full-public-seed counterparts. -/
import D5.S3.Estimation.DecisionRisk.CARRevelationScaling
import D5.S3.TotalVariation.DataProcessing
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Cast

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators ENNReal
open D5.S3.Divergence.ClassicalDPI
open D5.S3.Estimation.DecisionRisk.DescentDefectBounds
open D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer
open D5.S3.TotalVariation.Pinsker D5.S3.TotalVariation.Metric
open D5.S3.Estimation.DecisionRisk.CARApproximateRecovery
namespace D5.S3.Estimation.DecisionRisk.CARUniformReverseObstruction

def w (n : ℕ) (B : Block (Fin n)) : ℝ :=
  (if B.1.card = 1 then 1 - n / (3 * ((n : ℝ) - 1)) else 0) +
  (if B.1.card = n then n / (3 * ((n : ℝ) - 1)) else 0)
def v (n : ℕ) (B : Block (Fin n)) : ℝ :=
  (if B.1.card = 2 then 2 / (3 * ((n : ℝ) - 1)) else 0) +
  (if B.1.card = n - 1 then 1 / (3 * ((n : ℝ) - 1)) else 0)
def forward (n : ℕ) (B C : Block (Fin n)) : ℝ :=
  if B.1.card = 1 then
    if C.1.card = 2 ∧ B.1 ⊆ C.1 then 1 / ((n : ℝ) - 1) else 0
  else if B.1.card = n then
    if C.1.card = n - 1 then 1 / n else 0
  else if B = C then 1 else 0
def reverse (n : ℕ) (B C : Block (Fin n)) : ℝ :=
  if B.1.card = 2 then
    (if C.1.card = n then 1 / (2 * ((n : ℝ) - 1)) else 0) +
    (if C.1.card = 1 ∧ C.1 ⊆ B.1 then
      (1 - 1 / (2 * ((n : ℝ) - 1))) / 2 else 0)
  else if B.1.card = n - 1 then
    if C.1.card = n then 1 else 0
  else if B = C then 1 else 0
def rejectLoss (n : ℕ) (i : Fin n) (d : Option (Fin n)) : ℝ :=
  match d with | none => 1 / 2 | some j => if i = j then 0 else 1
abbrev ListAction (n : ℕ) := {D : Finset (Fin n) // D.card = 2}
def listLoss (n : ℕ) (i : Fin n) (D : ListAction n) : ℝ :=
  if i ∈ D.1 then 0 else 1
def mix (n : ℕ) (u : Block (Fin n) → ℝ) (B : Block (Fin n)) : ℝ :=
  (1 - 2 / n) * (if B.1.card = 1 then 1 else 0) + (2 / n) * u B
abbrev Seed (n : ℕ) := Option (Block (Fin n)) × Option (Block (Fin n))
def publicExperiment (n : ℕ) (p : Seed n → ℝ)
    (P : Seed n → Finpartition (Finset.univ : Finset (Fin n)))
    (i : Fin n) (o : Seed n × Block (Fin n)) : ℝ :=
  if (P o.1).part i = o.2.1 then p o.1 else 0

theorem result (n : ℕ) (hn : 4 ≤ n) :
    letI : NeZero n := ⟨by omega⟩
    let W := row (w n)
    let V := row (v n)
    let ε : ℝ := 1 / (3 * ((n : ℝ) - 1))
    let ρ : ℝ := (2 * n - 3) / (6 * ((n : ℝ) - 1))
    let Δ := fun i j => pair (v n) i j - pair (w n) i j
    let R := (1 / 2 : ℝ) * Finset.univ.sup' Finset.univ_nonempty
      (fun i => ∑ j ∈ Finset.univ.erase i, max (Δ i j) 0)
    let R' := (1 / 2 : ℝ) * Finset.univ.sup' Finset.univ_nonempty
      (fun i => ∑ j ∈ Finset.univ.erase i,
        max (pair (mix n (v n)) i j - pair (mix n (w n)) i j) 0)
    (∀ B, 0 ≤ w n B ∧ 0 ≤ v n B) ∧
    IsRowStochastic W ∧ IsRowStochastic V ∧
    (∀ i j, i ≠ j → pair (w n) i j = n / (3 * ((n : ℝ) - 1)) ∧
      pair (v n) i j = n / (3 * ((n : ℝ) - 1))) ∧
    (∀ i j, Δ i j = 0) ∧ R = 0 ∧
    ∃ (F G : FiniteMarkovKernel (Block (Fin n)) (Block (Fin n))),
      F.1 = forward n ∧ G.1 = reverse n ∧
      (∀ i, totalVariation (V i) (channelOutput F.1 (W i)) = ε) ∧
      (∀ i, totalVariation (W i) (channelOutput G.1 (V i)) = ρ) ∧
      (∀ B : Block (Fin n),
        (∀ d : Option (Fin n),
          min ((B.1.card - 1 : ℕ) : ℝ) ((B.1.card : ℝ) / 2) / n ≤
            (∑ i ∈ B.1, rejectLoss n i d) / n) ∧
        ∃ d : Option (Fin n), (∑ i ∈ B.1, rejectLoss n i d) / n =
          min ((B.1.card - 1 : ℕ) : ℝ) ((B.1.card : ℝ) / 2) / n) ∧
      (∀ B : Block (Fin n),
        (∀ d : ListAction n, ((B.1.card - 2 : ℕ) : ℝ) / n ≤
          (∑ i ∈ B.1, listLoss n i d) / n) ∧
        ∃ d : ListAction n, (∑ i ∈ B.1, listLoss n i d) / n =
          ((B.1.card - 2 : ℕ) : ℝ) / n) ∧
      (∃ d : FiniteMarkovKernel (Block (Fin n)) (Option (Fin n)),
        (∀ u ∈ ({w n, v n} : Finset (Block (Fin n) → ℝ)),
          ∀ e : FiniteMarkovKernel (Block (Fin n)) (Option (Fin n)),
          finiteBayesCost (fun _ => 1 / (n : ℝ)) (rejectLoss n) (row u) d.1 ≤
          finiteBayesCost (fun _ => 1 / (n : ℝ)) (rejectLoss n) (row u) e.1)) ∧
      finiteBayesRisk (fun _ => 1 / (n : ℝ)) (rejectLoss n) W =
        ENNReal.ofReal (n / (6 * ((n : ℝ) - 1))) ∧
      finiteBayesRisk (fun _ => 1 / (n : ℝ)) (rejectLoss n) V = ENNReal.ofReal (1 / 2) ∧
      (∃ d : FiniteMarkovKernel (Block (Fin n)) (ListAction n),
        (∀ u ∈ ({w n, v n} : Finset (Block (Fin n) → ℝ)),
          ∀ e : FiniteMarkovKernel (Block (Fin n)) (ListAction n),
          finiteBayesCost (fun _ => 1 / (n : ℝ)) (listLoss n) (row u) d.1 ≤
          finiteBayesCost (fun _ => 1 / (n : ℝ)) (listLoss n) (row u) e.1)) ∧
      finiteBayesRisk (fun _ => 1 / (n : ℝ)) (listLoss n) W =
        ENNReal.ofReal (((n : ℝ) - 2) / (3 * ((n : ℝ) - 1))) ∧
      finiteBayesRisk (fun _ => 1 / (n : ℝ)) (listLoss n) V =
        ENNReal.ofReal (((n : ℝ) - 3) / (3 * ((n : ℝ) - 1))) ∧
      finiteDeficiency V W = ENNReal.ofReal ε ∧
      finiteDeficiency W V = ENNReal.ofReal ρ ∧
      ρ / ε = (n : ℝ) - 3 / 2 ∧
      (∀ C : ℝ, ρ ≤ C * ε → (n : ℝ) - 3 / 2 ≤ C) ∧
      min 1 (R + (n : ℝ) / 2 * ε) = n / (6 * ((n : ℝ) - 1)) ∧
      min 1 (R + (n : ℝ) / 2 * ε) < ρ ∧
      0 < (2 / n : ℝ) ∧ 2 / (n : ℝ) ≤ 1 ∧
      ∃ (p : Seed n → ℝ)
        (P Q : Seed n → Finpartition (Finset.univ : Finset (Fin n))),
        (∀ s, 0 ≤ p s) ∧ (∑ s, p s = 1) ∧
        (∀ B, (∑ s, if B.1 ∈ (P s).parts then p s else 0) = mix n (w n) B) ∧
        (∀ B, (∑ s, if B.1 ∈ (Q s).parts then p s else 0) = mix n (v n) B) ∧
        (∃ (H : FiniteMarkovKernel (Seed n × Block (Fin n)) (Block (Fin n)))
           (J : FiniteMarkovKernel (Block (Fin n)) (Seed n × Block (Fin n))),
          (∀ i, channelOutput H.1 (publicExperiment n p P i) = row (mix n (w n)) i) ∧
          (∀ i, channelOutput J.1 (row (mix n (w n)) i) = publicExperiment n p P i)) ∧
        (∃ (H : FiniteMarkovKernel (Seed n × Block (Fin n)) (Block (Fin n)))
           (J : FiniteMarkovKernel (Block (Fin n)) (Seed n × Block (Fin n))),
          (∀ i, channelOutput H.1 (publicExperiment n p Q i) = row (mix n (v n)) i) ∧
          (∀ i, channelOutput J.1 (row (mix n (v n)) i) = publicExperiment n p Q i)) ∧
        (∀ i j, pair (mix n (v n)) i j - pair (mix n (w n)) i j = 0) ∧
        R' = 0 ∧
        finiteDeficiency (publicExperiment n p Q) (publicExperiment n p P) =
          ENNReal.ofReal ((2 / n) * ε) ∧
        finiteDeficiency (publicExperiment n p P) (publicExperiment n p Q) =
          ENNReal.ofReal ((2 / n) * ρ) ∧
        ((2 / n) * ρ) / ((2 / n) * ε) = (n : ℝ) - 3 / 2 ∧
        min 1 (R' + (n : ℝ) / 2 * ((2 / n) * ε)) < (2 / n) * ρ := by
  classical
  letI : NeZero n := ⟨by omega⟩
  dsimp only
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hm0 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hnN : 0 < n := by omega
  have hn1 : 1 ≤ n := by omega
  have count (S : Finset (Fin n)) (k : ℕ) (hk : 0 < k) (hSk : S.card ≤ k) (z : ℝ) :
      (∑ B : Block (Fin n), if B.1.card = k ∧ S ⊆ B.1 then z else 0) =
        ((n - S.card).choose (k - S.card) : ℝ) * z := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    congr 1
    norm_cast
    calc
      (Finset.univ.filter (fun B : Block (Fin n) => B.1.card = k ∧ S ⊆ B.1)).card =
          (((Finset.univ : Finset (Fin n)).powersetCard k).filter (S ⊆ ·)).card := by
        apply Finset.card_bij (fun B _ => B.1)
        · intro B hB
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB
          exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hB.1⟩, hB.2⟩
        · intro B hB C hC h; exact Subtype.ext h
        · intro B hB
          obtain ⟨hB, hS⟩ := Finset.mem_filter.mp hB
          obtain ⟨_, hcard⟩ := Finset.mem_powersetCard.mp hB
          let b : Block (Fin n) := ⟨B, Finset.card_pos.mp (hcard ▸ hk)⟩
          exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard, hS⟩, rfl⟩
      _ = _ := by
        simpa using Finset.card_filter_powersetCard_subset S Finset.univ k
          (Finset.subset_univ _) hSk
  have allcount (k : ℕ) (hk : 0 < k) (z : ℝ) :
      (∑ B : Block (Fin n), if B.1.card = k then z else 0) = (n.choose k : ℝ) * z := by
    simpa using count ∅ k hk (by simp) z
  have incount (i : Fin n) (k : ℕ) (hk : 0 < k) (z : ℝ) :
      (∑ B : Block (Fin n), if B.1.card = k ∧ i ∈ B.1 then z else 0) =
        ((n-1).choose (k-1) : ℝ) * z := by
    simpa using count {i} k hk (by simpa using (show 1 ≤ k by omega)) z
  have castm : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by simpa using (Nat.cast_sub hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - (1 : ℕ))
  have cm : (n - 1).choose (n - 1 - 1) = n - 1 := by
    rw [Nat.choose_symm (by omega), Nat.choose_one_right]
  have cn : n.choose (n - 1) = n := by
    rw [Nat.choose_symm hn1, Nat.choose_one_right]
  have row_sum (u : Block (Fin n) → ℝ) (i : Fin n) :
      (∑ B, row u i B) = ∑ B, if i ∈ B.1 then u B else 0 := rfl
  have hw0 (B : Block (Fin n)) : 0 ≤ w n B := by
    dsimp [w]
    have hb : (n : ℝ) / (3 * ((n : ℝ) - 1)) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr; linarith
    positivity
  have hv0 (B : Block (Fin n)) : 0 ≤ v n B := by dsimp [v]; positivity
  have hwrow (i : Fin n) : ∑ B, row (w n) i B = 1 := by
    have h : ∀ B : Block (Fin n), row (w n) i B =
        (if B.1.card = 1 ∧ i ∈ B.1 then 1 - n / (3 * ((n : ℝ) - 1)) else 0) +
        (if B.1.card = n ∧ i ∈ B.1 then n / (3 * ((n : ℝ) - 1)) else 0) := by
      intro B; by_cases hi : i ∈ B.1 <;> simp [row, w, hi]
    simp_rw [h]
    rw [Finset.sum_add_distrib, incount i 1 (by omega), incount i n hnN]
    simp
  have hvrow (i : Fin n) : ∑ B, row (v n) i B = 1 := by
    have h : ∀ B : Block (Fin n), row (v n) i B =
        (if B.1.card = 2 ∧ i ∈ B.1 then 2 / (3 * ((n : ℝ) - 1)) else 0) +
        (if B.1.card = n-1 ∧ i ∈ B.1 then 1 / (3 * ((n : ℝ) - 1)) else 0) := by
      intro B; by_cases hi : i ∈ B.1 <;> simp [row, v, hi]
    simp_rw [h]
    rw [Finset.sum_add_distrib, incount i 2 (by omega), incount i (n-1) (by omega)]
    simp only [Nat.reduceSub, Nat.choose_one_right, cm, castm]
    field_simp [ne_of_gt hm0]
    <;> ring
  have hW : IsRowStochastic (row (w n)) :=
    ⟨fun i B => by unfold row; split_ifs; exact hw0 B; exact le_rfl, hwrow⟩
  have hV : IsRowStochastic (row (v n)) :=
    ⟨fun i B => by unfold row; split_ifs; exact hv0 B; exact le_rfl, hvrow⟩
  let sing (i : Fin n) : Block (Fin n) := ⟨{i}, Finset.singleton_nonempty i⟩
  let full : Block (Fin n) := ⟨Finset.univ, Finset.univ_nonempty⟩
  have single_eq (i : Fin n) (B : Block (Fin n)) :
      B.1.card = 1 ∧ i ∈ B.1 ↔ B = sing i := by
    constructor
    · rintro ⟨hc, hi⟩
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc
      have hij : i = j := by simpa only [hj, Finset.mem_singleton] using hi
      apply Subtype.ext
      simpa only [sing, hij] using hj
    · rintro rfl; simp [sing]
  have full_eq (B : Block (Fin n)) : B.1.card = n ↔ B = full := by
    have h : B.1.card = n ↔ B.1 = Finset.univ := by
      simpa only [Fintype.card_fin] using B.1.card_eq_iff_eq_univ
    exact h.trans ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have wrow (i : Fin n) (B : Block (Fin n)) : row (w n) i B =
      (if B = sing i then 1 - n / (3 * ((n : ℝ) - 1)) else 0) +
      (if B = full then n / (3 * ((n : ℝ) - 1)) else 0) := by
    have h1 := single_eq i B
    have hf : (B.1.card = n ∧ i ∈ B.1) ↔ B = full := by
      rw [full_eq]
      constructor
      · exact And.left
      · intro h; exact ⟨h, by simp [h, full]⟩
    simp only [← h1, ← hf]
    by_cases hi : i ∈ B.1 <;> simp [row, w, hi]
  have wsum (i : Fin n) (f : Block (Fin n) → ℝ) :
      (∑ B, row (w n) i B * f B) =
        (1 - n / (3 * ((n : ℝ) - 1))) * f (sing i) +
          n / (3 * ((n : ℝ) - 1)) * f full := by
    simp only [wrow, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have twocount (i j : Fin n) (hij : i ≠ j) (k : ℕ) (hk : 2 ≤ k) (z : ℝ) :
      (∑ B : Block (Fin n), if B.1.card = k ∧ i ∈ B.1 ∧ j ∈ B.1 then z else 0) =
        ((n - 2).choose (k - 2) : ℝ) * z := by
    simpa [hij, and_assoc, Finset.insert_subset_iff, Finset.singleton_subset_iff] using count {i,j} k (by omega)
      (by simpa [hij] using hk) z
  have hp (i j : Fin n) (hij : i ≠ j) :
      pair (w n) i j = n / (3 * ((n : ℝ) - 1)) ∧
      pair (v n) i j = n / (3 * ((n : ℝ) - 1)) := by
    constructor
    · have he : pair (w n) i j = ∑ B, row (w n) i B * (if j ∈ B.1 then 1 else 0) := by
        unfold pair; apply Finset.sum_congr rfl; intro B _
        by_cases hi : i ∈ B.1 <;> by_cases hj : j ∈ B.1 <;> simp [row, hi, hj]
      rw [he, wsum]; simp [sing, full, Ne.symm hij]
    · have he : ∀ B : Block (Fin n), (if i ∈ B.1 ∧ j ∈ B.1 then v n B else 0) =
          (if B.1.card = 2 ∧ i ∈ B.1 ∧ j ∈ B.1 then 2 / (3 * ((n : ℝ) - 1)) else 0) +
          (if B.1.card = n-1 ∧ i ∈ B.1 ∧ j ∈ B.1 then 1 / (3 * ((n : ℝ) - 1)) else 0) := by
        intro B; by_cases hi : i ∈ B.1 <;> by_cases hj : j ∈ B.1 <;> simp [v, hi, hj]
      simp only [pair, he, Finset.sum_add_distrib]
      rw [twocount i j hij 2 (by omega), twocount i j hij (n-1) (by omega)]
      have hc : (n-2).choose (n-1-2) = n-2 := by
        have he : n-1-2 = (n-2)-1 := by omega
        rw [he, Nat.choose_symm (by omega), Nat.choose_one_right]
      simp only [Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, one_mul, hc,
        Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_ofNat]
      field_simp [ne_of_gt hm0] <;> ring
  have hΔ (i j : Fin n) : pair (v n) i j - pair (w n) i j = 0 := by
    by_cases hij : i = j
    · subst j
      have hw : pair (w n) i i = ∑ B, row (w n) i B := by simp only [pair, and_self, row]
      have hv : pair (v n) i i = ∑ B, row (v n) i B := by simp only [pair, and_self, row]
      rw [hw, hv, hwrow, hvrow, sub_self]
    · rw [(hp i j hij).1, (hp i j hij).2, sub_self]
  have hR : (1 / 2 : ℝ) * Finset.univ.sup' Finset.univ_nonempty
      (fun i => ∑ j ∈ Finset.univ.erase i, max (pair (v n) i j - pair (w n) i j) 0) = 0 := by
    simp only [hΔ, max_self, Finset.sum_const_zero, Finset.sup'_const, mul_zero]
  have downcount (S : Finset (Fin n)) (k : ℕ) (hk : 0 < k) (z : ℝ) :
      (∑ B : Block (Fin n), if B.1.card = k ∧ B.1 ⊆ S then z else 0) =
        (S.card.choose k : ℝ) * z := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    congr 1
    norm_cast
    calc
      (Finset.univ.filter (fun B : Block (Fin n) => B.1.card = k ∧ B.1 ⊆ S)).card =
          (S.powersetCard k).card := by
        apply Finset.card_bij (fun B _ => B.1)
        · intro B hB
          obtain ⟨_, hc, hs⟩ := Finset.mem_filter.mp hB
          exact Finset.mem_powersetCard.mpr ⟨hs, hc⟩
        · intro B hB C hC h; exact Subtype.ext h
        · intro B hB
          obtain ⟨hs, hc⟩ := Finset.mem_powersetCard.mp hB
          exact ⟨⟨B, Finset.card_pos.mp (hc ▸ hk)⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, hs⟩, rfl⟩
      _ = _ := Finset.card_powersetCard _ _
  have hf : IsRowStochastic (forward n) := by
    constructor
    · intro B C; unfold forward; split_ifs <;> positivity
    · intro B
      by_cases h1 : B.1.card = 1
      · simp only [forward, h1, if_true]
        rw [count B.1 2 (by omega) (by omega)]
        simp only [h1, Nat.reduceSub, Nat.choose_one_right, castm]
        exact mul_one_div_cancel (ne_of_gt hm0)
      · by_cases hN : B.1.card = n
        · simp only [forward, hN, show n ≠ 1 by omega, if_false, if_true]
          rw [allcount (n-1) (by omega), cn]
          exact mul_one_div_cancel (ne_of_gt hn0)
        · simp only [forward, h1, if_false, hN]
          exact Fintype.sum_ite_eq B (fun _ => (1 : ℝ))
  have hg : IsRowStochastic (reverse n) := by
    constructor
    · intro B C
      have hx : 1 / (2 * ((n : ℝ) - 1)) ≤ 1 := by
        apply (div_le_one (by positivity)).mpr; linarith only [hnR]
      unfold reverse; split_ifs <;> positivity
    · intro B
      by_cases h2 : B.1.card = 2
      · simp only [reverse, h2, if_true, Finset.sum_add_distrib]
        rw [allcount n hnN, downcount B.1 1 (by omega)]
        simp only [Nat.choose_self, Nat.cast_one, one_mul, h2,
          Nat.choose_one_right, Nat.cast_ofNat]
        ring
      · by_cases hm : B.1.card = n-1
        · simp only [reverse, hm, show n - 1 ≠ 2 by omega, if_false, if_true]
          rw [allcount n hnN]; simp
        · simp only [reverse, h2, if_false, hm]
          exact Fintype.sum_ite_eq B (fun _ => (1 : ℝ))
  let F : FiniteMarkovKernel (Block (Fin n)) (Block (Fin n)) := ⟨forward n, hf⟩
  let G : FiniteMarkovKernel (Block (Fin n)) (Block (Fin n)) := ⟨reverse n, hg⟩
  have foutput (i : Fin n) (C : Block (Fin n)) :
      channelOutput F.1 (row (w n) i) C =
        (if C.1.card = 2 ∧ i ∈ C.1 then
          (1 - n / (3 * ((n : ℝ) - 1))) / ((n : ℝ) - 1) else 0) +
        (if C.1.card = n-1 then 1 / (3 * ((n : ℝ) - 1)) else 0) := by
    change (∑ B, row (w n) i B * forward n B C) = _
    rw [wsum]
    have hnne : n ≠ 1 := by omega
    simp only [forward, sing, Finset.card_singleton, if_true, Finset.singleton_subset_iff,
      full, Finset.card_univ, Fintype.card_fin, hnne, if_false]
    split_ifs <;> field_simp [ne_of_gt hn0, ne_of_gt hm0] <;> ring
  have outcount (i : Fin n) (k : ℕ) (hk : 0 < k) (z : ℝ) :
      (∑ B : Block (Fin n), if B.1.card = k ∧ i ∉ B.1 then z else 0) =
        ((n.choose k : ℝ) - ((n-1).choose (k-1) : ℝ)) * z := by
    have hsplit : (∑ B : Block (Fin n), if B.1.card = k then z else 0) =
        (∑ B : Block (Fin n), if B.1.card = k ∧ i ∈ B.1 then z else 0) +
        (∑ B : Block (Fin n), if B.1.card = k ∧ i ∉ B.1 then z else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro B _
      by_cases hc : B.1.card = k <;> by_cases hi : i ∈ B.1 <;> simp [hc, hi]
    rw [allcount k hk, incount i k hk] at hsplit
    linarith only [hsplit]
  have ferror (i : Fin n) : totalVariation (row (v n) i)
      (channelOutput F.1 (row (w n) i)) = 1 / (3 * ((n : ℝ) - 1)) := by
    have gap : 2 / (3 * ((n : ℝ) - 1)) -
        (1 - n / (3 * ((n : ℝ) - 1))) / ((n : ℝ) - 1) =
          (1 / (3 * ((n : ℝ) - 1))) / ((n : ℝ) - 1) := by
      field_simp [ne_of_gt hm0] <;> ring
    have he (C : Block (Fin n)) :
        |row (v n) i C - channelOutput F.1 (row (w n) i) C| =
        (if C.1.card = 2 ∧ i ∈ C.1 then
          (1 / (3 * ((n : ℝ) - 1))) / ((n : ℝ) - 1) else 0) +
        (if C.1.card = n-1 ∧ i ∉ C.1 then 1 / (3 * ((n : ℝ) - 1)) else 0) := by
      rw [foutput]
      by_cases h2 : C.1.card = 2
      · have hm : C.1.card ≠ n-1 := by omega
        by_cases hi : i ∈ C.1 <;>
          simp only [row, v, h2, hm, hi, if_true, if_false, and_true, and_false,
            true_and, false_and, not_true_eq_false, not_false_eq_true, add_zero,
            zero_add, sub_zero, sub_self, abs_zero, gap, show (2 : ℕ) ≠ n-1 by omega]
        exact abs_of_nonneg (by positivity)
      · by_cases hm : C.1.card = n-1 <;> by_cases hi : i ∈ C.1 <;>
          simp [row, v, h2, hm, hi, show n-1 ≠ 2 by omega, abs_of_nonneg (le_of_lt (by positivity :
            0 < (1 : ℝ) / (3 * ((n : ℝ) - 1))))] <;> omega
    simp only [totalVariation, he, Finset.sum_add_distrib]
    rw [incount i 2 (by omega), outcount i (n-1) (by omega)]
    simp only [Nat.reduceSub, Nat.choose_one_right, cn, cm, castm]
    field_simp [ne_of_gt hm0] <;> ring
  have vsum (i : Fin n) (f : Block (Fin n) → ℝ) :
      (∑ B, row (v n) i B * f B) =
        (2 / (3 * ((n : ℝ) - 1))) *
          (∑ B, if B.1.card = 2 ∧ i ∈ B.1 then f B else 0) +
        (1 / (3 * ((n : ℝ) - 1))) *
          (∑ B, if B.1.card = n-1 ∧ i ∈ B.1 then f B else 0) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro B _
    by_cases hi : i ∈ B.1 <;> by_cases h2 : B.1.card = 2 <;>
      by_cases hm : B.1.card = n-1 <;> simp [row, v, hi, h2, hm, show (2 : ℕ) ≠ n-1 by omega,
        show n-1 ≠ 2 by omega, show n ≠ 3 by omega] <;> ring
  have gfull (i : Fin n) : channelOutput G.1 (row (v n) i) full =
      n / (3 * ((n : ℝ) - 1)) := by
    change (∑ B, row (v n) i B * reverse n B full) = _
    rw [vsum]
    have h2 (B : Block (Fin n)) :
        (if B.1.card = 2 ∧ i ∈ B.1 then reverse n B full else 0) =
        (if B.1.card = 2 ∧ i ∈ B.1 then 1 / (2 * ((n : ℝ) - 1)) else 0) := by
      by_cases h : B.1.card = 2 ∧ i ∈ B.1
      · simp [h, reverse, h.1, full, show n ≠ 1 by omega]
      · simp only [if_neg h]
    have hm (B : Block (Fin n)) :
        (if B.1.card = n-1 ∧ i ∈ B.1 then reverse n B full else 0) =
        (if B.1.card = n-1 ∧ i ∈ B.1 then (1 : ℝ) else 0) := by
      by_cases h : B.1.card = n-1 ∧ i ∈ B.1
      · simp [h, reverse, h.1, full, show n-1 ≠ 2 by omega]
      · simp only [if_neg h]
    simp_rw [h2, hm]
    rw [incount i 2 (by omega), incount i (n-1) (by omega)]
    simp only [Nat.reduceSub, Nat.choose_one_right, cm, castm]
    field_simp [ne_of_gt hm0] <;> ring
  have gsingle (i j : Fin n) : channelOutput G.1 (row (v n) i) (sing j) =
      if i = j then (2 * n - 3) / (6 * ((n : ℝ) - 1))
      else (2 * n - 3) / (6 * ((n : ℝ) - 1)^2) := by
    change (∑ B, row (v n) i B * reverse n B (sing j)) = _
    rw [vsum]
    have h2 (B : Block (Fin n)) :
        (if B.1.card = 2 ∧ i ∈ B.1 then reverse n B (sing j) else 0) =
        (if B.1.card = 2 ∧ i ∈ B.1 ∧ j ∈ B.1 then
          (1 - 1 / (2 * ((n : ℝ) - 1))) / 2 else 0) := by
      by_cases h : B.1.card = 2 ∧ i ∈ B.1
      · simp [h, reverse, h.1, h.2, sing, show (1 : ℕ) ≠ n by omega]
      · rw [if_neg h, if_neg (show ¬(B.1.card = 2 ∧ i ∈ B.1 ∧ j ∈ B.1) from fun hh => h ⟨hh.1, hh.2.1⟩)]
    have hm (B : Block (Fin n)) :
        (if B.1.card = n-1 ∧ i ∈ B.1 then reverse n B (sing j) else 0) = 0 := by
      by_cases h : B.1.card = n-1 ∧ i ∈ B.1
      · simp [h, reverse, h.1, sing, show n-1 ≠ 2 by omega, show (1 : ℕ) ≠ n by omega]
      · simp only [if_neg h]
    simp_rw [h2, hm]
    simp only [Finset.sum_const_zero, mul_zero, add_zero]
    by_cases hij : i = j
    · simp only [hij, and_self, if_true]
      rw [incount j 2 (by omega)]
      simp only [Nat.reduceSub, Nat.choose_one_right, castm]
      field_simp [ne_of_gt hm0] <;> ring
    · rw [twocount i j hij 2 (by omega)]
      simp only [Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, one_mul, if_neg hij]
      field_simp [ne_of_gt hm0] <;> ring
  have gother (i : Fin n) (C : Block (Fin n)) (h1 : C.1.card ≠ 1) (hN : C.1.card ≠ n) :
      channelOutput G.1 (row (v n) i) C = 0 := by
    change (∑ B, row (v n) i B * reverse n B C) = 0
    apply Finset.sum_eq_zero; intro B _
    by_cases h2 : B.1.card = 2
    · simp [reverse, h2, h1, hN]
    · by_cases hm : B.1.card = n-1
      · simp [reverse, h2, hm, h1, hN]
      · simp [row, v, h2, hm]
  have gerror (i : Fin n) : totalVariation (row (w n) i)
      (channelOutput G.1 (row (v n) i)) = (2 * n - 3) / (6 * ((n : ℝ) - 1)) := by
    let r : ℝ := (2 * n - 3) / (6 * ((n : ℝ) - 1))
    have hr : 0 ≤ r := by
      dsimp [r]; exact div_nonneg (by linarith only [hnR]) (by positivity)
    have hs : 1 - n / (3 * ((n : ℝ) - 1)) - r = r := by
      dsimp [r]; field_simp [ne_of_gt hm0] <;> ring
    have hrm : (2 * n - 3) / (6 * ((n : ℝ) - 1)^2) = r / ((n : ℝ) - 1) := by
      dsimp [r]; field_simp [ne_of_gt hm0] <;> ring
    have he (C : Block (Fin n)) :
        |row (w n) i C - channelOutput G.1 (row (v n) i) C| =
        (if C.1.card = 1 ∧ i ∈ C.1 then r else 0) +
        (if C.1.card = 1 ∧ i ∉ C.1 then r / ((n : ℝ) - 1) else 0) := by
      by_cases h1 : C.1.card = 1
      · obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h1
        have hC : C = sing j := Subtype.ext hj
        rw [hC, gsingle]
        by_cases hij : i = j
        · simp only [row, w, sing, Finset.card_singleton, Finset.mem_singleton,
            hij, if_true, show (1 : ℕ) ≠ n by omega, if_false, add_zero,
            not_true_eq_false, and_false, and_self]
          change |1 - n / (3 * ((n : ℝ) - 1)) - r| = r
          rw [hs, abs_of_nonneg hr]
        · simp only [row, w, sing, Finset.card_singleton, Finset.mem_singleton,
            hij, if_false, and_false, and_true, not_false_eq_true, zero_add, zero_sub]
          rw [hrm, abs_neg, abs_of_nonneg (div_nonneg hr hm0.le)]; rfl
      · by_cases hN : C.1.card = n
        · have hC : C = full := (full_eq C).mp hN
          rw [hC, gfull]
          simp [row, w, full, show n ≠ 1 by omega]
        · rw [gother i C h1 hN]
          simp [row, w, h1, hN]
    simp only [totalVariation, he, Finset.sum_add_distrib]
    rw [incount i 1 (by omega), outcount i 1 (by omega)]
    simp only [Nat.sub_self, Nat.choose_zero_right, Nat.choose_one_right,
      Nat.cast_one, one_mul]
    change (1 / 2 : ℝ) * (r + ((n : ℝ) - 1) * (r / ((n : ℝ) - 1))) = r
    field_simp [ne_of_gt hm0] <;> ring
  have cost_expand {D : Type} [Fintype D] (u : Block (Fin n) → ℝ)
      (l : Fin n → D → ℝ) (e : Block (Fin n) → D → ℝ) :
      finiteBayesCost (fun _ => 1 / (n : ℝ)) l (row u) e =
        (1 / (n : ℝ)) * ∑ B, u B * ∑ d, e B d * ∑ i ∈ B.1, l i d := by
    simp only [finiteBayesCost, channelOutput, Finset.mul_sum, Finset.sum_mul]
    calc
      (∑ i, ∑ d, ∑ B, 1 / (n : ℝ) * (row u i B * e B d * l i d)) =
          ∑ B, ∑ d, ∑ i, 1 / (n : ℝ) * (row u i B * e B d * l i d) := by
        rw [Finset.sum_comm]
        apply Eq.trans (Finset.sum_congr rfl (fun d _ => Finset.sum_comm))
        exact Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl; intro B _
        apply Finset.sum_congr rfl; intro d _
        have ht (i : Fin n) : 1 / (n : ℝ) * (row u i B * e B d * l i d) =
            if i ∈ B.1 then 1 / (n : ℝ) * (u B * (e B d * l i d)) else 0 := by
          by_cases hi : i ∈ B.1
          · simp only [row, if_pos hi]; ring
          · simp only [row, if_neg hi, zero_mul, mul_zero]
        simp_rw [ht]
        exact Fintype.sum_ite_mem B.1 _
  have optimal {D : Type} [Fintype D] (l : Fin n → D → ℝ)
      (m : Block (Fin n) → ℝ)
      (hmin : ∀ B d, m B ≤ ∑ i ∈ B.1, l i d)
      (hatt : ∀ B, ∃ d, (∑ i ∈ B.1, l i d) = m B) :
      ∃ d : FiniteMarkovKernel (Block (Fin n)) D,
        ∀ u : Block (Fin n) → ℝ, (∀ B, 0 ≤ u B) →
          finiteBayesCost (fun _ => 1 / (n : ℝ)) l (row u) d.1 =
            (1 / (n : ℝ)) * ∑ B, u B * m B ∧
          (∀ e : FiniteMarkovKernel (Block (Fin n)) D,
            finiteBayesCost (fun _ => 1 / (n : ℝ)) l (row u) d.1 ≤
              finiteBayesCost (fun _ => 1 / (n : ℝ)) l (row u) e.1) ∧
          finiteBayesRisk (fun _ => 1 / (n : ℝ)) l (row u) =
            ENNReal.ofReal ((1 / (n : ℝ)) * ∑ B, u B * m B) := by
    choose f hf using hatt
    let d : FiniteMarkovKernel (Block (Fin n)) D :=
      ⟨fun B a => if f B = a then 1 else 0,
        ⟨by intro B a; dsimp only; split_ifs <;> norm_num,
          fun B => Fintype.sum_ite_eq (f B) (fun _ => (1 : ℝ))⟩⟩
    have hd (u : Block (Fin n) → ℝ) :
        finiteBayesCost (fun _ => 1 / (n : ℝ)) l (row u) d.1 =
          (1 / (n : ℝ)) * ∑ B, u B * m B := by
      rw [cost_expand]
      simp only [d, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true, hf]
    have hbound (u : Block (Fin n) → ℝ) (hu : ∀ B, 0 ≤ u B)
        (e : FiniteMarkovKernel (Block (Fin n)) D) :
        (1 / (n : ℝ)) * ∑ B, u B * m B ≤
          finiteBayesCost (fun _ => 1 / (n : ℝ)) l (row u) e.1 := by
      rw [cost_expand]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum; intro B _
      apply mul_le_mul_of_nonneg_left _ (hu B)
      calc m B = ∑ a, e.1 B a * m B := by rw [← Finset.sum_mul, e.2.2, one_mul]
           _ ≤ _ := Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hmin B a) (e.2.1 B a)
    refine ⟨d, fun u hu => ⟨hd u, ?_, ?_⟩⟩
    · intro e; rw [hd]; exact hbound u hu e
    · apply le_antisymm
      · exact (iInf_le _ d).trans_eq (congrArg ENNReal.ofReal (hd u))
      · exact le_iInf fun e => ENNReal.ofReal_le_ofReal (hbound u hu e)
  let mr (B : Block (Fin n)) : ℝ := if B.1.card = 1 then 0 else B.1.card / 2
  have reject_min (B : Block (Fin n)) (d : Option (Fin n)) :
      mr B ≤ ∑ i ∈ B.1, rejectLoss n i d := by
    clear * - mr
    have hk : 1 ≤ B.1.card := B.2.card_pos
    cases d with
    | none =>
      simp only [rejectLoss, Finset.sum_const, nsmul_eq_mul]
      dsimp only [mr]; split_ifs
      · positivity
      · exact le_of_eq (by ring)
    | some j =>
      have hsum : (∑ i ∈ B.1, rejectLoss n i (some j)) = (B.1.erase j).card := by
        simp only [rejectLoss, Finset.sum_ite, Finset.sum_const_zero, zero_add,
          Finset.sum_const, nsmul_eq_mul, mul_one]
        congr 2
        ext i; simp [Finset.mem_erase, and_comm]
      rw [hsum]
      by_cases hj : j ∈ B.1
      · rw [Finset.card_erase_of_mem hj]
        rw [Nat.cast_sub hk]
        dsimp only [mr]; split_ifs with h1
        · simp [h1]
        · have hk2 : (2 : ℝ) ≤ B.1.card := by exact_mod_cast (show 2 ≤ B.1.card by omega)
          norm_num; linarith only [hk2]
      · rw [Finset.erase_eq_of_notMem hj]
        dsimp only [mr]; split_ifs
        · positivity
        · exact div_le_self (by positivity) (by norm_num)
  have reject_att (B : Block (Fin n)) : ∃ d, (∑ i ∈ B.1, rejectLoss n i d) = mr B := by
    clear * - mr
    by_cases h1 : B.1.card = 1
    · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h1
      refine ⟨some i, ?_⟩; simp [hi, rejectLoss, mr, h1]
    · refine ⟨none, ?_⟩; simp [rejectLoss, mr, h1]; ring
  have mr_eq (B : Block (Fin n)) : mr B =
      min ((B.1.card - 1 : ℕ) : ℝ) ((B.1.card : ℝ) / 2) := by
    clear * - mr
    by_cases h : B.1.card = 1
    · simp [mr, h]
    · dsimp only [mr]; rw [if_neg h]
      symm; apply min_eq_right
      have hk : 1 ≤ B.1.card := B.2.card_pos
      rw [Nat.cast_sub hk, Nat.cast_one]
      have hk2 : (2 : ℝ) ≤ B.1.card := by exact_mod_cast (show 2 ≤ B.1.card by omega)
      linarith only [hk2]
  have blockr (B : Block (Fin n)) :
      (∀ d : Option (Fin n),
        min ((B.1.card - 1 : ℕ) : ℝ) ((B.1.card : ℝ) / 2) / n ≤
          (∑ i ∈ B.1, rejectLoss n i d) / n) ∧
      ∃ d : Option (Fin n), (∑ i ∈ B.1, rejectLoss n i d) / n =
        min ((B.1.card - 1 : ℕ) : ℝ) ((B.1.card : ℝ) / 2) / n := by
    rw [← mr_eq]
    refine ⟨fun d => div_le_div_of_nonneg_right (reject_min B d) hn0.le, ?_⟩
    obtain ⟨d, hd⟩ := reject_att B
    exact ⟨d, congrArg (fun r : ℝ => r / n) hd⟩
  obtain ⟨dr, hdr⟩ := optimal (rejectLoss n) mr reject_min reject_att
  let ml (B : Block (Fin n)) : ℝ := (B.1.card - 2 : ℕ)
  have list_sum (B : Block (Fin n)) (D : ListAction n) :
      (∑ i ∈ B.1, listLoss n i D) = ((B.1 \ D.1).card : ℝ) := by
    clear * -
    simp only [listLoss, Finset.sum_ite, Finset.sum_const_zero, zero_add,
      Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 2
    ext i; simp
  have list_min (B : Block (Fin n)) (D : ListAction n) :
      ml B ≤ ∑ i ∈ B.1, listLoss n i D := by
    clear * - ml list_sum
    rw [list_sum]
    dsimp only [ml]
    exact_mod_cast (show B.1.card - 2 ≤ (B.1 \ D.1).card by
      simpa only [D.2] using Finset.le_card_sdiff D.1 B.1)
  have list_att (B : Block (Fin n)) : ∃ D, (∑ i ∈ B.1, listLoss n i D) = ml B := by
    clear * - hn ml list_sum
    by_cases hk : 2 ≤ B.1.card
    · obtain ⟨D, hD, hDc⟩ := Finset.exists_subset_card_eq hk
      refine ⟨⟨D, hDc⟩, ?_⟩
      rw [list_sum, Finset.card_sdiff_of_subset hD, hDc]
    · obtain ⟨D, hBD, _, hDc⟩ := Finset.exists_subsuperset_card_eq
        (Finset.subset_univ B.1) (by omega : B.1.card ≤ 2)
        (by simpa using (show 2 ≤ n by omega))
      refine ⟨⟨D, hDc⟩, ?_⟩
      rw [list_sum, Finset.sdiff_eq_empty_iff_subset.mpr hBD]
      simp [ml, Nat.sub_eq_zero_of_le (by omega : B.1.card ≤ 2)]
  have blockl (B : Block (Fin n)) :
      (∀ d : ListAction n, ((B.1.card - 2 : ℕ) : ℝ) / n ≤
        (∑ i ∈ B.1, listLoss n i d) / n) ∧
      ∃ d : ListAction n, (∑ i ∈ B.1, listLoss n i d) / n =
        ((B.1.card - 2 : ℕ) : ℝ) / n := by
    refine ⟨fun d => div_le_div_of_nonneg_right (list_min B d) hn0.le, ?_⟩
    obtain ⟨d, hd⟩ := list_att B
    exact ⟨d, congrArg (fun r : ℝ => r / n) hd⟩
  obtain ⟨dl, hdl⟩ := optimal (listLoss n) ml list_min list_att
  have weight_sum (k : ℕ) (hk : 0 < k) (z : ℝ) (f : ℕ → ℝ) :
      (∑ B : Block (Fin n), (if B.1.card = k then z else 0) * f B.1.card) =
        (n.choose k : ℝ) * (z * f k) := by
    have he (B : Block (Fin n)) : (if B.1.card = k then z else 0) * f B.1.card =
        if B.1.card = k then z * f k else 0 := by
      by_cases h : B.1.card = k <;> simp only [h, if_true, if_false, zero_mul]
    simp_rw [he]; exact allcount k hk _
  have wprofile (f : ℕ → ℝ) : (∑ B : Block (Fin n), w n B * f B.1.card) =
      n * ((1 - n / (3 * ((n : ℝ) - 1))) * f 1) +
        (n / (3 * ((n : ℝ) - 1))) * f n := by
    simp only [w, add_mul, Finset.sum_add_distrib]
    rw [weight_sum 1 (by omega), weight_sum n hnN]
    simp only [Nat.choose_one_right, Nat.choose_self, Nat.cast_one, one_mul]
  have vprofile (f : ℕ → ℝ) : (∑ B : Block (Fin n), v n B * f B.1.card) =
      (n * ((n : ℝ) - 1) / 2) * ((2 / (3 * ((n : ℝ) - 1))) * f 2) +
        n * ((1 / (3 * ((n : ℝ) - 1))) * f (n-1)) := by
    simp only [v, add_mul, Finset.sum_add_distrib]
    rw [weight_sum 2 (by omega), weight_sum (n-1) (by omega), cn, Nat.cast_choose_two]
  have rW : finiteBayesRisk (fun _ => 1 / (n : ℝ)) (rejectLoss n) (row (w n)) =
      ENNReal.ofReal (n / (6 * ((n : ℝ) - 1))) := by
    clear * - hn hn0 hm0 hdr hw0 wprofile mr
    rw [(hdr (w n) hw0).2.2]
    congr 1
    change (1 / (n : ℝ)) * (∑ B, w n B * (if B.1.card = 1 then 0 else (B.1.card : ℝ) / 2)) = _
    rw [wprofile (fun k => if k = 1 then 0 else (k : ℝ) / 2)]
    simp only [if_true, show n ≠ 1 by omega, if_false, mul_zero, zero_add]
    field_simp [ne_of_gt hn0, ne_of_gt hm0] <;> ring
  have rV : finiteBayesRisk (fun _ => 1 / (n : ℝ)) (rejectLoss n) (row (v n)) =
      ENNReal.ofReal (1 / 2) := by
    clear * - hn hn0 hm0 hdr hv0 vprofile mr castm
    rw [(hdr (v n) hv0).2.2]
    congr 1
    change (1 / (n : ℝ)) * (∑ B, v n B * (if B.1.card = 1 then 0 else (B.1.card : ℝ) / 2)) = _
    rw [vprofile (fun k => if k = 1 then 0 else (k : ℝ) / 2)]
    simp only [show (2 : ℕ) ≠ 1 by omega, show n-1 ≠ 1 by omega, if_false, Nat.cast_ofNat, castm]
    field_simp [ne_of_gt hn0, ne_of_gt hm0] <;> ring
  have lW : finiteBayesRisk (fun _ => 1 / (n : ℝ)) (listLoss n) (row (w n)) =
      ENNReal.ofReal (((n : ℝ) - 2) / (3 * ((n : ℝ) - 1))) := by
    clear * - hn hn0 hm0 hdl hw0 wprofile ml
    rw [(hdl (w n) hw0).2.2]
    congr 1
    change (1 / (n : ℝ)) * (∑ B, w n B * ((B.1.card - 2 : ℕ) : ℝ)) = _
    rw [wprofile (fun k => ((k - 2 : ℕ) : ℝ))]
    simp only [Nat.reduceSub, Nat.cast_zero, mul_zero, zero_add,
      Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_ofNat]
    field_simp [ne_of_gt hn0, ne_of_gt hm0] <;> ring
  have lV : finiteBayesRisk (fun _ => 1 / (n : ℝ)) (listLoss n) (row (v n)) =
      ENNReal.ofReal (((n : ℝ) - 3) / (3 * ((n : ℝ) - 1))) := by
    clear * - hn hn0 hm0 hdl hv0 vprofile ml castm
    rw [(hdl (v n) hv0).2.2]
    congr 1
    change (1 / (n : ℝ)) * (∑ B, v n B * ((B.1.card - 2 : ℕ) : ℝ)) = _
    rw [vprofile (fun k => ((k - 2 : ℕ) : ℝ))]
    simp only [Nat.sub_self, Nat.cast_zero, mul_zero, zero_add,
      Nat.cast_sub (by omega : 2 ≤ n-1), castm, Nat.cast_ofNat]
    field_simp [ne_of_gt hn0, ne_of_gt hm0] <;> ring
  have prior : (∀ _ : Fin n, 0 ≤ (1 / (n : ℝ))) ∧ (∑ _ : Fin n, 1 / (n : ℝ)) = 1 := by
    clear * - hn0
    refine ⟨fun _ => by positivity, ?_⟩
    simp [ne_of_gt hn0]
  have reject_bounded (i : Fin n) (d : Option (Fin n)) :
      0 ≤ rejectLoss n i d ∧ rejectLoss n i d ≤ 1 := by
    cases d with
    | none => norm_num [rejectLoss]
    | some j => simp only [rejectLoss]; split_ifs <;> norm_num
  have list_bounded (i : Fin n) (d : ListAction n) :
      0 ≤ listLoss n i d ∧ listLoss n i d ≤ 1 := by
    unfold listLoss; split_ifs <;> norm_num
  have upperF : finiteDeficiency (row (v n)) (row (w n)) ≤
      ENNReal.ofReal (1 / (3 * ((n : ℝ) - 1))) := by
    calc finiteDeficiency (row (v n)) (row (w n)) ≤
        ENNReal.ofReal (uniformSimulationError (row (v n)) (row (w n)) F) := iInf_le _ F
      _ = _ := by simp only [uniformSimulationError, ferror, Finset.sup'_const]
  have upperG : finiteDeficiency (row (w n)) (row (v n)) ≤
      ENNReal.ofReal ((2 * n - 3) / (6 * ((n : ℝ) - 1))) := by
    calc finiteDeficiency (row (w n)) (row (v n)) ≤
        ENNReal.ofReal (uniformSimulationError (row (w n)) (row (v n)) G) := iInf_le _ G
      _ = _ := by simp only [uniformSimulationError, gerror, Finset.sup'_const]
  have defF : finiteDeficiency (row (v n)) (row (w n)) =
      ENNReal.ofReal (1 / (3 * ((n : ℝ) - 1))) := by
    apply le_antisymm upperF
    have hb := deficiency_risk_bound (fun _ => 1 / (n : ℝ)) (listLoss n)
      (row (w n)) (row (v n)) prior hW hV list_bounded
    rw [lW, lV] at hb
    have he : ENNReal.ofReal (((n : ℝ) - 2) / (3 * ((n : ℝ) - 1))) =
        ENNReal.ofReal (((n : ℝ) - 3) / (3 * ((n : ℝ) - 1))) +
          ENNReal.ofReal (1 / (3 * ((n : ℝ) - 1))) := by
      rw [← ENNReal.ofReal_add (div_nonneg (by linarith only [hnR]) (by positivity)) (by positivity)]
      congr 1; ring
    rw [he] at hb
    exact (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).mp hb
  have defG : finiteDeficiency (row (w n)) (row (v n)) =
      ENNReal.ofReal ((2 * n - 3) / (6 * ((n : ℝ) - 1))) := by
    apply le_antisymm upperG
    have hb := deficiency_risk_bound (fun _ => 1 / (n : ℝ)) (rejectLoss n)
      (row (v n)) (row (w n)) prior hV hW reject_bounded
    rw [rV, rW] at hb
    have he : ENNReal.ofReal (1 / 2 : ℝ) =
        ENNReal.ofReal (n / (6 * ((n : ℝ) - 1))) +
          ENNReal.ofReal ((2 * n - 3) / (6 * ((n : ℝ) - 1))) := by
      rw [← ENNReal.ofReal_add (div_nonneg hn0.le (by positivity))
        (div_nonneg (by linarith only [hnR]) (by positivity))]
      congr 1; field_simp [ne_of_gt hm0] <;> ring
    rw [he] at hb
    exact (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).mp hb
  let comp {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
      (H : FiniteMarkovKernel X Y) (J : FiniteMarkovKernel Y Z) : FiniteMarkovKernel X Z :=
    ⟨fun x z => ∑ y, H.1 x y * J.1 y z,
      ⟨fun x z => Finset.sum_nonneg fun y _ => mul_nonneg (H.2.1 x y) (J.2.1 y z),
        by intro x; rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum, J.2.2, mul_one]; exact H.2.2 x⟩⟩
  have comp_out {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
      (H : FiniteMarkovKernel X Y) (J : FiniteMarkovKernel Y Z) (p : X → ℝ) :
      channelOutput (comp H J).1 p = channelOutput J.1 (channelOutput H.1 p) := by
    funext z
    simp only [channelOutput, comp, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  have transfer {X Y X' Y' : Type} [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
      (U : Fin n → X → ℝ) (T : Fin n → Y → ℝ)
      (U' : Fin n → X' → ℝ) (T' : Fin n → Y' → ℝ)
      (H : FiniteMarkovKernel X' X) (J : FiniteMarkovKernel Y Y')
      (hH : ∀ i, channelOutput H.1 (U' i) = U i)
      (hJ : ∀ i, channelOutput J.1 (T i) = T' i) :
      finiteDeficiency T' U' ≤ finiteDeficiency T U := by
    apply le_iInf; intro K
    let L := comp H (comp K J)
    apply (iInf_le _ L).trans
    apply ENNReal.ofReal_le_ofReal
    apply Finset.sup'_le; intro i hi
    change totalVariation (T' i) (channelOutput L.1 (U' i)) ≤ _
    dsimp only [L]
    rw [comp_out, comp_out, hH, ← hJ]
    exact (D5.S3.TotalVariation.DataProcessing.total_variation_channel_le
      (T i) (channelOutput K.1 (U i)) J.1 J.2).trans
      (Finset.le_sup' (fun j => totalVariation (T j) (channelOutput K.1 (U j))) (Finset.mem_univ i))
  have htpos : 0 < (2 / (n : ℝ)) := div_pos (by norm_num) hn0
  have ht0 : 0 ≤ (2 / (n : ℝ)) := htpos.le
  have ht1 : 2 / (n : ℝ) ≤ 1 := (div_le_one hn0).mpr (by linarith only [hnR])
  have supplier := CARRevelationScaling.result (w n) (v n) hw0 hv0 hwrow hvrow
  obtain ⟨scaling, _, realization⟩ := supplier
  obtain ⟨p, P, Q, hp0, hp1, hpw, hpv, hnormw, hnormv⟩ :=
    realization (by simpa using (show 2 ≤ n by omega)) (2 / n) ht0 (by simp)
  obtain ⟨Hw, Jw, hHw, hJw⟩ := hnormw
  obtain ⟨Hv, Jv, hHv, hJv⟩ := hnormv
  have hs := scaling (2 / n) ht0 ht1
  have scF : finiteDeficiency (row (mix n (v n))) (row (mix n (w n))) =
      ENNReal.ofReal ((2 / n) * (1 / (3 * ((n : ℝ) - 1)))) := by
    have h := hs.1
    rw [defF, ← ENNReal.ofReal_mul ht0] at h
    exact h
  have scG : finiteDeficiency (row (mix n (w n))) (row (mix n (v n))) =
      ENNReal.ofReal ((2 / n) * ((2 * n - 3) / (6 * ((n : ℝ) - 1)))) := by
    have h := hs.2
    rw [defG, ← ENNReal.ofReal_mul ht0] at h
    exact h
  have pubF : finiteDeficiency (publicExperiment n p Q) (publicExperiment n p P) =
      ENNReal.ofReal ((2 / n) * (1 / (3 * ((n : ℝ) - 1)))) := by
    rw [← scF]
    exact le_antisymm
      (transfer _ _ _ _ Hw Jv hHw hJv)
      (transfer _ _ _ _ Jw Hv hJw hHv)
  have pubG : finiteDeficiency (publicExperiment n p P) (publicExperiment n p Q) =
      ENNReal.ofReal ((2 / n) * ((2 * n - 3) / (6 * ((n : ℝ) - 1)))) := by
    rw [← scG]
    exact le_antisymm
      (transfer _ _ _ _ Hv Jw hHv hJw)
      (transfer _ _ _ _ Jv Hw hJv hHw)
  have pubpair (i j : Fin n) : pair (mix n (v n)) i j - pair (mix n (w n)) i j = 0 := by
    have he : pair (mix n (v n)) i j - pair (mix n (w n)) i j =
        (2 / (n : ℝ)) * (pair (v n) i j - pair (w n) i j) := by
      simp only [pair, ← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro B _
      by_cases h : i ∈ B.1 ∧ j ∈ B.1 <;> simp [h, mix] <;> ring
    rw [he, hΔ, mul_zero]
  have ratio : ((2 * n - 3) / (6 * ((n : ℝ) - 1))) /
      (1 / (3 * ((n : ℝ) - 1))) = (n : ℝ) - 3 / 2 := by
    clear * - hm0
    field_simp [ne_of_gt hm0] <;> ring
  have coeff (C : ℝ) (h : (2 * n - 3) / (6 * ((n : ℝ) - 1)) ≤
      C * (1 / (3 * ((n : ℝ) - 1)))) : (n : ℝ) - 3 / 2 ≤ C := by
    clear * - hm0 ratio h
    rw [← ratio]
    exact (div_le_iff₀ (by positivity)).mpr h
  have he : (n : ℝ) / 2 * (1 / (3 * ((n : ℝ) - 1))) = n / (6 * ((n : ℝ) - 1)) := by
    clear * - hm0
    field_simp [ne_of_gt hm0] <;> ring
  have strict0 : (n : ℝ) / 2 * (1 / (3 * ((n : ℝ) - 1))) <
      (2 * n - 3) / (6 * ((n : ℝ) - 1)) := by
    clear * - hnR hm0 he
    rw [he]
    exact (div_lt_div_iff_of_pos_right (by positivity)).mpr (by linarith only [hnR])
  have strict : min 1 ((n : ℝ) / 2 * (1 / (3 * ((n : ℝ) - 1)))) <
      (2 * n - 3) / (6 * ((n : ℝ) - 1)) := lt_of_le_of_lt (min_le_right _ _) strict0
  have pubratio : ((2 / (n : ℝ)) * ((2 * n - 3) / (6 * ((n : ℝ) - 1)))) /
      ((2 / n) * (1 / (3 * ((n : ℝ) - 1)))) = (n : ℝ) - 3 / 2 := by
    clear * - hn0 hm0
    field_simp [ne_of_gt hn0, ne_of_gt hm0] <;> ring
  have pubstrict : min 1 ((n : ℝ) / 2 * ((2 / n) * (1 / (3 * ((n : ℝ) - 1))))) <
      (2 / n) * ((2 * n - 3) / (6 * ((n : ℝ) - 1))) := by
    clear * - hn0 strict0 htpos
    apply lt_of_le_of_lt (min_le_right _ _)
    calc (n : ℝ) / 2 * ((2 / n) * (1 / (3 * ((n : ℝ) - 1)))) =
        (2 / n) * ((n : ℝ) / 2 * (1 / (3 * ((n : ℝ) - 1)))) := by ring
      _ < _ := mul_lt_mul_of_pos_left strict0 htpos
  refine ⟨fun B => ⟨hw0 B, hv0 B⟩, hW, hV, hp, hΔ, hR, F, G, rfl, rfl,
    ferror, gerror, blockr, blockl, ?_, rW, rV, ?_, lW, lV, defF, defG, ratio, coeff, ?_, ?_,
    htpos, ht1, p, P, Q, hp0, hp1, hpw, hpv, ⟨Hw, Jw, hHw, hJw⟩, ⟨Hv, Jv, hHv, hJv⟩,
    pubpair, ?_, pubF, pubG, pubratio, ?_⟩
  · refine ⟨dr, ?_⟩
    intro u hu e
    rcases Finset.mem_insert.mp hu with h | h
    · subst u; exact (hdr (w n) hw0).2.1 e
    · have h : u = v n := Finset.mem_singleton.mp h
      subst u; exact (hdr (v n) hv0).2.1 e
  · refine ⟨dl, ?_⟩
    intro u hu e
    rcases Finset.mem_insert.mp hu with h | h
    · subst u; exact (hdl (w n) hw0).2.1 e
    · have h : u = v n := Finset.mem_singleton.mp h
      subst u; exact (hdl (v n) hv0).2.1 e
  · rw [hR, zero_add, he]
    have hsix0 : (0 : ℝ) < 6 * ((n : ℝ) - 1) := mul_pos (by norm_num) hm0
    have hbound : (n : ℝ) / (6 * ((n : ℝ) - 1)) ≤ 1 :=
      (div_le_one hsix0).mpr (by linarith only [hnR])
    exact min_eq_right hbound
  · simpa only [hR, zero_add] using strict
  · simp only [pubpair, max_self, Finset.sum_const_zero, Finset.sup'_const, mul_zero]
  · simpa only [pubpair, max_self, Finset.sum_const_zero, Finset.sup'_const, mul_zero,
      zero_add] using pubstrict

end D5.S3.Estimation.DecisionRisk.CARUniformReverseObstruction
