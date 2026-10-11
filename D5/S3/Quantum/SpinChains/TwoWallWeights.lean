/- GID: D5/S3/Quantum/SpinChains/TwoWallWeights
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinChains/TwoWallWeights
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integer inversion weights bound and lower the literal two-wall bond action. -/

import D5.S3.Quantum.SpinChains.TwoWallSl2

open scoped BigOperators

namespace D5.S3.Quantum.SpinChains.TwoWallWeights

open TwoWallWords TwoWallMarked TwoWallSl2 Sl2WeightFiltration
open HypereclecticNonShortening (level)
open D5.S1.Words.ParityCode.OddTopWeight (ones)

private theorem wall_exists {a b : ℕ} (w : Word a b) : ∃ p, w.1 p = wall := by
  by_contra hn
  push Not at hn
  have hc := w.2.2.2
  simp [count, hn] at hc

private noncomputable def coordinates {a b : ℕ} (w : Word a b) : Coordinates a b :=
  decode ⟨(w, Classical.choose (wall_exists w)), Classical.choose_spec (wall_exists w)⟩

private theorem coordinates_word {a b : ℕ} (w : Word a b) :
    (encode (coordinates w)).1.1 = w :=
  congrArg (fun x : MarkedWord a b => x.1.1)
    ((marked_coordinates a b).2.1 _)

/-- The integer eigenvalue of the literal delta word. -/
noncomputable def wordWeight {a b : ℕ} (w : Word a b) : ℤ :=
  integerWeight (coordinates w)

variable (K : Type*) [Field K] [CharZero K]

private theorem h_delta {a b : ℕ} (w : Word a b) :
    h K a b (delta K w) = (wordWeight w : K) • delta K w := by
  simpa only [coordinates_word, wordWeight] using
    ((literal_action K a b).2.2.2.2.2 (coordinates w)).1

private theorem h_apply {a b : ℕ} (x : Space K a b) (w : Word a b) :
    h K a b x w = (wordWeight w : K) * x w := by
  classical
  conv_lhs => rw [← (basis K a b).sum_repr x]
  rw [map_sum]
  simp only [map_smul]
  change (∑ v : Word a b, x v • h K a b (delta K v)) w = _
  simp only [h_delta K]
  simp [delta, basis, Finsupp.coe_basisSingleOne,
    Finsupp.single_apply, mul_comm]

private theorem weight_eq {a b : ℕ} (c : Coordinates a b) :
    wordWeight (encode c).1.1 = integerWeight c := by
  have hh := h_delta ℚ (encode c).1.1
  have hc := ((literal_action ℚ a b).2.2.2.2.2 c).1
  rw [hc] at hh
  have he := congrArg (fun x : Space ℚ a b => x (encode c).1.1) hh
  simp only [Finsupp.smul_apply, delta, basis, Finsupp.coe_basisSingleOne,
    Finsupp.single_eq_same, smul_eq_mul, mul_one] at he
  exact Int.cast_injective he.symm

private theorem binary_bound {m : ℕ} (u : Fin m → Bool) :
    ones u ≤ m ∧ level u ≤ ones u * (m - ones u) := by
  classical
  let z : ℕ := ∑ j : Fin m, if u j = false then 1 else 0
  have hz : ones u + z = m := by
    dsimp [z]
    rw [ones, ← Finset.sum_add_distrib]
    have he (j : Fin m) :
        (if u j then 1 else 0) + (if u j = false then 1 else 0 : ℕ) = 1 := by
      cases u j <;> rfl
    simp_rw [he]
    simp
  refine ⟨by omega, ?_⟩
  have hl : level u ≤ ones u * z := by
    calc
      level u ≤ ∑ i : Fin m, ∑ j : Fin m,
          (if u i then 1 else 0) * (if u j = false then 1 else 0 : ℕ) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        split_ifs <;> simp_all
      _ = ones u * z := by
        simp only [ones, z, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_comm
  simpa only [show z = m - ones u by omega] using hl

private theorem coordinate_bound {a b : ℕ} (c : Coordinates a b) :
    -(a * b : ℤ) ≤ integerWeight c ∧ integerWeight c ≤ (a * b : ℤ) := by
  have hu := binary_bound c.u
  have hv := binary_bound c.v
  have hl : (c.m : ℤ) + c.n = (a : ℤ) + b := by exact_mod_cast c.length
  have hf : (ones c.u : ℤ) + ones c.v = (b : ℤ) := by exact_mod_cast c.filling
  have hum : (ones c.u : ℤ) ≤ c.m := by exact_mod_cast hu.1
  have hvn : (ones c.v : ℤ) ≤ c.n := by exact_mod_cast hv.1
  have hlu : (level c.u : ℤ) ≤ (ones c.u : ℤ) * ((c.m : ℤ) - ones c.u) := by
    simpa only [Nat.cast_mul, Nat.cast_sub hu.1] using
      (show (level c.u : ℤ) ≤ ((ones c.u * (c.m - ones c.u) : ℕ) : ℤ) by
        exact_mod_cast hu.2)
  have hlv : (level c.v : ℤ) ≤ (ones c.v : ℤ) * ((c.n : ℤ) - ones c.v) := by
    simpa only [Nat.cast_mul, Nat.cast_sub hv.1] using
      (show (level c.v : ℤ) ≤ ((ones c.v * (c.n - ones c.v) : ℕ) : ℤ) by
        exact_mod_cast hv.2)
  have cross : 0 ≤ (ones c.u : ℤ) * ((c.n : ℤ) - ones c.v) +
      (ones c.v : ℤ) * ((c.m : ℤ) - ones c.u) :=
    add_nonneg (mul_nonneg (by omega) (by omega))
      (mul_nonneg (by omega) (by omega))
  dsimp only [integerWeight]
  constructor <;> nlinarith [Int.natCast_nonneg (level c.u),
    Int.natCast_nonneg (level c.v)]

/-- The literal words have a finite integral weight decomposition and weights in [-ab,ab]. -/
theorem weight_structure (a b : ℕ) :
    (∀ c : Coordinates a b, wordWeight (encode c).1.1 = integerWeight c) ∧
    (∀ w : Word a b, h K a b (delta K w) = (wordWeight w : K) • delta K w) ∧
    IntegralWeights (h K a b) ∧
    (∀ w : Word a b, -(a * b : ℤ) ≤ wordWeight w ∧ wordWeight w ≤ (a * b : ℤ)) := by
  classical
  refine ⟨weight_eq, h_delta K, ?_, fun w => coordinate_bound (coordinates w)⟩
  refine ⟨(Finset.univ : Finset (Word a b)).image wordWeight,
    le_antisymm le_top ?_⟩
  rw [← (basis K a b).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨w, rfl⟩
  apply Submodule.mem_iSup_of_mem (wordWeight w)
  apply Submodule.mem_iSup_of_mem (Finset.mem_image.mpr ⟨w, Finset.mem_univ w, rfl⟩)
  exact Module.End.mem_eigenspace_iff.mpr (h_delta K w)

#print axioms weight_structure

private theorem weightLE_eq_supported (a b : ℕ) (s : ℤ) :
    weightLE (h K a b) s = Finsupp.supported K K {w : Word a b | wordWeight w ≤ s} := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro t
    apply iSup_le
    intro ht x hx
    rw [Finsupp.mem_supported]
    intro w hw
    have hn : x w ≠ 0 := Finsupp.mem_support_iff.mp hw
    have he := congrArg (fun y : Space K a b => y w)
      (Module.End.mem_eigenspace_iff.mp hx)
    rw [h_apply] at he
    simp only [Finsupp.smul_apply, smul_eq_mul] at he
    have hw' : wordWeight w = t := Int.cast_injective (mul_right_cancel₀ hn he)
    change wordWeight w ≤ s
    rwa [hw']
  · rw [Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    apply Submodule.mem_iSup_of_mem (wordWeight w)
    apply Submodule.mem_iSup_of_mem hw
    exact Module.End.mem_eigenspace_iff.mpr (h_delta K w)

private theorem F3_map (a b : ℕ) (s : ℤ) :
    (weightLE (h K a b) s).map (F3 K a b) ≤ weightLE (h K a b) (s - 2) := by
  rw [← (literal_action K a b).2.2.2.1]
  simp only [weightLE, Submodule.map_iSup]
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  apply Submodule.map_le_iff_le_comap.mpr
  intro x hx
  apply Submodule.mem_iSup_of_mem (t - 2)
  apply Submodule.mem_iSup_of_mem (by omega : t - 2 ≤ s - 2)
  simpa using lowering_pow_weight (literal_action K a b).2.2.1 hx 1

private theorem nilpotent_of_filtration (a b : ℕ) (A : Module.End K (Space K a b))
    (ha : ∀ s : ℤ, (weightLE (h K a b) s).map A ≤ weightLE (h K a b) (s - 2)) :
    A ^ (a * b + 1) = 0 := by
  apply (basis K a b).ext
  intro w
  have hw : delta K w ∈ weightLE (h K a b) (a * b : ℤ) := by
    rw [weightLE_eq_supported]
    exact Finsupp.single_mem_supported K 1 ((weight_structure K a b).2.2.2 w).2
  have hs := filtration_pow_map_le (weightLE (h K a b)) A ha (a * b : ℤ) (a * b + 1)
  have hx := hs (Submodule.mem_map_of_mem hw)
  rw [weightLE_eq_supported, Finsupp.mem_supported'] at hx
  change (A ^ (a * b + 1)) (delta K w) = 0
  ext v
  apply hx
  change ¬ wordWeight v ≤ _
  rw [not_le]
  have hb := ((weight_structure K a b).2.2.2 v).1
  push_cast
  nlinarith

private theorem F3_move {a b : ℕ} (w : Word a b) (p : Pos a b)
    (hp : Allowed 2 w p) : wordWeight (swapWord p w) = wordWeight w - 2 := by
  classical
  let w' := swapWord p w
  let z := F3 ℚ a b (delta ℚ w) w'
  have hz : 0 < z := by
    dsimp only [z]
    rw [F3, (cyclic_action ℚ a b).2.2.2.1]
    rw [Finsupp.finsetSum_apply]
    apply Finset.sum_pos'
    · intro q _
      simp only [bond]
      split_ifs
      · simp only [delta, basis, Finsupp.coe_basisSingleOne, Finsupp.single_apply]
        split_ifs <;> norm_num
      · simp
    · refine ⟨p, Finset.mem_univ p, ?_⟩
      simp [bond, hp, w', delta, basis, Finsupp.coe_basisSingleOne]
  have hf := (literal_action ℚ a b).2.2.1.hf
  rw [(literal_action ℚ a b).2.2.2.1] at hf
  have he := congrArg (fun A : Module.End ℚ (Space ℚ a b) => A (delta ℚ w) w') hf
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    h_delta, h_apply, map_smul, Finsupp.sub_apply, Finsupp.smul_apply,
    smul_eq_mul] at he
  have he' : (wordWeight w' : ℚ) * z = ((wordWeight w : ℚ) - 2) * z := by
    dsimp only [z]
    linarith
  have he'' := mul_right_cancel₀ (ne_of_gt hz) he'
  exact_mod_cast he''

/-- Each enabled 21 to 12 bond drops weight by two; F3 lowers the filtration and dies by ab+1. -/
theorem F3_weight_control (a b : ℕ) :
    (∀ (w : Word a b) (p : Pos a b), Allowed 2 w p →
      wordWeight (swapWord p w) = wordWeight w - 2) ∧
    (∀ s : ℤ, (weightLE (h K a b) s).map (F3 K a b) ≤
      weightLE (h K a b) (s - 2)) ∧
    F3 K a b ^ (a * b + 1) = 0 :=
  ⟨F3_move, F3_map K a b, nilpotent_of_filtration K a b _ (F3_map K a b)⟩

#print axioms F3_weight_control

end D5.S3.Quantum.SpinChains.TwoWallWeights
