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
private theorem F3_weight_control (a b : ℕ) :
    (∀ (w : Word a b) (p : Pos a b), Allowed 2 w p →
      wordWeight (swapWord p w) = wordWeight w - 2) ∧
    (∀ s : ℤ, (weightLE (h K a b) s).map (F3 K a b) ≤
      weightLE (h K a b) (s - 2)) ∧
    F3 K a b ^ (a * b + 1) = 0 :=
  ⟨F3_move, F3_map K a b, nilpotent_of_filtration K a b _ (F3_map K a b)⟩


private theorem weight_cons {m : ℕ} (u : Fin m → Bool) (d : Bool) :
    HypereclecticNonShortening.weight (Fin.cons d u) =
      HypereclecticNonShortening.weight u + (if d then (m : ℚ) else 0) - ones u := by
  open HypereclecticNonShortening in
    rw [weight, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ]
  have hs : (∑ i : Fin m, if u i then ((m + 1 : ℕ) : ℚ) - 1 -
      2 * ((i.val + 1 : ℕ) : ℚ) else 0) =
      HypereclecticNonShortening.weight u - ones u := by
    rw [HypereclecticNonShortening.weight, ones, Nat.cast_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases u i with
    | false => simp
    | true => simp; ring
  rw [hs]
  cases d with
  | false => simp
  | true => simp; ring

private theorem weight_snoc {m : ℕ} (u : Fin m → Bool) (d : Bool) :
    HypereclecticNonShortening.weight (Fin.snoc u d) =
      HypereclecticNonShortening.weight u + ones u - (if d then (m : ℚ) else 0) := by
  rw [HypereclecticNonShortening.weight, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  have hs : (∑ i : Fin m, if u i then ((m + 1 : ℕ) : ℚ) - 1 -
      2 * (i.val : ℚ) else 0) =
      HypereclecticNonShortening.weight u + ones u := by
    rw [HypereclecticNonShortening.weight, ones, Nat.cast_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases u i with
    | false => simp
    | true => simp; ring
  rw [hs]
  cases d with
  | false => simp
  | true => simp; ring

private def chi {m : ℕ} (u : Fin m → Bool) : ℤ :=
  2 * (level u : ℤ) - (ones u : ℤ) * ((m : ℤ) - ones u)

private theorem chi_cast {m : ℕ} (u : Fin m → Bool) :
    (chi u : ℚ) = HypereclecticNonShortening.weight u := by
  rw [HypereclecticNonShortening.weight_eq_level]
  simp only [chi, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]

private theorem chi_boundaries {m : ℕ} (u : Fin m → Bool) :
    chi (Fin.cons true u) = chi u + ((m : ℤ) - ones u) ∧
    chi (Fin.snoc u true) = chi u - ((m : ℤ) - ones u) ∧
    chi (Fin.cons false u) = chi u - ones u ∧
    chi (Fin.snoc u false) = chi u + ones u := by
  have hc (d : Bool) : chi (Fin.cons d u) =
      chi u + (if d then (m : ℤ) else 0) - ones u := by
    have hh := weight_cons u d
    rw [← chi_cast, ← chi_cast] at hh
    exact_mod_cast hh
  have hs (d : Bool) : chi (Fin.snoc u d) =
      chi u + ones u - (if d then (m : ℤ) else 0) := by
    have hh := weight_snoc u d
    rw [← chi_cast, ← chi_cast] at hh
    exact_mod_cast hh
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hh := hc true
    simp only [if_true] at hh
    linarith
  · have hh := hs true
    simp only [if_true] at hh
    linarith
  · simpa using hc false
  · simpa using hs false

private theorem ones_cons {m : ℕ} (u : Fin m → Bool) (d : Bool) :
    ones (Fin.cons d u) = (if d then 1 else 0) + ones u := by
  rw [ones, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rfl

private theorem ones_snoc {m : ℕ} (u : Fin m → Bool) (d : Bool) :
    ones (Fin.snoc u d) = ones u + (if d then 1 else 0) := by
  rw [ones, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rfl

private def firstSource {a b m n : ℕ} (p : Pos a b) (u : Fin m → Bool)
    (v : Fin n → Bool) (s : Bool) (hl : m + 1 + n = a + b)
    (hf : (if s then 1 else 0) + ones u + ones v = b) : Coordinates a b :=
  ⟨p, m + 1, n, Fin.cons s u, v, hl, by simpa only [ones_cons] using hf⟩

private def firstTarget {a b m n : ℕ} (p : Pos a b) (u : Fin m → Bool)
    (v : Fin n → Bool) (s : Bool) (hl : m + 1 + n = a + b)
    (hf : (if s then 1 else 0) + ones u + ones v = b) : Coordinates a b :=
  ⟨p + 1, m, n + 1, u, Fin.snoc v s, by omega,
    by rw [ones_snoc]; omega⟩

private theorem first_weight {a b m n : ℕ} (p : Pos a b) (u : Fin m → Bool)
    (v : Fin n → Bool) (s : Bool) (hl : m + 1 + n = a + b)
    (hf : (if s then 1 else 0) + ones u + ones v = b) :
    integerWeight (firstTarget p u v s hl hf) =
      integerWeight (firstSource p u v s hl hf) + (if s then -(a : ℤ) else b) := by
  change chi u + chi (Fin.snoc v s) = chi (Fin.cons s u) + chi v + _
  have hli : (m : ℤ) + 1 + n = (a : ℤ) + b := by exact_mod_cast hl
  cases s
  · rw [(chi_boundaries u).2.2.1, (chi_boundaries v).2.2.2]
    simp only [Bool.false_eq_true, if_false, zero_add] at hf ⊢
    have hfi : (ones u : ℤ) + ones v = (b : ℤ) := by exact_mod_cast hf
    omega
  · rw [(chi_boundaries u).1, (chi_boundaries v).2.1]
    simp only [if_true] at hf ⊢
    have hfi : 1 + (ones u : ℤ) + ones v = (b : ℤ) := by exact_mod_cast hf
    omega

private theorem offset_injective {a b : ℕ} (p : Pos a b)
    {i j : ℕ} (hi : i < a + b + 2) (hj : j < a + b + 2)
    (he : p + (i : Pos a b) = p + (j : Pos a b)) : i = j := by
  have hh := congrArg ZMod.val (add_left_cancel he)
  simpa only [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] using hh

private theorem first_encode {a b m n : ℕ} (p : Pos a b) (u : Fin m → Bool)
    (v : Fin n → Bool) (s : Bool) (hl : m + 1 + n = a + b)
    (hf : (if s then 1 else 0) + ones u + ones v = b) :
    (encode (firstTarget p u v s hl hf)).1.1 =
      swapWord p (encode (firstSource p u v s hl hf)).1.1 := by
  let c := firstSource p u v s hl hf
  let d := firstTarget p u v s hl hf
  have hc := (marked_coordinates a b).2.2.2.1 c
  have hd := (marked_coordinates a b).2.2.2.1 d
  dsimp only [c, d, firstSource, firstTarget] at hc hd
  apply Subtype.ext
  funext r
  let i : ℕ := (r - p).val
  have hi : i < a + b + 2 := ZMod.val_lt _
  have hr : p + (i : Pos a b) = r := by
    dsimp [i]
    rw [ZMod.natCast_zmod_val]
    abel
  rw [← hr]
  change (encode d).1.1.1 (p + (i : Pos a b)) =
    (encode c).1.1.1 (Equiv.swap p (p + 1) (p + (i : Pos a b)))
  by_cases h0 : i = 0
  · rw [h0, Nat.cast_zero, add_zero, Equiv.swap_apply_left]
    have ht := hd.2.2.2 (Fin.last n)
    have hp : p + 1 + ((m + 2 + n : ℕ) : Pos a b) = p := by
      rw [add_assoc, show (1 : Pos a b) = ((1 : ℕ) : Pos a b) from rfl,
        ← Nat.cast_add, show 1 + (m + 2 + n) = a + b + 2 by omega,
        ZMod.natCast_self, add_zero]
    have hs := hc.2.2.1 (0 : Fin (m + 1))
    simp only [Fin.val_last, Fin.snoc_last, hp] at ht
    simp only [Fin.val_zero, zero_add, Nat.cast_one, Fin.cons_zero] at hs
    exact ht.trans hs.symm
  by_cases h1 : i = 1
  · rw [h1, Nat.cast_one, Equiv.swap_apply_right]
    exact hd.1.trans hc.1.symm
  have hn0 : p + (i : Pos a b) ≠ p := by
    intro he
    apply h0
    exact offset_injective p hi (by omega) (by simpa using he)
  have hn1 : p + (i : Pos a b) ≠ p + 1 := by
    intro he
    apply h1
    exact offset_injective p hi (by omega) (by simpa using he)
  rw [Equiv.swap_apply_of_ne_of_ne hn0 hn1]
  by_cases hm : i ≤ m + 1
  · let j : Fin m := ⟨i - 2, by omega⟩
    have ht := hd.2.2.1 j
    have hs := hc.2.2.1 j.succ
    have hp : p + 1 + ((j.val + 1 : ℕ) : Pos a b) = p + (i : Pos a b) := by
      rw [add_assoc, show (1 : Pos a b) = ((1 : ℕ) : Pos a b) from rfl,
        ← Nat.cast_add, show 1 + (j.val + 1) = i by dsimp [j]; omega]
    have hq : j.succ.val + 1 = i := by change i - 2 + 1 + 1 = i; omega
    rw [hp] at ht
    rw [hq] at hs
    simpa only [c, d, firstSource, firstTarget, Fin.cons_succ] using ht.trans hs.symm
  by_cases he : i = m + 2
  · rw [he]
    have hp : p + 1 + ((m + 1 : ℕ) : Pos a b) = p + ((m + 2 : ℕ) : Pos a b) := by
      rw [add_assoc, show (1 : Pos a b) = ((1 : ℕ) : Pos a b) from rfl,
        ← Nat.cast_add, show 1 + (m + 1) = m + 2 by omega]
    have ht := hd.2.1
    have hs := hc.2.1
    rw [hp] at ht
    have hq : m + 1 + 1 = m + 2 := by omega
    rw [hq] at hs
    exact ht.trans hs.symm
  · let j : Fin n := ⟨i - (m + 3), by omega⟩
    have ht := hd.2.2.2 j.castSucc
    have hs := hc.2.2.2 j
    have hp : p + 1 + ((m + 2 + j.val : ℕ) : Pos a b) = p + (i : Pos a b) := by
      rw [add_assoc, show (1 : Pos a b) = ((1 : ℕ) : Pos a b) from rfl,
        ← Nat.cast_add, show 1 + (m + 2 + j.val) = i by dsimp [j]; omega]
    have hq : m + 1 + 2 + j.val = i := by dsimp [j]; omega
    simp only [Fin.val_castSucc, Fin.snoc_castSucc] at ht
    rw [hp] at ht
    rw [hq] at hs
    exact ht.trans hs.symm

private theorem wall_move {a b : ℕ} (w : Word a b) (p : Pos a b) (s : Bool)
    (hp0 : w.1 p = wall) (hp1 : w.1 (p + 1) = if s then two else one) :
    wordWeight (swapWord p w) = wordWeight w + (if s then -(a : ℤ) else b) := by
  let x : MarkedWord a b := ⟨(w,p), hp0⟩
  let c := decode x
  have he : encode c = x := (marked_coordinates a b).2.1 x
  have hw : (encode c).1.1 = w := congrArg (fun y : MarkedWord a b => y.1.1) he
  have hc : c.p = p := congrArg (fun y : MarkedWord a b => y.1.2) he
  have lay := (marked_coordinates a b).2.2.2.1 c
  rcases c with ⟨q, m, n, u, v, hl, hf⟩
  dsimp only at hc
  subst q
  cases m with
  | zero =>
    have hs := lay.2.1
    simp only [Nat.zero_add, Nat.cast_one, hw] at hs
    cases s <;> simp_all [wall, one, two]
  | succ m =>
    have hs := lay.2.2.1 (0 : Fin (m + 1))
    simp only [Fin.val_zero, zero_add, Nat.cast_one, hw] at hs
    have hu : u 0 = s := by
      cases s <;> cases hh : u 0 <;> simp_all [one, two]
    have hu' : u = Fin.cons s (Fin.tail u) := by
      rw [← hu, Fin.cons_self_tail]
    have hf' : (if s then 1 else 0) + ones (Fin.tail u) + ones v = b := by
      rw [hu', ones_cons] at hf
      exact hf
    have hw' : (encode (firstSource p (Fin.tail u) v s hl hf')).1.1 = w := by
      simpa only [firstSource, ← hu'] using hw
    rw [← hw', ← first_encode p (Fin.tail u) v s hl hf', weight_eq, weight_eq]
    exact first_weight p (Fin.tail u) v s hl hf'

private theorem F1_move {a b : ℕ} (w : Word a b) (p : Pos a b)
    (hp : Allowed 0 w p) : wordWeight (swapWord p w) = wordWeight w - a := by
  simpa only [if_true, sub_eq_add_neg] using wall_move w p true hp.1 hp.2

private theorem F2_move {a b : ℕ} (w : Word a b) (p : Pos a b)
    (hp : Allowed 1 w p) : wordWeight (swapWord p w) = wordWeight w - b := by
  have hp0 : (swapWord p w).1 p = wall := by
    change w.1 (Equiv.swap p (p + 1) p) = wall
    rw [Equiv.swap_apply_left]
    exact hp.2
  have hp1 : (swapWord p w).1 (p + 1) = one := by
    change w.1 (Equiv.swap p (p + 1) (p + 1)) = one
    rw [Equiv.swap_apply_right]
    exact hp.1
  have hh := wall_move (swapWord p w) p false hp0 hp1
  have hi : swapWord p (swapWord p w) = w := by
    apply Subtype.ext
    funext r
    simp [swapWord, permute]
  rw [hi] at hh
  simpa only [Bool.false_eq_true, if_false] using (eq_sub_iff_add_eq.mpr hh.symm)

/-- The three oriented moves have exact integer weight drops a, b and two. -/
private theorem exact_weight_drops (a b : ℕ) :
    (∀ (w : Word a b) (p : Pos a b), Allowed 0 w p →
      wordWeight (swapWord p w) = wordWeight w - a) ∧
    (∀ (w : Word a b) (p : Pos a b), Allowed 1 w p →
      wordWeight (swapWord p w) = wordWeight w - b) ∧
    (∀ (w : Word a b) (p : Pos a b), Allowed 2 w p →
      wordWeight (swapWord p w) = wordWeight w - 2) :=
  ⟨F1_move, F2_move, F3_move⟩


private theorem F_map (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (i : Fin 3) (s : ℤ) :
    (weightLE (h K a b) s).map (F K a b i) ≤ weightLE (h K a b) (s - 2) := by
  classical
  rw [weightLE_eq_supported, weightLE_eq_supported, Finsupp.supported_eq_span_single]
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  rintro _ ⟨w, hw, rfl⟩
  change F K a b i (delta K w) ∈
    Finsupp.supported K K {v : Word a b | wordWeight v ≤ s - 2}
  rw [(cyclic_action K a b).2.2.2.1]
  apply Submodule.sum_mem
  intro p _
  by_cases hp : Allowed i w p
  · rw [bond, if_pos hp]
    apply Finsupp.single_mem_supported K 1
    change wordWeight (swapWord p w) ≤ s - 2
    have hd := exact_weight_drops a b
    fin_cases i
    · rw [hd.1 w p hp]
      change wordWeight w ≤ s at hw
      omega
    · rw [hd.2.1 w p hp]
      change wordWeight w ≤ s at hw
      omega
    · rw [hd.2.2 w p hp]
      change wordWeight w ≤ s at hw
      omega
  · rw [bond, if_neg hp]
    exact Submodule.zero_mem _

private theorem T_map (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (ξ : Fin 3 → K) (s : ℤ) :
    (weightLE (h K a b) s).map (T K a b ξ) ≤ weightLE (h K a b) (s - 2) := by
  apply Submodule.map_le_iff_le_comap.mpr
  intro x hx
  change T K a b ξ x ∈ weightLE (h K a b) (s - 2)
  simp only [T, LinearMap.add_apply, LinearMap.smul_apply]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (F_map K a b ha hb 0 s (Submodule.mem_map_of_mem hx))
    · exact Submodule.smul_mem _ _ (F_map K a b ha hb 1 s (Submodule.mem_map_of_mem hx))
  · exact Submodule.smul_mem _ _ (F_map K a b ha hb 2 s (Submodule.mem_map_of_mem hx))

/-- Exact local drops give strict filtration descent and the uniform nilpotence exponent. -/
theorem weight_control (a b : ℕ) :
    (∀ (w : Word a b) (p : Pos a b), Allowed 0 w p →
      wordWeight (swapWord p w) = wordWeight w - a) ∧
    (∀ (w : Word a b) (p : Pos a b), Allowed 1 w p →
      wordWeight (swapWord p w) = wordWeight w - b) ∧
    (∀ (w : Word a b) (p : Pos a b), Allowed 2 w p →
      wordWeight (swapWord p w) = wordWeight w - 2) ∧
    (2 ≤ a → 2 ≤ b →
      (∀ (i : Fin 3) (s : ℤ), (weightLE (h K a b) s).map (F K a b i) ≤
        weightLE (h K a b) (s - 2)) ∧
      (∀ (ξ : Fin 3 → K) (s : ℤ), (weightLE (h K a b) s).map (T K a b ξ) ≤
        weightLE (h K a b) (s - 2)) ∧
      (∀ ξ : Fin 3 → K, T K a b ξ ^ (a * b + 1) = 0)) ∧
    F3 K a b ^ (a * b + 1) = 0 := by
  have hd := exact_weight_drops a b
  refine ⟨hd.1, hd.2.1, hd.2.2, ?_, (F3_weight_control K a b).2.2⟩
  intro ha hb
  exact ⟨F_map K a b ha hb, T_map K a b ha hb,
    fun ξ => nilpotent_of_filtration K a b _ (T_map K a b ha hb ξ)⟩

#print axioms weight_control

end D5.S3.Quantum.SpinChains.TwoWallWeights
