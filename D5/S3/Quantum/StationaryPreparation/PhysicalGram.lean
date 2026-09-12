/- GID: D5/S3/Quantum/StationaryPreparation/PhysicalGram
   generality: G
   mirror-B: D5/B/S3/Quantum/StationaryPreparation/PhysicalGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact fixed-isometry stationary preparation yields residuals, Gram formulas, and rank bounds. -/

import D5.S3.Quantum.StationaryPreparation.PhysicalResiduals
import D5.S3.Quantum.Algebra.StationaryGramRank
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators TensorProduct ComplexOrder

namespace D5.S3.Quantum.StationaryPreparation.PhysicalGram
open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit
open D5.S3.Quantum.Entanglement.OccupancyWordSectors

universe u v

variable {σ : Type u} [Fintype σ] [DecidableEq σ] [Nonempty σ]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]
def ResidualEvolution (a : σ → ℕ)
    (V : H →ₗᵢ[ℂ] (EuclideanSpace ℂ σ ⊗[ℂ] H)) (φ : Box a → H) : Prop :=
  ∀ (r : Box a) (w : List σ), w.length ≤ mass (values r) →
    wordOp V w (φ r) =
      if (∀ i, w.count i ≤ (r i).val) then
        realSqrt ((M (values (sub r (counts w))) : ℝ) /
          (M (values r) : ℝ)) • φ (sub r (counts w))
      else 0

def G (a : σ → ℕ) (φ : Box a → H) : Matrix (Box a) (Box a) ℂ := Matrix.gram ℂ φ

def z (a : σ → ℕ) (f : H) (φ : Box a → H) (d : Box a) : ℂ := inner ℂ (φ d) f

def D (a : σ → ℕ) : Matrix (Box a) (Box a) ℂ :=
  Matrix.diagonal (fun r => realSqrt (M (values r) : ℝ))

def Dinv (a : σ → ℕ) : Matrix (Box a) (Box a) ℂ :=
  Matrix.diagonal (fun r => (realSqrt (M (values r) : ℝ))⁻¹)

def B (a : σ → ℕ) (φ : Box a → H) : Matrix (Box a) (Box a) ℂ :=
  D a * G a φ * D a

structure NormalizedGram (a : σ → ℕ) (f : H) (φ : Box a → H) : Prop where
  comparable : ∀ r s : Box a, (∀ i, (s i).val ≤ (r i).val) →
    G a φ r s =
      realSqrt (((M (values s) : ℝ) * (M (values (sub r (values s))) : ℝ)) /
        (M (values r) : ℝ)) * z a f φ (sub r (values s))
  reverse : ∀ r s : Box a, (∀ i, (r i).val ≤ (s i).val) →
    G a φ r s =
      realSqrt (((M (values r) : ℝ) * (M (values (sub s (values r))) : ℝ)) /
        (M (values s) : ℝ)) * star (z a f φ (sub s (values r)))
  incomparable : ∀ r s : Box a,
    (¬ ∀ i, (s i).val ≤ (r i).val) →
    (¬ ∀ i, (r i).val ≤ (s i).val) → G a φ r s = 0
  hermitian : (G a φ).IsHermitian
  diagonal : ∀ r : Box a, G a φ r r = 1
  moment_zero : z a f φ 0 = 1
  positive : (G a φ).PosSemidef
  rank_le_memory : (G a φ).rank ≤ Module.finrank ℂ H
  diagonal_inverse : D a * Dinv a = 1 ∧ Dinv a * D a = 1
  scaled_actual : B a φ = Matrix.gram ℂ
    (fun r => realSqrt (M (values r) : ℝ) • φ r)
  scaled_positive : (B a φ).PosSemidef
  scaled_zero : B a φ 0 0 = 1
  scaled_rank : (B a φ).rank = (G a φ).rank
  recurrence : ∀ r s : Box a, r ≠ 0 → s ≠ 0 →
    B a φ r s = ∑ i, if 0 < (r i).val ∧ 0 < (s i).val
      then B a φ (lower r i) (lower s i) else 0
  lower_bound : (∏ i, (a i + 1)) - Finset.univ.sup a ≤ (G a φ).rank
  zero_capacity : (∀ i, a i = 0) →
    G a φ = 1 ∧ (G a φ).rank = 1 ∧ 1 ≤ Module.finrank ℂ H

theorem residual_word_formula
    (a : σ → ℕ)
    (V : H →ₗᵢ[ℂ] (EuclideanSpace ℂ σ ⊗[ℂ] H))
    (φ : Box a → H) (hstep : Step a V φ) :
    ResidualEvolution a V φ := by
  classical
  have profile_count (b : σ → ℕ) (i : σ) : (profile b).count i = b i := by
    simp [profile, Multiset.count_sum', Multiset.count_replicate]
  have M_eq_multiplicity (b : σ → ℕ) :
      M b = D5.S3.Quantum.Entanglement.OccupancyWordSectors.multiplicity
        (mass b) (profile b) := by
    rw [D5.S3.Quantum.Entanglement.OccupancyWordSectors.multiplicity_eq_factorial
        (profile b) (by simp [profile, mass])]
    simp only [profile_count]
    rfl
  have profile_lower_erase (b : σ → ℕ) (i : σ) (hi : 0 < b i) :
      profile (Function.update b i (b i - 1)) = (profile b).erase i := by
    apply Multiset.ext.mpr
    intro j
    rw [profile_count]
    by_cases hji : j = i
    · subst j
      rw [Multiset.count_erase_self]
      rw [profile_count]
      simp [Function.update]
    · rw [Multiset.count_erase_of_ne]
      · simpa [Function.update, hji] using (profile_count b j).symm
      · exact hji
  have mass_lower {a : σ → ℕ} (r : Box a) (i : σ) (hi : 0 < (r i).val) :
      mass (values (lower r i)) = mass (values r) - 1 := by
    have hb : values (lower r i) = Function.update (values r) i ((values r) i - 1) := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [values, lower, sub, Function.update]
      · simp [values, lower, sub, Function.update, hji]
    have hprof := profile_lower_erase (values r) i hi
    rw [← hb] at hprof
    have hmem : i ∈ profile (values r) := by
      rw [← Multiset.count_pos, profile_count]
      exact hi
    have hcL : (profile (values (lower r i))).card =
        mass (values (lower r i)) := by simp [profile, mass]
    have hcR : (profile (values r)).card = mass (values r) := by simp [profile, mass]
    calc
      mass (values (lower r i)) = (profile (values (lower r i))).card := hcL.symm
      _ = ((profile (values r)).erase i).card := by rw [hprof]
      _ = (profile (values r)).card - 1 := Multiset.card_erase_of_mem hmem
      _ = mass (values r) - 1 := by rw [hcR]
  have M_lower_recurrence {a : σ → ℕ} (r : Box a) (i : σ) (hi : 0 < (r i).val) :
      mass (values r) * M (values (lower r i)) = (r i).val * M (values r) := by
    have hb : values (lower r i) = Function.update (values r) i ((r i).val - 1) := by
      funext j
      by_cases hj : j = i
      · subst j
        simp [values, lower, sub, Function.update]
      · simp [values, lower, sub, Function.update, hj]
    have hp : profile (values (lower r i)) = (profile (values r)).erase i := by
      rw [hb]
      exact profile_lower_erase (values r) i hi
    have hle : (r i).val ≤ mass (values r) := by
      change values r i ≤ ∑ j, values r j
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hm : 0 < mass (values r) := hi.trans_le hle
    have hmem : i ∈ profile (values r) := by
      rw [← Multiset.count_pos, profile_count]
      exact hi
    have hcard : (profile (values r)).card = mass (values r) := by simp [profile, mass]
    have hrec := multiplicity_erase_mul (a := profile (values r))
      (n := mass (values r) - 1) (by omega) i hmem
    rw [Nat.sub_add_cancel hm, profile_count] at hrec
    rw [M_eq_multiplicity, M_eq_multiplicity, mass_lower r i hi, hp]
    exact hrec
  have mass_pos_of_ne_zero {a : σ → ℕ} (r : Box a) (hr : r ≠ 0) : 0 < mass (values r) := by
    classical
    by_contra h
    have hz : mass (values r) = 0 := Nat.eq_zero_of_not_pos h
    have hall : ∀ i, (r i).val = 0 := by
      intro i
      have hi : (r i).val ≤ mass (values r) := by
        change (values r) i ≤ ∑ j, (values r) j
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    apply hr
    funext i
    apply Fin.ext
    exact hall i
  have realSqrt_mul_ratio {A R L q m : ℕ} (hA : 0 < A) (hR : 0 < R)
      (hL : 0 < L) (hm : 0 < m) (hq : 0 < q) (hrel : m * L = q * R) :
      realSqrt ((q : ℝ) / m) * realSqrt ((A : ℝ) / L) =
        realSqrt ((A : ℝ) / R) := by
    dsimp [realSqrt]
    norm_cast
    rw [← Real.sqrt_mul (by positivity : 0 ≤ (q : ℝ) / m)]
    congr 1
    field_simp
    exact_mod_cast hrel.symm
  have sub_lower_counts {a : σ → ℕ} (r : Box a) (i : σ) (w : List σ)
      (hlegal : ∀ j, counts (i :: w) j ≤ (r j).val) :
      sub (lower r i) (counts w) = sub r (counts (i :: w)) := by
    funext j
    apply Fin.ext
    by_cases hji : j = i
    · subst j
      have hri : 0 < (r i).val := by
        have := hlegal i
        simp [counts] at this
        omega
      simp only [sub, lower]
      change (r i).val - 1 - counts w i = (r i).val - counts (i :: w) i
      simp [counts] at hlegal ⊢
      omega
    · simp only [sub, lower]
      have hj := hlegal j
      have hji' : i ≠ j := Ne.symm hji
      simp [counts, hji, hji'] at hj ⊢
  have M_pos (b : σ → ℕ) : 0 < M b := by
    rw [M_eq_multiplicity]
    exact D5.S3.Quantum.Entanglement.OccupancyWordSectors.multiplicity_pos
      (profile b) (by simp [profile, mass])
  have realSqrt_self_ratio {n : ℕ} (hn : 0 < n) :
      realSqrt ((n : ℝ) / n) = 1 := by
    dsimp [realSqrt]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    rw [div_self hn', Real.sqrt_one]
    norm_num
  have scalar_step {A : ℕ} {a : σ → ℕ} (r : Box a) (i : σ)
      (hA : 0 < A) (hi : 0 < (r i).val) :
      realSqrt (((r i).val : ℝ) / (mass (values r) : ℝ)) *
          realSqrt ((A : ℝ) / (M (values (lower r i)) : ℝ)) =
        realSqrt ((A : ℝ) / (M (values r) : ℝ)) := by
    have hmpos : 0 < mass (values r) := by
      have hle : (r i).val ≤ mass (values r) := by
        change (values r) i ≤ ∑ j, (values r) j
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ i)
      omega
    apply realSqrt_mul_ratio hA (M_pos (values r))
      (M_pos (values (lower r i))) hmpos hi
    exact M_lower_recurrence r i hi
  have wordOp_smul (V : H →ₗᵢ[ℂ] (EuclideanSpace ℂ σ ⊗[ℂ] H))
      (w : List σ) (c : ℂ) (x : H) :
      wordOp V w (c • x) = c • wordOp V w x := by
    induction w generalizing x with
    | nil => rfl
    | cons i w ih =>
        simp [wordOp, letter, ih]
  intro r w hw
  induction w generalizing r with
  | nil =>
      have hm : 0 < M (values r) := M_pos (values r)
      have hratio : realSqrt ((M (values r) : ℝ) / (M (values r) : ℝ)) = 1 :=
        realSqrt_self_ratio hm
      have hsub : sub r (counts []) = r := by
        funext j
        apply Fin.ext
        simp [sub, counts]
      rw [hsub]
      simp [wordOp, hratio]
  | cons i w ih =>
      by_cases hlegal : ∀ j, counts (i :: w) j ≤ (r j).val
      · have hri : 0 < (r i).val := by
          have h := hlegal i
          have hc : 0 < counts (i :: w) i := by simp [counts]
          exact lt_of_lt_of_le hc h
        have hr0 : r ≠ 0 := by
          intro hr
          subst r
          simp at hri
        have hmass : mass (values r) = mass (values (lower r i)) + 1 := by
          rw [mass_lower r i hri]
          have hmpos := mass_pos_of_ne_zero r hr0
          omega
        have htail : w.length ≤ mass (values (lower r i)) := by
          have := hw
          simp only [List.length_cons] at this
          omega
        have htail_ok : ∀ j, counts w j ≤ (lower r i j).val := by
          intro j
          by_cases hji : j = i
          · subst j
            have hh := hlegal i
            simp [counts, lower, sub] at hh ⊢
            omega
          · have hh := hlegal j
            simp [counts, lower, sub, hji, Ne.symm hji] at hh ⊢
            omega
        rw [wordOp, hstep r hr0 i, if_pos hri]
        rw [wordOp_smul]
        rw [ih (lower r i) htail]
        have htail_ok' : ∀ j, List.count j w ≤ (lower r i j).val := by
          simpa [counts] using htail_ok
        rw [if_pos htail_ok']
        rw [sub_lower_counts r i w hlegal]
        have hlegal' : ∀ j, List.count j (i :: w) ≤ (r j).val := by
          simpa [counts] using hlegal
        rw [if_pos hlegal']
        rw [smul_smul]
        apply congrArg (fun c : ℂ => c • φ (sub r (counts (i :: w))))
        apply scalar_step r i (M_pos (values (sub r (counts (i :: w))))) hri
      · have hr0 : r ≠ 0 := by
          intro hr
          subst r
          have : 0 < (i :: w).length := by simp
          have hm0 : mass (values (0 : Box a)) = 0 := by simp [mass, values]
          omega
        by_cases hri : 0 < (r i).val
        · have htail : w.length ≤ mass (values (lower r i)) := by
            have hm := mass_lower r i hri
            have hw' := hw
            simp only [List.length_cons] at hw'
            omega
          have htail_bad : ¬ ∀ j, counts w j ≤ (lower r i j).val := by
            intro ht
            apply hlegal
            intro j
            by_cases hji : j = i
            · subst j
              have hh := ht i
              simp [counts, lower, sub] at hh ⊢
              omega
            · have hh := ht j
              simp [counts, lower, sub, hji, Ne.symm hji] at hh ⊢
              omega
          rw [wordOp, hstep r hr0 i, if_pos hri, wordOp_smul]
          have htail_bad' : ¬ ∀ j, List.count j w ≤ (lower r i j).val := by
            simpa [counts] using htail_bad
          have hlegal' : ¬ ∀ j, List.count j (i :: w) ≤ (r j).val := by
            simpa [counts] using hlegal
          rw [ih (lower r i) htail, if_neg htail_bad']
          rw [if_neg hlegal']
          simp
        · rw [wordOp, hstep r hr0 i, if_neg hri]
          have hlegal' : ¬ ∀ j, List.count j (i :: w) ≤ (r j).val := by
            simpa [counts] using hlegal
          rw [if_neg hlegal']
          simpa using (wordOp_smul V w (0 : ℂ) (0 : H))

theorem stationary_normalized_gram
    (a : σ → ℕ)
    (V : H →ₗᵢ[ℂ] (EuclideanSpace ℂ σ ⊗[ℂ] H))
    (f : H) (φ : Box a → H)
    (hunit : ∀ r : Box a, ‖φ r‖ = 1)
    (hzero : φ 0 = f) (hstep : Step a V φ) :
    NormalizedGram a f φ := by
  classical
  have profile_count (b : σ → ℕ) (i : σ) : (profile b).count i = b i := by
    simp [profile, Multiset.count_sum', Multiset.count_replicate]
  have list_len_mass_counts (l : List σ) : l.length = mass (counts l) := by
    simpa [mass, counts] using
      (Multiset.sum_count_eq_card (m := (l : Multiset σ))
        (fun _ _ => Finset.mem_univ _)).symm
  have box_le (a : σ → ℕ) (r : Box a) (i : σ) : (r i).val ≤ a i := Nat.le_of_lt_succ (r i).isLt
  have continuation_inner (V : H →ₗᵢ[ℂ] (EuclideanSpace ℂ σ ⊗[ℂ] H))
      (n : ℕ) (x y : H) :
      inner ℂ x y = ∑ w : Fin n → σ,
        inner ℂ (wordOp V (List.ofFn w) x) (wordOp V (List.ofFn w) y) := by
    induction n generalizing x y with
    | zero => simp [wordOp]
    | succ n ih =>
      have hls : inner ℂ x y = ∑ i, inner ℂ (letter V i x) (letter V i y) := by
        rw [← V.inner_map_map x y, ← tensorCoordinates.inner_map_map]
        simp only [PiLp.inner_apply]
        rfl
      calc
        inner ℂ x y = ∑ i, inner ℂ (letter V i x) (letter V i y) := hls
        _ = ∑ i, ∑ w : Fin n → σ,
            inner ℂ (wordOp V (List.ofFn w) (letter V i x))
              (wordOp V (List.ofFn w) (letter V i y)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact ih _ _
        _ = ∑ w : Fin (n+1) → σ,
            inner ℂ (wordOp V (List.ofFn w) x) (wordOp V (List.ofFn w) y) := by
          let F : σ × (Fin n → σ) → ℂ := fun p =>
            inner ℂ (wordOp V (List.ofFn p.2) (letter V p.1 x))
              (wordOp V (List.ofFn p.2) (letter V p.1 y))
          have hprod : (∑ p : σ × (Fin n → σ), F p) =
              ∑ i : σ, ∑ w : Fin n → σ, F (i, w) := by
            simpa only [Finset.univ_product_univ] using
              (Finset.sum_product (Finset.univ : Finset σ)
                (Finset.univ : Finset (Fin n → σ)) F)
          rw [← hprod]
          rw [← (Fin.consEquiv (fun _ : Fin (n+1) => σ)).sum_comp]
          apply Finset.sum_congr rfl
          intro p hp
          rcases p with ⟨i, w⟩
          change inner ℂ (wordOp V (List.ofFn w) (letter V i x))
              (wordOp V (List.ofFn w) (letter V i y)) =
            inner ℂ (wordOp V (List.ofFn (Fin.cons i w)) x)
              (wordOp V (List.ofFn (Fin.cons i w)) y)
          rw [show List.ofFn (Fin.cons i w) = i :: List.ofFn w by simp]
          simp only [wordOp]
  have M_eq_multiplicity (b : σ → ℕ) :
      M b = D5.S3.Quantum.Entanglement.OccupancyWordSectors.multiplicity
        (mass b) (profile b) := by
    rw [D5.S3.Quantum.Entanglement.OccupancyWordSectors.multiplicity_eq_factorial
        (profile b) (by simp [profile, mass])]
    simp only [profile_count]
    rfl
  have profile_lower_erase (b : σ → ℕ) (i : σ) (hi : 0 < b i) :
      profile (Function.update b i (b i - 1)) = (profile b).erase i := by
    apply Multiset.ext.mpr
    intro j
    rw [profile_count]
    by_cases hji : j = i
    · subst j
      rw [Multiset.count_erase_self]
      rw [profile_count]
      simp [Function.update]
    · rw [Multiset.count_erase_of_ne]
      · simpa [Function.update, hji] using (profile_count b j).symm
      · exact hji
  have mass_lower {a : σ → ℕ} (r : Box a) (i : σ) (hi : 0 < (r i).val) :
      mass (values (lower r i)) = mass (values r) - 1 := by
    have hb : values (lower r i) = Function.update (values r) i ((values r) i - 1) := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [values, lower, sub, Function.update]
      · simp [values, lower, sub, Function.update, hji]
    have hprof := profile_lower_erase (values r) i hi
    rw [← hb] at hprof
    have hmem : i ∈ profile (values r) := by
      rw [← Multiset.count_pos, profile_count]
      exact hi
    have hcL : (profile (values (lower r i))).card =
        mass (values (lower r i)) := by simp [profile, mass]
    have hcR : (profile (values r)).card = mass (values r) := by simp [profile, mass]
    calc
      mass (values (lower r i)) = (profile (values (lower r i))).card := hcL.symm
      _ = ((profile (values r)).erase i).card := by rw [hprof]
      _ = (profile (values r)).card - 1 := Multiset.card_erase_of_mem hmem
      _ = mass (values r) - 1 := by rw [hcR]
  have M_lower_recurrence {a : σ → ℕ} (r : Box a) (i : σ) (hi : 0 < (r i).val) :
      mass (values r) * M (values (lower r i)) = (r i).val * M (values r) := by
    have hb : values (lower r i) = Function.update (values r) i ((r i).val - 1) := by
      funext j
      by_cases hj : j = i
      · subst j
        simp [values, lower, sub, Function.update]
      · simp [values, lower, sub, Function.update, hj]
    have hp : profile (values (lower r i)) = (profile (values r)).erase i := by
      rw [hb]
      exact profile_lower_erase (values r) i hi
    have hle : (r i).val ≤ mass (values r) := by
      change values r i ≤ ∑ j, values r j
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hm : 0 < mass (values r) := hi.trans_le hle
    have hmem : i ∈ profile (values r) := by
      rw [← Multiset.count_pos, profile_count]
      exact hi
    have hcard : (profile (values r)).card = mass (values r) := by simp [profile, mass]
    have hrec := multiplicity_erase_mul (a := profile (values r))
      (n := mass (values r) - 1) (by omega) i hmem
    rw [Nat.sub_add_cancel hm, profile_count] at hrec
    rw [M_eq_multiplicity, M_eq_multiplicity, mass_lower r i hi, hp]
    exact hrec
  have mass_pos_of_ne_zero {a : σ → ℕ} (r : Box a) (hr : r ≠ 0) : 0 < mass (values r) := by
    classical
    by_contra h
    have hz : mass (values r) = 0 := Nat.eq_zero_of_not_pos h
    have hall : ∀ i, (r i).val = 0 := by
      intro i
      have hi : (r i).val ≤ mass (values r) := by
        change (values r) i ≤ ∑ j, (values r) j
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    apply hr
    funext i
    apply Fin.ext
    exact hall i
  have M_pos (b : σ → ℕ) : 0 < M b := by
    rw [M_eq_multiplicity]
    exact D5.S3.Quantum.Entanglement.OccupancyWordSectors.multiplicity_pos
      (profile b) (by simp [profile, mass])
  have M_zero {a : σ → ℕ} : M (values (0 : Box a)) = 1 := by
    simp [M, values, mass]
  classical
  have hevolve := residual_word_formula a V φ hstep
  have hcard (b : σ → ℕ) :
      (Finset.univ.filter (fun w : Fin (mass b) → σ =>
        counts (List.ofFn w) = b)).card = M b := by
    rw [M_eq_multiplicity]
    congr 1
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, sectorWords]
    constructor
    · intro hw
      apply Multiset.ext.mpr
      intro i
      simpa [occupation, profile_count, counts] using congrFun hw i
    · intro hw
      funext i
      simpa [occupation, profile_count, counts] using congrArg (Multiset.count i) hw
  have hshort (r s : Box a) (hlen : mass (values s) ≤ mass (values r)) :
      G a φ r s =
        if (∀ i, (s i).val ≤ (r i).val) then
          realSqrt (((M (values s) : ℝ) * (M (values (sub r (values s))) : ℝ)) /
            (M (values r) : ℝ)) * z a f φ (sub r (values s)) else 0 := by
    rw [G, Matrix.gram_apply, continuation_inner V (mass (values s))]
    have hterm (w : Fin (mass (values s)) → σ) :
        inner ℂ (wordOp V (List.ofFn w) (φ r)) (wordOp V (List.ofFn w) (φ s)) =
          if counts (List.ofFn w) = values s then
            if (∀ i, (s i).val ≤ (r i).val) then
              (realSqrt ((M (values (sub r (values s))) : ℝ) / M (values r)) *
                realSqrt (1 / (M (values s) : ℝ))) * z a f φ (sub r (values s))
            else 0
          else 0 := by
      have hwlen : (List.ofFn w).length = mass (values s) := List.length_ofFn
      rw [hevolve r _ (hwlen.le.trans hlen), hevolve s _ hwlen.le]
      by_cases hc : counts (List.ofFn w) = values s
      · have hs : ∀ i, (List.ofFn w).count i ≤ (s i).val := by
          intro i
          exact (congrFun hc i).le
        have hss : sub s (values s) = 0 := by
          funext i
          apply Fin.ext
          simp [sub, values]
        rw [if_pos hs]
        change inner ℂ
          (if (∀ i, counts (List.ofFn w) i ≤ (r i).val) then _ else _)
          (realSqrt ((M (values (sub s (counts (List.ofFn w)))) : ℝ) /
            M (values s)) • φ (sub s (counts (List.ofFn w)))) = _
        rw [hc, hss, M_zero, hzero, if_pos rfl]
        by_cases hrs : ∀ i, (s i).val ≤ (r i).val
        · have hvr : ∀ i, values s i ≤ (r i).val := hrs
          rw [if_pos hvr, if_pos hrs, inner_smul_left, inner_smul_right]
          simp only [Nat.cast_one, realSqrt, Complex.conj_ofReal, z]
          ring
        · have hvr : ¬ ∀ i, values s i ≤ (r i).val := hrs
          rw [if_neg hvr, if_neg hrs, inner_zero_left]
      · have hs : ¬ ∀ i, (List.ofFn w).count i ≤ (s i).val := by
          intro hs
          apply hc
          have hsum : (∑ i, (List.ofFn w).count i) = ∑ i, (s i).val := by
            exact (list_len_mass_counts (List.ofFn w)).symm.trans hwlen
          funext i
          exact Finset.sum_eq_sum_iff_of_le (fun j _ => hs j) |>.mp hsum i (Finset.mem_univ i)
        simp [if_neg hs, hc]
    simp_rw [hterm]
    rw [← Finset.sum_filter, Finset.sum_const, hcard]
    by_cases hrs : ∀ i, (s i).val ≤ (r i).val
    · rw [if_pos hrs, if_pos hrs, nsmul_eq_mul, ← mul_assoc]
      congr 1
      have hreal : (M (values s) : ℝ) *
          (Real.sqrt ((M (values (sub r (values s))) : ℝ) / M (values r)) *
            Real.sqrt (1 / (M (values s) : ℝ))) =
          Real.sqrt (((M (values s) : ℝ) * M (values (sub r (values s)))) /
            M (values r)) := by
        rw [Real.sqrt_div (Nat.cast_nonneg _), Real.sqrt_div zero_le_one, Real.sqrt_one,
          Real.sqrt_div (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),
          Real.sqrt_mul (Nat.cast_nonneg _)]
        calc
          _ = ((M (values s) : ℝ) / Real.sqrt (M (values s) : ℝ)) *
              Real.sqrt (M (values (sub r (values s))) : ℝ) /
                Real.sqrt (M (values r) : ℝ) := by ring
          _ = _ := by rw [Real.div_sqrt]
      simpa only [realSqrt, Complex.ofReal_mul, Complex.ofReal_natCast] using
        congrArg Complex.ofReal hreal
    · rw [if_neg hrs, if_neg hrs, nsmul_zero]
  have hcomparable (r s : Box a) (hrs : ∀ i, (s i).val ≤ (r i).val) :=
    hshort r s (Finset.sum_le_sum (fun i _ => hrs i))
  have hdiag (r : Box a) : G a φ r r = 1 := by
    simp [G, Matrix.gram_apply, inner_self_eq_norm_sq_to_K, hunit]
  have hupper : (G a φ).rank ≤ Module.finrank ℂ H := by
    rw [G, Matrix.gram_eq_conjTranspose_mul (stdOrthonormalBasis ℂ H) φ]
    exact le_trans (Matrix.rank_mul_le_right _ _)
      (by simpa using (Matrix.rank_le_card_height
        (Matrix.of fun i r => ((stdOrthonormalBasis ℂ H).repr (φ r)).ofLp i)))
  have hDne (r : Box a) : realSqrt (M (values r) : ℝ) ≠ 0 := by
    dsimp [realSqrt]
    have hp : (0 : ℝ) < (M (values r) : ℝ) := by exact_mod_cast M_pos (values r)
    exact_mod_cast (Real.sqrt_pos.2 hp).ne'
  have hDdet : (D a).det ≠ 0 := by
    rw [D, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun r _ => hDne r)
  have hscaled : B a φ = Matrix.gram ℂ
      (fun r => realSqrt (M (values r) : ℝ) • φ r) := by
    ext r s
    simp only [B, D, G, Matrix.gram_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      inner_smul_left, inner_smul_right, realSqrt, Complex.conj_ofReal]
    ring
  have hpositive : (B a φ).PosSemidef := by
    rw [hscaled]
    exact Matrix.posSemidef_gram ℂ _
  have h00 : B a φ 0 0 = 1 := by
    simp only [B, D, Matrix.diagonal_mul, Matrix.mul_diagonal, M_zero, realSqrt,
      Nat.cast_one, Real.sqrt_one, Complex.ofReal_one, one_mul, mul_one]
    exact hdiag 0
  have hrank : (B a φ).rank = (G a φ).rank := by
    calc
      (B a φ).rank = (D a * G a φ).rank :=
        Matrix.rank_mul_eq_left_of_det_ne_zero (D a) (D a * G a φ) hDdet
      _ = (G a φ).rank :=
        Matrix.rank_mul_eq_right_of_det_ne_zero (D a) (G a φ) hDdet
  have hscaled_step (r : Box a) (hr : r ≠ 0) (i : σ) :
      letter V i (realSqrt (M (values r) : ℝ) • φ r) =
        if 0 < (r i).val then realSqrt (M (values (lower r i)) : ℝ) • φ (lower r i)
        else 0 := by
    rw [show letter V i (realSqrt (M (values r) : ℝ) • φ r) =
      realSqrt (M (values r) : ℝ) • letter V i (φ r) by simp [letter]]
    rw [hstep r hr i]
    by_cases hi : 0 < (r i).val
    · rw [if_pos hi, if_pos hi, smul_smul]
      congr 1
      have hm : (mass (values r) : ℝ) ≠ 0 := by
        exact_mod_cast (mass_pos_of_ne_zero r hr).ne'
      have hrel := M_lower_recurrence r i hi
      have heq : (M (values r) : ℝ) * ((r i).val / (mass (values r) : ℝ)) =
          M (values (lower r i)) := by
        rw [← mul_div_assoc]
        apply (div_eq_iff hm).mpr
        exact_mod_cast (by simpa [mul_comm] using hrel.symm)
      dsimp [realSqrt]
      rw [← Complex.ofReal_mul, ← Real.sqrt_mul (Nat.cast_nonneg _), heq]
    · simp [hi]
  have hrec : ∀ r s : Box a, r ≠ 0 → s ≠ 0 →
      B a φ r s = ∑ i, if 0 < (r i).val ∧ 0 < (s i).val
        then B a φ (lower r i) (lower s i) else 0 := by
    intro r s hr hs
    rw [hscaled, Matrix.gram_apply, ← V.inner_map_map,
      ← tensorCoordinates.inner_map_map, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    change inner ℂ (letter V i _) (letter V i _) = _
    rw [hscaled_step r hr i, hscaled_step s hs i]
    by_cases hi : 0 < (r i).val <;> by_cases hj : 0 < (s i).val <;>
      simp [hi, hj, Matrix.gram_apply]
  have hlower := D5.S3.Quantum.Algebra.StationaryGramRank.stationary_gram_rank_lower_bound
    a (B a φ) hpositive h00 (by
      intro r s hr hs
      rw [hrec r s hr hs]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs with hi
      · apply congrArg₂ (B a φ)
        · funext j
          apply Fin.ext
          dsimp only [lower, sub]
          split_ifs <;> rfl
        · funext j
          apply Fin.ext
          dsimp only [lower, sub]
          split_ifs <;> rfl
      · rfl)
  have rank_instance (I J : Fintype (Box a)) :
      @Matrix.rank (Box a) (Box a) ℂ I inferInstance (B a φ) =
        @Matrix.rank (Box a) (Box a) ℂ J inferInstance (B a φ) :=
    congrArg (fun K => @Matrix.rank (Box a) (Box a) ℂ K inferInstance (B a φ))
      (Subsingleton.elim I J)
  have hlowerG : (∏ i, (a i + 1)) - Finset.univ.sup a ≤ (G a φ).rank :=
    hlower.trans_eq ((rank_instance _ _).trans hrank)
  refine ⟨?_, ?_, ?_, Matrix.isHermitian_gram ℂ φ, hdiag, ?_,
    Matrix.posSemidef_gram ℂ φ, hupper, ?_, hscaled, hpositive, h00, hrank,
    hrec, hlowerG, ?_⟩
  · intro r s hrs
    have h := hcomparable r s hrs
    rw [if_pos hrs] at h
    exact h
  · intro r s hrs
    have h := hcomparable s r hrs
    rw [if_pos hrs] at h
    change inner ℂ (φ r) (φ s) = _
    rw [← inner_conj_symm (𝕜 := ℂ) (φ r) (φ s)]
    change star (G a φ s r) = _
    rw [h]
    simp [realSqrt]
  · intro r s hrs hsr
    rcases le_total (mass (values s)) (mass (values r)) with hlen | hlen
    · have h := hshort r s hlen
      rw [if_neg hrs] at h
      exact h
    · have h : G a φ s r = 0 := by
        have h := hshort s r hlen
        rw [if_neg hsr] at h
        exact h
      change inner ℂ (φ r) (φ s) = 0
      rw [← inner_conj_symm (𝕜 := ℂ) (φ r) (φ s)]
      change star (G a φ s r) = 0
      rw [h, star_zero]
  · simpa [z, ← hzero, G] using hdiag 0
  · constructor <;> ext r s <;> by_cases hrs : r = s <;>
      simp [D, Dinv, Matrix.mul_diagonal, Matrix.one_apply, hrs, hDne]
  · intro ha
    have hall (r : Box a) : r = 0 := by
      funext i
      apply Fin.ext
      have hb := box_le a r i
      simp only [ha i] at hb
      exact Nat.eq_zero_of_le_zero hb
    have hG : G a φ = 1 := by
      ext r s
      rw [hall r, hall s, hdiag]
      simp
    have hcardBox : Fintype.card (Box a) = 1 := by
      simp [Box, D5.S1.Ledger.BoundedTimeSlice.TailBox, Fintype.card_pi, ha]
    have hGrank : (G a φ).rank = 1 := by rw [hG, Matrix.rank_one, hcardBox]
    exact ⟨hG, hGrank, hGrank ▸ hupper⟩

theorem physical_gram_from_exact_preparation
    (a : σ → ℕ) (P : PhysicalPreparation (H := H) a) :
    let φ := residual a P.V P.initial
    NormalizedResiduals a P.V P.initial P.final φ ∧
    ResidualEvolution a P.V φ ∧
    NormalizedGram a P.final φ ∧
    (∏ i, (a i + 1)) - Finset.univ.sup a ≤ Module.finrank ℂ H := by
  have hr := actual_residuals_of_preparation a P
  have hg := stationary_normalized_gram a P.V P.final _ hr.unit hr.zero hr.step
  exact ⟨hr, residual_word_formula a P.V _ hr.step, hg,
    hg.lower_bound.trans hg.rank_le_memory⟩

end D5.S3.Quantum.StationaryPreparation.PhysicalGram
