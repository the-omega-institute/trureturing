/- GID: D5/S3/Quantum/Walks/HadamardSojournRigidity
   generality: I
   mirror-B: D5/B/S3/Quantum/Walks/HadamardSojournRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact conditional positive sojourn weights for a two-state quantum walk. -/

import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse
import OmegaBuild.Commands

/-! Positive sojourn time in the fixed direction basis of a two-state quantum walk. -/

compile_only_with_mathlib

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Walks.HadamardSojournRigidity

open scoped Matrix BigOperators

private abbrev Coin := Matrix (Fin 2) (Fin 2) ℂ

private def direction (right : Bool) : Fin 2 := if right then 1 else 0

private def displacement (right : Bool) : ℤ := if right then 1 else -1

private def step (U : Coin) (right : Bool) : Coin :=
  fun i j => if i = direction right then U i j else 0

private def wordOperator (U : Coin) : List Bool → Coin
  | [] => 1
  | right :: rest => wordOperator U rest * step U right

private def positiveIntervals (x : ℤ) : List Bool → ℕ
  | [] => 0
  | right :: rest =>
      (if 0 < x ∨ (x = 0 ∧ right = true) then 1 else 0) +
        positiveIntervals (x + displacement right) rest

private def words : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (words n).map (false :: ·) ++ (words n).map (true :: ·)

private def returningWords (n k : ℕ) : List (List Bool) :=
  (words n).filter fun w =>
    decide ((w.map displacement).sum = 0 ∧ positiveIntervals 0 w = k)

/-- The coherent sum over length-`n` return paths with `k` positive intervals.
The left and right coin coordinates are zero and one, respectively. -/
def amplitude (U : Matrix (Fin 2) (Fin 2) ℂ) (n k : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((returningWords n k).map (wordOperator U)).sum

private def normSquared (v : Fin 2 → ℂ) : ℝ :=
  ∑ i, Complex.normSq (v i)

/-- The squared Hilbert norm of the coherent return amplitude on the initial vector. -/
def weight (U : Matrix (Fin 2) (Fin 2) ℂ) (φ : Fin 2 → ℂ) (n k : ℕ) : ℝ :=
  normSquared (amplitude U n k *ᵥ φ)

/-- The denominator is positive, and the conditional law at time `4*m` is
uniform on the positive even counts strictly below `4*m`, and zero elsewhere. -/
def exactUniform (U : Matrix (Fin 2) (Fin 2) ℂ) (φ : Fin 2 → ℂ) (m : ℕ) : Prop :=
  let total := ∑ j ∈ Finset.range (4 * m + 1), weight U φ (4 * m) j
  0 < total ∧ ∀ k : ℕ,
    weight U φ (4 * m) k / total =
      if 0 < k ∧ k < 4 * m ∧ Even k then 1 / (2 * (m : ℝ) - 1) else 0

private def rotation (c s : ℝ) : Coin :=
  !![(c : ℂ), (s : ℂ); (s : ℂ), -(c : ℂ)]

private lemma wordOperator_cons_apply (U : Coin) (b : Bool) (w : List Bool)
    (i j : Fin 2) :
    wordOperator U (b :: w) i j = wordOperator U w i (direction b) * U (direction b) j := by
  simp [wordOperator, Matrix.mul_apply, step, mul_ite]

private lemma list_sum_apply (xs : List Coin) (i j : Fin 2) :
    xs.sum i j = (xs.map fun A => A i j).sum := by
  induction xs with
  | nil => rfl
  | cons A xs ih => simp [ih]

private def threeAmplitudes (c s : ℂ) : Coin × Coin × Coin :=
  let x := c ^ 2
  let y := s ^ 2
  let p := x ^ 2 - 3 * x * y + y ^ 2
  let q := 3 * x ^ 2 - 5 * x * y + y ^ 2
  let r := x ^ 2 - 5 * x * y + 3 * y ^ 2
  let d := x ^ 2 - 4 * x * y + 2 * y ^ 2
  let e := 2 * x ^ 2 - 4 * x * y + y ^ 2
  (!![-x * y * p, -c * s ^ 3 * p; c * s ^ 3 * q, -x * y * r],
   !![-x * y * d, -c * s ^ 3 * e; c * s ^ 3 * e, -x * y * d],
   !![-x * y * r, -c * s ^ 3 * q; c * s ^ 3 * p, -x * y * p])

private lemma rotation_amplitudes_eight (c s : ℝ) :
    (amplitude (rotation c s) 8 2, amplitude (rotation c s) 8 4,
      amplitude (rotation c s) 8 6) = threeAmplitudes c s := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    dsimp only <;>

    ext i j <;>
    fin_cases i <;> fin_cases j <;>
    simp only [amplitude, list_sum_apply, List.map_map] <;>
    (conv in (returningWords 8 _) => reduce) <;>
    simp [wordOperator_cons_apply, wordOperator.eq_1, threeAmplitudes, rotation, direction] <;> ring

private lemma rotation_gram_eight (c s : ℝ) :
    let G₂ := amplitude (rotation c s) 8 2
    let G₄ := amplitude (rotation c s) 8 4
    let G₆ := amplitude (rotation c s) 8 6
    G₂ᴴ * G₂ + G₆ᴴ * G₆ - (2 : ℂ) • (G₄ᴴ * G₄) =
      Complex.ofReal (2 * c ^ 4 * s ^ 6 * (c ^ 2 - s ^ 2) ^ 2 * (c ^ 2 + s ^ 2)) • (1 : Coin) := by
  have h := rotation_amplitudes_eight c s
  dsimp only
  have h₂ : amplitude (rotation c s) 8 2 = (threeAmplitudes c s).1 := congrArg Prod.fst h
  have h₄ : amplitude (rotation c s) 8 4 = (threeAmplitudes c s).2.1 := congrArg (fun p => p.2.1) h
  have h₆ : amplitude (rotation c s) 8 6 = (threeAmplitudes c s).2.2 := congrArg (fun p => p.2.2) h
  rw [h₂, h₄, h₆]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [threeAmplitudes, Matrix.mul_apply, Fin.sum_univ_two, map_ofNat] <;> ring

private lemma normSquared_dot (v : Fin 2 → ℂ) :
    (normSquared v : ℂ) = star v ⬝ᵥ v := by
  simp [normSquared, dotProduct, Pi.star_apply, mul_comm, Complex.mul_conj]

private lemma normSquared_gram (A : Coin) (v : Fin 2 → ℂ) :
    (normSquared (A *ᵥ v) : ℂ) = star v ⬝ᵥ ((Aᴴ * A) *ᵥ v) := by
  rw [normSquared_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

private lemma rotation_weight_eight (c s : ℝ) (v : Fin 2 → ℂ)
    (hv : normSquared v = 1) :
    weight (rotation c s) v 8 2 + weight (rotation c s) v 8 6 -
      2 * weight (rotation c s) v 8 4 =
      2 * c ^ 4 * s ^ 6 * (c ^ 2 - s ^ 2) ^ 2 * (c ^ 2 + s ^ 2) := by
  apply Complex.ofReal_injective
  push_cast
  simp only [weight, normSquared_gram]
  have h := congrArg (fun A : Coin => star v ⬝ᵥ (A *ᵥ v)) (rotation_gram_eight c s)
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul, ← normSquared_dot, hv,
    Complex.ofReal_one, mul_one] at h
  push_cast at h
  exact h

private lemma mem_words {n : ℕ} {w : List Bool} : w ∈ words n ↔ w.length = n := by
  induction n generalizing w with
  | zero => cases w <;> simp [words]
  | succ n ih =>
    cases w with
    | nil => simp [words]
    | cons b w => cases b <;> simp [words, ih]

private lemma displacement_sum (w : List Bool) :
    (w.map displacement).sum = (w.count true : ℤ) - (w.count false : ℤ) := by
  induction w with
  | nil => simp
  | cons b w ih => cases b <;> simp [displacement, ih] <;> omega

private lemma word_length_counts (w : List Bool) : w.length = w.count false + w.count true := by
  induction w with
  | nil => simp
  | cons b w ih => cases b <;> simp [ih] <;> omega

private lemma returning_counts {w : List Bool} {n k : ℕ} (hw : w ∈ returningWords n k) :
    w.count false = n / 2 ∧ w.count true = n / 2 := by
  simp only [returningWords, List.mem_filter, decide_eq_true_eq] at hw
  have hlen := mem_words.mp hw.1
  have hcount := word_length_counts w
  have hbal := displacement_sum w
  omega

private def phase (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ)

private lemma phase_norm (z : ℂ) : Complex.normSq (phase z) = 1 := by
  by_cases hz : z = 0
  · simp [phase, hz]
  · rw [phase, ite_eq_right hz, Complex.normSq_div, Complex.normSq_ofReal,
      ← pow_two, ← Complex.normSq_eq_norm_sq]
    exact div_self (fun h => hz (Complex.normSq_eq_zero.mp h))

private lemma phase_mul_norm (z : ℂ) : phase z * (‖z‖ : ℂ) = z := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [phase, ite_eq_right hz, div_mul_cancel₀]
    exact_mod_cast norm_ne_zero_iff.mpr hz

private lemma normSq_star (z : ℂ) : Complex.normSq (star z) = Complex.normSq z :=
  Complex.normSq_conj z

private lemma mul_star_phase {z : ℂ} (hz : Complex.normSq z = 1) : z * star z = 1 := by
  rw [show z * star z = (Complex.normSq z : ℂ) from Complex.mul_conj z, hz, Complex.ofReal_one]

private lemma star_mul_phase {z : ℂ} (hz : Complex.normSq z = 1) : star z * z = 1 := by
  rw [mul_comm, mul_star_phase hz]

private lemma normal_form (U : Coin) (hU : Uᴴ * U = 1) :
    ∃ c s : ℝ, 0 ≤ c ∧ 0 ≤ s ∧ c ^ 2 + s ^ 2 = 1 ∧
      ∃ p v : Fin 2 → ℂ,
        (∀ i, Complex.normSq (p i) = 1) ∧ (∀ i, Complex.normSq (v i) = 1) ∧
        ∀ i j, U i j = p i * rotation c s i j * v j := by
  let a := U 0 0
  let b := U 0 1
  let c := U 1 0
  let d := U 1 1
  let δ := a * d - b * c
  have h00 : star a * a + star c * c = 1 := by
    simpa [a, c, Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hU 0) 0
  have h01 : star a * b + star c * d = 0 := by
    simpa [a, b, c, d, Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hU 0) 1
  have h11 : star b * b + star d * d = 1 := by
    simpa [b, d, Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hU 1) 1
  have hb : b = -δ * star c := by
    change b = -(a * d - b * c) * star c
    linear_combination a * h01 - b * h00
  have hd : d = δ * star a := by
    change d = (a * d - b * c) * star a
    linear_combination c * h01 - d * h00
  have norm_mul (z : ℂ) : star z * z = (Complex.normSq z : ℂ) :=
    (mul_comm _ _).trans (Complex.mul_conj z)
  have hnorm₀ : Complex.normSq a + Complex.normSq c = 1 := by
    rw [norm_mul, norm_mul] at h00
    exact_mod_cast h00
  have hnorm₁ : Complex.normSq b + Complex.normSq d = 1 := by
    rw [norm_mul, norm_mul] at h11
    exact_mod_cast h11
  have hδ : Complex.normSq δ = 1 := by
    rw [hb, hd] at hnorm₁
    simp only [Complex.normSq_mul, Complex.normSq_neg, normSq_star,
      ← mul_add, add_comm (Complex.normSq c), hnorm₀, mul_one] at hnorm₁
    exact hnorm₁
  let p : Fin 2 → ℂ := ![phase a, phase c]
  let v : Fin 2 → ℂ := ![1, -δ * star (phase a) * star (phase c)]
  refine ⟨‖a‖, ‖c‖, norm_nonneg _, norm_nonneg _, ?_, p, v, ?_, ?_, ?_⟩
  · simpa [Complex.sq_norm] using hnorm₀
  · intro i
    fin_cases i <;> simp [p, phase_norm]
  · intro i
    fin_cases i <;> simp [v, Complex.normSq_mul, phase_norm, hδ]
  · intro i j
    fin_cases i <;> fin_cases j
    · simpa [p, v, rotation, a] using (phase_mul_norm a).symm
    · change b = phase a * (‖c‖ : ℂ) * (-δ * star (phase a) * star (phase c))
      have hsc : star c = (‖c‖ : ℂ) * star (phase c) := by
        conv_lhs => rw [← phase_mul_norm c]
        simp [star_mul]
      rw [hb, hsc]
      linear_combination -((‖c‖ : ℂ) * δ * star (phase c)) * (mul_star_phase (phase_norm a)).symm
    · simpa [p, v, rotation, c] using (phase_mul_norm c).symm
    · change d = phase c * (-(‖a‖ : ℂ)) * (-δ * star (phase a) * star (phase c))
      have hsa : star a = (‖a‖ : ℂ) * star (phase a) := by
        conv_lhs => rw [← phase_mul_norm a]
        simp [star_mul]
      rw [hd, hsa]
      linear_combination ((‖a‖ : ℂ) * δ * star (phase a)) * (mul_star_phase (phase_norm c)).symm


private def wordPhase (p v : Fin 2 → ℂ) (w : List Bool) : ℂ :=
  (p 0 * v 0) ^ w.count false * (p 1 * v 1) ^ w.count true

private lemma wordOperator_phases (U R : Coin) (p v : Fin 2 → ℂ)
    (hv : ∀ i, Complex.normSq (v i) = 1)
    (hU : ∀ i j, U i j = p i * R i j * v j)
    (w : List Bool) (i j : Fin 2) :
    wordOperator U w i j = wordPhase p v w * star (v i) * wordOperator R w i j * v j := by
  induction w generalizing j with
  | nil =>
    by_cases hij : i = j
    · subst j
      simpa [wordOperator, wordPhase] using (star_mul_phase (hv i)).symm
    · simp [wordOperator, wordPhase, hij]
  | cons b w ih =>
    rw [wordOperator_cons_apply, wordOperator_cons_apply, ih, hU]
    have hphase : wordPhase p v (b :: w) =
        wordPhase p v w * (p (direction b) * v (direction b)) := by
      cases b <;> simp [wordPhase, direction, pow_succ] <;> ring
    rw [hphase]
    calc
      _ = (wordPhase p v w * p (direction b) * v (direction b) * star (v i) *
          wordOperator R w i (direction b) * R (direction b) j * v j) := by ring
      _ = _ := by ring

private lemma amplitude_phases (U R : Coin) (p v : Fin 2 → ℂ)
    (hv : ∀ i, Complex.normSq (v i) = 1)
    (hU : ∀ i j, U i j = p i * R i j * v j)
    (n k : ℕ) (i j : Fin 2) :
    amplitude U n k i j =
      ((p 0 * v 0) ^ (n / 2) * (p 1 * v 1) ^ (n / 2)) *
        star (v i) * amplitude R n k i j * v j := by
  simp only [amplitude, list_sum_apply, List.map_map]
  change ((returningWords n k).map fun w => wordOperator U w i j).sum =
    _ * ((returningWords n k).map fun w => wordOperator R w i j).sum * v j
  let W := returningWords n k
  let a := (p 0 * v 0) ^ (n / 2) * (p 1 * v 1) ^ (n / 2) * star (v i)
  have hsum : (W.map (fun w => (a * wordOperator R w i j) * v j)).sum =
      a * (W.map (fun w => wordOperator R w i j)).sum * v j := by
    rw [List.sum_map_mul_right, List.sum_map_mul_left]
  rw [← hsum]
  congr 1
  apply List.map_congr_left
  intro w hw
  obtain ⟨h₀, h₁⟩ := returning_counts hw
  rw [wordOperator_phases U R p v hv hU, wordPhase, h₀, h₁]

private lemma weight_phases (U R : Coin) (p v : Fin 2 → ℂ)
    (hp : ∀ i, Complex.normSq (p i) = 1) (hv : ∀ i, Complex.normSq (v i) = 1)
    (hU : ∀ i j, U i j = p i * R i j * v j)
    (φ : Fin 2 → ℂ) (n k : ℕ) :
    weight U φ n k = weight R (fun i => v i * φ i) n k := by
  let z := (p 0 * v 0) ^ (n / 2) * (p 1 * v 1) ^ (n / 2)
  have hz : Complex.normSq z = 1 := by
    simp [z, Complex.normSq_mul, map_pow, hp, hv]
  unfold weight normSquared
  apply Finset.sum_congr rfl
  intro i _
  have hi : (amplitude U n k *ᵥ φ) i =
      (z * star (v i)) * (amplitude R n k *ᵥ (fun j => v j * φ j)) i := by
    simp only [Matrix.mulVec, dotProduct, amplitude_phases U R p v hv hU, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [z]
    ring
  rw [hi]
  simp [Complex.normSq_mul, hz, hv]

private lemma exactUniform_phases (U R : Coin) (p v : Fin 2 → ℂ)
    (hp : ∀ i, Complex.normSq (p i) = 1) (hv : ∀ i, Complex.normSq (v i) = 1)
    (hU : ∀ i j, U i j = p i * R i j * v j)
    (φ : Fin 2 → ℂ) (m : ℕ) :
    exactUniform U φ m ↔ exactUniform R (fun i => v i * φ i) m := by
  simp only [exactUniform, weight_phases U R p v hp hv hU]

private lemma rotation_necessary (c s : ℝ) (v : Fin 2 → ℂ)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1)
    (hv : normSquared v = 1) (hunif : exactUniform (rotation c s) v 2) :
    c = s := by
  let total := ∑ j ∈ Finset.range 9, weight (rotation c s) v 8 j
  have htotal : 0 < total := hunif.1
  have h₂ : weight (rotation c s) v 8 2 = (1 / 3 : ℝ) * total := by
    apply (div_eq_iff htotal.ne').mp
    simpa [show (2 * (2 : ℝ) - 1) = 3 by norm_num, exactUniform, total,
      show Even (2 : ℕ) from ⟨1, rfl⟩] using hunif.2 2
  have h₄ : weight (rotation c s) v 8 4 = (1 / 3 : ℝ) * total := by
    apply (div_eq_iff htotal.ne').mp
    simpa [show (2 * (2 : ℝ) - 1) = 3 by norm_num, exactUniform, total,
      show Even (4 : ℕ) from ⟨2, rfl⟩] using hunif.2 4
  have h₆ : weight (rotation c s) v 8 6 = (1 / 3 : ℝ) * total := by
    apply (div_eq_iff htotal.ne').mp
    simpa [show (2 * (2 : ℝ) - 1) = 3 by norm_num, exactUniform, total,
      show Even (6 : ℕ) from ⟨3, rfl⟩] using hunif.2 6
  have h₄positive : 0 < weight (rotation c s) v 8 4 := by rw [h₄]; positivity
  have hamplitude : amplitude (rotation c s) 8 4 = (threeAmplitudes c s).2.1 :=
    congrArg (fun p => p.2.1) (rotation_amplitudes_eight c s)
  have hc' : c ≠ 0 := by
    intro he
    have hz : amplitude (rotation c s) 8 4 = 0 := by
      rw [hamplitude, he]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [threeAmplitudes]
    simp [weight, hz, normSquared] at h₄positive
  have hs' : s ≠ 0 := by
    intro he
    have hz : amplitude (rotation c s) 8 4 = 0 := by
      rw [hamplitude, he]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [threeAmplitudes]
    simp [weight, hz, normSquared] at h₄positive
  have hbalance := rotation_weight_eight c s v hv
  rw [h₂, h₄, h₆, hcs, mul_one] at hbalance
  have hzero : 2 * c ^ 4 * s ^ 6 * (c ^ 2 - s ^ 2) ^ 2 = 0 := by linarith
  have hnonzero : 2 * c ^ 4 * s ^ 6 ≠ 0 := by positivity
  have hsquares : c ^ 2 - s ^ 2 = 0 := by
    have hsq := (mul_eq_zero.mp hzero).resolve_left hnonzero
    rw [pow_two, mul_self_eq_zero] at hsq
    exact hsq
  exact (sq_eq_sq₀ hc hs).mp (sub_eq_zero.mp hsquares)

private def signCoin : Coin := !![1, 1; 1, -1]

private def uniformMatrix : Coin := !![1, 1; -1, 1]

private lemma wordOperator_scale (U : Coin) (z : ℂ) (w : List Bool) :
    wordOperator (z • U) w = z ^ w.length • wordOperator U w := by
  induction w with
  | nil => simp [wordOperator]
  | cons b w ih =>
    have hstep : step (z • U) b = z • step U b := by
      ext i j
      by_cases h : i = direction b <;> simp [step, h]
    simp [wordOperator, hstep, ih, pow_succ, smul_smul, mul_comm z]

private lemma amplitude_scale (U : Coin) (z : ℂ) (n k : ℕ) :
    amplitude (z • U) n k = z ^ n • amplitude U n k := by
  have hlen : ∀ w ∈ returningWords n k, w.length = n := by
    intro w hw
    exact mem_words.mp (List.mem_of_mem_filter hw)
  unfold amplitude
  have hsum (t : List Coin) : (t.map fun A => z ^ n • A).sum = z ^ n • t.sum := by
    induction t with
    | nil => simp
    | cons A t ih => simp [ih, smul_add]
  rw [← hsum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro w hw
  rw [wordOperator_scale, hlen w hw]
  rfl

private lemma uniformMatrix_gram : uniformMatrixᴴ * uniformMatrix = (2 : ℂ) • (1 : Coin) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [uniformMatrix, Matrix.mul_apply, Fin.sum_univ_two]

private lemma unit_after_phases (v φ : Fin 2 → ℂ)
    (hv : ∀ i, Complex.normSq (v i) = 1) (hφ : normSquared φ = 1) :
    normSquared (fun i => v i * φ i) = 1 := by
  simpa only [normSquared, Complex.normSq_mul, hv, one_mul] using hφ


private lemma normSquared_smul (z : ℂ) (v : Fin 2 → ℂ) :
    normSquared (z • v) = Complex.normSq z * normSquared v := by
  simp [normSquared, Complex.normSq_mul, Pi.smul_apply, smul_eq_mul, mul_add]

private lemma uniformMatrix_norm (v : Fin 2 → ℂ) (hv : normSquared v = 1) :
    normSquared (uniformMatrix *ᵥ v) = 2 := by
  apply Complex.ofReal_injective
  rw [normSquared_gram, uniformMatrix_gram, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, ← normSquared_dot, hv]
  norm_num

private lemma rotation_modulus (c s : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s) (i j : Fin 2) :
    ‖rotation c s i j‖ = if i = j then c else s := by
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Real.norm_eq_abs, abs_of_nonneg hc, abs_of_nonneg hs]


section FormalSeries

set_option maxHeartbeats 1200000

-- Elapsed time is the outer series degree. The polynomial degree counts positive intervals.
private abbrev Poly := Polynomial ℂ
private abbrev Series := PowerSeries Poly
private abbrev PolyMatrix := Matrix (Fin 2) (Fin 2) Poly
private abbrev SeriesMatrix := Matrix (Fin 2) (Fin 2) Series

private def intervalMark (x : ℤ) (b : Bool) : Poly :=
  if 0 < x ∨ (x = 0 ∧ b = true) then Polynomial.X else 1

private def pathPolynomial (U : Coin) (x : ℤ) (w : List Bool) : PolyMatrix :=
  if x + (w.map displacement).sum = 0 then
    (Polynomial.X : Poly) ^ positiveIntervals x w • (wordOperator U w).map Polynomial.C
  else 0

private def walkPolynomial (U : Coin) (x : ℤ) (n : ℕ) : PolyMatrix :=
  ((words n).map (pathPolynomial U x)).sum

private lemma pathPolynomial_cons (U : Coin) (x : ℤ) (b : Bool) (w : List Bool) :
    pathPolynomial U x (b :: w) =
      intervalMark x b • (pathPolynomial U (x + displacement b) w *
        (step U b).map Polynomial.C) := by
  simp only [pathPolynomial, List.map_cons, List.sum_cons, ← add_assoc]
  split
  · rw [wordOperator, Matrix.map_mul (f := Polynomial.C)]
    simp only [positiveIntervals, pow_add, intervalMark, smul_mul_assoc, ← smul_smul]
    split <;> simp
  · simp

private lemma walkPolynomial_succ (U : Coin) (x : ℤ) (n : ℕ) :
    walkPolynomial U x (n + 1) =
      intervalMark x false • (walkPolynomial U (x - 1) n * (step U false).map Polynomial.C) +
      intervalMark x true • (walkPolynomial U (x + 1) n * (step U true).map Polynomial.C) := by
  simp only [walkPolynomial, words, List.map_append, List.sum_append]
  congr 1
  all_goals
    simp only [List.map_map]
    induction (words n) with
    | nil => simp
    | cons w l ih =>
      simp only [List.map_cons, List.sum_cons, add_mul, smul_add]
      change pathPolynomial U x (_ :: w) + _ = _ + _
      rw [ih]
      congr 1
      exact pathPolynomial_cons U x _ w

private lemma list_sum_apply_poly (xs : List PolyMatrix) (i j : Fin 2) :
    xs.sum i j = (xs.map fun A => A i j).sum := by
  induction xs with
  | nil => rfl
  | cons A xs ih => simp [ih]

private lemma coeff_returnWords (U : Coin) (n k : ℕ) (i j : Fin 2) :
    (walkPolynomial U 0 n i j).coeff k = amplitude U n k i j := by
  simp only [walkPolynomial, amplitude, list_sum_apply_poly, list_sum_apply, List.map_map]
  change Polynomial.lcoeff ℂ k ((words n).map fun w => pathPolynomial U 0 w i j).sum =
    ((returningWords n k).map fun w => wordOperator U w i j).sum
  rw [← List.sum_map_hom _ _ (Polynomial.lcoeff ℂ k)]
  unfold returningWords
  generalize words n = l
  change (l.map fun w => (pathPolynomial U 0 w i j).coeff k).sum =
    ((l.filter fun w =>
      decide ((w.map displacement).sum = 0 ∧ positiveIntervals 0 w = k)).map
      fun w => wordOperator U w i j).sum
  have hword (w : List Bool) : (pathPolynomial U 0 w i j).coeff k =
      if (w.map displacement).sum = 0 ∧ positiveIntervals 0 w = k then
        wordOperator U w i j else 0 := by
    by_cases h₀ : (w.map displacement).sum = 0
    · simp only [pathPolynomial, zero_add, h₀, ite_true, true_and,
        Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, Polynomial.X_pow_eq_monomial,
        Polynomial.monomial_mul_C, one_mul, Polynomial.coeff_monomial]
    · simp [pathPolynomial, h₀]
  simp_rw [hword]
  induction l with
  | nil => simp
  | cons w l ih =>
    by_cases hw : (w.map displacement).sum = 0 ∧ positiveIntervals 0 w = k
    · simp only [List.map_cons, List.sum_cons, List.filter_cons, hw, true_and, decide_true,
        ite_true, ih]
    · simp only [List.map_cons, List.sum_cons, List.filter_cons, hw, decide_false, Bool.false_eq_true,
        ite_false, zero_add, ih]

private def tvar : Series := PowerSeries.C Polynomial.X

private def zvar : Series := PowerSeries.X

private def walkSeries (U : Coin) (x : ℤ) : SeriesMatrix :=
  fun i j => PowerSeries.mk fun n => walkPolynomial U x n i j

private def seriesStep (U : Coin) (b : Bool) : SeriesMatrix :=
  (step U b).map (PowerSeries.C.comp Polynomial.C)

private lemma series_recursion (U : Coin) (x : ℤ) :
    walkSeries U x = (if x = 0 then 1 else 0) +
      (zvar * PowerSeries.C (intervalMark x false)) •
        (walkSeries U (x - 1) * seriesStep U false) +
      (zvar * PowerSeries.C (intervalMark x true)) •
        (walkSeries U (x + 1) * seriesStep U true) := by
  apply Matrix.ext
  intro i j
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    by_cases hx : x = 0
    · subst x
      simp [walkSeries, walkPolynomial, pathPolynomial, words, wordOperator, positiveIntervals,
        zvar, PowerSeries.coeff_zero_eq_constantCoeff_apply, Matrix.one_apply]
    · simp [walkSeries, walkPolynomial, pathPolynomial, words, hx, zvar,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
  | succ n =>
    simp only [walkSeries, PowerSeries.coeff_mk, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, mul_assoc, zvar, PowerSeries.coeff_succ_X_mul, map_add]
    have hnil : (PowerSeries.coeff (n + 1)) ((if x = 0 then (1 : SeriesMatrix) else 0) i j) = 0 := by
      split <;> simp [Matrix.one_apply]
      split <;> simp
    rw [hnil, zero_add, walkPolynomial_succ]
    simp [seriesStep, Matrix.mul_apply, Fin.sum_univ_two, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_mul_C, Matrix.map_apply, walkSeries]

private lemma series_recursion_unique (U : Coin) (F : ℤ → SeriesMatrix)
    (hF : ∀ x, F x = (if x = 0 then 1 else 0) +
      (zvar * PowerSeries.C (intervalMark x false)) • (F (x - 1) * seriesStep U false) +
      (zvar * PowerSeries.C (intervalMark x true)) • (F (x + 1) * seriesStep U true)) :
    ∀ x, walkSeries U x = F x := by
  have hcoeff (n : ℕ) (x : ℤ) (i j : Fin 2) :
      PowerSeries.coeff n (walkSeries U x i j) = PowerSeries.coeff n (F x i j) := by
    induction n generalizing x i j with
    | zero =>
      rw [series_recursion U x, hF x]
      simp [zvar, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    | succ n ih =>
      rw [series_recursion U x, hF x]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_assoc, zvar,
        PowerSeries.coeff_succ_X_mul, map_add, seriesStep, Matrix.mul_apply, Fin.sum_univ_two,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, Matrix.map_apply, RingHom.comp_apply, ih]
  intro x
  apply Matrix.ext
  intro i j
  exact PowerSeries.ext (fun n => hcoeff n x i j)

private def seriesHalf : Series :=
  PowerSeries.C (Polynomial.C (1 / 2 : ℂ))

-- The half-line excursions use the alternating Catalan series at degrees divisible by four.
private def catalanBase : Series :=
  PowerSeries.subst (PowerSeries.X ^ 4 : Series)
    (PowerSeries.rescale (-1) (PowerSeries.catalanSeries.map (Nat.castRingHom Poly)))

private def markedStep (a : Poly) : Series := PowerSeries.C a * PowerSeries.X

private def catalanAt (a : Poly) : Series := PowerSeries.rescale a catalanBase

private lemma catalanBase_eq :
    catalanBase + (PowerSeries.X : Series) ^ 4 * catalanBase ^ 2 = 1 := by
  let S := PowerSeries.catalanSeries.map (Nat.castRingHom Poly)
  have hS : S ^ 2 * PowerSeries.X + 1 = S := by
    simpa only [S, map_add, map_mul, map_one, map_pow, PowerSeries.map_X] using
      congrArg (PowerSeries.map (Nat.castRingHom Poly)) PowerSeries.catalanSeries_sq_mul_X_add_one
  have hR : (PowerSeries.rescale (-1) S) ^ 2 * (-PowerSeries.X) + 1 =
      PowerSeries.rescale (-1) S := by
    simpa only [map_add, map_mul, map_one, map_pow, PowerSeries.rescale_neg_one_X] using
      congrArg (PowerSeries.rescale (-1 : Poly)) hS
  have hs : PowerSeries.HasSubst ((PowerSeries.X : Series) ^ 4) :=
    PowerSeries.HasSubst.X_pow (by decide : 4 ≠ 0)
  let ev := PowerSeries.substAlgHom (R := Poly) hs
  have he := congrArg ev hR
  simp only [map_add, map_mul, map_one, map_pow, map_neg] at he
  have hev : ev PowerSeries.X = (PowerSeries.X : Series) ^ 4 := by
    exact PowerSeries.substAlgHom_X (R := Poly) hs
  rw [hev] at he
  simp only [ev, PowerSeries.coe_substAlgHom, S] at he
  have he' : catalanBase ^ 2 * (-(PowerSeries.X : Series) ^ 4) + 1 = catalanBase := he
  linear_combination -he'

private lemma catalanAt_eq (a : Poly) :
    catalanAt a + (markedStep a) ^ 4 * (catalanAt a) ^ 2 = 1 := by
  simpa only [catalanAt, markedStep, map_add, map_mul, map_one, map_pow, PowerSeries.rescale_X] using
    congrArg (PowerSeries.rescale a) catalanBase_eq

private lemma coeff_catalanAt (a : Poly) (n : ℕ) :
    PowerSeries.coeff n (catalanAt a) =
      if 4 ∣ n then a ^ n * (-1 : Poly) ^ (n / 4) * (catalan (n / 4) : Poly) else 0 := by
  rw [catalanAt, PowerSeries.coeff_rescale, catalanBase, PowerSeries.coeff_subst_X_pow (by decide)]
  split <;> simp [PowerSeries.coeff_rescale, PowerSeries.coeff_map, PowerSeries.catalanSeries_coeff,
    mul_assoc]

private def leftStepSeries : SeriesMatrix := !![1, 1; 0, 0]
private def rightStepSeries : SeriesMatrix := !![0, 0; 1, -1]

private def positiveTransfer (x C : Series) : SeriesMatrix :=
  !![x + x ^ 3 * C, x - x ^ 3 * C; 0, 0]

private def negativeTransfer (x C : Series) : SeriesMatrix :=
  !![0, 0; x - x ^ 3 * C, -(x + x ^ 3 * C)]

private lemma positiveTransfer_eq (x C : Series) (h : C + x ^ 4 * C ^ 2 = 1) :
    positiveTransfer x C = x • (leftStepSeries + (positiveTransfer x C) ^ 2 * rightStepSeries) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [positiveTransfer, leftStepSeries, rightStepSeries, pow_two] <;>
    first | linear_combination x ^ 3 * h | linear_combination -(x ^ 3) * h

private lemma negativeTransfer_eq (x C : Series) (h : C + x ^ 4 * C ^ 2 = 1) :
    negativeTransfer x C = x • (rightStepSeries + (negativeTransfer x C) ^ 2 * leftStepSeries) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [negativeTransfer, leftStepSeries, rightStepSeries, pow_two] <;>
    first | linear_combination x ^ 3 * h | linear_combination -(x ^ 3) * h

private def boundaryKernel (f g : Series) : SeriesMatrix := !![1-f, f; -g, 1-g]

private lemma boundaryKernel_eq (x y C D : Series) :
    boundaryKernel (x ^ 2 - x ^ 4 * C) (y ^ 2 - y ^ 4 * D) =
      1 - x • (positiveTransfer x C * rightStepSeries) -
        y • (negativeTransfer y D * leftStepSeries) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [boundaryKernel, positiveTransfer, negativeTransfer, leftStepSeries, rightStepSeries] <;> ring

private def boundaryInverse (h k J : Series) : SeriesMatrix :=
  J • !![1+k, h-1; 1-k, 1+h]

private lemma boundaryInverse_eq (h k J f g : Series)
    (hf : h = 1 - 2 * f) (hg : k = 1 - 2 * g) (hJ : (1 + h * k) * J = 1) :
    boundaryInverse h k J * boundaryKernel f g = 1 := by
  subst h
  subst k
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [boundaryInverse, boundaryKernel, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination hJ | ring

private lemma rescale_boundary_algebra (h k H K J L b : Series)
    (hH : h * H = 1) (hK : k * K = 1)
    (hJ : (1 + h * k) * J = 1) (hL : (1 + H * K) * L = 1)
    (hb : k * (1 - h ^ 2) = b * h * (1 - k ^ 2)) :
    (1 - b) • (boundaryInverse h k J + boundaryInverse H K L - (2 : SeriesMatrix)) =
      (h - b * k - (1 - b)) • (uniformMatrix.map (PowerSeries.C.comp Polynomial.C)) := by
  have hKJ : L = h * k * J := by
    have hproduct : (1 + H * K) * (h * k) = 1 + h * k := by
      calc
        _ = h * k + (h * H) * (k * K) := by ring
        _ = _ := by rw [hH, hK]; ring
    calc
      L = L * ((1 + h * k) * J) := by rw [hJ, mul_one]
      _ = L * ((1 + H * K) * (h * k)) * J := by rw [hproduct]; ring
      _ = h * k * J := by rw [← mul_assoc L, mul_comm L, hL, one_mul]
  have hratio : (1 - b) * (h + k) * J = h - b * k := by
    have hp : (1 - b) * (h + k) = (h - b * k) * (1 + h * k) := by
      linear_combination hb
    rw [hp, mul_assoc, hJ, mul_one]
  have hs (h k H K J L : Series) (hH : h * H = 1) (hK : k * K = 1)
      (hJ : (1 + h * k) * J = 1) (hL : L = h * k * J) :
      boundaryInverse h k J + boundaryInverse H K L - (2 : SeriesMatrix) =
      ((h + k) * J - 1) • (uniformMatrix.map (PowerSeries.C.comp Polynomial.C)) := by
    subst L
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [boundaryInverse, uniformMatrix, Matrix.ofNat_apply]
    · linear_combination hJ + J * h * hK
    · linear_combination J * k * hH - hJ
    · linear_combination hJ - J * h * hK
    · linear_combination hJ + J * k * hH

  rw [hs h k H K J L hH hK hJ hKJ, smul_smul]
  have H : (1 - b) * ((h + k) * J - 1) = h - b * k - (1 - b) := by
    linear_combination hratio
  rw [H]

private lemma step_signCoin_series (b : Bool) :
    seriesStep signCoin b = if b then rightStepSeries else leftStepSeries := by
  apply Matrix.ext
  intro i j
  cases b <;> fin_cases i <;> fin_cases j <;>
    simp [seriesStep, signCoin, step, direction, leftStepSeries, rightStepSeries]

private def scalarH (a : Poly) : Series :=
  1 - 2 * ((markedStep a) ^ 2 - (markedStep a) ^ 4 * catalanAt a)

private lemma scalarH_unit (a : Poly) :
    scalarH a * (scalarH a + 4 * (markedStep a) ^ 2) = 1 := by
  unfold scalarH
  linear_combination 4 * (markedStep a) ^ 4 * (catalanAt_eq a)

private def boundaryDet (a b : Poly) : Series := (1 + scalarH a * scalarH b) * seriesHalf

private lemma constantCoeff_half : seriesHalf.constantCoeff = Polynomial.C (1 / 2 : ℂ) := by
  simp [seriesHalf]

private lemma constantCoeff_det (a b : Poly) :
    (boundaryDet a b).constantCoeff = 1 := by
  simp only [boundaryDet, scalarH, map_mul, map_add, map_sub, map_pow, map_one, map_ofNat,
    markedStep, PowerSeries.constantCoeff_X, mul_zero,
    zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 4 ≠ 0),
    zero_mul, sub_zero, mul_one, constantCoeff_half]
  have h : (2 : Poly) * Polynomial.C (1 / 2 : ℂ) = 1 := by
    rw [← map_ofNat Polynomial.C, ← map_mul]
    norm_num
  simpa only [one_add_one_eq_two] using h

private def boundaryScalar (a b : Poly) : Series :=
  seriesHalf * PowerSeries.invOfUnit (boundaryDet a b) 1

private lemma boundaryScalar_eq (a b : Poly) :
    (1 + scalarH a * scalarH b) * boundaryScalar a b = 1 := by
  rw [boundaryScalar, ← mul_assoc]
  exact PowerSeries.mul_invOfUnit (boundaryDet a b) 1 (constantCoeff_det a b)

private def positiveStepVar : Series := markedStep Polynomial.X

private lemma positiveStepVar_eq : positiveStepVar = zvar * tvar := by
  exact mul_comm _ _

private lemma markedStep_one : markedStep 1 = zvar := by simp [markedStep, zvar]

private def minusTransfer : SeriesMatrix := negativeTransfer zvar (catalanAt 1)
private def plusTransfer : SeriesMatrix := positiveTransfer positiveStepVar (catalanAt Polynomial.X)

private def boundary : SeriesMatrix :=
  boundaryInverse (scalarH Polynomial.X) (scalarH 1) (boundaryScalar Polynomial.X 1)

private lemma transportPower (D P Q : SeriesMatrix) (z : Series)
    (h : D = z • (P + D ^ 2 * Q)) (n : ℕ) :
    D ^ (n + 1) = z • (D ^ n * P + D ^ (n + 2) * Q) := by
  calc
    D ^ (n + 1) = D ^ n * D := pow_succ _ _
    _ = D ^ n * (z • (P + D ^ 2 * Q)) := congrArg (D ^ n * ·) h
    _ = _ := by rw [mul_smul_comm, mul_add, ← mul_assoc, ← pow_add]

private def halfLineExtension (B L R : SeriesMatrix) (x : ℤ) : SeriesMatrix :=
  match x with
  | .ofNat n => B * L ^ n
  | .negSucc n => B * R ^ (n + 1)

@[simp] private lemma halfLineExtension_zero (B L R : SeriesMatrix) :
    halfLineExtension B L R 0 = B := by
  change B * L ^ 0 = B
  rw [pow_zero, mul_one]

private lemma halfLineExtension_ofNat (B L R : SeriesMatrix) (n : ℕ) :
    halfLineExtension B L R (.ofNat n) = B * L ^ n := rfl

private lemma halfLineExtension_negSucc (B L R : SeriesMatrix) (n : ℕ) :
    halfLineExtension B L R (.negSucc n) = B * R ^ (n + 1) := rfl

private lemma model_origin :
    boundary = 1 + zvar • ((boundary * minusTransfer) * leftStepSeries) +
      positiveStepVar • ((boundary * plusTransfer) * rightStepSeries) := by
  have h := boundaryInverse_eq (scalarH Polynomial.X) (scalarH 1)
    (boundaryScalar Polynomial.X 1)
    (positiveStepVar ^ 2 - positiveStepVar ^ 4 * catalanAt Polynomial.X)
    (markedStep 1 ^ 2 - markedStep 1 ^ 4 * catalanAt 1) rfl rfl
    (boundaryScalar_eq _ _)
  have hh : boundary * boundaryKernel (positiveStepVar ^ 2 - positiveStepVar ^ 4 * catalanAt Polynomial.X)
      (markedStep 1 ^ 2 - markedStep 1 ^ 4 * catalanAt 1) = 1 := h
  rw [boundaryKernel_eq, markedStep_one, mul_sub, mul_sub, mul_one,
    mul_smul_comm, mul_smul_comm, ← mul_assoc, ← mul_assoc] at hh
  have hp : boundary - positiveStepVar • ((boundary * plusTransfer) * rightStepSeries) -
      zvar • ((boundary * minusTransfer) * leftStepSeries) = 1 := hh
  exact (sub_eq_iff_eq_add.mp (sub_eq_iff_eq_add.mp hp))

private lemma halfLineExtension_recursion (B L R P Q : SeriesMatrix) (Z : Series)
    (hL : L = (Z * PowerSeries.C Polynomial.X) • (P + L ^ 2 * Q))
    (hR : R = Z • (Q + R ^ 2 * P))
    (hB : B = 1 + Z • ((B * R) * P) +
      (Z * PowerSeries.C Polynomial.X) • ((B * L) * Q))
    (x : ℤ) :
    halfLineExtension B L R x = (if x = 0 then 1 else 0) +
      (Z * PowerSeries.C (intervalMark x false)) • (halfLineExtension B L R (x - 1) * P) +
      (Z * PowerSeries.C (intervalMark x true)) • (halfLineExtension B L R (x + 1) * Q) := by
  rcases x with n | n
  · cases n with
    | zero =>
      have hnat : Int.ofNat 0 = 0 := rfl
      rw [hnat, halfLineExtension_zero, show (0 : ℤ) - 1 = Int.negSucc 0 by decide,
        show (0 : ℤ) + 1 = Int.ofNat 1 by decide, halfLineExtension_negSucc, halfLineExtension_ofNat]
      rw [show intervalMark 0 false = 1 by rfl, show intervalMark 0 true = Polynomial.X by rfl]
      simpa only [↓reduceIte, map_one, mul_one, pow_one, Nat.zero_add] using hB
    | succ n =>
      have hl : (Int.ofNat (n + 1)) - 1 = Int.ofNat n := by
        simp only [Int.ofNat_eq_natCast]
        omega
      have hr : (Int.ofNat (n + 1)) + 1 = Int.ofNat (n + 2) := by
        simp only [Int.ofNat_eq_natCast]
        omega
      have hp : 0 < Int.ofNat (n + 1) := by
        simp only [Int.ofNat_eq_natCast]
        omega
      have hi (b : Bool) : intervalMark (Int.ofNat (n + 1)) b = Polynomial.X :=
        ite_eq_left (Or.inl hp)
      rw [hl, hr, halfLineExtension_ofNat, halfLineExtension_ofNat, halfLineExtension_ofNat,
        ite_eq_right hp.ne', hi false, hi true, zero_add]
      have h := congrArg (B * ·) (transportPower _ _ _ _ hL n)
      rw [mul_smul_comm, mul_add, smul_add, ← mul_assoc, ← mul_assoc] at h
      exact h
  · have hlt : Int.negSucc n < 0 := by omega
    have hl : Int.negSucc n - 1 = Int.negSucc (n + 1) := by omega
    have hi (b : Bool) : intervalMark (Int.negSucc n) b = 1 :=
      ite_eq_right (fun h => h.elim hlt.not_gt (fun he => hlt.ne he.1))
    have hr : halfLineExtension B L R (Int.negSucc n + 1) = B * R ^ n := by
      cases n with
      | zero =>
        rw [show Int.negSucc 0 + 1 = 0 by decide, halfLineExtension_zero, pow_zero, mul_one]
      | succ n =>
        rw [show Int.negSucc (n + 1) + 1 = Int.negSucc n by omega, halfLineExtension_negSucc]
    rw [halfLineExtension_negSucc, hl, halfLineExtension_negSucc, hr, hi false, hi true,
      ite_eq_right hlt.ne, zero_add, map_one, mul_one]
    have h := congrArg (B * ·) (transportPower _ _ _ _ hR n)
    rw [mul_smul_comm, mul_add, smul_add, ← mul_assoc, ← mul_assoc] at h
    exact h.trans (add_comm _ _)

private lemma walkSeries_signCoin_zero : walkSeries signCoin 0 = boundary := by
  let F := halfLineExtension boundary plusTransfer minusTransfer
  have hplus : plusTransfer = positiveStepVar • (leftStepSeries + plusTransfer ^ 2 * rightStepSeries) :=
    positiveTransfer_eq positiveStepVar _ (catalanAt_eq Polynomial.X)
  have hminus : minusTransfer = zvar • (rightStepSeries + minusTransfer ^ 2 * leftStepSeries) := by
    unfold minusTransfer
    apply negativeTransfer_eq
    simpa only [markedStep_one] using catalanAt_eq 1
  have hs := series_recursion_unique signCoin F (fun x => by
    rw [step_signCoin_series, step_signCoin_series]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact halfLineExtension_recursion _ _ _ _ _ _ (positiveStepVar_eq ▸ hplus) hminus
      (positiveStepVar_eq ▸ model_origin) x)
  exact (hs 0).trans (halfLineExtension_zero _ _ _)

private def imaginaryMark : Poly := Polynomial.C Complex.I

private lemma imaginaryMark_sq : imaginaryMark ^ 2 = -1 := by
  rw [imaginaryMark, ← map_pow, Complex.I_sq, map_neg, map_one]

private lemma imaginaryMark_fourth : imaginaryMark ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, imaginaryMark_sq]
  simp

private lemma rescale_catalanAt (a : Poly) :
    PowerSeries.rescale imaginaryMark (catalanAt a) = catalanAt a := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_rescale, coeff_catalanAt]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [pow_mul, imaginaryMark_fourth, one_pow, one_mul]
  · simp

private lemma rescale_markedStep_pow (a : Poly) (n : ℕ) :
    PowerSeries.rescale imaginaryMark (markedStep a ^ n) =
      PowerSeries.C (imaginaryMark ^ n) * markedStep a ^ n := by
  have hc : PowerSeries.rescale imaginaryMark (PowerSeries.C a) = PowerSeries.C a := by
    apply PowerSeries.ext
    intro k
    by_cases hk : k = 0 <;> simp [PowerSeries.coeff_C, hk]
  simp [markedStep, PowerSeries.rescale_X, hc, mul_pow, mul_left_comm]

private lemma rescale_scalarH (a : Poly) :
    PowerSeries.rescale imaginaryMark (scalarH a) =
      scalarH a + 4 * markedStep a ^ 2 := by
  unfold scalarH
  simp only [map_sub, map_mul, map_one, map_ofNat, rescale_markedStep_pow,
    imaginaryMark_sq, imaginaryMark_fourth, map_neg, map_one, one_mul, neg_one_mul,
    rescale_catalanAt]
  ring

-- Divide out the sojourn marker only after taking coefficients in the time variable.
private lemma boundary_even :
    (1 - tvar ^ 2) •
      (boundary + boundary.map (PowerSeries.rescale imaginaryMark) - (2 : SeriesMatrix)) =
      (2 * positiveStepVar ^ 4 * catalanAt Polynomial.X -
        tvar ^ 2 * (2 * zvar ^ 4 * catalanAt 1)) •
        uniformMatrix.map (PowerSeries.C.comp Polynomial.C) := by
  let h := scalarH Polynomial.X
  let k := scalarH 1
  let H := h + 4 * positiveStepVar ^ 2
  let K := k + 4 * markedStep 1 ^ 2
  let J := boundaryScalar Polynomial.X 1
  let L := PowerSeries.rescale imaginaryMark J
  have hmap : boundary.map (PowerSeries.rescale imaginaryMark) = boundaryInverse H K L := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [boundary, boundaryInverse, h, k, H, K, J, L, rescale_scalarH, positiveStepVar]
  have hL : (1 + H * K) * L = 1 := by
    simpa only [h, k, H, K, J, L, positiveStepVar, map_mul, map_add, map_one, rescale_scalarH]
      using congrArg (PowerSeries.rescale imaginaryMark) (boundaryScalar_eq Polynomial.X 1)
  have hpos : h * H = 1 := scalarH_unit Polynomial.X
  have hneg : k * K = 1 := scalarH_unit 1
  have hb : k * (1 - h ^ 2) = tvar ^ 2 * h * (1 - k ^ 2) := by
    change h * (h + 4 * positiveStepVar ^ 2) = 1 at hpos
    change k * (k + 4 * markedStep 1 ^ 2) = 1 at hneg
    rw [positiveStepVar_eq] at hpos
    rw [markedStep_one] at hneg
    linear_combination -(k * hpos) + tvar ^ 2 * h * hneg
  rw [hmap]
  have heven := rescale_boundary_algebra h k H K J L (tvar ^ 2) hpos hneg
    (boundaryScalar_eq Polynomial.X 1) hL hb
  change (1 - tvar ^ 2) • (boundary + boundaryInverse H K L - (2 : SeriesMatrix)) = _ at heven
  rw [heven]
  have hs : h - tvar ^ 2 * k - (1 - tvar ^ 2) =
      2 * positiveStepVar ^ 4 * catalanAt Polynomial.X -
        tvar ^ 2 * (2 * zvar ^ 4 * catalanAt 1) := by
    unfold h k scalarH
    rw [markedStep_one]
    change 1 - 2 * (positiveStepVar ^ 2 - positiveStepVar ^ 4 * catalanAt Polynomial.X) -
      tvar ^ 2 * (1 - 2 * (zvar ^ 2 - zvar ^ 4 * catalanAt 1)) - (1 - tvar ^ 2) = _
    rw [positiveStepVar_eq]
    ring
  rw [hs]

private def alternatingCatalan (m : ℕ) : ℂ := (-1 : ℂ) ^ m * (catalan m : ℂ)

private lemma coeff_step_catalan (a : Poly) (m : ℕ) :
    PowerSeries.coeff (4 * (m + 1)) (markedStep a ^ 4 * catalanAt a) =
      Polynomial.C (alternatingCatalan m) * a ^ (4 * (m + 1)) := by
  have hm : 4 * (m + 1) = 4 * m + 4 := by omega
  rw [hm]
  simp only [markedStep, mul_pow, ← map_pow, mul_assoc, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul, coeff_catalanAt, dvd_mul_right, ite_true]
  rw [show 4 * m / 4 = m by omega, pow_add]
  simp [alternatingCatalan, mul_assoc]
  ring

private def supportPolynomial (m : ℕ) : Poly :=
  ∑ j ∈ Finset.range (2 * m + 1), Polynomial.X ^ (2 * (j + 1))

private lemma supportPolynomial_mul (m : ℕ) :
    (1 - (Polynomial.X : Poly) ^ 2) * supportPolynomial m =
      Polynomial.X ^ 2 - Polynomial.X ^ (4 * (m + 1)) := by
  have he (l : ℕ) :
      (1 - (Polynomial.X : Poly) ^ 2) *
          (∑ j ∈ Finset.range l, Polynomial.X ^ (2 * (j + 1))) =
        Polynomial.X ^ 2 - Polynomial.X ^ (2 * (l + 1)) := by
    induction l with
    | zero => simp
    | succ l ih =>
      rw [Finset.sum_range_succ, mul_add, ih, show 2 * (l + 1 + 1) = 2 * (l + 1) + 2 by omega,
        pow_add]
      ring
  simpa [supportPolynomial, show 2 * (2 * m + 1 + 1) = 4 * (m + 1) by omega] using he (2 * m + 1)

private lemma coeff_supportPolynomial (m k : ℕ) :
    (supportPolynomial m).coeff k =
      if 0 < k ∧ k < 4 * (m + 1) ∧ Even k then 1 else 0 := by
  classical
  unfold supportPolynomial
  rw [Polynomial.finsetSum_coeff]
  split_ifs with hk
  · obtain ⟨hp, ht, j, hj⟩ := hk
    rw [Finset.sum_eq_single (j - 1)]
    · rw [Polynomial.coeff_X_pow, ite_eq_left (by omega)]
    · intro l hl hne
      rw [Polynomial.coeff_X_pow, ite_eq_right (by omega)]
    · intro hn
      simp only [Finset.mem_range] at hn
      omega
  · apply Finset.sum_eq_zero
    intro j hj
    rw [Polynomial.coeff_X_pow, ite_eq_right]
    intro h
    apply hk
    simp only [Finset.mem_range] at hj
    exact ⟨by omega, by omega, j + 1, by omega⟩

private lemma boundary_coeff (m : ℕ) (i j : Fin 2) :
    walkPolynomial signCoin 0 (4 * (m + 1)) i j =
      Polynomial.C (-alternatingCatalan m * uniformMatrix i j) * supportPolynomial m := by
  let n := 4 * (m + 1)
  have hn : n ≠ 0 := by dsimp [n]; omega
  have h := congrArg (fun A : SeriesMatrix => PowerSeries.coeff n (A i j)) boundary_even
  have hrescale : imaginaryMark ^ n = 1 := by
    dsimp [n]
    rw [pow_mul, imaginaryMark_fourth, one_pow]
  have hconstant : PowerSeries.coeff n ((2 : SeriesMatrix) i j) = 0 := by
    by_cases hij : i = j <;> simp [Matrix.ofNat_apply, hij, ← map_ofNat (PowerSeries.C (R := Poly)), PowerSeries.coeff_C, hn]
  have hleft :
      PowerSeries.coeff n ((1 - tvar ^ 2) *
        (boundary i j + PowerSeries.rescale imaginaryMark (boundary i j) - (2 : SeriesMatrix) i j)) =
      (1 - Polynomial.X ^ 2) * (2 * PowerSeries.coeff n (boundary i j)) := by
    rw [show (1 - tvar ^ 2 : Series) = PowerSeries.C (1 - (Polynomial.X : Poly) ^ 2) by
      simp [tvar]]
    rw [PowerSeries.coeff_C_mul]
    simp [PowerSeries.coeff_rescale, hrescale, hconstant, two_mul]
  have hright : PowerSeries.coeff n
      ((2 * positiveStepVar ^ 4 * catalanAt Polynomial.X -
        tvar ^ 2 * (2 * zvar ^ 4 * catalanAt 1)) *
        PowerSeries.C (Polynomial.C (uniformMatrix i j))) =
      2 * (Polynomial.X ^ n - Polynomial.X ^ 2) *
        Polynomial.C (alternatingCatalan m * uniformMatrix i j) := by
    have htwo : (2 : Series) = PowerSeries.C (2 : Poly) := (map_ofNat PowerSeries.C _).symm
    have hvar : tvar ^ 2 = PowerSeries.C (Polynomial.X ^ 2 : Poly) := by
      simp only [tvar, map_pow]
    rw [PowerSeries.coeff_mul_C, map_sub, ← markedStep_one, htwo, hvar]
    simp only [mul_assoc, PowerSeries.coeff_C_mul, positiveStepVar, n, coeff_step_catalan,
      one_pow, mul_one, map_mul]
    ring
  change PowerSeries.coeff n ((1 - tvar ^ 2) *
    (boundary i j + PowerSeries.rescale imaginaryMark (boundary i j) - (2 : SeriesMatrix) i j)) =
    PowerSeries.coeff n ((2 * positiveStepVar ^ 4 * catalanAt Polynomial.X -
      tvar ^ 2 * (2 * zvar ^ 4 * catalanAt 1)) *
        PowerSeries.C (Polynomial.C (uniformMatrix i j))) at h
  rw [hleft, hright, ← walkSeries_signCoin_zero] at h
  simp only [walkSeries, PowerSeries.coeff_mk] at h
  have hx : (1 - (Polynomial.X : Poly) ^ 2) ≠ 0 := by
    intro he
    have hc := congrArg (fun p : Poly => p.coeff 0) he
    norm_num [Polynomial.coeff_X_pow] at hc
  apply mul_left_cancel₀ (mul_ne_zero (show (2 : Poly) ≠ 0 by norm_num) hx)
  calc
    _ = 2 * (Polynomial.X ^ n - Polynomial.X ^ 2) *
        Polynomial.C (alternatingCatalan m * uniformMatrix i j) := by
          rw [← h]
          ring
    _ = _ := by
      let C := Polynomial.C (alternatingCatalan m * uniformMatrix i j)
      have hneg : Polynomial.C (-alternatingCatalan m * uniformMatrix i j) = -C := by
        rw [neg_mul, map_neg]
      rw [hneg]
      have hh : (1 - (Polynomial.X : Poly) ^ 2) * supportPolynomial m =
          Polynomial.X ^ 2 - Polynomial.X ^ n := supportPolynomial_mul m
      change 2 * (Polynomial.X ^ n - Polynomial.X ^ 2) * C =
        2 * (1 - Polynomial.X ^ 2) * (-C * supportPolynomial m)
      linear_combination 2 * C * hh

private lemma signCoin_allTimes (m k : ℕ) :
    amplitude signCoin (4 * (m + 1)) k =
      if 0 < k ∧ k < 4 * (m + 1) ∧ Even k then
        (-alternatingCatalan m) • uniformMatrix else 0 := by
  apply Matrix.ext
  intro i j
  rw [← coeff_returnWords, boundary_coeff, Polynomial.coeff_C_mul, coeff_supportPolynomial]
  split <;> simp

private lemma catalan_nonzero (m : ℕ) : catalan m ≠ 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [catalan_succ']
    have h := Finset.single_le_sum
      (f := fun ij : ℕ × ℕ => catalan ij.1 * catalan ij.2)
      (fun ij _ => Nat.zero_le _) (show (0, m) ∈ Finset.antidiagonal m by simp)
    rw [catalan_zero, one_mul] at h
    exact (lt_of_lt_of_le (Nat.pos_of_ne_zero ih) h).ne'

private lemma rotation_balanced_uniform (c : ℝ) (hc : c ≠ 0) (v : Fin 2 → ℂ)
    (hv : normSquared v = 1) (m : ℕ) : exactUniform (rotation c c) v (m + 1) := by
  have hR : rotation c c = (c : ℂ) • signCoin := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [rotation, signCoin]
  let a : ℝ := Complex.normSq ((c : ℂ) ^ (4 * (m + 1)) * -alternatingCatalan m) * 2
  have ha : 0 < a := by
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    have hm : (catalan m : ℂ) ≠ 0 := by exact_mod_cast catalan_nonzero m
    exact mul_pos (Complex.normSq_pos.mpr
      (mul_ne_zero (pow_ne_zero _ hc') (neg_ne_zero.mpr (mul_ne_zero (by simp) hm)))) (by norm_num)
  let supported := fun k : ℕ => 0 < k ∧ k < 4 * (m+1) ∧ Even k
  have (k : ℕ) : Decidable (supported k) := inferInstanceAs (Decidable (0 < k ∧ k < 4 * (m+1) ∧ Even k))
  have hw (k : ℕ) :
      weight (rotation c c) v (4 * (m + 1)) k = if supported k then a else 0 := by
    rw [weight, hR, amplitude_scale, signCoin_allTimes]
    split
    · rw [smul_smul, Matrix.smul_mulVec, normSquared_smul, uniformMatrix_norm v hv]
    · simp [normSquared]
  let S := (Finset.range (2*m+1)).image fun j => 2 * (j+1)
  have hS : (Finset.range (4*(m+1)+1)).filter supported = S := by
    ext k
    simp only [S, Finset.mem_filter, Finset.mem_range, Finset.mem_image, supported]
    constructor
    · rintro ⟨_, hp, hk, j, hj⟩
      exact ⟨j-1, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨by omega, by omega, by omega, j+1, by omega⟩
  have hScard : S.card = 2*m+1 := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro u v h
      change 2 * (u + 1) = 2 * (v + 1) at h
      omega
  have hsum : (∑ j ∈ Finset.range (4 * (m+1) + 1), weight (rotation c c) v (4 * (m+1)) j) =
      (2 * (m : ℝ) + 1) * a := by
    simp only [hw, ← Finset.sum_filter, hS, Finset.sum_const, hScard, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  unfold exactUniform
  rw [hsum]
  refine ⟨by positivity, fun k => ?_⟩
  rw [hw]
  by_cases hk : 0 < k ∧ k < 4 * (m + 1) ∧ Even k
  · simp only [supported, ite_eq_left hk]
    have hn : (2 * (m : ℝ) + 1) * a ≠ 0 := by positivity
    apply (div_eq_iff hn).mpr
    have hpositive : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
    have hden : 2 * ((m + 1 : ℕ) : ℝ) - 1 = 2 * (m : ℝ) + 1 := by push_cast; ring
    rw [hden, ← mul_assoc, one_div_mul_cancel hpositive, one_mul]
  · simp [supported, hk]

end FormalSeries

/-- The time-eight test, balance in the direction basis, and all positive
multiples of four give equivalent conditions. -/
theorem exactUniform_rigidity
    (U : Matrix (Fin 2) (Fin 2) ℂ) (φ : Fin 2 → ℂ)
    (hU : Uᴴ * U = 1) (hφ : (∑ i, Complex.normSq (φ i)) = 1) :
    (exactUniform U φ 2 ↔ ∀ i j, ‖U i j‖ = 1 / Real.sqrt 2) ∧
      ((∀ i j, ‖U i j‖ = 1 / Real.sqrt 2) ↔
        ∀ m : ℕ, 1 ≤ m → exactUniform U φ m) := by
  obtain ⟨c, s, hc, hs, hcs, p, v, hp, hv, hentries⟩ := normal_form U hU
  have hu := unit_after_phases v φ hv hφ
  have hmod (i j : Fin 2) : ‖U i j‖ = if i = j then c else s := by
    rw [hentries, Complex.norm_mul, Complex.norm_mul]
    have hphase {z : ℂ} (h : Complex.normSq z = 1) : ‖z‖ = 1 := by
      rw [Complex.norm_def, h, Real.sqrt_one]
    rw [hphase (hp i), hphase (hv j), one_mul, mul_one, rotation_modulus c s hc hs]
  have necessity (h : exactUniform U φ 2) : ∀ i j, ‖U i j‖ = 1 / Real.sqrt 2 := by
    have hrot := (exactUniform_phases U (rotation c s) p v hp hv hentries φ 2).mp h
    have heq := rotation_necessary c s _ hc hs hcs hu hrot
    have htarget : (1 / Real.sqrt 2) ^ 2 = (1 / 2 : ℝ) := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hcval : c = 1 / Real.sqrt 2 := by
      apply (sq_eq_sq₀ hc (by positivity)).mp
      rw [htarget]
      rw [← heq] at hcs
      linarith
    intro i j
    rw [hmod, ← heq, ite_self, hcval]
  have sufficiency (h : ∀ i j, ‖U i j‖ = 1 / Real.sqrt 2) (m : ℕ) (hm : 1 ≤ m) :
      exactUniform U φ m := by
    have hdiag : c = 1 / Real.sqrt 2 := by simpa only [hmod, ite_true] using h 0 0
    have hoff : s = 1 / Real.sqrt 2 := by simpa [hmod] using h 0 1
    have heq : s = c := hoff.trans hdiag.symm
    have hc' : c ≠ 0 := by rw [hdiag]; positivity
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    apply (exactUniform_phases U (rotation c s) p v hp hv hentries φ (j + 1)).mpr
    rw [heq]
    exact rotation_balanced_uniform c hc' _ hu j
  exact ⟨⟨necessity, fun h => sufficiency h 2 (by decide)⟩,
    ⟨sufficiency, fun h => necessity (h 2 (by decide))⟩⟩

end D5.S3.Quantum.Walks.HadamardSojournRigidity
