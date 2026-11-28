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
import D5.S3.Combinatorics.Probability.QuantumWalks.HadamardSojournSeries
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

private lemma step_signCoin_series (b : Bool) :
    seriesStep signCoin b = if b then !![0, 0; 1, -1] else !![1, 1; 0, 0] := by
  apply Matrix.ext
  intro i j
  cases b <;> fin_cases i <;> fin_cases j <;>
    simp [seriesStep, signCoin, step, direction]

private def alternatingCatalan (m : ℕ) : ℂ := (-1 : ℂ) ^ m * (catalan m : ℂ)

private lemma signCoin_allTimes (m k : ℕ) :
    amplitude signCoin (4 * (m + 1)) k =
      if 0 < k ∧ k < 4 * (m + 1) ∧ Even k then
        (-alternatingCatalan m) • uniformMatrix else 0 := by
  obtain ⟨F, hF, hcoeff⟩ := Omega.HadamardSojournSeries.exists_solution
  have hs := series_recursion_unique signCoin F (fun x => by
    rw [step_signCoin_series, step_signCoin_series]
    exact hF x)
  apply Matrix.ext
  intro i j
  refine (coeff_returnWords signCoin (4 * (m + 1)) k i j).symm.trans ?_
  calc
    (walkPolynomial signCoin 0 (4 * (m + 1)) i j).coeff k =
        (PowerSeries.coeff (4 * (m + 1)) (walkSeries signCoin 0 i j)).coeff k := by
      rw [walkSeries, PowerSeries.coeff_mk]
    _ = _ := by
      rw [hs 0, Matrix.ite_apply]
      simp only [Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul, alternatingCatalan, uniformMatrix]
      exact hcoeff m k i j

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
