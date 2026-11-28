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

private lemma positiveIntervals_le (x : ℤ) (w : List Bool) :
    positiveIntervals x w ≤ w.length := by
  induction w generalizing x with
  | nil => simp [positiveIntervals]
  | cons b w ih =>
    have h := ih (x + displacement b)
    simp only [positiveIntervals, List.length_cons]
    split <;> omega

private lemma amplitude_zero_of_lt (U : Coin) {n k : ℕ} (h : n < k) :
    amplitude U n k = 0 := by
  have hempty : returningWords n k = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro w hw
    simp only [returningWords, List.mem_filter, decide_eq_true_eq] at hw
    have hlen := mem_words.mp hw.1
    have hle := positiveIntervals_le 0 w
    omega
  simp [amplitude, hempty]


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

private lemma signCoin_eight (k : ℕ) :
    amplitude signCoin 8 k =
      if k = 2 ∨ k = 4 ∨ k = 6 then uniformMatrix else 0 := by
  have hsmall (i : Fin 9) :
      amplitude signCoin 8 i.val =
        if i.val = 2 ∨ i.val = 4 ∨ i.val = 6 then uniformMatrix else 0 := by
    fin_cases i <;>
      ext a b <;> fin_cases a <;> fin_cases b <;>
      simp only [amplitude, list_sum_apply, List.map_map] <;>
      (conv in (returningWords 8 _) => reduce) <;>
      norm_num [wordOperator_cons_apply, wordOperator.eq_1, signCoin, uniformMatrix, direction]
  by_cases hk : k < 9
  · exact hsmall ⟨k, hk⟩
  · rw [amplitude_zero_of_lt _ (by omega)]
    exact (ite_eq_right (by omega)).symm

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

private lemma rotation_balanced_uniform_eight (c : ℝ) (hc : c ≠ 0) (v : Fin 2 → ℂ)
    (hv : normSquared v = 1) : exactUniform (rotation c c) v 2 := by
  have hR : rotation c c = (c : ℂ) • signCoin := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rotation, signCoin]
  let a : ℝ := Complex.normSq ((c : ℂ) ^ 8) * 2
  have ha : 0 < a := by
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    exact mul_pos (Complex.normSq_pos.mpr (pow_ne_zero _ hc')) (by norm_num)
  have hw (k : ℕ) :
      weight (rotation c c) v 8 k = if k = 2 ∨ k = 4 ∨ k = 6 then a else 0 := by
    rw [weight, hR, amplitude_scale, signCoin_eight]
    split
    · rw [Matrix.smul_mulVec, normSquared_smul, uniformMatrix_norm v hv]
    · simp [normSquared]
  have hsum : (∑ j ∈ Finset.range 9, weight (rotation c c) v 8 j) = 3 * a := by
    simp only [hw, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    ring
  have hsupport (k : ℕ) :
      (0 < k ∧ k < 8 ∧ Even k) ↔ k = 2 ∨ k = 4 ∨ k = 6 := by
    constructor
    · rintro ⟨h₀, h₈, j, hj⟩
      omega
    · rintro (rfl | rfl | rfl)
      · exact ⟨by decide, by decide, 1, rfl⟩
      · exact ⟨by decide, by decide, 2, rfl⟩
      · exact ⟨by decide, by decide, 3, rfl⟩
  unfold exactUniform
  change 0 < (∑ j ∈ Finset.range 9, _) ∧ _
  rw [hsum]
  refine ⟨by positivity, fun k => ?_⟩
  change weight (rotation c c) v 8 k / (3 * a) =
    if 0 < k ∧ k < 8 ∧ Even k then 1 / (2 * (2 : ℝ) - 1) else 0
  simp only [hw, hsupport k]
  split
  · norm_num
    have hn : 3 * a ≠ 0 := by positivity
    apply (div_eq_iff hn).mpr
    ring
  · simp

private lemma rotation_modulus (c s : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s) (i j : Fin 2) :
    ‖rotation c s i j‖ = if i = j then c else s := by
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Real.norm_eq_abs, abs_of_nonneg hc, abs_of_nonneg hs]

/-- At time eight the conditional law is defined and uniform on counts two, four and six
exactly when the unitary coin has all four moduli equal to the reciprocal square root of two. -/
theorem exactUniform_eight_iff
    (U : Matrix (Fin 2) (Fin 2) ℂ) (φ : Fin 2 → ℂ)
    (hU : Uᴴ * U = 1) (hφ : (∑ i, Complex.normSq (φ i)) = 1) :
    exactUniform U φ 2 ↔ ∀ i j, ‖U i j‖ = 1 / Real.sqrt 2 := by
  obtain ⟨c, s, hc, hs, hcs, p, v, hp, hv, hentries⟩ := normal_form U hU
  have hu := unit_after_phases v φ hv hφ
  have hmod (i j : Fin 2) : ‖U i j‖ = if i = j then c else s := by
    rw [hentries, Complex.norm_mul, Complex.norm_mul]
    have hphase {z : ℂ} (h : Complex.normSq z = 1) : ‖z‖ = 1 := by
      rw [Complex.norm_def, h, Real.sqrt_one]
    rw [hphase (hp i), hphase (hv j), one_mul, mul_one, rotation_modulus c s hc hs]
  have htarget : (1 / Real.sqrt 2) ^ 2 = (1 / 2 : ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [exactUniform_phases U (rotation c s) p v hp hv hentries]
  constructor
  · intro h i j
    have heq := rotation_necessary c s _ hc hs hcs hu h
    have hcval : c = 1 / Real.sqrt 2 := by
      apply (sq_eq_sq₀ hc (by positivity)).mp
      rw [htarget]
      rw [← heq] at hcs
      linarith
    rw [hmod, ← heq, ite_self, hcval]
  · intro h
    have hdiag : c = 1 / Real.sqrt 2 := by simpa only [hmod, ite_true] using h 0 0
    have hoff : s = 1 / Real.sqrt 2 := by simpa [hmod] using h 0 1
    rw [← hoff] at hdiag
    subst c
    apply rotation_balanced_uniform_eight _ _ _ hu
    rw [hoff]
    positivity

end D5.S3.Quantum.Walks.HadamardSojournRigidity
