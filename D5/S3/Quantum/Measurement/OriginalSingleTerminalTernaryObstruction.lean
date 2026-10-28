/- GID: D5/S3/Quantum/Measurement/OriginalSingleTerminalTernaryObstruction
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/OriginalSingleTerminalTernaryObstruction
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: Complete original causal single-terminal records obey a common closed ternary score obstruction. -/

import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.Quantum.Tomography.RankOneContextCommutator
import D5.S3.Quantum.FiniteDimensional
import D5.S3.TotalVariation.Metric
import D5.S3.Weil.ZetaLinear.RankTrace

/-! # Original single-terminal ternary obstruction

The actual finite causal branch law supplies a common continuous score halfspace
for joint ternary postprocessing, its convex hull and its operator-norm closure.
-/

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace D5.S3.Quantum.Measurement.OriginalSingleTerminalTernaryObstruction

open D5.S3.Quantum.Tomography.RankOneContextCommutator
open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.FiniteDimensional
open D5.S3.TotalVariation.Pinsker
open D5.S3.TotalVariation.Metric

abbrev Mat := Matrix (Fin 3) (Fin 3) ℂ
abbrev Tuple := Fin 3 → Mat

def xi : Fin 3 → ℂ := fun _ => ((Real.sqrt 3 : ℝ) : ℂ)⁻¹
def e : Fin 3 → ℂ := ((Real.sqrt 6 : ℝ) : ℂ)⁻¹ • ![1, 1, -2]
def f : Fin 3 → ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • ![1, -1, 0]
def q : Fin 3 → ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (xi + e)
def originalU : Mat := !![1, 0, 0; 0, 0, 1; 0, 1, 0]
def W : Mat := 1 - (2 : ℂ) • rankOneDensity f
def E : Mat := rankOneDensity q

/-- The fixed original source, including its code-sector five-dimensional origin.
The bundled unitaries represent the original supplied unitary matrices. -/
structure Source where
  d : ℝ
  theta : ℝ
  d_pos : 0 < d
  d_lt_one : d < 1
  angle : Real.sin (2 * theta) ≠ 0
  V : Bool → Matrix.unitaryGroup (Fin 3) ℂ
  N : Matrix.unitaryGroup (Fin 3) ℂ
  V_zero : (V false : Mat) = originalU * NormedSpace.exp ((Complex.I * theta) • W)
  V_one : (V true : Mat) = (V false : Mat) * W
  mixing : (N : Mat) * rankOneDensity xi ≠ rankOneDensity xi * (N : Mat)
  B : Matrix (Fin 5) (Fin 3) ℂ
  isometry : Bᴴ * B = 1
  K : Bool → Matrix (Fin 5) (Fin 5) ℂ
  intertwines : ∀ b, K b * B = (Real.sqrt 2)⁻¹ • (B * (V b : Mat))

def preparation (S : Source) : Mat :=
  rankOneDensity (((Real.sqrt S.d : ℝ) : ℂ) • (originalU *ᵥ q) +
    (Complex.I * (Real.sqrt (1 - S.d) : ℝ)) • (originalU *ᵥ f))

inductive Letter
  | j (b : Bool)
  | n
  deriving DecidableEq

/-- Only the two original instrument outcomes, the same installed control,
and a single terminal followed by stopping occur in this syntax. Marks are
arbitrary deterministic functions of the full history, including timeout and mismatch. -/
inductive CausalTree (Mark : Type)
  | stop (mark : Mark)
  | control (next : CausalTree Mark)
  | instrument (zero one : CausalTree Mark)

namespace CausalTree
variable {Mark : Type}

def Leaf : CausalTree Mark → Type
  | .stop _ => Unit
  | .control t => Leaf t
  | .instrument t u => Leaf t ⊕ Leaf u

instance leafFintype (t : CausalTree Mark) : Fintype (Leaf t) := by
  induction t with
  | stop _ => exact inferInstanceAs (Fintype Unit)
  | control t ih => exact ih
  | instrument t u ht hu =>
      letI := ht
      letI := hu
      exact inferInstanceAs (Fintype (Leaf t ⊕ Leaf u))

def word : (t : CausalTree Mark) → Leaf t → List Letter
  | .stop _, _ => []
  | .control t, l => .n :: word t l
  | .instrument t _, .inl l => .j false :: word t l
  | .instrument _ u, .inr l => .j true :: word u l

def mark : (t : CausalTree Mark) → Leaf t → Mark
  | .stop m, _ => m
  | .control t, l => mark t l
  | .instrument t _, .inl l => mark t l
  | .instrument _ u, .inr l => mark u l
end CausalTree

def jcount : List Letter → ℕ
  | [] => 0
  | .n :: w => jcount w
  | .j _ :: w => jcount w + 1

def alpha (w : List Letter) : ℝ := (1 / 2 : ℝ) ^ jcount w

def gate (S : Source) : Letter → Matrix.unitaryGroup (Fin 3) ℂ
  | .j b => S.V b
  | .n => S.N

def wordUnitary (S : Source) : List Letter → Matrix.unitaryGroup (Fin 3) ℂ
  | [] => 1
  | a :: w => wordUnitary S w * gate S a

def branch (S : Source) (a : Letter) (X : Mat) : Mat :=
  match a with
  | .j b => (1 / 2 : ℝ) • ((S.V b : Mat) * X * star (S.V b : Mat))
  | .n => (S.N : Mat) * X * star (S.N : Mat)

def wordRun (S : Source) : List Letter → Mat → Mat
  | [], X => X
  | a :: w, X => wordRun S w (branch S a X)

def leafRun {Mark : Type} (S : Source) :
    (t : CausalTree Mark) → t.Leaf → Mat → Mat
  | .stop _, _, X => X
  | .control t, l, X => leafRun S t l (branch S .n X)
  | .instrument t _, .inl l, X => leafRun S t l (branch S (.j false) X)
  | .instrument _ u, .inr l, X => leafRun S u l (branch S (.j true) X)

def terminal (b : Bool) : Mat := if b then E else 1 - E

def leafProbability {Mark : Type} (S : Source) (t : CausalTree Mark)
    (X : Mat) (l : t.Leaf) (b : Bool) : ℝ :=
  (Matrix.trace (terminal b * leafRun S t l X)).re

def leafProjection {Mark : Type} (S : Source) (t : CausalTree Mark)
    (l : t.Leaf) : Mat :=
  star (wordUnitary S (t.word l) : Mat) * E * (wordUnitary S (t.word l) : Mat)

private theorem word_run (S : Source) (w : List Letter) (X : Mat) :
    wordRun S w X = alpha w •
      ((wordUnitary S w : Mat) * X * star (wordUnitary S w : Mat)) := by
  induction w generalizing X with
  | nil => simp [wordRun, alpha, jcount, wordUnitary]
  | cons a w ih =>
    cases a with
    | n =>
      simp [wordRun, ih, branch, alpha, jcount, wordUnitary, gate, star_mul,
        mul_assoc]
    | j b =>
      simp [wordRun, ih, branch, alpha, jcount, wordUnitary, gate, star_mul,
        mul_assoc, pow_succ, smul_smul]

private theorem leaf_run {Mark : Type} (S : Source) (t : CausalTree Mark)
    (l : t.Leaf) (X : Mat) : leafRun S t l X = wordRun S (t.word l) X := by
  induction t generalizing X with
  | stop m => rfl
  | control t ih => exact ih l (branch S .n X)
  | instrument t u ht hu => cases l with
    | inl l => exact ht l (branch S (.j false) X)
    | inr l => exact hu l (branch S (.j true) X)

private theorem alpha_sum {Mark : Type} (t : CausalTree Mark) :
    ∑ l : t.Leaf, alpha (t.word l) = 1 := by
  induction t with
  | stop m =>
    change (∑ _ : Unit, (1 : ℝ)) = 1
    simp
  | control t ih => exact ih
  | instrument t u ht hu =>
    change (∑ l : t.Leaf ⊕ u.Leaf, alpha ((CausalTree.instrument t u).word l)) = 1
    rw [Fintype.sum_sum_type]
    simp only [CausalTree.word, alpha, jcount, pow_succ, ← Finset.sum_mul]
    change (∑ l : t.Leaf, alpha (t.word l)) * (1 / 2) +
      (∑ l : u.Leaf, alpha (u.word l)) * (1 / 2) = 1
    rw [ht, hu]
    norm_num

private theorem alpha_positive (w : List Letter) : 0 < alpha w := by
  exact pow_pos (by norm_num) _

private theorem leaf_born {Mark : Type} (S : Source) (t : CausalTree Mark)
    (X : Mat) (l : t.Leaf) (b : Bool) :
    leafProbability S t X l b = alpha (t.word l) *
      (Matrix.trace ((if b then leafProjection S t l else 1 - leafProjection S t l) * X)).re := by
  have hU := Matrix.UnitaryGroup.star_mul_self (wordUnitary S (t.word l))
  rw [leafProbability, leaf_run, word_run]
  simp only [Matrix.mul_smul, Matrix.trace_smul]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  congr 1
  have hcycle := Matrix.trace_mul_cycle (terminal b) ((wordUnitary S (t.word l) : Mat) * X)
    (star (wordUnitary S (t.word l) : Mat))
  have hpull : star (wordUnitary S (t.word l) : Mat) * terminal b *
      (wordUnitary S (t.word l) : Mat) =
      if b then leafProjection S t l else 1 - leafProjection S t l := by
    cases b <;> simp [terminal, leafProjection, mul_sub, sub_mul, hU]
  congr 1
  rw [← hpull]
  simpa only [mul_assoc] using hcycle



private theorem q_unit : star q ⬝ᵥ q = 1 := by
  have h2 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h6 : (Real.sqrt 6 : ℝ) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  simp [q, xi, e, dotProduct, Fin.sum_univ_succ, Pi.star_apply,
    Matrix.vecHead, Matrix.vecTail]
  ring_nf
  simp only [map_ofNat]
  ring_nf
  have hc2 : (((Real.sqrt 2 : ℝ) : ℂ) ^ 2) = 2 := by exact_mod_cast h2
  have hc3 : (((Real.sqrt 3 : ℝ) : ℂ) ^ 2) = 3 := by exact_mod_cast h3
  have hc6 : (((Real.sqrt 6 : ℝ) : ℂ) ^ 2) = 6 := by exact_mod_cast h6
  have hi2 : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ 2 = 1 / 2 := by
    rw [inv_pow, hc2]; norm_num
  have hi3 : (((Real.sqrt 3 : ℝ) : ℂ)⁻¹) ^ 2 = 1 / 3 := by
    rw [inv_pow, hc3]; norm_num
  have hi6 : (((Real.sqrt 6 : ℝ) : ℂ)⁻¹) ^ 2 = 1 / 6 := by
    rw [inv_pow, hc6]; norm_num
  rw [hi2, hi3, hi6]
  norm_num

private theorem E_rank_one : IsNormalizedRankOneProjection E := by
  have hh := pure_state_handshake q q_unit
  refine ⟨?_, (hh 1).1, ?_, ?_⟩
  · simp [E, rankOneDensity, Matrix.conjTranspose_vecMulVec]
  · simpa only [E, rankOneDensity, Matrix.trace_vecMulVec, dotProduct_comm] using q_unit
  · intro X
    rw [E, (hh X).2.1, (hh X).2.2, Matrix.trace_mul_comm]

private theorem projector_positive {P : Mat} (hP : IsNormalizedRankOneProjection P) :
    P.PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose P
  simpa only [hP.1, hP.2.1] using h

private theorem complement_positive {P : Mat} (hP : IsNormalizedRankOneProjection P) :
    (1 - P).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose (1 - P)
  have hs : (1 - P)ᴴ = 1 - P := by simp [hP.1]
  have hi : (1 - P) * (1 - P) = 1 - P := by
    noncomm_ring [hP.2.1]
  simpa only [hs, hi] using h

private theorem conjugate_rank_one (S : Source) (w : List Letter) :
    IsNormalizedRankOneProjection
      (star (wordUnitary S w : Mat) * E * (wordUnitary S w : Mat)) := by
  let U : Mat := wordUnitary S w
  have hU : star U * U = 1 := (wordUnitary S w).2.1
  have hU' : U * star U = 1 := (wordUnitary S w).2.2
  have hE := E_rank_one
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (star U * E * U)ᴴ = star U * E * U
    simp only [← Matrix.star_eq_conjTranspose, star_mul, star_star]
    rw [show star E = E from hE.1]
    simp only [mul_assoc]
  · change star U * E * U * (star U * E * U) = star U * E * U
    calc
      _ = star U * (E * (U * star U) * E) * U := by noncomm_ring
      _ = _ := by rw [hU', mul_one, hE.2.1]
  · rw [Matrix.trace_mul_cycle, hU', one_mul, hE.2.2.1]
  · intro X
    change star U * E * U * X * (star U * E * U) = _
    calc
      _ = star U * (E * (U * X * star U) * E) * U := by noncomm_ring
      _ = star U * (Matrix.trace (E * (U * X * star U)) • E) * U := by
        rw [hE.2.2.2]
      _ = Matrix.trace (star U * E * U * X) • (star U * E * U) := by
        have ht : Matrix.trace (E * (U * X * star U)) =
            Matrix.trace (star U * E * U * X) := by
          simpa only [mul_assoc] using Matrix.trace_mul_cycle E (U * X) (star U)
        rw [ht]
        simp only [mul_smul_comm, smul_mul_assoc]

private theorem overlap_bounds {P R : Mat}
    (hP : IsNormalizedRankOneProjection P) (hR : IsNormalizedRankOneProjection R) :
    0 ≤ (Matrix.trace (P * R)).re ∧ (Matrix.trace (P * R)).re ≤ 1 := by
  have hp := born_probability_skeleton P (projector_positive hP) hP.2.2.1
  have hl := hp.2.2 R (by simpa only [Matrix.star_eq_conjTranspose] using hR.1) hR.2.1
  have hc : (1 - R) * (1 - R) = 1 - R := by noncomm_ring [hR.2.1]
  have hu := hp.2.2 (1 - R) (by simp [Matrix.star_eq_conjTranspose, hR.1]) hc
  have hl' := (Complex.nonneg_iff.mp hl).1
  have hu' := (Complex.nonneg_iff.mp hu).1
  simp only [bornProbability, Matrix.mul_sub, Matrix.mul_one,
    Matrix.trace_sub, hP.2.2.1, Complex.sub_re, Complex.one_re] at hl' hu'
  exact ⟨hl', by linarith⟩



private theorem projector_norm {P : Mat} (hP : IsNormalizedRankOneProjection P) :
    ‖P‖ = 1 := by
  have hn : P ≠ 0 := by
    intro hz
    have ht := hP.2.2.1
    simp only [hz, Matrix.trace_zero] at ht
    exact zero_ne_one ht
  have hp : 0 < ‖P‖ := norm_pos_iff.mpr hn
  have heq : ‖P‖ * ‖P‖ = ‖P‖ := by
    rw [← CStarRing.norm_star_mul_self, show star P = P from hP.1, hP.2.1]
  nlinarith

private theorem projector_trace_bound {P : Mat} (hP : IsNormalizedRankOneProjection P)
    (X : Mat) : |(Matrix.trace (P * X)).re| ≤ ‖X‖ := by
  have hn := congrArg norm (hP.2.2.2 X)
  rw [norm_smul, projector_norm hP, mul_one] at hn
  calc
    |(Matrix.trace (P * X)).re| ≤ ‖Matrix.trace (P * X)‖ := Complex.abs_re_le_norm _
    _ = ‖P * X * P‖ := hn.symm
    _ ≤ ‖P * X‖ * ‖P‖ := norm_mul_le _ _
    _ ≤ (‖P‖ * ‖X‖) * ‖P‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = ‖X‖ := by rw [projector_norm hP]; ring

/-- A single joint stochastic relabeling of both terminal cells of every actual leaf. -/
def Stochastic {Mark : Type} (t : CausalTree Mark) :=
  {c : t.Leaf → Bool → Fin 3 → ℝ //
    (∀ l b a, 0 ≤ c l b a) ∧ (∀ l b, ∑ a, c l b a = 1)}

def effects {Mark : Type} (S : Source) (t : CausalTree Mark) (c : Stochastic t) : Tuple :=
  fun a => ∑ l : t.Leaf, alpha (t.word l) •
    (c.1 l true a • leafProjection S t l + c.1 l false a • (1 - leafProjection S t l))

def postProbability {Mark : Type} (S : Source) (t : CausalTree Mark)
    (c : Stochastic t) (X : Mat) (a : Fin 3) : ℝ :=
  ∑ l : t.Leaf, ∑ b : Bool, c.1 l b a * leafProbability S t X l b

def score (B : RankOneContext 3) (M : Tuple) : ℝ :=
  (∑ i, (Matrix.trace (B.projector i * M i)).re) / 3

def IsPOVM (M : Tuple) : Prop :=
  (∀ a, (M a).PosSemidef) ∧ ∑ a, M a = 1

def operationalImage (S : Source) (Mark : Type) : Set Tuple :=
  {M | ∃ (t : CausalTree Mark) (c : Stochastic t), M = effects S t c}

private theorem effects_sum {Mark : Type} (S : Source) (t : CausalTree Mark)
    (c : Stochastic t) : ∑ a, effects S t c a = 1 := by
  have hleaf (l : t.Leaf) : ∑ a : Fin 3,
      (c.1 l true a • leafProjection S t l +
        c.1 l false a • (1 - leafProjection S t l)) = 1 := by
    rw [Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.sum_smul,
      c.2.2 l true, c.2.2 l false]
    simp
  calc
    _ = ∑ l : t.Leaf, alpha (t.word l) • (∑ a : Fin 3,
      (c.1 l true a • leafProjection S t l +
        c.1 l false a • (1 - leafProjection S t l))) := by
        simp only [effects, Finset.smul_sum]
        exact Finset.sum_comm
    _ = (∑ l : t.Leaf, alpha (t.word l)) • (1 : Mat) := by
      simp only [hleaf, Finset.sum_smul]
    _ = 1 := by rw [alpha_sum]; simp

private theorem effects_positive {Mark : Type} (S : Source) (t : CausalTree Mark)
    (c : Stochastic t) (a : Fin 3) : (effects S t c a).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro l _
  have hr := conjugate_rank_one S (t.word l)
  exact ((projector_positive hr).smul (c.2.1 l true a) |>.add
    ((complement_positive hr).smul (c.2.1 l false a))).smul
    (alpha_positive (t.word l)).le

private theorem post_born {Mark : Type} (S : Source) (t : CausalTree Mark)
    (c : Stochastic t) (X : Mat) (a : Fin 3) :
    postProbability S t c X a = (Matrix.trace (effects S t c a * X)).re := by
  simp only [postProbability, effects, Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Fintype.sum_bool, leaf_born, Bool.false_eq_true, ↓reduceIte,
    Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
    Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring



private theorem leaf_score (B : RankOneContext 3) (R : Mat)
    (hR : IsNormalizedRankOneProjection R) (c : Bool → Fin 3 → ℝ)
    (hc : ∀ b i, 0 ≤ c b i) (hs : ∀ b, ∑ i, c b i = 1) :
    ∑ i, (Matrix.trace (B.projector i *
      (c true i • R + c false i • (1 - R)))).re ≤ 2 := by
  have hb (i : Fin 3) := overlap_bounds (B.rankOne i) hR
  have h1 : ∑ i, c true i * (Matrix.trace (B.projector i * R)).re ≤ 1 := by
    calc
      _ ≤ ∑ i, c true i * 1 := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hb i).2 (hc true i)
      _ = 1 := by simpa using hs true
  have h0 : ∑ i, c false i * (1 - (Matrix.trace (B.projector i * R)).re) ≤ 1 := by
    calc
      _ ≤ ∑ i, c false i * 1 := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (by linarith [(hb i).1]) (hc false i)
      _ = 1 := by simpa using hs false
  have heq : (∑ i, (Matrix.trace (B.projector i *
      (c true i • R + c false i • (1 - R)))).re) =
      (∑ i, c true i * (Matrix.trace (B.projector i * R)).re) +
      (∑ i, c false i * (1 - (Matrix.trace (B.projector i * R)).re)) := by
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one,
      Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, Complex.add_re,
      Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.sub_re, (B.rankOne _).2.2.1, Complex.one_re,
      Finset.sum_add_distrib]
  rw [heq]
  linarith

private theorem effects_score {Mark : Type} (S : Source) (t : CausalTree Mark)
    (c : Stochastic t) (B : RankOneContext 3) : score B (effects S t c) ≤ 2 / 3 := by
  have hleaf (l : t.Leaf) := leaf_score B (leafProjection S t l)
    (conjugate_rank_one S (t.word l)) (c.1 l) (c.2.1 l) (c.2.2 l)
  have hsum : (∑ i, (Matrix.trace (B.projector i * effects S t c i)).re) ≤ 2 := by
    calc
      _ = ∑ l : t.Leaf, alpha (t.word l) * (∑ i,
        (Matrix.trace (B.projector i *
          (c.1 l true i • leafProjection S t l +
            c.1 l false i • (1 - leafProjection S t l)))).re) := by
        simp only [effects, Matrix.mul_smul, Matrix.trace_sum,
          Matrix.trace_smul, Complex.re_sum, Complex.real_smul, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Finset.mul_sum]
        exact Finset.sum_comm
      _ ≤ ∑ l : t.Leaf, alpha (t.word l) * 2 := Finset.sum_le_sum fun l _ =>
        mul_le_mul_of_nonneg_left (hleaf l) (alpha_positive (t.word l)).le
      _ = 2 := by rw [← Finset.sum_mul, alpha_sum]; norm_num
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).2 (by linarith)

private theorem score_continuous (B : RankOneContext 3) : Continuous (score B) := by
  unfold score Matrix.trace Matrix.diag
  fun_prop

private theorem score_combo (B : RankOneContext 3) (M L : Tuple) (a b : ℝ) :
    score B (a • M + b • L) = a * score B M + b * score B L := by
  simp only [score, Pi.add_apply, Pi.smul_apply, Matrix.mul_add, Matrix.mul_smul,
    Matrix.trace_add, Matrix.trace_smul, Complex.add_re, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

private theorem povm_convex : Convex ℝ {M : Tuple | IsPOVM M} := by
  intro M hM L hL a b ha hb hab
  constructor
  · intro i
    exact ((hM.1 i).smul ha).add ((hL.1 i).smul hb)
  · change (∑ i, (a • M i + b • L i)) = 1
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum,
      hM.2, hL.2, ← add_smul, hab, one_smul]

private theorem povm_closed : IsClosed {M : Tuple | IsPOVM M} := by
  have hp : IsClosed {M : Tuple | ∀ a, (M a).PosSemidef} := by
    convert isClosed_iInter (fun a : Fin 3 =>
      Matrix.posSemidef_is_closed.preimage
        (continuous_apply a : Continuous (fun M : Tuple => M a))) using 1
    ext M
    simp
  have hs : IsClosed {M : Tuple | ∑ a, M a = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  exact hp.inter hs

private theorem score_halfspace_convex (B : RankOneContext 3) :
    Convex ℝ {M : Tuple | score B M ≤ 2 / 3} := by
  intro M hM L hL a b ha hb hab
  change score B (a • M + b • L) ≤ 2 / 3
  rw [score_combo]
  calc
    _ ≤ a * (2 / 3) + b * (2 / 3) :=
      add_le_add (mul_le_mul_of_nonneg_left hM ha) (mul_le_mul_of_nonneg_left hL hb)
    _ = 2 / 3 := by rw [← add_mul, hab, one_mul]

private theorem closed_hull_score (S : Source) (Mark : Type) (B : RankOneContext 3)
    {M : Tuple} (hM : M ∈ closure (convexHull ℝ (operationalImage S Mark))) :
    IsPOVM M ∧ score B M ≤ 2 / 3 := by
  have hs : operationalImage S Mark ⊆ {M : Tuple | IsPOVM M ∧ score B M ≤ 2 / 3} := by
    rintro M ⟨t, c, rfl⟩
    exact ⟨⟨effects_positive S t c, effects_sum S t c⟩, effects_score S t c B⟩
  have hc : Convex ℝ {M : Tuple | IsPOVM M ∧ score B M ≤ 2 / 3} :=
    povm_convex.inter (score_halfspace_convex B)
  have ht : IsClosed {M : Tuple | IsPOVM M ∧ score B M ≤ 2 / 3} :=
    povm_closed.inter (isClosed_le (score_continuous B) continuous_const)
  exact closure_minimal (convexHull_min hs hc) ht hM



/-- The maximum across the three genuine Hilbert-L2 operator distances. -/
def maxDistance (B : RankOneContext 3) (M : Tuple) : ℝ :=
  max ‖M 0 - B.projector 0‖
    (max ‖M 1 - B.projector 1‖ ‖M 2 - B.projector 2‖)

private theorem max_distance_eq_pi_norm (B : RankOneContext 3) (M : Tuple) :
    maxDistance B M = ‖M - B.projector‖ := by
  apply le_antisymm
  · exact max_le (norm_le_pi_norm (M - B.projector) 0)
      (max_le (norm_le_pi_norm (M - B.projector) 1)
        (norm_le_pi_norm (M - B.projector) 2))
  · apply (pi_norm_le_iff_of_nonempty (M - B.projector)).2
    intro i
    fin_cases i
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)

private theorem small_correct_response (B : RankOneContext 3) (M : Tuple)
    (hscore : score B M ≤ 2 / 3) :
    ∃ i, (Matrix.trace (B.projector i * M i)).re ≤ 2 / 3 := by
  by_contra! h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  norm_num [score, Fin.sum_univ_succ] at hscore
  linarith

private theorem state_distribution (B : RankOneContext 3) (M : Tuple)
    (hM : IsPOVM M) (i : Fin 3) :
    (∀ a, 0 ≤ (Matrix.trace (B.projector i * M a)).re) ∧
      ∑ a, (Matrix.trace (B.projector i * M a)).re = 1 := by
  refine ⟨fun a => RHLinalg.trace_mul_nonneg_of_posSemidef
    (projector_positive (B.rankOne i)) (hM.1 a), ?_⟩
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.mul_sum, hM.2,
    Matrix.mul_one, (B.rankOne i).2.2.1, Complex.one_re]

private theorem ideal_basis_distribution (B : RankOneContext 3) (i a : Fin 3) :
    (Matrix.trace (B.projector i * B.projector a)).re = if a = i then 1 else 0 := by
  have hp := state_distribution B B.projector
    ⟨fun j => projector_positive (B.rankOne j), B.resolvesIdentity⟩ i
  have hd : (Matrix.trace (B.projector i * B.projector i)).re = 1 := by
    rw [(B.rankOne i).2.1, (B.rankOne i).2.2.1, Complex.one_re]
  by_cases ha : a = i
  · simpa only [ha, ite_true] using hd
  · rw [if_neg ha]
    have hbound := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ ({i, a} : Finset (Fin 3)))
      (fun j _ _ => hp.1 j)
    rw [Finset.sum_insert (by simp [Ne.symm ha]), Finset.sum_singleton, hd, hp.2] at hbound
    exact le_antisymm (by linarith) (hp.1 a)

private theorem separation (B : RankOneContext 3) (M : Tuple)
    (hM : IsPOVM M) (hscore : score B M ≤ 2 / 3) :
    (1 / 3 : ℝ) ≤ maxDistance B M ∧
      ∃ i : Fin 3, (B.projector i).PosSemidef ∧ Matrix.trace (B.projector i) = 1 ∧
        (∀ a, 0 ≤ (Matrix.trace (B.projector i * M a)).re) ∧
        (∑ a, (Matrix.trace (B.projector i * M a)).re) = 1 ∧
        (∀ a, (Matrix.trace (B.projector i * B.projector a)).re = if a = i then 1 else 0) ∧
        (1 / 3 : ℝ) ≤ totalVariation
          (fun a => (Matrix.trace (B.projector i * M a)).re)
          (fun a => (Matrix.trace (B.projector i * B.projector a)).re) := by
  obtain ⟨i, hi⟩ := small_correct_response B M hscore
  have hb := projector_trace_bound (B.rankOne i) (M i - B.projector i)
  simp only [Matrix.mul_sub, Matrix.trace_sub, (B.rankOne i).2.1,
    (B.rankOne i).2.2.1, Complex.sub_re, Complex.one_re] at hb
  have hn : (1 / 3 : ℝ) ≤ ‖M i - B.projector i‖ := by
    linarith [neg_le_abs ((Matrix.trace (B.projector i * M i)).re - 1)]
  have hp := state_distribution B M hM i
  have hsum : (∑ a, (Matrix.trace (B.projector i * M a)).re) =
      ∑ a : Fin 3, (if a = i then (1 : ℝ) else 0) := by
    rw [hp.2]
    simp
  have htv := (total_variation_eq_sup_event_gap
    (fun a => (Matrix.trace (B.projector i * M a)).re)
    (fun a => if a = i then 1 else 0) hsum).2
      (show |(∑ a ∈ ({i} : Finset (Fin 3)),
        (Matrix.trace (B.projector i * M a)).re) -
        ∑ a ∈ ({i} : Finset (Fin 3)), (if a = i then (1 : ℝ) else 0)| ∈
        Set.range (fun A : Finset (Fin 3) =>
          |(∑ a ∈ A, (Matrix.trace (B.projector i * M a)).re) -
            ∑ a ∈ A, (if a = i then (1 : ℝ) else 0)|) from ⟨{i}, rfl⟩)
  simp only [Finset.sum_singleton, ite_true] at htv
  constructor
  · rw [max_distance_eq_pi_norm]
    exact hn.trans (norm_le_pi_norm (M - B.projector) i)
  · refine ⟨i, projector_positive (B.rankOne i), (B.rankOne i).2.2.1, hp.1, hp.2,
      ideal_basis_distribution B i, ?_⟩
    simp_rw [ideal_basis_distribution]
    linarith [neg_le_abs ((Matrix.trace (B.projector i * M i)).re - 1)]



inductive Action
  | j
  | n

/-- A fixed action string with checkpoints and a past-label-dependent stopping table.
The end is forced, and continuing never changes the remaining action string. -/
def fixedStoppingTree {Mark : Type} (checkpoint : ℕ → Bool)
    (stop : List Letter → Bool) (mark : List Letter → Mark) :
    List Action → List Letter → CausalTree Mark
  | [], past => .stop (mark past)
  | a :: rest, past =>
    if checkpoint past.length && stop past then .stop (mark past)
    else match a with
      | .n => .control (fixedStoppingTree checkpoint stop mark rest (past ++ [.n]))
      | .j => .instrument
          (fixedStoppingTree checkpoint stop mark rest (past ++ [.j false]))
          (fixedStoppingTree checkpoint stop mark rest (past ++ [.j true]))

private theorem leaf_marginal {Mark : Type} (S : Source) (t : CausalTree Mark)
    (X : Mat) (hX : Matrix.trace X = 1) (l : t.Leaf) :
    ∑ b : Bool, leafProbability S t X l b = alpha (t.word l) := by
  simp only [Fintype.sum_bool, leaf_born, Bool.false_eq_true, ↓reduceIte,
    Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re,
    hX, Complex.one_re]
  ring

private theorem leaf_probability_positive {Mark : Type} (S : Source)
    (t : CausalTree Mark) (X : Mat) (hX : X.PosSemidef) (l : t.Leaf) (b : Bool) :
    0 ≤ leafProbability S t X l b := by
  have hstate : (leafRun S t l X).PosSemidef := by
    rw [leaf_run, word_run]
    exact (hX.mul_mul_conjTranspose_same (wordUnitary S (t.word l) : Mat)).smul
      (alpha_positive (t.word l)).le
  apply RHLinalg.trace_mul_nonneg_of_posSemidef _ hstate
  cases b
  · exact complement_positive E_rank_one
  · exact projector_positive E_rank_one



abbrev Mat5 := Matrix (Fin 5) (Fin 5) ℂ

def liftedControl (S : Source) : Mat5 :=
  S.B * (S.N : Mat) * S.Bᴴ + (1 - S.B * S.Bᴴ)

def liftedGate (S : Source) : Letter → Mat5
  | .j b => S.K b
  | .n => liftedControl S

def liftedWord (S : Source) : List Letter → Mat5
  | [] => 1
  | a :: w => liftedWord S w * liftedGate S a

def sqrtAlpha (w : List Letter) : ℝ := (Real.sqrt 2)⁻¹ ^ jcount w

def liftedTerminal (S : Source) (b : Bool) : Mat5 :=
  if b then S.B * E * S.Bᴴ else 1 - S.B * E * S.Bᴴ

def liftedProbability {Mark : Type} (S : Source) (t : CausalTree Mark)
    (X : Mat) (l : t.Leaf) (b : Bool) : ℝ :=
  (Matrix.trace (liftedTerminal S b *
    (liftedWord S (t.word l) * (S.B * X * S.Bᴴ) *
      (liftedWord S (t.word l))ᴴ))).re

private theorem lifted_control_code (S : Source) : liftedControl S * S.B = S.B * (S.N : Mat) := by
  simp [liftedControl, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, S.isometry]

private theorem word_intertwines (S : Source) (w : List Letter) :
    liftedWord S w * S.B = sqrtAlpha w • (S.B * (wordUnitary S w : Mat)) := by
  induction w with
  | nil => simp [liftedWord, sqrtAlpha, jcount, wordUnitary]
  | cons a w ih =>
    have hg : liftedGate S a * S.B =
        (match a with | .n => 1 | .j _ => (Real.sqrt 2)⁻¹) • (S.B * (gate S a : Mat)) := by
      cases a with
      | n => simpa [liftedGate, gate] using lifted_control_code S
      | j b => exact S.intertwines b
    calc
      _ = liftedWord S w * (liftedGate S a * S.B) := Matrix.mul_assoc _ _ _
      _ = _ := by
        rw [hg, Matrix.mul_smul, ← Matrix.mul_assoc, ih]
        cases a <;>
          simp [sqrtAlpha, jcount, wordUnitary, Matrix.mul_assoc, pow_succ,
            Matrix.smul_mul, smul_smul, mul_comm]

private theorem sqrt_alpha_square (w : List Letter) : sqrtAlpha w * sqrtAlpha w = alpha w := by
  have h2 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
    rw [← _root_.mul_inv_rev, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [sqrtAlpha, alpha, ← mul_pow, h2]

private theorem lifted_leaf_state {Mark : Type} (S : Source) (t : CausalTree Mark)
    (X : Mat) (l : t.Leaf) :
    liftedWord S (t.word l) * (S.B * X * S.Bᴴ) * (liftedWord S (t.word l))ᴴ =
      S.B * leafRun S t l X * S.Bᴴ := by
  rw [show liftedWord S (t.word l) * (S.B * X * S.Bᴴ) * (liftedWord S (t.word l))ᴴ =
      (liftedWord S (t.word l) * S.B) * X * (liftedWord S (t.word l) * S.B)ᴴ by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]]
  rw [word_intertwines, leaf_run, word_run]
  simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_mul,
    ← Matrix.star_eq_conjTranspose, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, sqrt_alpha_square, Matrix.mul_assoc]

private theorem terminal_pullback (S : Source) (b : Bool) :
    S.Bᴴ * liftedTerminal S b * S.B = terminal b := by
  have h1 : S.Bᴴ * (1 : Mat5) * S.B = 1 := by
    rw [Matrix.mul_one, S.isometry]
  have hE : S.Bᴴ * (S.B * E * S.Bᴴ) * S.B = E := by
    calc
      _ = (S.Bᴴ * S.B) * E * (S.Bᴴ * S.B) := by simp only [Matrix.mul_assoc]
      _ = E := by rw [S.isometry]; simp
  cases b <;> simp only [liftedTerminal, terminal, Bool.false_eq_true, ↓reduceIte,
    Matrix.mul_sub, Matrix.sub_mul, h1, hE]


private theorem lifted_leaf_probability {Mark : Type} (S : Source) (t : CausalTree Mark)
    (X : Mat) (l : t.Leaf) (b : Bool) :
    liftedProbability S t X l b = leafProbability S t X l b := by
  unfold liftedProbability
  rw [lifted_leaf_state]
  have ht := Matrix.trace_mul_comm
    (liftedTerminal S b * (S.B * leafRun S t l X)) S.Bᴴ
  have ht' : Matrix.trace (liftedTerminal S b * (S.B * leafRun S t l X * S.Bᴴ)) =
      Matrix.trace ((S.Bᴴ * liftedTerminal S b * S.B) * leafRun S t l X) := by
    simpa only [Matrix.mul_assoc] using ht
  rw [ht', terminal_pullback]
  rfl



private theorem f_unit : star f ⬝ᵥ f = 1 := by
  have h2 : (((Real.sqrt 2 : ℝ) : ℂ) ^ 2) = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  simp [f, dotProduct, Fin.sum_univ_succ]
  ring_nf
  rw [inv_pow, h2]
  norm_num

private theorem qf_orthogonal : star q ⬝ᵥ f = 0 ∧ star f ⬝ᵥ q = 0 := by
  constructor <;>
    simp [q, xi, e, f, dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail]

private theorem original_U_dot (v w : Fin 3 → ℂ) :
    star (originalU *ᵥ v) ⬝ᵥ (originalU *ᵥ w) = star v ⬝ᵥ w := by
  have hU : originalUᴴ * originalU = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [originalU, Matrix.mul_apply, Fin.sum_univ_succ]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    hU, Matrix.one_mulVec]

private theorem preparation_density (S : Source) :
    (preparation S).PosSemidef ∧ Matrix.trace (preparation S) = 1 := by
  refine ⟨Matrix.posSemidef_vecMulVec_self_star _, ?_⟩
  have hd : Real.sqrt S.d ^ 2 = S.d := Real.sq_sqrt S.d_pos.le
  have hd' : Real.sqrt (1 - S.d) ^ 2 = 1 - S.d :=
    Real.sq_sqrt (by linarith [S.d_lt_one])
  have hdC : ((Real.sqrt S.d : ℂ)) ^ 2 = S.d := by exact_mod_cast hd
  have hdC' : ((Real.sqrt (1 - S.d) : ℂ)) ^ 2 = 1 - S.d := by exact_mod_cast hd'
  rw [preparation, rankOneDensity, Matrix.trace_vecMulVec, dotProduct_comm]
  simp only [star_add, star_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, original_U_dot, q_unit, f_unit,
    qf_orthogonal.1, qf_orthogonal.2, smul_eq_mul, mul_zero,
    add_zero, zero_add, mul_one]
  simp only [Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  linear_combination hdC + hdC'

private theorem post_distribution {Mark : Type} (S : Source) (t : CausalTree Mark)
    (c : Stochastic t) (X : Mat) (hX : X.PosSemidef) (htr : Matrix.trace X = 1) :
    (∀ a, 0 ≤ postProbability S t c X a) ∧ ∑ a, postProbability S t c X a = 1 := by
  constructor
  · intro a
    rw [post_born]
    exact RHLinalg.trace_mul_nonneg_of_posSemidef (effects_positive S t c a) hX
  · simp_rw [post_born]
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul,
      effects_sum, Matrix.one_mul, htr, Complex.one_re]

/-- The common score, operator-distance and normalized mathematical basis-state
separation conclusions for one joint ternary POVM. -/
def BasisObstruction (B : RankOneContext 3) (M : Tuple) : Prop :=
  score B M ≤ 2 / 3 ∧ (1 / 3 : ℝ) ≤ maxDistance B M ∧
    ∃ i : Fin 3, (B.projector i).PosSemidef ∧ Matrix.trace (B.projector i) = 1 ∧
      (∀ a, 0 ≤ (Matrix.trace (B.projector i * M a)).re) ∧
      (∑ a, (Matrix.trace (B.projector i * M a)).re) = 1 ∧
      (∀ a, (Matrix.trace (B.projector i * B.projector a)).re = if a = i then 1 else 0) ∧
      (1 / 3 : ℝ) ≤ totalVariation
        (fun a => (Matrix.trace (B.projector i * M a)).re)
        (fun a => (Matrix.trace (B.projector i * B.projector a)).re)

/-- Complete original single-terminal inclusion and ternary obstruction.
The universal tree domain includes every fixed-string checkpoint/stopping table
through `fixedStoppingTree`. All input matrices in the Born identities are
mathematical inputs; `preparation S` remains the sole installed preparation. -/
theorem complete_original_single_terminal_ternary_obstruction (S : Source) (Mark : Type) :
    ((preparation S).PosSemidef ∧ Matrix.trace (preparation S) = 1) ∧
    (∀ t : CausalTree Mark,
      (∑ l : t.Leaf, alpha (t.word l)) = 1 ∧
      ∀ l : t.Leaf,
        0 < alpha (t.word l) ∧
        alpha (t.word l) = ((2 : ℝ) ^ jcount (t.word l))⁻¹ ∧
        IsNormalizedRankOneProjection (leafProjection S t l) ∧
        ∀ X : Mat,
          leafRun S t l X = alpha (t.word l) •
            ((wordUnitary S (t.word l) : Mat) * X *
              star (wordUnitary S (t.word l) : Mat)) ∧
          (∀ b : Bool, leafProbability S t X l b = alpha (t.word l) *
            (Matrix.trace ((if b then leafProjection S t l else
              1 - leafProjection S t l) * X)).re) ∧
          (∀ b : Bool, liftedProbability S t X l b = leafProbability S t X l b) ∧
          (X.PosSemidef → Matrix.trace X = 1 →
            (∀ b : Bool, 0 ≤ leafProbability S t X l b) ∧
              (∑ b : Bool, leafProbability S t X l b) = alpha (t.word l))) ∧
    (∀ (t : CausalTree Mark) (c : Stochastic t),
      IsPOVM (effects S t c) ∧
      (∀ (X : Mat) (a : Fin 3),
        postProbability S t c X a = (Matrix.trace (effects S t c a * X)).re) ∧
      (∀ X : Mat, X.PosSemidef → Matrix.trace X = 1 →
        (∀ a, 0 ≤ postProbability S t c X a) ∧ ∑ a, postProbability S t c X a = 1) ∧
      ∀ B : RankOneContext 3, BasisObstruction B (effects S t c)) ∧
    (∀ B : RankOneContext 3,
      Continuous (score B) ∧
      (∀ (M L : Tuple) (a b : ℝ),
        score B (a • M + b • L) = a * score B M + b * score B L) ∧
      Convex ℝ {M : Tuple | score B M ≤ 2 / 3} ∧
      IsClosed {M : Tuple | score B M ≤ 2 / 3} ∧
      (∀ M ∈ convexHull ℝ (operationalImage S Mark),
        IsPOVM M ∧ BasisObstruction B M) ∧
      (∀ M ∈ closure (convexHull ℝ (operationalImage S Mark)),
        IsPOVM M ∧ BasisObstruction B M) ∧
      ∀ M : Tuple, maxDistance B M = ‖M - B.projector‖) ∧
    (∀ X : Mat, ‖X‖ = ‖Matrix.toEuclideanCLM (𝕜 := ℂ) X‖) ∧
    (∀ (checkpoint : ℕ → Bool) (stop : List Letter → Bool)
      (mark : List Letter → Mark) (actions : List Action) (past : List Letter)
      (c : Stochastic (fixedStoppingTree checkpoint stop mark actions past)),
      effects S (fixedStoppingTree checkpoint stop mark actions past) c ∈
        operationalImage S Mark) := by
  refine ⟨preparation_density S, ?_, ?_, ?_, Matrix.cstar_norm_def, ?_⟩
  · intro t
    refine ⟨alpha_sum t, fun l => ?_⟩
    refine ⟨alpha_positive _, ?_, conjugate_rank_one S (t.word l), fun X => ?_⟩
    · simp [alpha, one_div, inv_pow]
    · refine ⟨?_, leaf_born S t X l, lifted_leaf_probability S t X l, ?_⟩
      · rw [leaf_run, word_run]
      · intro hX htr
        exact ⟨leaf_probability_positive S t X hX l, leaf_marginal S t X htr l⟩
  · intro t c
    refine ⟨⟨effects_positive S t c, effects_sum S t c⟩, post_born S t c,
      fun X hX htr => post_distribution S t c X hX htr, fun B => ?_⟩
    exact ⟨effects_score S t c B,
      separation B (effects S t c) ⟨effects_positive S t c, effects_sum S t c⟩
        (effects_score S t c B)⟩
  · intro B
    have hclosed (M : Tuple)
        (hM : M ∈ closure (convexHull ℝ (operationalImage S Mark))) :
        IsPOVM M ∧ BasisObstruction B M := by
      have h := closed_hull_score S Mark B hM
      exact ⟨h.1, h.2, separation B M h.1 h.2⟩
    exact ⟨score_continuous B, score_combo B, score_halfspace_convex B,
      isClosed_le (score_continuous B) continuous_const,
      fun M hM => hclosed M (subset_closure hM), hclosed, max_distance_eq_pi_norm B⟩
  · intro checkpoint stop mark actions past c
    exact ⟨fixedStoppingTree checkpoint stop mark actions past, c, rfl⟩

#print axioms complete_original_single_terminal_ternary_obstruction

end D5.S3.Quantum.Measurement.OriginalSingleTerminalTernaryObstruction
