/- GID: D5/S3/Quantum/SpinFactor/OriginalDContract
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinFactor/OriginalDContract
   mirror-E: none(waiver:source-only-contract)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.CrossProduct]
   utility: none
   digest: The complete H2 original carrier, directed two-label positivity, and phase-balance contract.

This module records the exact original-domain contract used by the H2 classification.
The arbitrary original map is kept as a total function.  No regularity, unit row,
translation, bilinearity, or source-realisation premise is hidden in the definitions.
The classification and the finite two-axis rotation argument are downstream consumers.
-/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic

/-! Directed positivity and finite phase balance on the original spin factor. -/

noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace D5.S3.Quantum.SpinFactor.OriginalDContract

abbrev Vec := Fin 3 → ℝ
abbrev E := ℝ × Vec

def unit : E := (1, 0)

def dot (x y : Vec) : ℝ := x ⬝ᵥ y

def vnorm (x : Vec) : ℝ := Real.sqrt (dot x x)

def jordan (a b : E) : E :=
  (a.1 * b.1 + dot a.2 b.2, a.1 • b.2 + b.1 • a.2)

def cone (a : E) : Prop := vnorm a.2 ≤ a.1

def originalNorm (a : E) : ℝ := |a.1| + vnorm a.2

structure Evaluation where
  mass : ℝ
  vector : Vec
  positive : vnorm vector ≤ mass

def evaluate (α : Evaluation) (a : E) : ℝ :=
  α.mass * a.1 + dot α.vector a.2

def allEvaluations : Set Evaluation := Set.univ

def cross (x y : Vec) : Vec :=
  ![x 1 * y 2 - x 2 * y 1,
    x 2 * y 0 - x 0 * y 2,
    x 0 * y 1 - x 1 * y 0]

inductive Orientation where
  | plus
  | minus

def crossD (ε : Orientation) (a b : E) : E :=
  (0, match ε with | .plus => cross a.2 b.2 | .minus => -(cross a.2 b.2))

def scalarPart (a : E) : ℝ := a.1
def vectorPart (a : E) : Vec := a.2

def readout (D : E → E → E) (α : Evaluation) (a b : E) : ℂ :=
  (evaluate α (jordan a b) : ℂ) - Complex.I * (evaluate α (D a b) : ℂ)

def gram2 (D : E → E → E) (α : Evaluation) (a b : E) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![readout D α a a, readout D α a b;
     readout D α b a, readout D α b b]

/-- Actual directed complex two-label positivity, with both off-diagonal entries
    computed from the same original D. -/
def P2 (D : E → E → E) : Prop :=
  ∀ (α : Evaluation) (a b : E), (gram2 D α a b).PosSemidef

def squareReadout (D : E → E → E) (α : Evaluation) (b c : E) : ℝ :=
  evaluate α (jordan b b) + evaluate α (jordan c c) +
    2 * evaluate α (D b c)

def phaseR (D : E → E → E) (a b c : E) : E :=
  b + D a b - jordan a c

def phaseS (D : E → E → E) (a b c : E) : E :=
  c + jordan a b + D a c

/-- The original ±1 phase-square balance, retaining the same D in every slot. -/
def PB (D : E → E → E) : Prop :=
  ∀ (α : Evaluation) (a b c : E),
    squareReadout D α (phaseR D a b c) (phaseS D a b c) =
      squareReadout D α (b - D a b + jordan a c) (c - jordan a b - D a c)

def skew (D : E → E → E) : Prop := ∀ a b, D b a = -D a b

def zeroRows (D : E → E → E) : Prop :=
  (∀ b, D (0, 0) b = 0) ∧ (∀ a, D a (0, 0) = 0)

def proportionalZero (D : E → E → E) : Prop :=
  ∀ (r : ℝ) (a : E), D (r • a) a = 0 ∧ D a (r • a) = 0

def basicOriginalD (D : E → E → E) : Prop :=
  skew D ∧ zeroRows D ∧ proportionalZero D

def finiteDifference (D : E → E → E) (a b c : E) : E :=
  D (b + D a b - jordan a c) (c + jordan a b + D a c) -
    D (b - D a b + jordan a c) (c - jordan a b - D a c) +
    (2 : ℝ) • jordan b (D a b - jordan a c) +
    (2 : ℝ) • jordan c (jordan a b + D a c)

def classificationStatement : Prop :=
  ∀ D : E → E → E, P2 D ∧ PB D ↔
    ∃ ε : Orientation, ∀ a b, D a b = crossD ε a b

private def evaluationLinear (α : Evaluation) : E →ₗ[ℝ] ℝ where
  toFun := evaluate α
  map_add' a b := by
    simp [evaluate, dot, dotProduct, Fin.sum_univ_three]
    ring
  map_smul' r a := by
    simp [evaluate, dot, dotProduct, Fin.sum_univ_three, smul_eq_mul]
    ring

private theorem evaluations_separate (a b : E)
    (h : ∀ α : Evaluation, evaluate α a = evaluate α b) : a = b := by
  have hs := h ⟨1, 0, by norm_num [vnorm, dot, dotProduct]⟩
  simp only [evaluate, one_mul, dot, zero_dotProduct, add_zero] at hs
  apply Prod.ext hs
  funext i
  have hv := h ⟨1, Pi.single i 1, by simp [vnorm, dot, single_dotProduct]⟩
  simp [evaluate, dot, single_dotProduct] at hv
  linarith

/-- The two directed entries force antisymmetry of the same total map. -/
theorem p2_skew (D : E → E → E) (hP : P2 D) : skew D := by
  intro a b
  apply evaluations_separate
  intro α
  have h := congrArg Complex.im ((hP α a b).1.apply 0 1)
  simp [gram2, readout, Complex.star_def] at h
  change evaluate α (D b a) = evaluationLinear α (-D a b)
  rw [map_neg]
  exact h

private theorem zero_of_eq_neg (a : E) (h : a = -a) : a = 0 := by
  apply Prod.ext
  · change a.1 = 0
    exact CharZero.eq_neg_self_iff.mp (congrArg Prod.fst h)
  · funext i
    change a.2 i = 0
    exact CharZero.eq_neg_self_iff.mp (congrArg (fun e : E => e.2 i) h)

private theorem p2_self (D : E → E → E) (hP : P2 D) (a : E) : D a a = 0 :=
  zero_of_eq_neg _ (p2_skew D hP a a)

/-- The exact real determinant bound retains the real off-diagonal entry. -/
theorem p2_determinant_bound (D : E → E → E) (hP : P2 D)
    (α : Evaluation) (a b : E) :
    (evaluate α (D a b)) ^ 2 ≤
      evaluate α (jordan a a) * evaluate α (jordan b b) -
        (evaluate α (jordan a b)) ^ 2 := by
  have hd := (hP α a b).det_nonneg
  have hj : jordan b a = jordan a b := by
    apply Prod.ext
    · simp [jordan, dot, dotProduct_comm, mul_comm, add_comm]
    · simp [jordan, add_comm]
  have hsk := p2_skew D hP a b
  have he : evaluate α (D b a) = -evaluate α (D a b) := by
    change evaluationLinear α (D b a) = -evaluationLinear α (D a b)
    rw [hsk, map_neg]
  have ez : evaluate α 0 = 0 := by simp [evaluate, dot]
  have hd' := (Complex.nonneg_iff.mp hd).1
  simp [Matrix.det_fin_two, gram2, readout, p2_self D hP, hj, he,
    ez, Complex.mul_re, Complex.mul_im] at hd'
  nlinarith

/-- Proportional original inputs vanish, including zero and negative scaling. -/
theorem p2_proportional (D : E → E → E) (hP : P2 D) : proportionalZero D := by
  intro r a
  have hz : D (r • a) a = 0 := by
    apply evaluations_separate
    intro α
    have hb := p2_determinant_bound D hP α (r • a) a
    have h1 : evaluate α (jordan (r • a) (r • a)) =
        r ^ 2 * evaluate α (jordan a a) := by
      simp [evaluate, jordan, dot, dotProduct, Fin.sum_univ_three, smul_eq_mul]
      ring
    have h2 : evaluate α (jordan (r • a) a) =
        r * evaluate α (jordan a a) := by
      simp [evaluate, jordan, dot, dotProduct, Fin.sum_univ_three, smul_eq_mul]
      ring
    rw [h1, h2] at hb
    have he : evaluate α (D (r • a) a) = 0 := by nlinarith [sq_nonneg (evaluate α (D (r • a) a))]
    simpa [evaluate, dot] using he
  refine ⟨hz, ?_⟩
  rw [p2_skew D hP (r • a) a, hz, neg_zero]

/-- Both original zero rows follow without any assumed regularity. -/
theorem p2_zero_rows (D : E → E → E) (hP : P2 D) : zeroRows D := by
  constructor
  · intro b
    change D 0 b = 0
    simpa using (p2_proportional D hP 0 b).1
  · intro a
    change D a 0 = 0
    simpa using (p2_proportional D hP 0 a).2

/-- Phase balance is equivalent to the element-valued finite-difference law. -/
theorem pb_iff_finite_difference (D : E → E → E) :
    PB D ↔ ∀ a b c, finiteDifference D a b c = 0 := by
  have expansion (α : Evaluation) (a b c : E) :
      squareReadout D α (phaseR D a b c) (phaseS D a b c) -
        squareReadout D α (b - D a b + jordan a c) (c - jordan a b - D a c) =
          2 * evaluate α (finiteDifference D a b c) := by
    simp [squareReadout, phaseR, phaseS, finiteDifference, evaluate, jordan,
      dot, dotProduct, Fin.sum_univ_three, smul_eq_mul]
    ring
  constructor
  · intro h a b c
    apply evaluations_separate
    intro α
    have he := expansion α a b c
    rw [h α a b c] at he
    simp only [sub_self] at he
    have hz : evaluate α (finiteDifference D a b c) = 0 := by linarith
    simpa [evaluate, dot] using hz
  · intro h α a b c
    have he := expansion α a b c
    rw [h a b c] at he
    simp [evaluate, dot] at he
    exact sub_eq_zero.mp he

private theorem dot_self_nonneg (x : Vec) : 0 ≤ dot x x := by
  unfold dot dotProduct
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

private theorem vnorm_sq (x : Vec) : vnorm x ^ 2 = dot x x :=
  Real.sq_sqrt (dot_self_nonneg x)

private theorem p2_scalar_pair (D : E → E → E) (hP : P2 D) (l k : ℝ) :
    D (l, 0) (k, 0) = 0 := by
  apply evaluations_separate
  intro α
  have hb := p2_determinant_bound D hP α (l, 0) (k, 0)
  have hz : evaluate α (D (l, 0) (k, 0)) = 0 := by
    have he : evaluate α (jordan (l, 0) (l, 0)) *
        evaluate α (jordan (k, 0) (k, 0)) -
          evaluate α (jordan (l, 0) (k, 0)) ^ 2 = 0 := by
      simp [evaluate, jordan, dot]
      ring
    rw [he] at hb
    nlinarith [sq_nonneg (evaluate α (D (l, 0) (k, 0)))]
  simpa [evaluate, dot] using hz

private theorem p2_scalar_face (D : E → E → E) (hP : P2 D)
    (l t : ℝ) (y : Vec) :
    (D (l, 0) (t, y)).1 = 0 ∧ dot y (D (l, 0) (t, y)).2 = 0 := by
  by_cases hy : y = 0
  · subst y
    rw [p2_scalar_pair D hP]
    simp [dot]
  have hYpos : 0 < vnorm y := by
    apply Real.sqrt_pos.mpr
    exact lt_of_le_of_ne (dot_self_nonneg y) (by
      intro h
      exact hy (dotProduct_self_eq_zero.mp h.symm))
  let αp : Evaluation := ⟨vnorm y, y, le_rfl⟩
  let αm : Evaluation := ⟨vnorm y, -y, by simp [vnorm, dot]⟩
  have hp := p2_determinant_bound D hP αp (l, 0) (t, y)
  have hm := p2_determinant_bound D hP αm (l, 0) (t, y)
  have hh : y ⬝ᵥ y = vnorm y ^ 2 := (vnorm_sq y).symm
  have hp0 : evaluate αp (D (l, 0) (t, y)) = 0 := by
    have he : evaluate αp (jordan (l, 0) (l, 0)) *
        evaluate αp (jordan (t, y) (t, y)) -
          evaluate αp (jordan (l, 0) (t, y)) ^ 2 = 0 := by
      simp [αp, evaluate, jordan, dot, dotProduct_add, dotProduct_smul, hh]
      ring
    rw [he] at hp
    nlinarith [sq_nonneg (evaluate αp (D (l, 0) (t, y)))]
  have hm0 : evaluate αm (D (l, 0) (t, y)) = 0 := by
    have he : evaluate αm (jordan (l, 0) (l, 0)) *
        evaluate αm (jordan (t, y) (t, y)) -
          evaluate αm (jordan (l, 0) (t, y)) ^ 2 = 0 := by
      simp [αm, evaluate, jordan, dot, dotProduct_add, dotProduct_smul, hh]
      ring
    rw [he] at hm
    nlinarith [sq_nonneg (evaluate αm (D (l, 0) (t, y)))]
  simp only [evaluate, αp, αm, dot, neg_dotProduct] at hp0 hm0
  constructor
  · nlinarith
  · change y ⬝ᵥ (D (l, 0) (t, y)).2 = 0
    linarith

/-- A finite PB substitution forces every unit row with nonzero input scalar to vanish. -/
theorem unit_row_nonzero_scalar (D : E → E → E) (hP : P2 D) (hPB : PB D)
    (l t : ℝ) (y : Vec) (ht : t ≠ 0) : D (l, 0) (t, y) = 0 := by
  let z := (D (l, 0) (t, y)).2
  have hf := p2_scalar_face D hP l t y
  have hd : D (l, 0) (t, y) = (0, z) := Prod.ext hf.1 rfl
  have hyz : y ⬝ᵥ z = 0 := hf.2
  have hzy : z ⬝ᵥ y = 0 := by simpa [dotProduct_comm] using hyz
  let Z := vnorm z
  let k := l * Z / (1 + l ^ 2)
  have hden : 1 + l ^ 2 ≠ 0 := by positivity
  have hk : (1 + l ^ 2) * k = l * Z := by dsimp [k]; field_simp
  let α : Evaluation := ⟨Z, z, le_rfl⟩
  have hzz : z ⬝ᵥ z = Z ^ 2 := (vnorm_sq z).symm
  have hp := p2_determinant_bound D hP α
    (t - l * k, y + z) (k + l * t, l • y)
  have hm := p2_determinant_bound D hP α
    (t + l * k, y - z) (k - l * t, -l • y)
  have hp0 : evaluate α (D (t - l * k, y + z) (k + l * t, l • y)) = 0 := by
    have he : evaluate α (jordan (t - l * k, y + z) (t - l * k, y + z)) *
        evaluate α (jordan (k + l * t, l • y) (k + l * t, l • y)) -
          evaluate α (jordan (t - l * k, y + z) (k + l * t, l • y)) ^ 2 = 0 := by
      simp [evaluate, jordan, α, dot, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, hyz, hzy, hzz]
      linear_combination (norm := ring_nf) (Z ^ 2 * (y ⬝ᵥ y) *
        ((1 + l ^ 2) * k - l * Z)) * hk
    rw [he] at hp
    nlinarith [sq_nonneg (evaluate α (D (t - l * k, y + z) (k + l * t, l • y)))]
  have hm0 : evaluate α (D (t + l * k, y - z) (k - l * t, -l • y)) = 0 := by
    have he : evaluate α (jordan (t + l * k, y - z) (t + l * k, y - z)) *
        evaluate α (jordan (k - l * t, -l • y) (k - l * t, -l • y)) -
          evaluate α (jordan (t + l * k, y - z) (k - l * t, -l • y)) ^ 2 = 0 := by
      simp [evaluate, jordan, α, dot, sub_dotProduct, dotProduct_sub,
        smul_dotProduct, dotProduct_smul, hyz, hzy, hzz]
      linear_combination (norm := ring_nf) (Z ^ 2 * (y ⬝ᵥ y) *
        ((1 + l ^ 2) * k - l * Z)) * hk
    rw [he] at hm
    nlinarith [sq_nonneg (evaluate α (D (t + l * k, y - z) (k - l * t, -l • y)))]
  have he := (pb_iff_finite_difference D).mp hPB (l, 0) (t, y) (k, 0)
  have heα := congrArg (evaluationLinear α) he
  have hr : (t, y) + D (l, 0) (t, y) - jordan (l, 0) (k, 0) =
      (t - l * k, y + z) := by rw [hd]; ext <;> simp [jordan, dot]
  have hs : (k, 0) + jordan (l, 0) (t, y) + D (l, 0) (k, 0) =
      (k + l * t, l • y) := by rw [p2_scalar_pair D hP]; ext <;> simp [jordan, dot]
  have hr' : (t, y) - D (l, 0) (t, y) + jordan (l, 0) (k, 0) =
      (t + l * k, y - z) := by rw [hd]; ext <;> simp [jordan, dot]
  have hs' : (k, 0) - jordan (l, 0) (t, y) - D (l, 0) (k, 0) =
      (k - l * t, -l • y) := by
    rw [p2_scalar_pair D hP]
    ext <;> simp [jordan, dot]
  simp only [finiteDifference, hr, hs, hr', hs', map_add, map_sub,
    map_smul, map_zero] at heα
  simp only [smul_eq_mul] at heα
  change evaluate α (D (t - l * k, y + z) (k + l * t, l • y)) -
    evaluate α (D (t + l * k, y - z) (k - l * t, -l • y)) +
      2 * evaluate α (jordan (t, y) (D (l, 0) (t, y) - jordan (l, 0) (k, 0))) +
      2 * evaluate α (jordan (k, 0) (jordan (l, 0) (t, y) + D (l, 0) (k, 0))) = 0 at heα
  rw [hp0, hm0, hd, p2_scalar_pair D hP] at heα
  simp [evaluate, jordan, α, dot, dotProduct_add, dotProduct_sub,
    dotProduct_smul, hyz, hzy, hzz] at heα
  have htz : t * Z ^ 2 = 0 := by nlinarith only [heα]
  have hz0 : Z = 0 := sq_eq_zero_iff.mp ((mul_eq_zero.mp htz).resolve_left ht)
  have hz : z = 0 := dotProduct_self_eq_zero.mp (by rw [hzz, hz0]; norm_num)
  rw [hd, hz]
  rfl

private theorem jordan_scalar (l : ℝ) (b : E) : jordan (l, 0) b = l • b := by
  apply Prod.ext
  · simp [jordan, dot, smul_eq_mul]
  · funext i
    simp [jordan]

private theorem jordan_comm (a b : E) : jordan a b = jordan b a := by
  apply Prod.ext
  · simp [jordan, dot, dotProduct_comm, mul_comm, add_comm]
  · simp [jordan, add_comm]

private def jordanLinear (a : E) : E →ₗ[ℝ] E where
  toFun := jordan a
  map_add' b c := by
    apply Prod.ext
    · simp [jordan, dot, dotProduct_add]
      ring
    · funext i
      simp [jordan]
      ring
  map_smul' r b := by
    apply Prod.ext
    · simp [jordan, dot, dotProduct_smul, smul_eq_mul]
      ring
    · funext i
      simp [jordan, smul_eq_mul]
      ring

private theorem pb_scalar_labels (D : E → E → E) (hPB : PB D)
    (l : ℝ) (b c : E) (hb : D (l, 0) b = 0) (hc : D (l, 0) c = 0) :
    D (b - l • c) (c + l • b) = D (b + l • c) (c - l • b) := by
  have hsum : (2 : ℝ) • jordan b (-(l • c)) +
      (2 : ℝ) • jordan c (l • b) = 0 := by
    have h1 : jordan b (-(l • c)) = -(l • jordan b c) := by
      change jordanLinear b (-(l • c)) = _
      rw [map_neg, map_smul]
      rfl
    have h2 : jordan c (l • b) = l • jordan b c := by
      change jordanLinear c (l • b) = _
      rw [map_smul]
      change l • jordan c b = _
      rw [jordan_comm]
    rw [h1, h2]
    simp
  have h := (pb_iff_finite_difference D).mp hPB (l, 0) b c
  simp only [finiteDifference, hb, hc, jordan_scalar, zero_sub, add_zero, sub_zero] at h
  rw [add_assoc, hsum, add_zero] at h
  exact sub_eq_zero.mp h

private theorem label_cayley (D : E → E → E) (hPB : PB D) (l : ℝ) (b c : E)
    (hb : D (l, 0) ((1 / (1 + l ^ 2)) • (b + l • c)) = 0)
    (hc : D (l, 0) ((1 / (1 + l ^ 2)) • (c - l • b)) = 0) :
    D b c = D (((1 - l ^ 2) / (1 + l ^ 2)) • b +
      ((2 * l) / (1 + l ^ 2)) • c)
      (((1 - l ^ 2) / (1 + l ^ 2)) • c - ((2 * l) / (1 + l ^ 2)) • b) := by
  have hden : 1 + l ^ 2 ≠ 0 := by positivity
  let b0 := (1 / (1 + l ^ 2)) • (b + l • c)
  let c0 := (1 / (1 + l ^ 2)) • (c - l • b)
  have h := pb_scalar_labels D hPB l b0 c0 hb hc
  have h1 : b0 - l • c0 = b := by
    ext <;> simp [b0, c0, smul_eq_mul] <;> field_simp <;> ring
  have h2 : c0 + l • b0 = c := by
    ext <;> simp [b0, c0, smul_eq_mul] <;> field_simp <;> ring
  have h3 : b0 + l • c0 = ((1 - l ^ 2) / (1 + l ^ 2)) • b +
      ((2 * l) / (1 + l ^ 2)) • c := by
    ext <;> simp [b0, c0, smul_eq_mul] <;> field_simp <;> ring
  have h4 : c0 - l • b0 = ((1 - l ^ 2) / (1 + l ^ 2)) • c -
      ((2 * l) / (1 + l ^ 2)) • b := by
    ext <;> simp [b0, c0, smul_eq_mul] <;> field_simp <;> ring
  simpa only [h1, h2, h3, h4] using h

private theorem pb_equal_labels (D : E → E → E) (hP : P2 D) (hPB : PB D)
    (a b : E) (hab : D a b = 0) : D (b - jordan a b) (b + jordan a b) = 0 := by
  have hsum : (2 : ℝ) • jordan b (-jordan a b) +
      (2 : ℝ) • jordan b (jordan a b) = 0 := by
    have hneg : jordan b (-jordan a b) = -jordan b (jordan a b) :=
      (jordanLinear b).map_neg _
    rw [hneg]
    simp
  have h := (pb_iff_finite_difference D).mp hPB a b b
  simp only [finiteDifference, hab, zero_sub, add_zero, sub_zero] at h
  rw [add_assoc, hsum, add_zero] at h
  apply zero_of_eq_neg
  exact (sub_eq_zero.mp h).trans (p2_skew D hP _ _)

/-- All scalar multiples of the original unit have zero rows, including pure-vector labels. -/
theorem unit_rows (D : E → E → E) (hP : P2 D) (hPB : PB D) (q : ℝ) (b : E) :
    D (q, 0) b = 0 := by
  by_cases ht : b.1 = 0
  · rcases b with ⟨t, y⟩
    change t = 0 at ht
    subst t
    by_cases hq : q = 0
    · subst q
      exact (p2_zero_rows D hP).1 _
    by_cases hy : y = 0
    · subst y
      exact p2_scalar_pair D hP q 0
    have hyy : dot y y ≠ 0 := by
      intro h
      exact hy (dotProduct_self_eq_zero.mp h)
    let r : ℝ := Real.sqrt 2
    have hrpos : 0 < r := by dsimp [r]; positivity
    have hr : r ≠ 0 := ne_of_gt hrpos
    have hr2 : r ^ 2 = 2 := by norm_num [r]
    let a : E := (0, (q / dot y y) • y)
    let v : E := (0, (1 / r) • y)
    have hv : v = (dot y y / (r * q)) • a := by
      apply Prod.ext
      · simp [v, a]
      · funext i
        simp [v, a, smul_eq_mul]
        field_simp
    have hav : D a v = 0 := by
      rw [hv]
      exact (p2_proportional D hP _ a).2
    have hj : jordan a v = (q / r, 0) := by
      apply Prod.ext
      · simp [a, v, jordan, dot, smul_dotProduct, dotProduct_smul]
        field_simp [show y ⬝ᵥ y ≠ 0 from hyy]
      · simp [a, v, jordan]
    let A : E := (-q / r, (1 / r) • y)
    let B : E := (q / r, (1 / r) • y)
    have hA : v - jordan a v = A := by rw [hj]; ext <;> simp [v, A, neg_div]
    have hB : v + jordan a v = B := by rw [hj]; ext <;> simp [v, B]
    have hAB : D A B = 0 := by
      simpa only [hA, hB] using pb_equal_labels D hP hPB a v hav
    let m := r - 1
    have hmlo : 0 < m := by dsimp [m]; nlinarith
    have hmhi : m < 1 := by dsimp [m]; nlinarith
    have hden : 1 + m ^ 2 ≠ 0 := by positivity
    have hb0 : ((1 / (1 + m ^ 2)) • (A + m • B)).1 ≠ 0 := by
      change (1 / (1 + m ^ 2)) * (-q / r + m * (q / r)) ≠ 0
      have he : -q / r + m * (q / r) = (q / r) * (m - 1) := by ring
      rw [he]
      exact mul_ne_zero (one_div_ne_zero hden)
        (mul_ne_zero (div_ne_zero hq hr) (sub_ne_zero.mpr (ne_of_lt hmhi)))
    have hc0 : ((1 / (1 + m ^ 2)) • (B - m • A)).1 ≠ 0 := by
      change (1 / (1 + m ^ 2)) * (q / r - m * (-q / r)) ≠ 0
      have he : q / r - m * (-q / r) = (q / r) * (1 + m) := by ring
      rw [he]
      exact mul_ne_zero (one_div_ne_zero hden)
        (mul_ne_zero (div_ne_zero hq hr) (by linarith))
    have h := label_cayley D hPB m A B
      (unit_row_nonzero_scalar D hP hPB m _ _ hb0)
      (unit_row_nonzero_scalar D hP hPB m _ _ hc0)
    have hC : (1 - m ^ 2) / (1 + m ^ 2) = 1 / r := by
      field_simp
      dsimp [m]
      linear_combination -(r - 1) * hr2
    have hS : 2 * m / (1 + m ^ 2) = 1 / r := by
      field_simp
      dsimp [m]
      linear_combination hr2
    rw [hC, hS] at h
    have hx : (1 / r) • A + (1 / r) • B = (0, y) := by
      apply Prod.ext
      · simp [A, B, smul_eq_mul]
        ring
      · funext i
        simp [A, B, smul_eq_mul]
        field_simp
        ring_nf
        simp [hr2]
    have hu : (1 / r) • B - (1 / r) • A = (q, 0) := by
      apply Prod.ext
      · simp [A, B, smul_eq_mul]
        field_simp
        ring_nf
        simp [hr2]
      · funext i
        simp [A, B, smul_eq_mul]
    rw [hx, hu, hAB] at h
    rw [p2_skew D hP (0, y) (q, 0), ← h, neg_zero]
  · exact unit_row_nonzero_scalar D hP hPB q b.1 b.2 ht

/-- Every exact real SO(2) label rotation preserves the same original D. -/
theorem label_rotation (D : E → E → E) (hP : P2 D) (hPB : PB D)
    (C S : ℝ) (hCS : C ^ 2 + S ^ 2 = 1) (b c : E) :
    D b c = D (C • b + S • c) (C • c - S • b) := by
  have hcay (l : ℝ) (b c : E) :
      D b c = D (((1 - l ^ 2) / (1 + l ^ 2)) • b +
        ((2 * l) / (1 + l ^ 2)) • c)
        (((1 - l ^ 2) / (1 + l ^ 2)) • c - ((2 * l) / (1 + l ^ 2)) • b) :=
    label_cayley D hPB l b c (unit_rows D hP hPB _ _) (unit_rows D hP hPB _ _)
  by_cases hC : C = -1
  · have hS : S = 0 := by rw [hC] at hCS; nlinarith [sq_nonneg S]
    have h1 : D b c = D c (-b) := by simpa using hcay 1 b c
    have h2 : D c (-b) = D (-b) (-c) := by simpa using hcay 1 c (-b)
    simpa [hC, hS] using h1.trans h2
  · have hden : 1 + C ≠ 0 := by intro h; apply hC; linarith
    let l := S / (1 + C)
    have hdenl : 1 + l ^ 2 ≠ 0 := by positivity
    have h1 : (1 - l ^ 2) / (1 + l ^ 2) = C := by
      apply (div_eq_iff hdenl).mpr
      dsimp [l]
      field_simp
      linear_combination -(1 + C) * hCS
    have h2 : 2 * l / (1 + l ^ 2) = S := by
      apply (div_eq_iff hdenl).mpr
      dsimp [l]
      field_simp
      linear_combination -S * hCS
    simpa only [h1, h2] using hcay l b c

private theorem same_axis_zero (D : E → E → E) (hP : P2 D) (hPB : PB D)
    (s t k : ℝ) (x : Vec) : D (s, x) (t, k • x) = 0 := by
  let L := Real.sqrt (1 + k ^ 2)
  have hLpos : 0 < L := by dsimp [L]; positivity
  have hL : L ≠ 0 := ne_of_gt hLpos
  have hL2 : L ^ 2 = 1 + k ^ 2 := Real.sq_sqrt (by positivity)
  have hCS : (k / L) ^ 2 + (-1 / L) ^ 2 = 1 := by
    field_simp
    nlinarith only [hL2]
  have h := label_rotation D hP hPB (k / L) (-1 / L) hCS (s, x) (t, k • x)
  have hfirst : (k / L) • (s, x) + (-1 / L) • (t, k • x) =
      ((k / L) * s + (-1 / L) * t, 0) := by
    apply Prod.ext rfl
    funext i
    simp [smul_eq_mul]
    ring
  rw [hfirst, unit_rows D hP hPB] at h
  exact h

/-- Collinear vector parts force zero for all original scalar parts and degeneracies. -/
theorem collinear_zero (D : E → E → E) (hP : P2 D) (hPB : PB D)
    (a b : E) (hab : cross a.2 b.2 = 0) : D a b = 0 := by
  by_cases ha : a.2 = 0
  · have he : a = (a.1, 0) := Prod.ext rfl ha
    rw [he]
    exact unit_rows D hP hPB _ _
  have hlin : ¬LinearIndependent ℝ ![a.2, b.2] := by
    intro h
    exact (crossProduct_ne_zero_iff_linearIndependent.mpr h) hab
  rw [LinearIndependent.pair_iff' ha, not_forall_not] at hlin
  obtain ⟨k, hk⟩ := hlin
  have hb : b = (b.1, k • a.2) := Prod.ext rfl hk.symm
  rw [hb]
  exact same_axis_zero D hP hPB a.1 b.1 k a.2

end D5.S3.Quantum.SpinFactor.OriginalDContract
