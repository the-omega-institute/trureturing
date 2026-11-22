/- GID: D5/S3/Quantum/Analysis/RefinedBMVExtremeCertificate
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact ordered derivative signs for the extreme refined BMV kernel. -/

import D5.S3.Quantum.Analysis.RefinedBMVDimThreeCertificate
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # Ordered derivative signs for the extreme refined BMV kernel -/

namespace RefinedBMV.ExtremeCertificate

open DimThree DimThree.Certificate

/-- The five ways the defect is evaluated with repeated entries or three distinct variables. -/
private inductive Shape
  | mixed | xx | yy | aay | xxy

private abbrev Exponents := ℕ × ℕ × ℕ

private def Shape.exponents : Shape → Exponents → Exponents
  | .mixed, g => g
  | .xx, (i, j, k) => (i, j + k, 0)
  | .yy, (i, j, k) => (i, 0, j + k)
  | .aay, (i, j, k) => (i + j, 0, k)
  | .xxy, (i, j, k) => (0, i + j, k)

private def Shape.args (a x y : R) : Shape → R × R × R
  | .mixed => (a, x, y)
  | .xx => (a, x, x)
  | .yy => (a, y, y)
  | .aay => (a, a, y)
  | .xxy => (x, x, y)

/-- The guard discards vanishing derivatives before forming the lowered exponents. -/
private def monomial [Add R] [Mul R] [Pow R Nat] [NatCast R] [Zero R]
    (dx dy : Bool) (a x y : R) (g : Exponents) : R :=
  if dx.toNat ≤ g.2.1 ∧ dy.toNat ≤ g.2.2 then
    (↑((if dx then g.2.1 else 1) * (if dy then g.2.2 else 1)) : R) *
      a ^ g.1 * x ^ (g.2.1 - dx.toNat) * y ^ (g.2.2 - dy.toNat)
  else 0

private def defectPartial [Add R] [Sub R] [Mul R] [Pow R Nat] [NatCast R] [Zero R]
    (p : ℕ) (shape : Shape) (dx dy : Bool) (a x y : R) : R :=
  ((gaps p).map fun g =>
    monomial dx dy a x y (shape.exponents (3 * g.1, 3 * g.2.1, 3 * g.2.2))).sum -
    (↑(gaps p).length : R) * monomial dx dy a x y (shape.exponents (p, p, p))

private theorem monomial_zero [CommRing R] (shape : Shape) (a x y : R) (i j k : ℕ) :
    monomial false false a x y (shape.exponents (i, j, k)) =
      (shape.args a x y).1 ^ i * (shape.args a x y).2.1 ^ j *
        (shape.args a x y).2.2 ^ k := by
  cases shape <;> simp [monomial, Shape.exponents, Shape.args, pow_add, mul_assoc]

private theorem partial_zero [CommRing R] (p : ℕ) (shape : Shape) (a x y : R) :
    defectPartial p shape false false a x y =
      defect p (shape.args a x y).1 (shape.args a x y).2.1 (shape.args a x y).2.2 := by
  simp only [defectPartial, monomial_zero, defect, pow_mul, mul_pow]

private theorem monomial_dx (a x y : ℝ) (dy : Bool) (g : Exponents) :
    HasDerivAt (fun z => monomial false dy a z y g) (monomial true dy a x y g) x := by
  obtain ⟨i, j, k⟩ := g
  cases dy <;> cases j <;> cases k <;>
    simp [monomial, Bool.toNat] <;>
    first
    | exact hasDerivAt_const x _
    | refine ((hasDerivAt_pow _ x).const_mul _).congr_deriv ?_
      push_cast
      ring
    | refine (HasDerivAt.mul_const ((hasDerivAt_pow _ x).const_mul _) _).congr_deriv ?_
      push_cast
      ring

private theorem monomial_dy (a x y : ℝ) (dx : Bool) (g : Exponents) :
    HasDerivAt (fun z => monomial dx false a x z g) (monomial dx true a x y g) y := by
  obtain ⟨i, j, k⟩ := g
  cases dx <;> cases j <;> cases k <;>
    simp [monomial, Bool.toNat] <;>
    first
    | exact hasDerivAt_const y _
    | refine ((hasDerivAt_pow _ y).const_mul _).congr_deriv ?_
      push_cast
      ring

private theorem hasDerivAt_list_sum {ι : Type*} (l : List ι) {f : ι → ℝ → ℝ}
    {f' : ι → ℝ} {x : ℝ} (h : ∀ i, HasDerivAt (f i) (f' i) x) :
    HasDerivAt (fun z => (l.map fun i => f i z).sum) (l.map f').sum x := by
  induction l with
  | nil => simpa using hasDerivAt_const x (0 : ℝ)
  | cons i l ih => simpa only [List.map_cons, List.sum_cons] using (h i).fun_add ih

private theorem partial_dx (p : ℕ) (shape : Shape) (dy : Bool) (a x y : ℝ) :
    HasDerivAt (fun z => defectPartial p shape false dy a z y)
      (defectPartial p shape true dy a x y) x := by
  unfold defectPartial
  exact (hasDerivAt_list_sum (gaps p)
    (f := fun g z => monomial false dy a z y
      (shape.exponents (3 * g.1, 3 * g.2.1, 3 * g.2.2)))
    (fun _ => monomial_dx a x y dy _)).fun_sub
    ((monomial_dx a x y dy (shape.exponents (p, p, p))).const_mul _)

private theorem partial_dy (p : ℕ) (shape : Shape) (dx : Bool) (a x y : ℝ) :
    HasDerivAt (fun z => defectPartial p shape dx false a x z)
      (defectPartial p shape dx true a x y) y := by
  unfold defectPartial
  exact (hasDerivAt_list_sum (gaps p)
    (f := fun g z => monomial dx false a x z
      (shape.exponents (3 * g.1, 3 * g.2.1, 3 * g.2.2)))
    (fun _ => monomial_dy a x y dx _)).fun_sub
    ((monomial_dy a x y dx (shape.exponents (p, p, p))).const_mul _)

/-- The polynomial under the square root in the numerator of the normalized kernel. -/
def q [Add R] [Sub R] [Mul R] [Pow R Nat] [NatCast R] [Zero R] (p : ℕ) (a x y : R) : R :=
  defect p a a y * defect p x x y

/-- The defect contribution to the numerator of the first partial derivative. -/
noncomputable def _root_.RefinedBMV.Extreme.XAt (p : ℕ) (a x y : ℝ) : ℝ :=
  2 * defect p a x x * deriv (fun t => defect p a t y) x -
    deriv (fun t => defect p a t t) x * defect p a x y

noncomputable def _root_.RefinedBMV.Extreme.X (a x y : ℝ) : ℝ :=
  RefinedBMV.Extreme.XAt 5 a x y

/-- The radicand contribution to the numerator of the first partial derivative. -/
noncomputable def _root_.RefinedBMV.Extreme.UAt (p : ℕ) (a x y : ℝ) : ℝ :=
  defect p a x x * deriv (fun t => q p a t y) x -
    deriv (fun t => defect p a t t) x * q p a x y

noncomputable def _root_.RefinedBMV.Extreme.U (a x y : ℝ) : ℝ :=
  RefinedBMV.Extreme.UAt 5 a x y

/-- The defect contribution to the numerator of the second partial derivative. -/
noncomputable def _root_.RefinedBMV.Extreme.YAt (p : ℕ) (a x y : ℝ) : ℝ :=
  2 * defect p a y y * deriv (defect p a x) y -
    deriv (fun t => defect p a t t) y * defect p a x y

noncomputable def _root_.RefinedBMV.Extreme.Y (a x y : ℝ) : ℝ :=
  RefinedBMV.Extreme.YAt 5 a x y

/-- The radicand contribution to the numerator of the second partial derivative. -/
noncomputable def _root_.RefinedBMV.Extreme.VAt (p : ℕ) (a x y : ℝ) : ℝ :=
  defect p a y y * deriv (q p a x) y -
    deriv (fun t => defect p a t t) y * q p a x y

noncomputable def _root_.RefinedBMV.Extreme.V (a x y : ℝ) : ℝ :=
  RefinedBMV.Extreme.VAt 5 a x y

open RefinedBMV.Extreme (X U Y V XAt UAt YAt VAt)

/-- The contribution of the mixed defect to the mixed derivative numerator. -/
noncomputable def Z (p : ℕ) (a x y : ℝ) : ℝ :=
  let r (x : ℝ) := defect p a x x
  let d := defect p a
  4 * r x * r y * deriv (fun v => deriv (d v) y) x -
    2 * r x * deriv r y * deriv (fun v => d v y) x -
    2 * r y * deriv r x * deriv (d x) y + deriv r x * deriv r y * d x y

/-- The contribution of the square root of `q` to the mixed derivative numerator. -/
noncomputable def P (p : ℕ) (a x y : ℝ) : ℝ :=
  let r (x : ℝ) := defect p a x x
  let Q := q p a
  r x * r y * (2 * Q x y * deriv (fun v => deriv (Q v) y) x -
      deriv (fun v => Q v y) x * deriv (Q x) y) -
    r x * deriv r y * Q x y * deriv (fun v => Q v y) x -
    r y * deriv r x * Q x y * deriv (Q x) y + deriv r x * deriv r y * Q x y ^ 2

section
variable {R : Type*} [Add R] [Sub R] [Mul R] [Pow R Nat] [NatCast R] [Zero R]

private def qPolynomial (p : ℕ) (a x y : R) : R :=
  defectPartial p .aay false false a x y * defectPartial p .xxy false false a x y

private def qxPolynomial (p : ℕ) (a x y : R) : R :=
  defectPartial p .aay false false a x y * defectPartial p .xxy true false a x y

private def qyPolynomial (p : ℕ) (a x y : R) : R :=
  defectPartial p .aay false true a x y * defectPartial p .xxy false false a x y +
    defectPartial p .aay false false a x y * defectPartial p .xxy false true a x y

private def qxyPolynomial (p : ℕ) (a x y : R) : R :=
  defectPartial p .aay false true a x y * defectPartial p .xxy true false a x y +
    defectPartial p .aay false false a x y * defectPartial p .xxy true true a x y

private def xPolynomial (p : ℕ) (a x y : R) : R :=
  let D := defectPartial p
  (↑(2 : ℕ) : R) * D .xx false false a x y * D .mixed true false a x y -
    D .xx true false a x y * D .mixed false false a x y

private def uPolynomial (p : ℕ) (a x y : R) : R :=
  let D := defectPartial p
  D .xx false false a x y * qxPolynomial p a x y -
    D .xx true false a x y * qPolynomial p a x y

private def yPolynomial (p : ℕ) (a x y : R) : R :=
  let D := defectPartial p
  (↑(2 : ℕ) : R) * D .yy false false a x y * D .mixed false true a x y -
    D .yy false true a x y * D .mixed false false a x y

private def vPolynomial (p : ℕ) (a x y : R) : R :=
  let D := defectPartial p
  D .yy false false a x y * qyPolynomial p a x y -
    D .yy false true a x y * qPolynomial p a x y

private def zPolynomial (p : ℕ) (a x y : R) : R :=
  let D := defectPartial p
  let r := D .xx false false a x y
  let h := D .yy false false a x y
  let rx := D .xx true false a x y
  let hy := D .yy false true a x y
  (↑(4 : ℕ) : R) * r * h * D .mixed true true a x y -
    (↑(2 : ℕ) : R) * r * hy * D .mixed true false a x y -
    (↑(2 : ℕ) : R) * h * rx * D .mixed false true a x y +
    rx * hy * D .mixed false false a x y

private def pPolynomial (p : ℕ) (a x y : R) : R :=
  let D := defectPartial p
  let r := D .xx false false a x y
  let h := D .yy false false a x y
  let rx := D .xx true false a x y
  let hy := D .yy false true a x y
  let Q := qPolynomial p a x y
  let Qx := qxPolynomial p a x y
  let Qy := qyPolynomial p a x y
  r * h * ((↑(2 : ℕ) : R) * Q * qxyPolynomial p a x y - Qx * Qy) -
    r * hy * Q * Qx - h * rx * Q * Qy + rx * hy * Q ^ (2 : ℕ)

end

private theorem partial_aay_const (p : ℕ) (dy : Bool) (a x y : ℝ) :
    defectPartial p .aay false dy a x y = defectPartial p .aay false dy a 0 y := by
  simp [defectPartial, Shape.exponents, monomial, Bool.toNat]

private theorem qPolynomial_dx (p : ℕ) (a x y : ℝ) :
    HasDerivAt (fun v => qPolynomial p a v y) (qxPolynomial p a x y) x := by
  simpa only [qxPolynomial, qPolynomial, partial_aay_const] using
    ((partial_dx p .xxy false a x y).const_mul (defectPartial p .aay false false a 0 y) :
      HasDerivAt (fun v => defectPartial p .aay false false a 0 y * defectPartial p .xxy false false a v y)
        _ x)

private theorem qPolynomial_dy (p : ℕ) (a x y : ℝ) :
    HasDerivAt (fun v => qPolynomial p a x v) (qyPolynomial p a x y) y := by
  exact (partial_dy p .aay false a x y).fun_mul (partial_dy p .xxy false a x y)

private theorem qyPolynomial_dx (p : ℕ) (a x y : ℝ) :
    HasDerivAt (fun v => qyPolynomial p a v y) (qxyPolynomial p a x y) x := by
  simpa only [qyPolynomial, qxyPolynomial, partial_aay_const] using
    ((partial_dx p .xxy false a x y).const_mul (defectPartial p .aay false true a 0 y)).fun_add
      ((partial_dx p .xxy true a x y).const_mul (defectPartial p .aay false false a 0 y))

private theorem qPolynomial_eq (p : ℕ) (a x y : ℝ) : qPolynomial p a x y = q p a x y := by
  simp only [qPolynomial, q, partial_zero, Shape.args]

private theorem edgePolynomials_eq (p : ℕ) (a x y : ℝ) :
    xPolynomial p a x y = XAt p a x y ∧ uPolynomial p a x y = UAt p a x y ∧
    yPolynomial p a x y = YAt p a x y ∧ vPolynomial p a x y = VAt p a x y := by
  have hrx := (partial_dx p .xx false a x y).deriv
  have hry := (partial_dy p .yy false a x y).deriv
  have hdx := (partial_dx p .mixed false a x y).deriv
  have hdy := (partial_dy p .mixed false a x y).deriv
  have hqx := (qPolynomial_dx p a x y).deriv
  have hqy := (qPolynomial_dy p a x y).deriv
  simp only [partial_zero, Shape.args] at hrx hry hdx hdy
  simp only [qPolynomial_eq] at hqx hqy
  simp [xPolynomial, uPolynomial, yPolynomial, vPolynomial, XAt, UAt, YAt, VAt,
    partial_zero, Shape.args, qPolynomial_eq, hrx, hry, hdx, hdy, hqx, hqy]

private theorem zPolynomial_eq (p : ℕ) (a x y : ℝ) : zPolynomial p a x y = Z p a x y := by
  have hxx := (partial_dx p .xx false a x y).deriv
  have hyy := (partial_dy p .yy false a x y).deriv
  have hx := (partial_dx p .mixed false a x y).deriv
  have hy (v : ℝ) := (partial_dy p .mixed false a v y).deriv
  have hxy := (partial_dx p .mixed true a x y).deriv
  simp only [partial_zero, Shape.args] at hxx hyy hx hy
  simp [zPolynomial, Z, partial_zero, Shape.args, ← hxx, ← hyy, ← hx, ← hy, ← hxy]

private theorem pPolynomial_eq (p : ℕ) (a x y : ℝ) : pPolynomial p a x y = P p a x y := by
  have hxx := (partial_dx p .xx false a x y).deriv
  have hyy := (partial_dy p .yy false a x y).deriv
  have hx := (qPolynomial_dx p a x y).deriv
  have hy (v : ℝ) := (qPolynomial_dy p a v y).deriv
  have hxy := (qyPolynomial_dx p a x y).deriv
  simp only [partial_zero, Shape.args] at hxx hyy
  simp only [qPolynomial_eq] at hx hy
  simp [pPolynomial, P, partial_zero, Shape.args, ← hxx, ← hyy, ← hx, ← hy, ← hxy,
    qPolynomial_eq]

private theorem eval_monomial {R : Type*} [CommRing R] (s t u : R) (dx dy : Bool)
    (a x y : Sparse) (g : Exponents) :
    (monomial dx dy a x y g).eval s t u =
      monomial dx dy (a.eval s t u) (x.eval s t u) (y.eval s t u) g := by
  unfold monomial
  split
  · simp only [eval_cast, eval_mul, eval_pow]
  · exact eval_zero s t u

private theorem eval_partial {R : Type*} [CommRing R] (s t u : R) (p : ℕ) (shape : Shape)
    (dx dy : Bool) (a x y : Sparse) :
    (defectPartial p shape dx dy a x y).eval s t u =
      defectPartial p shape dx dy (a.eval s t u) (x.eval s t u) (y.eval s t u) := by
  simp only [defectPartial, eval_sub, eval_mul, eval_cast, eval_sum, List.map_map, Function.comp_def,
    eval_monomial]

private theorem shape_degree (shape : Shape) (i j k : ℕ) :
    (shape.exponents (i, j, k)).1 + (shape.exponents (i, j, k)).2.1 +
      (shape.exponents (i, j, k)).2.2 = i + j + k := by
  cases shape <;> simp [Shape.exponents] <;> omega

/-- Each derivative contributes a factor at most the total degree. -/
private abbrev monomialBudget (d : ℕ) : ℕ := d * d * 3 ^ d

private abbrev defectBudget (p : ℕ) : ℕ :=
  2 * (gaps p).length * monomialBudget (3 * p)

private theorem monomial_bound {d : ℕ} (hd₀ : 0 < d) {a x y : Sparse}
    (ha : Controlled a.terms 1 3) (hx : Controlled x.terms 1 3) (hy : Controlled y.terms 1 3)
    (dx dy : Bool) (g : Exponents) (hd : g.1 + g.2.1 + g.2.2 = d) :
    Controlled (monomial dx dy a x y g).terms (d - dx.toNat - dy.toNat) (monomialBudget d) := by
  unfold monomial
  split
  next h =>
    let k := (if dx then g.2.1 else 1) * (if dy then g.2.2 else 1)
    have hk : k ≤ d * d := by
      have hx' : (if dx then g.2.1 else 1) ≤ d := by split <;> omega
      have hy' : (if dy then g.2.2 else 1) ≤ d := by split <;> omega
      exact Nat.mul_le_mul hx' hy'
    have hh := mul_bound (mul_bound (mul_bound (constant_bound k) (pow_bound ha g.1))
      (pow_bound hx (g.2.1 - dx.toNat))) (pow_bound hy (g.2.2 - dy.toNat))
    have he : g.1 + (g.2.1 - dx.toNat) + (g.2.2 - dy.toNat) =
        d - dx.toNat - dy.toNat := by omega
    simp only [Nat.one_mul, Nat.zero_add] at hh
    rw [he] at hh
    refine mono hh ?_
    rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add]
    exact Nat.mul_le_mul hk (Nat.pow_le_pow_right (by decide) (by omega))
  next =>
    exact empty_controlled _ _

private theorem partial_bound {p : ℕ} (hp : 0 < p) {a x y : Sparse}
    (ha : Controlled a.terms 1 3) (hx : Controlled x.terms 1 3) (hy : Controlled y.terms 1 3)
    (shape : Shape) (dx dy : Bool) :
    Controlled (defectPartial p shape dx dy a x y).terms (3 * p - dx.toNat - dy.toNat) (defectBudget p) := by
  let M := fun g : Exponents => monomial dx dy a x y
    (shape.exponents (3 * g.1, 3 * g.2.1, 3 * g.2.2))
  have hs := sum_bound ((gaps p).map M) _ (monomialBudget (3 * p)) (by
    intro m hm
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hm
    apply monomial_bound (d := 3 * p) (by omega) ha hx hy
    have h := gap_degree p g hg
    rw [shape_degree]
    omega)
  have hg := mul_bound (constant_bound (gaps p).length)
    (monomial_bound (d := 3 * p) (by omega) ha hx hy dx dy (shape.exponents (p, p, p)) (by rw [shape_degree]; omega))
  have h := sub_bound hs (by simpa only [Nat.zero_add] using hg)
  change Controlled (((gaps p).map M).sum -
    Sparse.constant (gaps p).length * monomial dx dy a x y (shape.exponents (p, p, p))).terms
      (3 * p - dx.toNat - dy.toNat) (defectBudget p)
  simpa only [List.length_map, defectBudget, Nat.two_mul, Nat.add_mul] using h

private theorem controlled_degree {terms : List Term} {d e b : ℕ}
    (h : Controlled terms d b) (he : d = e) : Controlled terms e b := he ▸ h

private abbrev qBudget (p : ℕ) : ℕ := (defectBudget p) ^ 2
private abbrev zBudget (p : ℕ) : ℕ := 9 * (defectBudget p) ^ 3
private abbrev pBudget (p : ℕ) : ℕ := 10 * (defectBudget p) ^ 6

private theorem q_bound {p : ℕ} (hp : 0 < p) {a x y : Sparse} (ha : Controlled a.terms 1 3)
    (hx : Controlled x.terms 1 3) (hy : Controlled y.terms 1 3) :
    Controlled (qPolynomial p a x y).terms (6 * p) (qBudget p) := by
  rw [qBudget, pow_two]
  exact controlled_degree (mul_bound (partial_bound hp ha hx hy .aay false false)
    (partial_bound hp ha hx hy .xxy false false)) (by simp [Bool.toNat]; omega)

private theorem z_bound {p : ℕ} (hp : 0 < p) {a x y : Sparse} (ha : Controlled a.terms 1 3)
    (hx : Controlled x.terms 1 3) (hy : Controlled y.terms 1 3) :
    Controlled (zPolynomial p a x y).terms (9 * p - 2) (zBudget p) := by
  have H (shape : Shape) (dx dy : Bool) := partial_bound hp ha hx hy shape dx dy
  have hm := mul_bound (mul_bound (mul_bound (constant_bound 4) (H .xx false false))
    (H .yy false false)) (H .mixed true true)
  have hx := mul_bound (mul_bound (mul_bound (constant_bound 2) (H .xx false false))
    (H .yy false true)) (H .mixed true false)
  have hy := mul_bound (mul_bound (mul_bound (constant_bound 2) (H .yy false false))
    (H .xx true false)) (H .mixed false true)
  have hxy := mul_bound (mul_bound (H .xx true false) (H .yy false true)) (H .mixed false false)
  exact mono (add_bound (sub_bound
    (sub_bound (controlled_degree hm (by simp [Bool.toNat]; omega))
      (controlled_degree hx (by simp [Bool.toNat]; omega)))
      (controlled_degree hy (by simp [Bool.toNat]; omega)))
      (controlled_degree hxy (by simp [Bool.toNat]; omega)))
    (by ring_nf; omega)

private theorem p_bound {p : ℕ} (hp : 0 < p) {a x y : Sparse} (ha : Controlled a.terms 1 3)
    (hx : Controlled x.terms 1 3) (hy : Controlled y.terms 1 3) :
    Controlled (pPolynomial p a x y).terms (18 * p - 2) (pBudget p) := by
  have H (shape : Shape) (dx dy : Bool) := partial_bound hp ha hx hy shape dx dy
  have hQ := q_bound hp ha hx hy
  have hQx : Controlled (qxPolynomial p a x y).terms (6 * p - 1) (qBudget p) := by
    rw [qBudget, pow_two]
    exact controlled_degree (mul_bound (H .aay false false) (H .xxy true false))
      (by simp [Bool.toNat]; omega)
  have hQy : Controlled (qyPolynomial p a x y).terms (6 * p - 1) (2 * qBudget p) := by
    have h₁ := controlled_degree (mul_bound (H .aay false true) (H .xxy false false))
      (show _ = 6 * p - 1 by simp [Bool.toNat]; omega)
    have h₂ := controlled_degree (mul_bound (H .aay false false) (H .xxy false true))
      (show _ = 6 * p - 1 by simp [Bool.toNat]; omega)
    exact mono (add_bound h₁ h₂) (by ring_nf; omega)
  have hQxy : Controlled (qxyPolynomial p a x y).terms (6 * p - 2) (2 * qBudget p) := by
    have h₁ := controlled_degree (mul_bound (H .aay false true) (H .xxy true false))
      (show _ = 6 * p - 2 by simp [Bool.toNat]; omega)
    have h₂ := controlled_degree (mul_bound (H .aay false false) (H .xxy true true))
      (show _ = 6 * p - 2 by simp [Bool.toNat]; omega)
    exact mono (add_bound h₁ h₂) (by ring_nf; omega)
  have hMixed := controlled_degree (mul_bound (mul_bound (constant_bound 2) hQ) hQxy)
    (show _ = 12 * p - 2 by omega)
  have hFirst := controlled_degree (mul_bound hQx hQy) (show _ = 12 * p - 2 by omega)
  have hm := mul_bound (mul_bound (H .xx false false) (H .yy false false))
    (sub_bound hMixed hFirst)
  have hx := mul_bound (mul_bound (mul_bound (H .xx false false) (H .yy false true)) hQ) hQx
  have hy := mul_bound (mul_bound (mul_bound (H .yy false false) (H .xx true false)) hQ) hQy
  have hxy := mul_bound (mul_bound (H .xx true false) (H .yy false true)) (pow_bound hQ 2)
  exact mono (add_bound (sub_bound
    (sub_bound (controlled_degree hm (by simp [Bool.toNat]; omega))
      (controlled_degree hx (by simp [Bool.toNat]; omega)))
      (controlled_degree hy (by simp [Bool.toNat]; omega)))
      (controlled_degree hxy (by simp [Bool.toNat]; omega)))
    (by ring_nf; omega)

private abbrev edgeBudget (p : ℕ) : ℕ := 3 * (defectBudget p) ^ 3
private abbrev edgeSquareBudget (p : ℕ) : ℕ := 18 * (defectBudget p) ^ 6

private theorem x_bound {p : ℕ} (hp : 0 < p) {a x y : Sparse} (ha : Controlled a.terms 1 3)
    (hx : Controlled x.terms 1 3) (hy : Controlled y.terms 1 3) :
    Controlled (xPolynomial p a x y).terms (6 * p - 1) (3 * (defectBudget p) ^ 2) := by
  have H (shape : Shape) (dx dy : Bool) := partial_bound hp ha hx hy shape dx dy
  have hd := mul_bound (mul_bound (constant_bound 2) (H .xx false false))
    (H .mixed true false)
  have hw := mul_bound (H .xx true false) (H .mixed false false)
  exact mono (sub_bound (controlled_degree hd (by simp [Bool.toNat]; omega))
    (controlled_degree hw (by simp [Bool.toNat]; omega)))
    (by ring_nf; omega)

private theorem u_bound {p : ℕ} (hp : 0 < p) {a x y : Sparse} (ha : Controlled a.terms 1 3)
    (hx : Controlled x.terms 1 3) (hy : Controlled y.terms 1 3) :
    Controlled (uPolynomial p a x y).terms (9 * p - 1) (edgeBudget p) := by
  have H (shape : Shape) (dx dy : Bool) := partial_bound hp ha hx hy shape dx dy
  have hQx : Controlled (qxPolynomial p a x y).terms (6 * p - 1) (qBudget p) := by
    rw [qBudget, pow_two]
    exact controlled_degree (mul_bound (H .aay false false) (H .xxy true false))
      (by simp [Bool.toNat]; omega)
  have hq := mul_bound (H .xx false false) hQx
  have hw := mul_bound (H .xx true false) (q_bound hp ha hx hy)
  exact mono (sub_bound (controlled_degree hq (by simp [Bool.toNat]; omega))
    (controlled_degree hw (by simp [Bool.toNat]; omega)))
    (by ring_nf; omega)

private theorem y_bound {p : ℕ} (hp : 0 < p) {a x y : Sparse} (ha : Controlled a.terms 1 3)
    (hx : Controlled x.terms 1 3) (hy : Controlled y.terms 1 3) :
    Controlled (yPolynomial p a x y).terms (6 * p - 1) (3 * (defectBudget p) ^ 2) := by
  have H (shape : Shape) (dx dy : Bool) := partial_bound hp ha hx hy shape dx dy
  have hd := mul_bound (mul_bound (constant_bound 2) (H .yy false false))
    (H .mixed false true)
  have hw := mul_bound (H .yy false true) (H .mixed false false)
  exact mono (sub_bound (controlled_degree hd (by simp [Bool.toNat]; omega))
    (controlled_degree hw (by simp [Bool.toNat]; omega)))
    (by ring_nf; omega)

private theorem v_bound {p : ℕ} (hp : 0 < p) {a x y : Sparse} (ha : Controlled a.terms 1 3)
    (hx : Controlled x.terms 1 3) (hy : Controlled y.terms 1 3) :
    Controlled (vPolynomial p a x y).terms (9 * p - 1) (edgeBudget p) := by
  have H (shape : Shape) (dx dy : Bool) := partial_bound hp ha hx hy shape dx dy
  have hQy : Controlled (qyPolynomial p a x y).terms (6 * p - 1) (2 * qBudget p) := by
    have h₁ := controlled_degree (mul_bound (H .aay false true) (H .xxy false false))
      (show _ = 6 * p - 1 by simp [Bool.toNat]; omega)
    have h₂ := controlled_degree (mul_bound (H .aay false false) (H .xxy false true))
      (show _ = 6 * p - 1 by simp [Bool.toNat]; omega)
    exact mono (add_bound h₁ h₂) (by ring_nf; omega)
  have hq := mul_bound (H .yy false false) hQy
  have hw := mul_bound (H .yy false true) (q_bound hp ha hx hy)
  exact mono (sub_bound (controlled_degree hq (by simp [Bool.toNat]; omega))
    (controlled_degree hw (by simp [Bool.toNat]; omega)))
    (by ring_nf; omega)

private inductive Sign
  | z | p | discriminant
  | gap | left | leftSquare | right | rightSquare

private def Sign.degree (p : ℕ) : Sign → ℕ
  | .z => 9 * p - 2
  | .p => 18 * p - 2
  | .discriminant => 36 * p - 4
  | .gap => 6 * p
  | .left | .right => 9 * p - 1
  | .leftSquare | .rightSquare => 18 * p - 2

private def Sign.budget (p : ℕ) : Sign → ℕ
  | .z => zBudget p
  | .p => pBudget p
  | .discriminant => (zBudget p) ^ 2 * (qBudget p) ^ 3 + (pBudget p) ^ 2
  | .gap => 2 * (defectBudget p) ^ 2
  | .left | .right => edgeBudget p
  | .leftSquare | .rightSquare => edgeSquareBudget p

-- The centered digit must strictly exceed the bound on the coefficient norm.
private def Sign.bits (sign : Sign) (p : ℕ) : ℕ := (sign.budget p).log2 + 1

private def Sign.polynomial [Add R] [Sub R] [Mul R] [Pow R Nat] [NatCast R] [Zero R]
    (sign : Sign) (p : ℕ) (a x y : R) : R :=
  match sign with
  | .z => 0 - zPolynomial p a x y
  | .p => 0 - pPolynomial p a x y
  | .discriminant => zPolynomial p a x y ^ (2 : ℕ) * qPolynomial p a x y ^ (3 : ℕ) -
      pPolynomial p a x y ^ (2 : ℕ)
  | .gap => defectPartial p .mixed false false a x y ^ (2 : ℕ) - qPolynomial p a x y
  | .left => 0 - uPolynomial p a x y
  | .leftSquare => uPolynomial p a x y ^ (2 : ℕ) -
      xPolynomial p a x y ^ (2 : ℕ) * qPolynomial p a x y
  | .right => vPolynomial p a x y
  | .rightSquare => vPolynomial p a x y ^ (2 : ℕ) -
      yPolynomial p a x y ^ (2 : ℕ) * qPolynomial p a x y

private theorem Sign.eval_polynomial {R : Type*} [CommRing R]
    (sign : Sign) (p : ℕ) (s t u : R) (a x y : Sparse) :
    (sign.polynomial p a x y).eval s t u =
      sign.polynomial p (a.eval s t u) (x.eval s t u) (y.eval s t u) := by
  cases sign <;> simp only [Sign.polynomial, zPolynomial, pPolynomial, qPolynomial, qxPolynomial,
    qyPolynomial, qxyPolynomial, xPolynomial, uPolynomial, yPolynomial, vPolynomial,
    eval_zero, eval_cast, eval_add, eval_sub, eval_mul, eval_pow, eval_partial]

private theorem Sign.controlled (sign : Sign) {p : ℕ} (hp : 0 < p)
    {a x y : Sparse} (ha : Controlled a.terms 1 3)
    (hx : Controlled x.terms 1 3) (hy : Controlled y.terms 1 3) :
    Controlled (sign.polynomial p a x y).terms (sign.degree p) (sign.budget p) := by
  have hzero (d : ℕ) : Controlled (0 : Sparse).terms d 0 := empty_controlled d 0
  cases sign with
  | z =>
    change Controlled (0 - zPolynomial p a x y).terms (9 * p - 2) (zBudget p)
    simpa only [Nat.zero_add] using sub_bound (hzero (9 * p - 2)) (z_bound hp ha hx hy)
  | p =>
    change Controlled (0 - pPolynomial p a x y).terms (18 * p - 2) (pBudget p)
    simpa only [Nat.zero_add] using sub_bound (hzero (18 * p - 2)) (p_bound hp ha hx hy)
  | discriminant =>
    have hz := controlled_degree
      (mul_bound (pow_bound (z_bound hp ha hx hy) 2) (pow_bound (q_bound hp ha hx hy) 3))
      (show _ = 36 * p - 4 by omega)
    have hp' := controlled_degree (pow_bound (p_bound hp ha hx hy) 2)
      (show _ = 36 * p - 4 by omega)
    exact sub_bound hz hp'
  | gap =>
    have hd := controlled_degree (pow_bound (partial_bound hp ha hx hy .mixed false false) 2)
      (show _ = 6 * p by simp [Bool.toNat]; omega)
    exact mono (sub_bound hd (q_bound hp ha hx hy)) (by simp only [Sign.budget]; ring_nf; omega)
  | left =>
    change Controlled (0 - uPolynomial p a x y).terms (9 * p - 1) (edgeBudget p)
    simpa only [Nat.zero_add] using sub_bound (hzero (9 * p - 1)) (u_bound hp ha hx hy)
  | leftSquare =>
    have hEdge := controlled_degree (pow_bound (u_bound hp ha hx hy) 2)
      (show _ = 18 * p - 2 by omega)
    have hScaled := controlled_degree (mul_bound (pow_bound (x_bound hp ha hx hy) 2)
      (q_bound hp ha hx hy)) (show _ = 18 * p - 2 by omega)
    exact mono (sub_bound hEdge hScaled)
      (by simp only [Sign.budget]; ring_nf; omega)
  | right => exact v_bound hp ha hx hy
  | rightSquare =>
    have hEdge := controlled_degree (pow_bound (v_bound hp ha hx hy) 2)
      (show _ = 18 * p - 2 by omega)
    have hScaled := controlled_degree (mul_bound (pow_bound (y_bound hp ha hx hy) 2)
      (q_bound hp ha hx hy)) (show _ = 18 * p - 2 by omega)
    exact mono (sub_bound hEdge hScaled)
      (by simp only [Sign.budget]; ring_nf; omega)

private theorem Sign.budget_lt (sign : Sign) (p : ℕ) :
    sign.budget p < 2 ^ sign.bits p :=
  Nat.lt_log2_self

private def Sign.base (sign : Sign) (p : ℕ) : ℕ := 2 ^ (sign.bits p + 1)

/-- Evaluate at the integer encoding of the three ordered gaps. -/
private def Sign.encoded (sign : Sign) (p : ℕ) : ℤ :=
  let b : ℤ := (sign.base p)
  sign.polynomial p 1 (1 + b) (1 + b + b ^ (sign.degree p + 1))

private def Sign.mask (sign : Sign) (p : ℕ) : ℕ := PackedCheck.centeredMask (sign.bits p) (sign.degree p)

private def Sign.check (sign : Sign) (p : ℕ) : Bool :=
  (((sign.encoded p) + ↑(sign.mask p)).toNat &&& (sign.mask p)) == (sign.mask p)

set_option maxHeartbeats 0 in
-- Each packed check evaluates the full integer certificate with kernel reduction.
private theorem Sign.passes_five (sign : Sign) : sign.check 5 = true := by
  cases sign <;> decide +kernel

set_option maxHeartbeats 0 in
-- The kernel reduces the complete degree-six packed integer masks.
private theorem Sign.passes_six (sign : Sign) : sign.check 6 = true := by
  cases sign <;> decide +kernel

set_option maxHeartbeats 0 in
-- The kernel reduces the complete degree-seven packed integer masks.
private theorem Sign.passes_seven (sign : Sign) : sign.check 7 = true := by
  cases sign <;> decide +kernel

set_option maxHeartbeats 0 in
private theorem Sign.passes_eight (sign : Sign) : sign.check 8 = true := by
  cases sign <;> decide +kernel

set_option maxHeartbeats 0 in
private theorem Sign.passes_nine (sign : Sign) : sign.check 9 = true := by
  cases sign <;> decide +kernel

set_option maxHeartbeats 0 in
private theorem Sign.passes_ten (sign : Sign) : sign.check 10 = true := by
  cases sign <;> decide +kernel

private theorem Sign.ordered_nonneg (sign : Sign) {p : ℕ}
    (hp : 0 < p) (hpass : sign.check p = true) (a x y : ℝ)
    (ha : 0 ≤ a) (hax : a ≤ x) (hxy : x ≤ y) :
    0 ≤ sign.polynomial p a x y := by
  let s : Sparse := ⟨[⟨(1, 0, 0), 1⟩]⟩
  let t : Sparse := ⟨[⟨(0, 1, 0), 1⟩]⟩
  let u : Sparse := ⟨[⟨(0, 0, 1), 1⟩]⟩
  have hs : Controlled s.terms 1 1 := by simp [Controlled, coefficientNorm, s, Term.degree]
  have ht : Controlled t.terms 1 1 := by simp [Controlled, coefficientNorm, t, Term.degree]
  have hu : Controlled u.terms 1 1 := by simp [Controlled, coefficientNorm, u, Term.degree]
  have hst := add_bound hs ht
  have hstu := add_bound hst hu
  let poly := sign.polynomial p s (s + t) (s + t + u)
  have hc : Controlled poly.terms (sign.degree p) (sign.budget p) :=
    sign.controlled hp (mono hs (by decide)) (mono hst (by decide)) hstu
  have eval_ordered {R : Type} [CommRing R] (v w z : R) :
      poly.eval v w z = sign.polynomial p v (v + w) (v + w + z) := by
    simp only [poly, Sign.eval_polynomial, eval_add]
    simp [s, t, u, Sparse.eval_unit_term]
  have he : poly.eval (1 : ℤ) ((sign.base p) : ℤ) (((sign.base p) : ℤ) ^ (sign.degree p + 1)) =
      (sign.encoded p) := eval_ordered (1 : ℤ) ((sign.base p) : ℤ) (((sign.base p) : ℤ) ^ (sign.degree p + 1))
  have h := Sparse.nonneg_of_packed (poly := poly) (d := (sign.degree p)) (w := (sign.bits p)) ha (sub_nonneg.mpr hax) (sub_nonneg.mpr hxy)
    hc.1 (hc.2.trans_lt (sign.budget_lt p)) (sign.encoded p)
    he (beq_iff_eq.mp hpass)
  simpa only [eval_ordered, add_sub_cancel, show a + (x - a) = x by ring,
    show x + (y - x) = y by ring] using h

private theorem ordered_of_check {p : ℕ} (hp : 0 < p)
    (hpass : ∀ sign : Sign, sign.check p = true) (a x y : ℝ) (ha : 0 ≤ a) (hax : a ≤ x) (hxy : x ≤ y) :
    Z p a x y ≤ 0 ∧ P p a x y ≤ 0 ∧ P p a x y ^ 2 ≤ Z p a x y ^ 2 * q p a x y ^ 3 := by
  have hz := Sign.ordered_nonneg .z hp (hpass .z) a x y ha hax hxy
  have hpSign := Sign.ordered_nonneg .p hp (hpass .p) a x y ha hax hxy
  have hd := Sign.ordered_nonneg .discriminant hp (hpass .discriminant) a x y ha hax hxy
  simp only [Sign.polynomial, zPolynomial_eq, pPolynomial_eq, qPolynomial_eq, sub_nonneg] at hz hpSign hd
  exact ⟨hz, hpSign, hd⟩

private theorem ordered_edges_of_check {p : ℕ} (hp : 0 < p)
    (hpass : ∀ sign : Sign, sign.check p = true) (a x y : ℝ) (ha : 0 ≤ a) (hax : a ≤ x) (hxy : x ≤ y) :
    q p a x y ≤ defect p a x y ^ 2 ∧
    UAt p a x y ≤ 0 ∧ XAt p a x y ^ 2 * q p a x y ≤ UAt p a x y ^ 2 ∧
    0 ≤ VAt p a x y ∧ YAt p a x y ^ 2 * q p a x y ≤ VAt p a x y ^ 2 := by
  obtain ⟨hx, hu, hy, hv⟩ := edgePolynomials_eq p a x y
  have hgap := Sign.ordered_nonneg .gap hp (hpass .gap) a x y ha hax hxy
  have hleft := Sign.ordered_nonneg .left hp (hpass .left) a x y ha hax hxy
  have hleftSq := Sign.ordered_nonneg .leftSquare hp (hpass .leftSquare) a x y ha hax hxy
  have hright := Sign.ordered_nonneg .right hp (hpass .right) a x y ha hax hxy
  have hrightSq := Sign.ordered_nonneg .rightSquare hp (hpass .rightSquare) a x y ha hax hxy
  simp only [Sign.polynomial, partial_zero, Shape.args, qPolynomial_eq, hx, hu, hy, hv,
    sub_nonneg] at hgap hleft hleftSq hright hrightSq
  exact ⟨hgap, hleft, hleftSq, hright, hrightSq⟩

/-- The exact three ordered scalar signs for the unrestricted `(5,3)` argument.
The signs also hold on the closed ordered chamber. -/
theorem ordered_five (a x y : ℝ) (ha : 0 ≤ a) (hax : a ≤ x) (hxy : x ≤ y) :
    Z 5 a x y ≤ 0 ∧ P 5 a x y ≤ 0 ∧ P 5 a x y ^ 2 ≤ Z 5 a x y ^ 2 * q 5 a x y ^ 3 :=
  ordered_of_check (by decide) Sign.passes_five a x y ha hax hxy

/-- The corner and the two edge derivative bounds on the closed ordered chamber. -/
theorem ordered_edges_five (a x y : ℝ) (ha : 0 ≤ a) (hax : a ≤ x) (hxy : x ≤ y) :
    q 5 a x y ≤ defect 5 a x y ^ 2 ∧
    U a x y ≤ 0 ∧ X a x y ^ 2 * q 5 a x y ≤ U a x y ^ 2 ∧
    0 ≤ V a x y ∧ Y a x y ^ 2 * q 5 a x y ≤ V a x y ^ 2 :=
  ordered_edges_of_check (by decide) Sign.passes_five a x y ha hax hxy

/-- Exact ordered scalar signs at degree six. -/
theorem ordered_six (a x y : ℝ) (ha : 0 ≤ a) (hax : a ≤ x) (hxy : x ≤ y) :
    Z 6 a x y ≤ 0 ∧ P 6 a x y ≤ 0 ∧ P 6 a x y ^ 2 ≤ Z 6 a x y ^ 2 * q 6 a x y ^ 3 :=
  ordered_of_check (by decide) Sign.passes_six a x y ha hax hxy

/-- Exact ordered scalar signs at degree six. -/
theorem ordered_edges_six (a x y : ℝ) (ha : 0 ≤ a) (hax : a ≤ x) (hxy : x ≤ y) :
    q 6 a x y ≤ defect 6 a x y ^ 2 ∧
    UAt 6 a x y ≤ 0 ∧ XAt 6 a x y ^ 2 * q 6 a x y ≤ UAt 6 a x y ^ 2 ∧
    0 ≤ VAt 6 a x y ∧ YAt 6 a x y ^ 2 * q 6 a x y ≤ VAt 6 a x y ^ 2 :=
  ordered_edges_of_check (by decide) Sign.passes_six a x y ha hax hxy

/-- Exact ordered scalar signs at degree seven. -/
theorem ordered_seven (a x y : ℝ) (ha : 0 ≤ a) (hax : a ≤ x) (hxy : x ≤ y) :
    Z 7 a x y ≤ 0 ∧ P 7 a x y ≤ 0 ∧ P 7 a x y ^ 2 ≤ Z 7 a x y ^ 2 * q 7 a x y ^ 3 :=
  ordered_of_check (by decide) Sign.passes_seven a x y ha hax hxy

/-- The degree-seven corner and edge derivative bounds on the closed ordered chamber. -/
theorem ordered_edges_seven (a x y : ℝ) (ha : 0 ≤ a) (hax : a ≤ x) (hxy : x ≤ y) :
    q 7 a x y ≤ defect 7 a x y ^ 2 ∧
    UAt 7 a x y ≤ 0 ∧ XAt 7 a x y ^ 2 * q 7 a x y ≤ UAt 7 a x y ^ 2 ∧
    0 ≤ VAt 7 a x y ∧ YAt 7 a x y ^ 2 * q 7 a x y ≤ VAt 7 a x y ^ 2 :=
  ordered_edges_of_check (by decide) Sign.passes_seven a x y ha hax hxy

/-- The degree-eight mixed derivative bounds on the closed ordered chamber. -/
theorem ordered_eight (a x y : ℝ) (ha : 0 ≤ a) (hax : a ≤ x) (hxy : x ≤ y) :
    Z 8 a x y ≤ 0 ∧ P 8 a x y ≤ 0 ∧ P 8 a x y ^ 2 ≤ Z 8 a x y ^ 2 * q 8 a x y ^ 3 :=
  ordered_of_check (by decide) Sign.passes_eight a x y ha hax hxy

/-- The degree-eight corner and edge derivative bounds on the closed ordered chamber. -/
theorem ordered_edges_eight (a x y : ℝ) (ha : 0 ≤ a) (hax : a ≤ x) (hxy : x ≤ y) :
    q 8 a x y ≤ defect 8 a x y ^ 2 ∧
    UAt 8 a x y ≤ 0 ∧ XAt 8 a x y ^ 2 * q 8 a x y ≤ UAt 8 a x y ^ 2 ∧
    0 ≤ VAt 8 a x y ∧ YAt 8 a x y ^ 2 * q 8 a x y ≤ VAt 8 a x y ^ 2 :=
  ordered_edges_of_check (by decide) Sign.passes_eight a x y ha hax hxy

/-- The degree-nine mixed derivative bounds on the closed ordered chamber. -/
theorem ordered_nine (a x y : ℝ) (ha : 0 ≤ a) (hax : a ≤ x) (hxy : x ≤ y) :
    Z 9 a x y ≤ 0 ∧ P 9 a x y ≤ 0 ∧ P 9 a x y ^ 2 ≤ Z 9 a x y ^ 2 * q 9 a x y ^ 3 :=
  ordered_of_check (by decide) Sign.passes_nine a x y ha hax hxy

/-- The degree-nine corner and edge derivative bounds on the closed ordered chamber. -/
theorem ordered_edges_nine (a x y : ℝ) (ha : 0 ≤ a) (hax : a ≤ x) (hxy : x ≤ y) :
    q 9 a x y ≤ defect 9 a x y ^ 2 ∧
    UAt 9 a x y ≤ 0 ∧ XAt 9 a x y ^ 2 * q 9 a x y ≤ UAt 9 a x y ^ 2 ∧
    0 ≤ VAt 9 a x y ∧ YAt 9 a x y ^ 2 * q 9 a x y ≤ VAt 9 a x y ^ 2 :=
  ordered_edges_of_check (by decide) Sign.passes_nine a x y ha hax hxy

/-- The degree-ten mixed derivative bounds on the closed ordered chamber. -/
theorem ordered_ten (a x y : ℝ) (ha : 0 ≤ a) (hax : a ≤ x) (hxy : x ≤ y) :
    Z 10 a x y ≤ 0 ∧ P 10 a x y ≤ 0 ∧ P 10 a x y ^ 2 ≤ Z 10 a x y ^ 2 * q 10 a x y ^ 3 :=
  ordered_of_check (by decide) Sign.passes_ten a x y ha hax hxy

/-- The degree-ten corner and edge derivative bounds on the closed ordered chamber. -/
theorem ordered_edges_ten (a x y : ℝ) (ha : 0 ≤ a) (hax : a ≤ x) (hxy : x ≤ y) :
    q 10 a x y ≤ defect 10 a x y ^ 2 ∧
    UAt 10 a x y ≤ 0 ∧ XAt 10 a x y ^ 2 * q 10 a x y ≤ UAt 10 a x y ^ 2 ∧
    0 ≤ VAt 10 a x y ∧ YAt 10 a x y ^ 2 * q 10 a x y ≤ VAt 10 a x y ^ 2 :=
  ordered_edges_of_check (by decide) Sign.passes_ten a x y ha hax hxy

#print axioms ordered_five
#print axioms ordered_edges_five
#print axioms ordered_six
#print axioms ordered_edges_six
#print axioms ordered_seven
#print axioms ordered_edges_seven
#print axioms ordered_eight
#print axioms ordered_edges_eight
#print axioms ordered_nine
#print axioms ordered_edges_nine
#print axioms ordered_ten
#print axioms ordered_edges_ten

end RefinedBMV.ExtremeCertificate
