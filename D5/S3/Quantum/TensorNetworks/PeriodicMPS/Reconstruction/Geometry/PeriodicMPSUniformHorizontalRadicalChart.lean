/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalRadicalChart
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalRadicalChart
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Component degrees in the two radical charts. -/
-- Adapted from uniform-horizontal-radical-degree/work_target.
module

public import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformHorizontalSpectralQuadratics
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-! The two square rules give a four-coefficient spectral filtration. -/

public section

set_option autoImplicit false

namespace UniformMPSHorizontalSpectral

open MvPolynomial
open scoped QuadraticAlgebra

noncomputable section

variable {σ R : Type*} [CommRing R]

/-- The free rank-four algebra with square rules `x^2 = D` and `y^2 = E`. -/
abbrev RadicalAlgebra {P : Type*} [CommRing P] (D E : P) :=
  QuadraticAlgebra (QuadraticAlgebra P D 0) (.C E) 0

section Reduction

variable {P : Type*} [CommRing P] {D E : P}

/-- The powers of the first and second radical index the four coefficients. -/
def radicalCoeff (z : RadicalAlgebra D E) (i j : Fin 2) : P :=
  let a := if j = 0 then z.re else z.im
  if i = 0 then a.re else a.im

def radicalX : RadicalAlgebra D E := .C ω

def radicalY : RadicalAlgebra D E := ω

@[simp] theorem radicalScalar_apply (p : P) :
    algebraMap P (RadicalAlgebra D E) p = .C (.C p) := rfl

private theorem radicalX_sq : (radicalX : RadicalAlgebra D E) ^ 2 =
    algebraMap P _ D := by
  ext <;> simp [radicalX, pow_two]

private theorem radicalY_sq : (radicalY : RadicalAlgebra D E) ^ 2 =
    algebraMap P _ E := by
  ext <;> simp [radicalY, pow_two]

@[simp] theorem radicalCoeff_zero (i j : Fin 2) :
    radicalCoeff (0 : RadicalAlgebra D E) i j = 0 := by
  simp [radicalCoeff]

@[simp] theorem radicalCoeff_add (z w : RadicalAlgebra D E) (i j : Fin 2) :
    radicalCoeff (z + w) i j = radicalCoeff z i j + radicalCoeff w i j := by
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [radicalCoeff, hi, hj]

@[simp] theorem radicalCoeff_neg (z : RadicalAlgebra D E) (i j : Fin 2) :
    radicalCoeff (-z) i j = -radicalCoeff z i j := by
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [radicalCoeff, hi, hj]

/-- The polynomial scalar times an arbitrary radical monomial. -/
def radicalTerm (p : P) (i j : ℕ) : RadicalAlgebra D E :=
  algebraMap P _ p * radicalX ^ i * radicalY ^ j

@[simp] theorem radicalTerm_zero (i j : ℕ) :
    radicalTerm (D := D) (E := E) (0 : P) i j = 0 := by
  simp only [radicalTerm, map_zero, zero_mul]

theorem radicalTerm_mul (p q : P) (i j s t : ℕ) :
    radicalTerm (D := D) (E := E) p i j * radicalTerm q s t =
      radicalTerm (p * q) (i + s) (j + t) := by
  simp only [radicalTerm, map_mul, pow_add]
  ac_rfl

theorem radicalCoeff_term (p : P) (i j s t : Fin 2) :
    radicalCoeff (radicalTerm (D := D) (E := E) p i j) s t =
      if s = i ∧ t = j then p else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases s <;> fin_cases t <;>
    simp [radicalCoeff, radicalTerm, radicalX, radicalY]

theorem radical_expansion (z : RadicalAlgebra D E) :
    z = ∑ i : Fin 2, ∑ j : Fin 2, radicalTerm (radicalCoeff z i j) i j := by
  rw [Fin.sum_univ_two]
  simp only [Fin.sum_univ_two, radicalCoeff, radicalTerm, radicalX, radicalY]
  ext <;> simp

end Reduction

section Filtration

variable {D E : MvPolynomial σ R}

/-- A present coefficient is charged for its basis element as well as its spectral support. -/
def RadicalDegreeLE (n : ℕ) (z : RadicalAlgebra D E) : Prop :=
  ∀ i j : Fin 2, radicalCoeff z i j = 0 ∨
    (radicalCoeff z i j).totalDegree + 3 * i.val + 6 * j.val ≤ n

theorem RadicalDegreeLE.mono {a b : ℕ} {z : RadicalAlgebra D E}
    (h : RadicalDegreeLE a z) (hab : a ≤ b) : RadicalDegreeLE b z :=
  fun i j => (h i j).imp_right (fun h' => h'.trans hab)

theorem RadicalDegreeLE.zero (n : ℕ) : RadicalDegreeLE n (0 : RadicalAlgebra D E) :=
  fun i j => Or.inl (radicalCoeff_zero i j)

theorem RadicalDegreeLE.add {n : ℕ} {z w : RadicalAlgebra D E}
    (hz : RadicalDegreeLE n z) (hw : RadicalDegreeLE n w) : RadicalDegreeLE n (z + w) := by
  intro i j
  rw [radicalCoeff_add]
  rcases hz i j with h | h
  · simpa only [h, zero_add] using hw i j
  rcases hw i j with h' | h'
  · simpa only [h', add_zero] using Or.inr h
  right
  have hsum := totalDegree_add (radicalCoeff z i j) (radicalCoeff w i j)
  omega

theorem RadicalDegreeLE.neg {n : ℕ} {z : RadicalAlgebra D E}
    (hz : RadicalDegreeLE n z) : RadicalDegreeLE n (-z) := by
  intro i j
  rw [radicalCoeff_neg]
  simpa using hz i j

theorem RadicalDegreeLE.sum {ι : Type*} (s : Finset ι) (f : ι → RadicalAlgebra D E)
    {n : ℕ} (h : ∀ i ∈ s, RadicalDegreeLE n (f i)) :
    RadicalDegreeLE n (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero n
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem radicalTerm_degreeLE (p : MvPolynomial σ R) (i j : Fin 2) {n : ℕ}
    (h : p = 0 ∨ p.totalDegree + 3 * i.val + 6 * j.val ≤ n) :
    RadicalDegreeLE n (radicalTerm (D := D) (E := E) p i j) := by
  intro s t
  rw [radicalCoeff_term]
  by_cases he : s = i ∧ t = j
  · obtain ⟨rfl, rfl⟩ := he
    simpa using h
  · exact Or.inl (ite_eq_right he)

theorem radicalScalar_degreeLE {p : MvPolynomial σ R} {n : ℕ} (h : p.totalDegree ≤ n) :
    RadicalDegreeLE n (algebraMap (MvPolynomial σ R) (RadicalAlgebra D E) p) := by
  simpa [radicalTerm] using radicalTerm_degreeLE (D := D) (E := E) p 0 0
    (n := n) (Or.inr (by simpa using h))

/-- Reduction uses the two square rules on each monomial and charges only its surviving basis. -/
theorem radicalTerm_degreeLE_of_squares (hD : D.totalDegree ≤ 6) (hE : E.totalDegree ≤ 12)
    (p : MvPolynomial σ R) (i j : ℕ) :
    RadicalDegreeLE (p.totalDegree + 3 * i + 6 * j)
      (radicalTerm (D := D) (E := E) p i j) := by
  obtain ⟨hr, hd⟩ := reduce_quadratic_monomial p D E
    (radicalX : RadicalAlgebra D E) (radicalY : RadicalAlgebra D E) i j hD hE
    radicalX_sq radicalY_sq
  change radicalTerm p i j = radicalTerm (p * D ^ (i / 2) * E ^ (j / 2)) (i % 2) (j % 2) at hr
  rw [hr]
  let s : Fin 2 := ⟨i % 2, Nat.mod_lt _ (by decide)⟩
  let t : Fin 2 := ⟨j % 2, Nat.mod_lt _ (by decide)⟩
  exact radicalTerm_degreeLE _ s t (Or.inr hd)

/-- Multiplication expands the two four-term expressions and reduces each pair. -/
theorem RadicalDegreeLE.mul (hD : D.totalDegree ≤ 6) (hE : E.totalDegree ≤ 12)
    {a b : ℕ} {z w : RadicalAlgebra D E}
    (hz : RadicalDegreeLE a z) (hw : RadicalDegreeLE b w) :
    RadicalDegreeLE (a + b) (z * w) := by
  rw [congrArg₂ (· * ·) (radical_expansion z) (radical_expansion w), Finset.sum_mul]
  apply sum _ _; intro i _
  rw [Finset.sum_mul]
  apply sum _ _; intro j _
  rw [Finset.mul_sum]
  apply sum _ _; intro s _
  rw [Finset.mul_sum]
  apply sum _ _; intro t _
  rw [radicalTerm_mul]
  rcases hz i j with hp | hp
  · rw [hp, zero_mul, radicalTerm_zero]
    exact zero (a + b)
  rcases hw s t with hq | hq
  · rw [hq, mul_zero, radicalTerm_zero]
    exact zero (a + b)
  let p := radicalCoeff z i j
  let q := radicalCoeff w s t
  apply (radicalTerm_degreeLE_of_squares hD hE (p * q) _ _).mono
  have hprod := totalDegree_mul p q
  change p.totalDegree + 3 * i.val + 6 * j.val ≤ a at hp
  change q.totalDegree + 3 * s.val + 6 * t.val ≤ b at hq
  omega

theorem RadicalDegreeLE.prod (hD : D.totalDegree ≤ 6) (hE : E.totalDegree ≤ 12)
    {ι : Type*} (s : Finset ι) (f : ι → RadicalAlgebra D E) (n : ι → ℕ)
    (h : ∀ i ∈ s, RadicalDegreeLE (n i) (f i)) :
    RadicalDegreeLE (∑ i ∈ s, n i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using radicalScalar_degreeLE (D := D) (E := E)
        (p := 1) (n := 0) (by simp)
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      exact (h i (Finset.mem_insert_self i s)).mul hD hE
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem RadicalDegreeLE.pow (hD : D.totalDegree ≤ 6) (hE : E.totalDegree ≤ 12)
    {n : ℕ} {z : RadicalAlgebra D E} (h : RadicalDegreeLE n z) (r : ℕ) :
    RadicalDegreeLE (r * n) (z ^ r) := by
  induction r with
  | zero =>
      simpa using radicalScalar_degreeLE (D := D) (E := E)
        (p := 1) (n := 0) (by simp)
  | succ r ih =>
      rw [pow_succ, Nat.succ_mul]
      exact ih.mul hD hE h

theorem eval₂Hom_radicalDegreeLE {S ι : Type*} [CommRing S]
    (f : S →+* R) (v : ι → RadicalAlgebra D E)
    (hD : D.totalDegree ≤ 6) (hE : E.totalDegree ≤ 12)
    (hv : ∀ i, RadicalDegreeLE 9 (v i)) (p : MvPolynomial ι S) :
    RadicalDegreeLE (9 * p.totalDegree)
      (eval₂Hom (((algebraMap (MvPolynomial σ R) (RadicalAlgebra D E)).comp C).comp f) v p) := by
  classical
  let subst := eval₂Hom
    (((algebraMap (MvPolynomial σ R) (RadicalAlgebra D E)).comp C).comp f) v
  change RadicalDegreeLE (9 * p.totalDegree) (subst p)
  have he := congrArg subst p.as_sum
  rw [map_sum] at he
  rw [he]
  apply RadicalDegreeLE.sum
  intro m hm
  rw [show subst (monomial m (p.coeff m)) = _ from eval₂Hom_monomial _ _ _ _]
  apply (RadicalDegreeLE.mul hD hE
    (radicalScalar_degreeLE (p := C (f (p.coeff m))) (n := 0) (by simp))
    (RadicalDegreeLE.prod hD hE _ _ (fun i => m i * 9)
      (fun i _ => (hv i).pow hD hE (m i)))).mono
  have hm' := le_totalDegree hm
  change m.sum (fun _ e => e) ≤ p.totalDegree at hm'
  simpa [Finsupp.sum, Finset.sum_mul, Nat.mul_comm 9] using Nat.mul_le_mul_right 9 hm'

end Filtration

section Charts

variable {D E : MvPolynomial σ R}

private def chartCoordinates (L W : MvPolynomial σ R) (half factor k : R) :
    Fin 5 → RadicalAlgebra D E :=
  let scalar := algebraMap (MvPolynomial σ R) (RadicalAlgebra D E)
  let d := scalar (C half) * (scalar L + radicalX)
  let db := scalar (C half) * (scalar L - radicalX)
  ![d, db, scalar (C factor) * (scalar W + radicalY) * db,
    scalar (C factor) * (scalar W - radicalY) * d, scalar (C k)]

private theorem chartCoordinates_degreeLE (L W : MvPolynomial σ R) (half factor k : R)
    (hL : L.totalDegree ≤ 3) (hW : W.totalDegree ≤ 6)
    (hD : D.totalDegree ≤ 6) (hE : E.totalDegree ≤ 12) (i : Fin 5) :
    RadicalDegreeLE 9 (chartCoordinates (D := D) (E := E) L W half factor k i) := by
  let scalar := algebraMap (MvPolynomial σ R) (RadicalAlgebra D E)
  have hx : RadicalDegreeLE 3 (radicalX : RadicalAlgebra D E) := by
    simpa [radicalTerm] using radicalTerm_degreeLE (D := D) (E := E)
      (1 : MvPolynomial σ R) 1 0 (n := 3) (Or.inr (by simp))
  have hy : RadicalDegreeLE 6 (radicalY : RadicalAlgebra D E) := by
    simpa [radicalTerm] using radicalTerm_degreeLE (D := D) (E := E)
      (1 : MvPolynomial σ R) 0 1 (n := 6) (Or.inr (by simp))
  have hc (r : R) : RadicalDegreeLE 0 (scalar (C r)) := radicalScalar_degreeLE (by simp)
  have hd : RadicalDegreeLE 3 (scalar (C half) * (scalar L + radicalX)) :=
    (hc half).mul hD hE ((radicalScalar_degreeLE hL).add hx)
  have hdb : RadicalDegreeLE 3 (scalar (C half) * (scalar L - radicalX)) := by
    rw [sub_eq_add_neg]
    exact (hc half).mul hD hE ((radicalScalar_degreeLE hL).add hx.neg)
  have hplus : RadicalDegreeLE 6 (scalar W + radicalY) := (radicalScalar_degreeLE hW).add hy
  have hminus : RadicalDegreeLE 6 (scalar W - radicalY) := by
    rw [sub_eq_add_neg]
    exact (radicalScalar_degreeLE hW).add hy.neg
  fin_cases i
  · exact hd.mono (by decide)
  · exact hdb.mono (by decide)
  · exact ((hc factor).mul hD hE hplus).mul hD hE hdb
  · exact ((hc factor).mul hD hE hminus).mul hD hE hd
  · exact (hc k).mono (by decide)

variable (a b c : MvPolynomial σ R) (U k two : Rˣ)

/-- The chart with second difference `y` and spectral-independent inverses of `2,U,k`.
The argument `two` supplies the unit representing 2. -/
def radicalCoordinatesU :
    Fin 5 → RadicalAlgebra (firstSquare (firstSum a b U k) U)
      (secondSquare (secondSumU b c U ↑(k⁻¹)) b U 1) :=
  chartCoordinates (firstSum a b U k) (secondSumU b c U ↑(k⁻¹))
    ↑(two⁻¹) (↑(two⁻¹) * ↑(U⁻¹)) k

/-- The chart with second difference `Z = k^2 y`. -/
def radicalCoordinatesK :
    Fin 5 → RadicalAlgebra (firstSquare (firstSum a b U k) U)
      (secondSquare (secondSumK b c U k) b U ((k : R) ^ 4)) :=
  chartCoordinates (firstSum a b U k) (secondSumK b c U k)
    ↑(two⁻¹) (↑(two⁻¹) * ↑(U⁻¹) * (↑(k⁻¹) : R) ^ 2) k

theorem radicalCoordinatesU_degreeLE
    (ha : a.totalDegree ≤ 2) (hb : b.totalDegree ≤ 3) (hc : c.totalDegree ≤ 4) (i : Fin 5) :
    RadicalDegreeLE 9 (radicalCoordinatesU a b c U k two i) := by
  obtain ⟨hL, hW, _, hx, hy, _⟩ := chart_quadratic_totalDegrees a b c U k ↑(k⁻¹) ha hb hc
  exact chartCoordinates_degreeLE _ _ _ _ _ hL hW hx hy i

theorem radicalCoordinatesK_degreeLE
    (ha : a.totalDegree ≤ 2) (hb : b.totalDegree ≤ 3) (hc : c.totalDegree ≤ 4) (i : Fin 5) :
    RadicalDegreeLE 9 (radicalCoordinatesK a b c U k two i) := by
  obtain ⟨hL, _, hV, hx, _, hZ⟩ := chart_quadratic_totalDegrees a b c U k ↑(k⁻¹) ha hb hc
  exact chartCoordinates_degreeLE _ _ _ _ _ hL hV hx hZ i

end Charts

end

end UniformMPSHorizontalSpectral
