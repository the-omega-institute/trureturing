/- GID: D5/S3/Quantum/Algebra/UnitBridgeRawGeometry
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/UnitBridgeRawGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.ContinuousMap.Algebra, mathlib/module/Mathlib.LinearAlgebra.CrossProduct]
   digest: Original continuous spin sections and the two raw moment identities. -/

import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! Continuous coordinate sections with the original, possibly incomplete carrier. -/

noncomputable section

namespace D5.S3.Quantum.Algebra.UnitBridgeRawGeometry

open scoped BigOperators

/-- The four continuous coordinate functions of a real spin section. -/
abbrev Sections (T : Type*) [TopologicalSpace T] := Fin 4 → C(T, ℝ)

/-- The specified Jordan multiplication, with scalar coordinate first. -/
def jordan {R : Type*} [CommRing R] (a b : Fin 4 → R) : Fin 4 → R :=
  ![a 0*b 0+a 1*b 1+a 2*b 2+a 3*b 3,
    a 0*b 1+b 0*a 1, a 0*b 2+b 0*a 2, a 0*b 3+b 0*a 3]

/-- The source operator L_a squared minus L_(a squared). -/
def hOp {R : Type*} [CommRing R] (a b : Fin 4 → R) :=
  jordan a (jordan a b) - jordan (jordan a a) b

/-- The quadratic Jordan operator U_a. -/
def uOp {R : Type*} [CommRing R] (a b : Fin 4 → R) :=
  (2 : ℕ) • jordan a (jordan a b) - jordan (jordan a a) b

/-- The constant unit or one of the three constant axes. -/
def axis {T : Type*} [TopologicalSpace T] (i : Fin 4) : Sections T :=
  fun j => if j = i then 1 else 0

/-- A scalar function embedded along the unit. -/
def central {T : Type*} [TopologicalSpace T] (f : C(T, ℝ)) : Sections T :=
  ![f, 0, 0, 0]

/-- An arbitrary real Jordan subalgebra containing literally all constant sections. -/
structure Original (T : Type*) [TopologicalSpace T] where
  carrier : Submodule ℝ (Sections T)
  jordan_mem : ∀ {a b}, a ∈ carrier → b ∈ carrier → jordan a b ∈ carrier
  constants : ∀ c : Fin 4 → ℝ, (fun i => ContinuousMap.const T (c i)) ∈ carrier

variable {T : Type*} [TopologicalSpace T]

private theorem axis_mem (E : Original T) (i : Fin 4) : axis i ∈ E.carrier := by
  convert E.constants (fun j => if j = i then 1 else 0) using 1
  ext j t
  by_cases h : j = i <;> simp [axis, h]

private theorem coordinate_mem (E : Original T) {a : Sections T} (ha : a ∈ E.carrier)
    (i : Fin 4) : central (a i) ∈ E.carrier := by
  let p (j : Fin 4) := jordan (axis j) (jordan (axis j) a)
  have hp (j : Fin 4) : p j ∈ E.carrier :=
    E.jordan_mem (axis_mem E j) (E.jordan_mem (axis_mem E j) ha)
  have hc : central (a 0) ∈ E.carrier := by
    have hm := E.carrier.smul_mem (1/2 : ℝ)
      (E.carrier.sub_mem (E.carrier.add_mem (E.carrier.add_mem (hp 1) (hp 2)) (hp 3)) ha)
    convert hm using 1
    ext j t
    fin_cases j <;> simp [p, jordan, axis, central, Matrix.vecHead, Matrix.vecTail] <;> ring
  have hi (j : Fin 4) (hj : j ≠ 0) : central (a j) ∈ E.carrier := by
    have hm := E.jordan_mem (E.carrier.sub_mem (hp j) hc) (axis_mem E j)
    convert hm using 1
    ext k t
    fin_cases j <;> fin_cases k <;>
      simp [p, jordan, axis, central, Matrix.vecHead, Matrix.vecTail] at hj ⊢
  fin_cases i
  · exact hc
  · exact hi 1 (by decide)
  · exact hi 2 (by decide)
  · exact hi 3 (by decide)

/-- The actual coefficient algebra, without inverse or square-root closure. -/
def scalarAlgebra (E : Original T) : Subalgebra ℝ C(T, ℝ) where
  carrier := {f | central f ∈ E.carrier}
  zero_mem' := by
    change central 0 ∈ E.carrier
    convert E.carrier.zero_mem using 1
    ext i t
    fin_cases i <;> simp [central]
  one_mem' := by
    change central 1 ∈ E.carrier
    convert axis_mem E 0 using 1
    ext i t
    fin_cases i <;> simp [axis, central]
  add_mem' := by
    intro f g hf hg
    simpa [central] using E.carrier.add_mem hf hg
  mul_mem' := by
    intro f g hf hg
    simpa [jordan, central] using E.jordan_mem hf hg
  algebraMap_mem' := by
    intro r
    change central ((algebraMap ℝ C(T, ℝ)) r) ∈ E.carrier
    convert E.constants ![r,0,0,0] using 1
    ext j t
    fin_cases j <;> simp [central, Algebra.algebraMap_eq_smul_one]

/-- Membership is precisely membership of all four coordinates in the actual scalar algebra. -/
theorem original_four_components (E : Original T) (a : Sections T) :
    a ∈ E.carrier ↔ ∀ i, a i ∈ scalarAlgebra E := by
  constructor
  · intro ha i
    exact coordinate_mem E ha i
  · intro ha
    have hm (i : Fin 4) := E.jordan_mem (ha i) (axis_mem E i)
    have hs := E.carrier.add_mem (E.carrier.add_mem
      (E.carrier.add_mem (hm 0) (hm 1)) (hm 2)) (hm 3)
    convert hs using 1
    ext i t
    fin_cases i <;> simp [jordan, central, axis, Matrix.vecHead, Matrix.vecTail]

/-- The Euclidean square of the vector part; this is not the source norm. -/
def rho {R : Type*} [CommRing R] (a : Fin 4 → R) :=
  a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2

/-- Dot product of the vector coordinates. -/
def vdot {R : Type*} [CommRing R] (a b : Fin 4 → R) :=
  a 1*b 1+a 2*b 2+a 3*b 3

/-- The positive definite auxiliary square used only in the moment argument. -/
def energy {R : Type*} [CommRing R] (a : Fin 4 → R) := a 0 ^ 2 + rho a

/-- The squared area of the two vector parts. -/
def area {R : Type*} [CommRing R] (a b : Fin 4 → R) :=
  rho a * rho b - vdot a b ^ 2

/-- Exactly the source supremum norm, with Euclidean vector length. -/
def sourceNorm (a : Sections T) : ℝ :=
  sSup (Set.range (fun t => |a 0 t| + Real.sqrt (rho (fun i => a i t))))

/-- Exactly the specified pointwise positive cone. -/
def sourcePositive (a : Sections T) : Prop :=
  ∀ t, Real.sqrt (rho (fun i => a i t)) ≤ a 0 t

namespace Original

abbrev Elem (E : Original T) := E.carrier

/-- Jordan multiplication stays in the same original carrier. -/
def product (E : Original T) (a b : E.Elem) : E.Elem :=
  ⟨jordan a.val b.val, E.jordan_mem a.property b.property⟩

/-- The original H operator, not a point-evaluation quotient. -/
def H (E : Original T) (a b : E.Elem) : E.Elem :=
  E.product a (E.product a b) - E.product (E.product a a) b

/-- The original U operator. -/
def U (E : Original T) (a b : E.Elem) : E.Elem :=
  (2 : ℝ) • E.product a (E.product a b) - E.product (E.product a a) b

end Original

/-- The same total skew relation, assuming only raw PY and NN. -/
structure Raw (E : Original T) where
  D : E.Elem → E.Elem → E.Elem
  skew : ∀ a b, D a b = -D b a
  py : ∀ a b, E.product (D a b) (D a b) =
    (1/2 : ℝ) • (E.U a (E.product b b) + E.U b (E.product a a)) -
      E.product (E.product a b) (E.product a b)
  nn : ∀ a b, D a (D a b) = E.H a b

private theorem h_energy (a b : Fin 4 → ℝ) :
    energy (hOp a b) = rho a * area a b := by
  simp [hOp, jordan, energy, area, rho, vdot]
  ring

private theorem moment_normality (a b p : Fin 4 → ℝ)
    (hp : energy p = area a b)
    (hn : energy (hOp a b) = area a p) :
    p 0 = 0 ∧ vdot a p = 0 := by
  have hr : 0 ≤ rho a := by unfold rho; positivity
  have hm : rho a * (p 0)^2 + (vdot a p)^2 = 0 := by
    rw [h_energy] at hn
    calc
      rho a * (p 0)^2 + (vdot a p)^2 = rho a * energy p - area a p := by
        dsimp [energy, area]
        ring
      _ = 0 := by rw [hp, ← hn]; ring
  have hd : vdot a p = 0 := by
    have := mul_nonneg hr (sq_nonneg (p 0))
    nlinarith [sq_nonneg (vdot a p)]
  refine ⟨?_, hd⟩
  by_cases hz : rho a = 0
  · have h1 : a 1 = 0 := by dsimp [rho] at hz; nlinarith [sq_nonneg (a 2), sq_nonneg (a 3)]
    have h2 : a 2 = 0 := by dsimp [rho] at hz; nlinarith [sq_nonneg (a 1), sq_nonneg (a 3)]
    have h3 : a 3 = 0 := by dsimp [rho] at hz; nlinarith [sq_nonneg (a 1), sq_nonneg (a 2)]
    simp [energy, area, rho, vdot, h1, h2, h3] at hp
    nlinarith [sq_nonneg (p 1), sq_nonneg (p 2), sq_nonneg (p 3)]
  · have he : rho a * (p 0)^2 = 0 := by simpa [hd] using hm
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp he).resolve_left hz)

private theorem raw_energy {E : Original T} (R : Raw E) (a b : E.Elem) (t : T) :
    energy (fun i => (R.D a b).val i t) =
      area (fun i => a.val i t) (fun i => b.val i t) := by
  have hp := congrArg (fun z : E.Elem => z.val 0 t) (R.py a b)
  convert hp using 1 <;>
    simp [Original.product, Original.U, jordan, energy, rho, area, vdot] <;> ring

/-- Raw PY and NN force scalar-zero outputs and both dot orthogonalities on original sections. -/
theorem raw_output_normal {E : Original T} (R : Raw E) (a b : E.Elem) (t : T) :
    (R.D a b).val 0 t = 0 ∧
    vdot (fun i => a.val i t) (fun i => (R.D a b).val i t) = 0 ∧
    vdot (fun i => b.val i t) (fun i => (R.D a b).val i t) = 0 := by
  have normal (a b : E.Elem) := moment_normality
    (fun i => a.val i t) (fun i => b.val i t) (fun i => (R.D a b).val i t)
    (raw_energy R a b t) (by
      have hn := raw_energy R a (R.D a b) t
      rw [R.nn] at hn
      simpa [Original.H, Original.product, hOp, jordan, energy, rho] using hn)
  refine ⟨(normal a b).1, (normal a b).2, ?_⟩
  have hs := congrArg (fun z : E.Elem => z.val) (R.skew a b)
  have hn := (normal b a).2
  have hv : vdot (fun i => b.val i t) (fun i => (R.D a b).val i t) =
      -vdot (fun i => b.val i t) (fun i => (R.D b a).val i t) := by
    rw [hs]
    simp [vdot]
    ring
  rw [hv, hn, neg_zero]

private theorem h_formula {R : Type*} [CommRing R] (a b : Fin 4 → R) :
    hOp a b = ![0, a 1 * vdot a b - rho a * b 1,
      a 2 * vdot a b - rho a * b 2, a 3 * vdot a b - rho a * b 3] := by
  ext i
  fin_cases i <;> simp [hOp, jordan, rho, vdot] <;> ring

private theorem energy_zero (p : Fin 4 → ℝ) (hp : energy p = 0) : p = 0 := by
  dsimp [energy, rho] at hp
  ext i
  fin_cases i <;> simp only [Pi.zero_apply] <;>
    nlinarith [sq_nonneg (p 0), sq_nonneg (p 1), sq_nonneg (p 2), sq_nonneg (p 3)]

private theorem area_zero_of_rho (a b : Fin 4 → ℝ) (h : rho a = 0) :
    area a b = 0 := by
  have h1 : a 1 = 0 := by dsimp [rho] at h; nlinarith [sq_nonneg (a 2), sq_nonneg (a 3)]
  have h2 : a 2 = 0 := by dsimp [rho] at h; nlinarith [sq_nonneg (a 1), sq_nonneg (a 3)]
  have h3 : a 3 = 0 := by dsimp [rho] at h; nlinarith [sq_nonneg (a 1), sq_nonneg (a 2)]
  simp [area, rho, vdot, h1, h2, h3]

private theorem normal_h_injective (a p q : Fin 4 → ℝ)
    (hp0 : p 0 = 0) (hq0 : q 0 = 0)
    (hp : vdot a p = 0) (hq : vdot a q = 0)
    (hz : rho a = 0 → p = q) (he : hOp a p = hOp a q) : p = q := by
  by_cases hr : rho a = 0
  · exact hz hr
  ext i
  have hi := congrFun he i
  rw [h_formula, h_formula] at hi
  fin_cases i
  · exact hp0.trans hq0.symm
  all_goals
    simp [hp, hq] at hi
    exact (mul_left_cancel₀ hr hi)

private theorem h_commute {E : Original T} (R : Raw E) (a b : E.Elem) :
    E.H a (R.D a b) = R.D a (E.H a b) := by
  rw [← R.nn a b, ← R.nn a (R.D a b)]

/-- Equal values of the original H row force equal values of the same original D row. -/
theorem raw_h_fibre {E : Original T} (R : Raw E) (a b c : E.Elem)
    (h : E.H a b = E.H a c) : R.D a b = R.D a c := by
  apply Subtype.ext
  ext i t
  have hp := raw_output_normal R a b t
  have hq := raw_output_normal R a c t
  have he : E.H a (R.D a b) = E.H a (R.D a c) := by
    rw [h_commute, h_commute, h]
  have hev : hOp (fun j => a.val j t) (fun j => (R.D a b).val j t) =
      hOp (fun j => a.val j t) (fun j => (R.D a c).val j t) := by
    ext j
    have hj := congrArg (fun z : E.Elem => z.val j t) he
    fin_cases j <;> simpa [Original.H, Original.product, hOp, jordan] using hj
  have hh := normal_h_injective (fun j => a.val j t)
    (fun j => (R.D a b).val j t) (fun j => (R.D a c).val j t)
    hp.1 hq.1 hp.2.1 hq.2.1 (by
      intro hz
      have hb := energy_zero _ ((raw_energy R a b t).trans (area_zero_of_rho _ _ hz))
      have hc := energy_zero _ ((raw_energy R a c t).trans (area_zero_of_rho _ _ hz))
      exact hb.trans hc.symm) hev
  exact congrFun hh i

private theorem shear_right {E : Original T} (R : Raw E) (a b : E.Elem) (r : ℝ) :
    R.D a (b + r • a) = R.D a b := by
  apply raw_h_fibre
  apply Subtype.ext
  ext i t
  fin_cases i <;> simp [Original.H, Original.product, jordan] <;> ring

private theorem shear_left {E : Original T} (R : Raw E) (a b : E.Elem) (r : ℝ) :
    R.D (a + r • b) b = R.D a b := by
  rw [R.skew, shear_right, ← R.skew]

private theorem diagonal_invariance {E : Original T} (R : Raw E)
    (a b : E.Elem) (r : ℝ) (hr : r ≠ 0) :
    R.D (r • a) (r⁻¹ • b) = R.D a b := by
  have h1 := shear_left R a b (-1)
  have h2 := shear_right R (a + (-1 : ℝ) • b) b 1
  have h3 := shear_left R (a + (-1 : ℝ) • b)
    (b + (1 : ℝ) • (a + (-1 : ℝ) • b)) (-1)
  have he1 : b + (1 : ℝ) • (a + (-1 : ℝ) • b) = a := by module
  rw [he1] at h3 h2
  have he2 : a + (-1 : ℝ) • b + (-1 : ℝ) • a = -b := by module
  rw [he2] at h3
  have h4 := shear_left R (-b) a r
  have h5 := shear_right R (-b + r • a) a (-r⁻¹)
  have he3 : a + -r⁻¹ • (-b + r • a) = r⁻¹ • b := by
    simp only [smul_add, smul_neg, smul_smul, neg_mul, inv_mul_cancel₀ hr, neg_one_smul]
    module
  rw [he3] at h5
  have h6 := shear_left R (-b + r • a) (r⁻¹ • b) r
  have he4 : -b + r • a + r • (r⁻¹ • b) = r • a := by
    rw [smul_smul, mul_inv_cancel₀ hr, one_smul]
    abel
  rw [he4] at h6
  exact h6.trans (h5.trans (h4.trans (h3.trans (h2.trans h1))))

private theorem zero_right {E : Original T} (R : Raw E) (a : E.Elem) : R.D a 0 = 0 := by
  apply Subtype.ext
  ext i t
  have h := raw_energy R a 0 t
  simp [area, rho, vdot] at h
  exact congrFun (energy_zero _ h) i

private theorem transfer {E : Original T} (R : Raw E)
    (a b : E.Elem) (r : ℝ) : R.D (r • a) b = R.D a (r • b) := by
  by_cases hr : r = 0
  · subst r
    simp only [zero_smul]
    rw [R.skew, zero_right, neg_zero, zero_right]
  · have h := diagonal_invariance R a (r • b) r hr
    simpa only [smul_smul, inv_mul_cancel₀ hr, one_smul] using h

/-- Real homogeneity of each original row follows from raw PY and NN. -/
theorem raw_real_homogeneity {E : Original T} (R : Raw E)
    (a b : E.Elem) (r : ℝ) :
    R.D a (r • b) = r • R.D a b ∧ R.D (r • a) b = r • R.D a b := by
  have right (a b : E.Elem) (r : ℝ) : R.D a (r • b) = r • R.D a b := by
    by_cases hr : r = 0
    · subst r; simp only [zero_smul]; exact zero_right R a
    have hd : R.D a (r • R.D a b) = r • E.H a b := by
      rw [← transfer]
      have he := diagonal_invariance R a b r hr
      rw [← he, R.nn]
      apply Subtype.ext
      ext i t
      fin_cases i <;> simp [Original.H, Original.product, jordan] <;>
        field_simp [hr] <;> ring
    have he : E.H a (R.D a (r • b)) = E.H a (r • R.D a b) := by
      rw [h_commute]
      have hh : E.H a (r • b) = r • E.H a b := by
        apply Subtype.ext
        ext i t
        fin_cases i <;> simp [Original.H, Original.product, jordan] <;> ring
      rw [hh, ← hd, R.nn]
    apply Subtype.ext
    ext i t
    have hp := raw_output_normal R a (r • b) t
    have hq := raw_output_normal R a b t
    have hv : hOp (fun j => a.val j t) (fun j => (R.D a (r • b)).val j t) =
        hOp (fun j => a.val j t) (fun j => (r • R.D a b).val j t) := by
      ext j
      have hj := congrArg (fun z : E.Elem => z.val j t) he
      fin_cases j <;> simpa [Original.H, Original.product, hOp, jordan] using hj
    have hn := normal_h_injective (fun j => a.val j t)
      (fun j => (R.D a (r • b)).val j t) (fun j => (r • R.D a b).val j t)
      hp.1 (by simp [hq.1]) hp.2.1 (by
        have hdq := hq.2.1
        dsimp [vdot] at hdq ⊢
        simp only [SetLike.val_smul, Pi.smul_apply, ContinuousMap.smul_apply, smul_eq_mul]
        nlinarith [hdq])
      (by
        intro hz
        have hb := energy_zero _ ((raw_energy R a (r • b) t).trans
          (area_zero_of_rho _ _ hz))
        have hc := energy_zero _ ((raw_energy R a b t).trans (area_zero_of_rho _ _ hz))
        ext j
        have hcj := congrFun hc j
        simpa [hcj] using congrFun hb j) hv
    exact congrFun hn i
  exact ⟨right a b r, (transfer R a b r).trans (right a b r)⟩

end D5.S3.Quantum.Algebra.UnitBridgeRawGeometry
