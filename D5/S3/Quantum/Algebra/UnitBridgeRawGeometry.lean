/- GID: D5/S3/Quantum/Algebra/UnitBridgeRawGeometry
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/UnitBridgeRawGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.ContinuousMap.Algebra, mathlib/module/Mathlib.LinearAlgebra.CrossProduct]
   digest: Original continuous spin sections and the two raw moment identities. -/

import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic

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
  2 • jordan a (jordan a b) - jordan (jordan a a) b

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
  simp [axis]

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
    fin_cases j <;> simp [p, jordan, axis, central] <;> ring
  fin_cases i
  · exact hc
  all_goals
    have hm := E.jordan_mem
      (E.carrier.sub_mem (hp _) hc) (axis_mem E _)
    convert hm using 1 <;> ext j t <;> fin_cases j <;>
      simp [p, jordan, axis, central] <;> ring

/-- The actual coefficient algebra, without inverse or square-root closure. -/
def scalarAlgebra (E : Original T) : Subalgebra ℝ C(T, ℝ) where
  carrier := {f | central f ∈ E.carrier}
  zero_mem' := by simpa [central] using E.carrier.zero_mem
  one_mem' := by simpa [axis, central] using axis_mem E 0
  add_mem' := by
    intro f g hf hg
    simpa [central] using E.carrier.add_mem hf hg
  mul_mem' := by
    intro f g hf hg
    simpa [jordan, central] using E.jordan_mem hf hg
  algebraMap_mem' := by
    intro r
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
    fin_cases i <;> simp [jordan, central, axis]

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
  2 • E.product a (E.product a b) - E.product (E.product a a) b

end Original

/-- The same total skew relation, assuming only raw PY and NN. -/
structure Raw (E : Original T) where
  D : E.Elem → E.Elem → E.Elem
  skew : ∀ a b, D a b = -D b a
  py : ∀ a b, E.product (D a b) (D a b) =
    (1/2 : ℝ) • (E.U a (E.product b b) + E.U b (E.product a a)) -
      E.product (E.product a b) (E.product a b)
  nn : ∀ a b, D a (D a b) = E.H a b

private theorem py_scalar (a b : Fin 4 → ℝ) :
    ((1/2 : ℝ) • (uOp a (jordan b b) + uOp b (jordan a a)) -
      jordan (jordan a b) (jordan a b)) 0 = area a b := by
  simp [uOp, jordan, area, rho, vdot]
  ring

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
    dsimp [area, energy] at hp hn ⊢
    nlinarith [sq_nonneg (p 0), sq_nonneg (vdot a p)]
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
  change _ = _ at hp
  simpa [Original.product, Original.U, uOp, jordan, energy, rho,
    area, vdot] using hp

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
      simpa [Original.H, Original.product, hOp, jordan] using hn)
  refine ⟨(normal a b).1, (normal a b).2, ?_⟩
  have hs := congrArg (fun z : E.Elem => z.val) (R.skew a b)
  have hn := (normal b a).2
  have hv : vdot (fun i => b.val i t) (fun i => (R.D a b).val i t) =
      -vdot (fun i => b.val i t) (fun i => (R.D b a).val i t) := by
    rw [hs]
    simp [vdot]
    ring
  rw [hv, hn, neg_zero]

end D5.S3.Quantum.Algebra.UnitBridgeRawGeometry
