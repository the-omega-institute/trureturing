/- GID: D5/S3/Quantum/Routing/HannSignedCertificate
   generality: G
   mirror-B: D5/B/S3/Quantum/Routing/HannSignedCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prescribed signed coefficient recursion on actual loaded router records. -/

import D5.S3.Quantum.Routing.HannRouterProfiles
import Mathlib.RingTheory.RootsOfUnity.Complex

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate

namespace D5.S3.Quantum.Routing.HannSignedCertificate

open HannSpatialQram
open HannRouterProfiles (Router routerLabel loadedLabel)
open ReversibleQram (Address)

/-- The prescribed positive-angle third root of unity. -/
def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

private theorem omega_primitive : IsPrimitiveRoot omega 3 :=
  Complex.isPrimitiveRoot_exp 3 (by norm_num)

private theorem omega_cube : omega ^ 3 = 1 := omega_primitive.pow_eq_one

private theorem omega_sum : 1 + omega + omega ^ 2 = 0 := by
  have h := omega_primitive.geom_sum_eq_zero (by norm_num : 1 < 3)
  simpa [Finset.sum_range_succ, add_assoc] using h

private theorem omega_inv : omega⁻¹ = omega ^ 2 := by
  apply inv_eq_of_mul_eq_one_right
  nlinarith only [omega_cube]

/-- The label exponents are wait=0, zero=1, one=2. -/
def labelIndex : Qutrit → ℤ
  | .wait => 0
  | .zero => 1
  | .one => 2

/-- The three specified Fourier coordinates, with nonnegative real square roots. -/
def localRecord (q : ℝ) (s : Qutrit) (e : Fin 3) : ℂ :=
  if e = 0 then (Real.sqrt ((1 + 2 * q) / 3) : ℂ)
  else (Real.sqrt ((1 - q) / 3) : ℂ) *
    omega ^ (if e = 1 then labelIndex s else -labelIndex s)

private theorem local_upper (s : Qutrit) (e : Fin 3) :
    localRecord 1 s e = localRecord 1 Qutrit.wait e := by
  simp [localRecord]

private theorem local_lower (e : Fin 3) :
    localRecord (-(1 / 2 : ℝ)) Qutrit.wait e =
      -localRecord (-(1 / 2 : ℝ)) Qutrit.zero e -
        localRecord (-(1 / 2 : ℝ)) Qutrit.one e := by
  fin_cases e <;>
    simp [localRecord, labelIndex, zpow_neg, omega_inv, pow_succ] <;>
    nlinarith only [omega_sum, omega_cube]

abbrev Environment (n : ℕ) := Router n → Fin 3
abbrev Coeff (n : ℕ) := Address n → ℂ

/-- One assignment is restricted along the actual child coordinates. -/
def restrict (n : ℕ) (q : Router (n + 1) → ℝ) (b : Bool) : Router n → ℝ :=
  fun v => q (some (b, v))

def childEnvironment (n : ℕ) (e : Environment (n + 1)) (b : Bool) : Environment n :=
  fun v => e (some (b, v))

/-- The local products observe literal router fields. -/
def treeRecord (n : ℕ) (q : Router n → ℝ) (t : Tree n) (e : Environment n) : ℂ :=
  ∏ v, localRecord (q v) (routerLabel n t v) (e v)

/-- Actual loaded records retain an arbitrary external bus. -/
def record (n : ℕ) (q : Router n → ℝ) (bus : Qutrit)
    (a : Address n) (e : Environment n) : ℂ :=
  ∏ v, localRecord (q v) (loadedLabel n a bus v) (e v)

def vacuumRecord (n : ℕ) (q : Router n → ℝ) (e : Environment n) : ℂ :=
  ∏ v, localRecord (q v) Qutrit.wait (e v)

/-- Complex coefficient synthesis, with the exact address order. -/
def synthesis (n : ℕ) (q : Router n → ℝ) (bus : Qutrit) :
    Coeff n →ₗ[ℂ] (Environment n → ℂ) where
  toFun x e := ∑ a, x a * record n q bus a e
  map_add' x y := by ext e; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by ext e; simp [Finset.mul_sum, mul_assoc]

/-- Zero extension along the selected first address bit. -/
def embed (n : ℕ) (b : Bool) (x : Coeff n) : Coeff (n + 1) :=
  fun a => if a.1 = b then x a.2 else 0

private theorem product_split (n : ℕ) (f : Router (n + 1) → ℂ) :
    (∏ v, f v) = f none * (∏ v : Router n, f (some (false, v))) *
      (∏ v : Router n, f (some (true, v))) := by
  rw [Fintype.prod_option, Fintype.prod_prod_type, Fintype.prod_bool]
  ring

private theorem record_split (n : ℕ) (q : Router (n + 1) → ℝ)
    (bus : Qutrit) (a : Address (n + 1)) (e : Environment (n + 1)) :
    record (n + 1) q bus a e =
      localRecord (q none) (encode a.1) (e none) *
        (if a.1 then vacuumRecord n (restrict n q false) (childEnvironment n e false)
         else record n (restrict n q false) bus a.2 (childEnvironment n e false)) *
        (if a.1 then record n (restrict n q true) bus a.2 (childEnvironment n e true)
         else vacuumRecord n (restrict n q true) (childEnvironment n e true)) := by
  simp only [record, HannRouterProfiles.loaded_label]
  rw [product_split]
  cases a with
  | mk b a =>
    cases b <;>
      simp [routerLabel, programmed, vacuumRecord, restrict, childEnvironment,
        HannRouterProfiles.vacuum_label]

private theorem vacuum_split (n : ℕ) (q : Router (n + 1) → ℝ)
    (e : Environment (n + 1)) :
    vacuumRecord (n + 1) q e = localRecord (q none) Qutrit.wait (e none) *
      vacuumRecord n (restrict n q false) (childEnvironment n e false) *
      vacuumRecord n (restrict n q true) (childEnvironment n e true) :=
  product_split n _

private theorem synthesis_embed (n : ℕ) (q : Router (n + 1) → ℝ) (bus : Qutrit)
    (b : Bool) (x : Coeff n) (e : Environment (n + 1)) :
    synthesis (n + 1) q bus (embed n b x) e =
      if b then localRecord (q none) Qutrit.one (e none) *
        vacuumRecord n (restrict n q false) (childEnvironment n e false) *
        synthesis n (restrict n q true) bus x (childEnvironment n e true)
      else localRecord (q none) Qutrit.zero (e none) *
        synthesis n (restrict n q false) bus x (childEnvironment n e false) *
        vacuumRecord n (restrict n q true) (childEnvironment n e true) := by
  change (∑ a, embed n b x a * record (n + 1) q bus a e) = _
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  cases b <;>
    simp [embed, record_split, encode, synthesis, Finset.mul_sum, Finset.sum_mul,
      mul_assoc, mul_left_comm, mul_comm]

end D5.S3.Quantum.Routing.HannSignedCertificate
