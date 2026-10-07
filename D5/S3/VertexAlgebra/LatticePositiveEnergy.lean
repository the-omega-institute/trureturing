/- GID: D5/S3/VertexAlgebra/LatticePositiveEnergy
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticePositiveEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual integral charge energy and finite oscillator sublevels. -/

/-
Actual integral charge energy and finite oscillator sublevels.
The half-norm identities are consumed from the realized integral cocycle.
The oscillator encoding adapts the finite-support argument in
PolynomialFockLZeroSpectrum and the source-advisory oscillator probe.
Mathlib material retains its Apache 2.0 license and original authorship.
Primary construction: Bakalov--Kac math/0402315v1 §4.1 (4.3)--(4.5).
Degree convention: Borcherds, PNAS 83 (1986), 3068--3071, author
retypesetting SHA822e39a2ec7bd33ad81193b06b7a66ae89abcec43c4cb7974d4bc513c3fce5b5,
§2 p.2. No assertion about Monster realization is made.
-/
import D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
import D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

set_option autoImplicit false
namespace D5.S3.VertexAlgebra.LatticePositiveEnergy
open LatticeGeneratingFieldLocality Matrix
open scoped BigOperators
noncomputable section

abbrev Exponent (D : LatticeData) := Index D →₀ ℕ
abbrev Label (D : LatticeData) := Charge D × Exponent D

def chargeEnergy (D : LatticeData) (a : Charge D) : ℤ := bilinear D a a / 2

theorem chargeEnergy_cocycle (D : LatticeData) (a : Charge D) :
    chargeEnergy D a = lowerCocycleExponent D a a :=
  (LatticeTwistedGroundRealization.SignQuotient.integral_cocycle_square D a).symm

theorem two_chargeEnergy (D : LatticeData) (a : Charge D) :
    2 * chargeEnergy D a = bilinear D a a := by
  rw [chargeEnergy_cocycle]
  have h := LatticeTwistedGroundRealization.SignQuotient.integral_cocycle_symmetrization D a a
  omega

@[simp] theorem chargeEnergy_zero (D : LatticeData) : chargeEnergy D 0 = 0 := by
  simp [chargeEnergy, bilinear]

theorem chargeEnergy_nonneg (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a : Charge D) :
    0 ≤ chargeEnergy D a := by
  by_cases ha : a = 0
  · simp [ha]
  · have hp := LatticeFiniteNegativeGeneration.norm_positive D hD a ha
    have he := two_chargeEnergy D a
    omega

theorem chargeEnergy_eq_zero_iff (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a : Charge D) :
    chargeEnergy D a = 0 ↔ a = 0 := by
  constructor
  · intro h
    by_contra ha
    have hp := LatticeFiniteNegativeGeneration.norm_positive D hD a ha
    have he := two_chargeEnergy D a
    omega
  · rintro rfl
    simp

def oscillatorEnergy {D : LatticeData} (d : Exponent D) : ℕ :=
  Finsupp.weight (fun x : Index D => x.2 + 1) d

def energy (D : LatticeData) (a : Label D) : ℤ :=
  chargeEnergy D a.1 + (oscillatorEnergy a.2 : ℤ)

theorem oscillatorLeFinite (D : LatticeData) (N : ℕ) :
    Finite {d : Exponent D // oscillatorEnergy d ≤ N} := by
  classical
  let A := {d : Exponent D // oscillatorEnergy d ≤ N}
  have hindex (d : A) (i : Fin D.rank) (k : ℕ) (hk : N ≤ k) : d.1 (i,k) = 0 := by
    by_contra hne
    have h := Finsupp.le_weight_of_ne_zero' (fun x : Index D => x.2 + 1) hne
    change k + 1 ≤ oscillatorEnergy d.1 at h
    have hd := d.2
    omega
  have hexponent (d : A) (x : Index D) : d.1 x ≤ N := by
    have h := Finsupp.le_weight (fun y : Index D => y.2 + 1) (s := x)
      (by omega) d.1
    exact h.trans d.2
  let encode (d : A) (x : Fin D.rank × Fin N) : Fin (N + 1) :=
    ⟨d.1 (x.1, x.2), Nat.lt_succ_of_le (hexponent d _)⟩
  have hinj : Function.Injective encode := by
    intro d e h
    apply Subtype.ext
    apply Finsupp.ext
    rintro ⟨i,k⟩
    by_cases hk : k < N
    · exact congrArg Fin.val (congrFun h (i, ⟨k,hk⟩))
    · rw [hindex d i k (Nat.le_of_not_lt hk), hindex e i k (Nat.le_of_not_lt hk)]
  exact Finite.of_injective encode hinj

@[simp] theorem oscillatorEnergy_eq_zero_iff (D : LatticeData) (d : Exponent D) :
    oscillatorEnergy d = 0 ↔ d = 0 := by
  constructor
  · intro hd
    ext x
    have h := Finsupp.le_weight (fun y : Index D => y.2 + 1) (s := x) (by omega) d
    change d x ≤ oscillatorEnergy d at h
    rw [hd] at h
    simpa using Nat.eq_zero_of_le_zero h
  · rintro rfl
    simp [oscillatorEnergy]

theorem energy_eq_zero_iff (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a : Label D) :
    energy D a = 0 ↔ a = (0,0) := by
  constructor
  · intro he
    have hq := chargeEnergy_nonneg D hD a.1
    have h : chargeEnergy D a.1 = 0 ∧ oscillatorEnergy a.2 = 0 := by
      dsimp [energy] at he
      omega
    exact Prod.ext ((chargeEnergy_eq_zero_iff D hD _).mp h.1)
      ((oscillatorEnergy_eq_zero_iff D _).mp h.2)
  · rintro rfl
    simp [energy, oscillatorEnergy]

#print axioms two_chargeEnergy
#print axioms chargeEnergy_nonneg
#print axioms oscillatorLeFinite
#print axioms energy_eq_zero_iff
end
end D5.S3.VertexAlgebra.LatticePositiveEnergy
