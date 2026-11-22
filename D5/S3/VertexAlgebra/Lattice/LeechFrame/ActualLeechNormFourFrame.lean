/- GID: D5/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechNormFourFrame
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LeechFrame/ActualLeechNormFourFrame
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Explicit integral charges and a complex norm-four basis of the actual Leech lattice. -/

import D5.S3.VertexAlgebra.Lattice.ActualLeechHyperbolic
import D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates

/-! # The actual Leech norm-four frame

The 24 directions are indexed by a consecutive coordinate pair and the sign on its
second coordinate. In the integral Golay realization the two entries are 4 and ±4.
Their parity and half-coordinate residue word are zero and their coordinate sum is
zero or eight. The real form is the dot product divided by eight.

The charges use the inverse of `ActualLeechHyperbolic.leechCoordinates`, the integral
equivalence chosen with `leechData` from
`RealLeech.exists_positive_even_unimodular_gram`. The proof uses the rank and pairing
identity from `leech_spec`. The complex basis uses the images of those same charges
under `chargeVector` and the complex bilinear Gram form `g`.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace D5.S3.VertexAlgebra.ActualLeechNormFourFrame

open D5.S3.Arith.Lattices.Golay
open GolayEncoder (code)
open IntegerLeech (Admissible IntVector red)
open DirectLeechDuality (spike)
open LatticeGeneratingFieldLocality (Charge bilinear)
open ActualLeechHyperbolic (leechData leechCoordinates leech_spec)
open LatticeLightConeCoordinates (E g chargeVector)

abbrev Index := Fin 12 × Bool

private def evenCoord (i : Fin 12) : Fin 24 := ⟨2 * i.val, by omega⟩

private def oddCoord (i : Fin 12) : Fin 24 := ⟨2 * i.val + 1, by omega⟩

private theorem evenCoord_injective : Function.Injective evenCoord := by
  intro i j h
  have hval := congrArg Fin.val h
  apply Fin.ext
  change 2 * i.val = 2 * j.val at hval
  omega

private theorem oddCoord_injective : Function.Injective oddCoord := by
  intro i j h
  have hval := congrArg Fin.val h
  apply Fin.ext
  change 2 * i.val + 1 = 2 * j.val + 1 at hval
  omega

private theorem evenCoord_ne_oddCoord (i j : Fin 12) : evenCoord i ≠ oddCoord j := by
  intro h
  have hval := congrArg Fin.val h
  change 2 * i.val = 2 * j.val + 1 at hval
  omega

/-- On each consecutive coordinate pair, take the plus sign for `true`. -/
def integralVector (p : Index) : IntVector :=
  spike (evenCoord p.1) 4 + spike (oddCoord p.1) (if p.2 then 4 else -4)

private theorem integralVector_values (p : Index) (k : Fin 24) :
    integralVector p k = 0 ∨ integralVector p k = 4 ∨ integralVector p k = -4 := by
  by_cases he : k = evenCoord p.1
  · subst k
    simp [integralVector, spike, evenCoord_ne_oddCoord]
  · by_cases ho : k = oddCoord p.1
    · rw [ho] at he ⊢
      by_cases hs : p.2 = true <;> simp [integralVector, spike, he, hs]
    · simp [integralVector, spike, he, ho]

/-- Parity zero, with zero Golay residue word and coordinate sum zero or eight. -/
theorem admissible (p : Index) : Admissible code (integralVector p) := by
  refine ⟨0, Or.inl rfl, ?_, ?_, ?_⟩
  · intro k
    rcases integralVector_values p k with h | h | h <;> rw [h] <;> decide
  · have hzero : red (fun k => (integralVector p k - 0) / 2) = 0 := by
      funext k
      change (((integralVector p k - 0) / 2 : ℤ) : ZMod 2) = 0
      rcases integralVector_values p k with h | h | h <;> rw [h] <;> decide
    rw [hzero]
    exact code.zero_mem
  · have hsum : (∑ k, integralVector p k) = 4 + (if p.2 then 4 else -4) := by
      simp [integralVector, Pi.add_apply, Finset.sum_add_distrib, spike]
    rw [hsum]
    cases p.2 <;> decide

/-- The unscaled real coordinates of the integral frame. -/
def realVector (p : Index) : RealLeech.Space := RealLeech.castLinear (integralVector p)

private theorem realVector_mem (p : Index) : realVector p ∈ RealLeech.lattice :=
  (RealLeech.mem_lattice _).mpr ⟨integralVector p, admissible p, rfl⟩

/-- A charge of the actual Leech data, pulled back along the Golay coordinate equivalence. -/
def charge (p : Index) : Charge leechData :=
  leechCoordinates.symm ⟨realVector p, realVector_mem p⟩

@[simp] theorem coordinates_charge (p : Index) :
    (leechCoordinates (charge p) : RealLeech.Space) = realVector p := by
  simp [charge]

private theorem dot_integralVector (p q : Index) :
    (∑ k, integralVector p k * integralVector q k) = if p = q then 32 else 0 := by
  have hd : (∑ k, integralVector p k * integralVector q k) =
      integralVector p (evenCoord q.1) * 4 +
        integralVector p (oddCoord q.1) * (if q.2 then 4 else -4) := by
    change (∑ k, integralVector p k *
      (spike (evenCoord q.1) 4 k + spike (oddCoord q.1) (if q.2 then 4 else -4) k)) = _
    simp [spike, mul_add, Finset.sum_add_distrib, mul_ite]
  rw [hd]
  obtain ⟨i, s⟩ := p
  obtain ⟨j, t⟩ := q
  by_cases h : i = j
  · subst j
    cases s <;> cases t <;>
      norm_num [integralVector, spike, evenCoord_ne_oddCoord, (evenCoord_ne_oddCoord i i).symm]
  · have he : evenCoord j ≠ evenCoord i := fun e => h (evenCoord_injective e).symm
    have ho : oddCoord j ≠ oddCoord i := fun e => h (oddCoord_injective e).symm
    simp [integralVector, spike, he, ho, evenCoord_ne_oddCoord,
      (evenCoord_ne_oddCoord i j).symm, h]

private theorem real_pairing (p q : Index) :
    RealLeech.pairing (realVector p) (realVector q) = if p = q then 4 else 0 := by
  change (1 / 8 : ℝ) * (∑ k, (integralVector p k : ℝ) * (integralVector q k : ℝ)) = _
  simp only [← Int.cast_mul, ← Int.cast_sum]
  rw [dot_integralVector]
  split <;> norm_num

/-- The Gram matrix of the 24 actual charges is four times the identity. -/
theorem charge_pairing (p q : Index) :
    bilinear leechData (charge p) (charge q) = if p = q then 4 else 0 := by
  have h := leech_spec.2.2.2 (charge p) (charge q)
  rw [coordinates_charge, coordinates_charge, real_pairing] at h
  by_cases hpq : p = q
  · rw [ite_eq_left hpq] at h ⊢
    exact_mod_cast h
  · rw [ite_eq_right hpq] at h ⊢
    exact_mod_cast h

@[simp] theorem charge_norm (p : Index) : bilinear leechData (charge p) (charge p) = 4 := by
  rw [charge_pairing, ite_eq_left rfl]

theorem charge_orthogonal {p q : Index} (h : p ≠ q) :
    bilinear leechData (charge p) (charge q) = 0 := by
  rw [charge_pairing, ite_eq_right h]

/-- The same charges in the complex space of the lattice VOA currents. -/
def complexVector (p : Index) : E leechData := chargeVector (charge p)

theorem complex_pairing (p q : Index) :
    g leechData (complexVector p) (complexVector q) = if p = q then 4 else 0 := by
  have hcast : g leechData (complexVector p) (complexVector q) =
      (bilinear leechData (charge p) (charge q) : ℂ) := by
    simp only [g, complexVector, chargeVector, bilinear, Int.cast_sum, Int.cast_mul]
  rw [hcast, charge_pairing]
  split <;> simp

private def complexForm : LinearMap.BilinForm ℂ (E leechData) where
  toFun := LatticeLightConeCoordinates.pairing leechData
  map_add' x y := LinearMap.ext fun z => LatticeLightConeCoordinates.g_add_left leechData x y z
  map_smul' c x := LinearMap.ext fun z => LatticeLightConeCoordinates.g_smul_left leechData x z c

private theorem complex_independent : LinearIndependent ℂ complexVector :=
  LinearMap.BilinForm.linearIndependent_of_iIsOrtho (B := complexForm)
    (fun p q h => by
      change g leechData (complexVector p) (complexVector q) = 0
      rw [complex_pairing, ite_eq_right h])
    (fun p => by
      change g leechData (complexVector p) (complexVector p) ≠ 0
      rw [complex_pairing, ite_eq_left rfl]
      norm_num)

/-- A basis of the complexified charge space used for the lattice VOA currents. -/
def complexBasis : Module.Basis Index ℂ (E leechData) :=
  basisOfLinearIndependentOfCardEqFinrank complex_independent
    (by simp [E, leech_spec.1])

@[simp] theorem complexBasis_apply (p : Index) : complexBasis p = complexVector p :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) p

end D5.S3.VertexAlgebra.ActualLeechNormFourFrame
