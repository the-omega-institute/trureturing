/- GID: D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeCosetCompression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Block lattice injections and longitudinal compression of complete native fields. -/

import D5.S3.VertexAlgebra.Sectors.LatticeDualCosetModule
import D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta
import Mathlib.Algebra.MvPolynomial.Rename
import Batteries.Tactic.OpenPrivate

/-!
The ambient field is the native Bakalov--Kac lattice field, with its original
half-diagonal cocycle. Its ungraded vertex-algebra construction requires only
an integral symmetric even-diagonal form, not positivity of the ambient form.
The projection is substitution along the rational Gram inverse, not deletion
of the added oscillators. All ranks, including either empty block, are allowed.

These constructions are for the intermediate-projection contraction problem;
they do not assert the product comparison or analytic sewing.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeCosetCompression

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeDiscriminantTheta MvPolynomial
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open scoped BigOperators VertexOperator

noncomputable section

open private rat_unit from D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta
open private bilinear_unit from D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration

variable (D : LatticeData) (e : ℕ)
variable (B : Matrix (Fin D.rank) (Fin e) ℤ) (C : Matrix (Fin e) (Fin e) ℤ)
variable (hC : ∀ i j, C i j = C j i) (hCe : ∀ i, Even (C i i))

/-- Old coordinates precede all external coordinates. No ambient positivity. -/
abbrev ambient : LatticeData where
  rank := D.rank + e
  G i j := Fin.addCases
    (fun k => Fin.addCases (D.G k) (B k) j)
    (fun k => Fin.addCases (fun l => B l k) (C k) j) i
  symmetric i j := by
    induction i using Fin.addCases <;> induction j using Fin.addCases
    all_goals simp [D.symmetric, hC]
  even_diagonal i := by
    induction i using Fin.addCases
    · simpa using D.even_diagonal _
    · simpa using hCe _

variable {e}

def liftCharge (a : Fin e → ℤ) (n : Charge D) :
    Charge (ambient D e B C hC hCe) := Fin.addCases n a

def oldCharge (n : Charge (ambient D e B C hC hCe)) : Charge D :=
  fun i => n (i.castAdd e)

def externalCharge (n : Charge (ambient D e B C hC hCe)) : Fin e → ℤ :=
  fun j => n (j.natAdd D.rank)

def polynomialInjection : Oscillator D →ₐ[ℂ] Oscillator (ambient D e B C hC hCe) :=
  rename (fun x : Index D => (x.1.castAdd e, x.2))

/-- The coefficients HB are rational even when the dual shifts are fractional. -/
def longitudinal : Matrix (Fin D.rank) (Fin e) ℚ :=
  inverseRat D * B.map (Int.castRingHom ℚ)

def projectionVariable (x : Index (ambient D e B C hC hCe)) : Oscillator D :=
  Fin.addCases (fun i => X (i, x.2))
    (fun j => ∑ i : Fin D.rank, (longitudinal D B i j : ℂ) • X (i, x.2)) x.1

def polynomialProjection : Oscillator (ambient D e B C hC hCe) →ₐ[ℂ] Oscillator D :=
  aeval (projectionVariable D B C hC hCe)

def injection (a : Fin e → ℤ) : Carrier D →ₗ[ℂ] Carrier (ambient D e B C hC hCe) :=
  Finsupp.lsum ℂ (fun n =>
    (Finsupp.lsingle (liftCharge D B C hC hCe a n)).comp
      (polynomialInjection D B C hC hCe).toLinearMap)

def projection (a : Fin e → ℤ) : Carrier (ambient D e B C hC hCe) →ₗ[ℂ] Carrier D :=
  Finsupp.lsum ℂ (fun n =>
    if externalCharge D B C hC hCe n = a then
      (Finsupp.lsingle (oldCharge D B C hC hCe n)).comp
        (polynomialProjection D B C hC hCe).toLinearMap
    else 0)

/-- Compression of the complete original field, on all finite-charge inputs. -/
def compressed (a b : Fin e → ℤ) (u : Carrier D) (m : ℤ) :
    Carrier D →ₗ[ℂ] Carrier D :=
  (projection D B C hC hCe (a+b)).comp
    (((Y (ambient D e B C hC hCe) (injection D B C hC hCe a u))[[m]]).comp
      (injection D B C hC hCe b))

/-- The transverse pairing, with the same order of the two external charges. -/
def schur (a b : Fin e → ℤ) : ℚ :=
  ∑ j, ∑ k, (a j : ℚ) *
    ((C j k : ℚ) - ∑ i, (B i j : ℚ) * longitudinal D B i k) * (b k : ℚ)

def correction (a b : Fin e → ℤ) (j : ℕ) : ℂ :=
  (-1 : ℂ)^j * (Ring.choose (schur D B C a b) j : ℚ)

private theorem gram_longitudinal (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (j : Fin e) :
    ∑ k, (D.G i k : ℚ) * longitudinal D B k j = (B i j : ℚ) := by
  have h : gramRat D * longitudinal D B = B.map (Int.castRingHom ℚ) := by
    rw [longitudinal, ← Matrix.mul_assoc, inverseRat,
      Matrix.mul_nonsing_inv _ (rat_unit D hD), Matrix.one_mul]
  simpa [Matrix.mul_apply, gramRat] using congrArg (fun M => M i j) h

private theorem gram_longitudinal_complex (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (j : Fin e) :
    ∑ k, (D.G i k : ℂ) * (longitudinal D B k j : ℂ) = (B i j : ℂ) := by
  exact_mod_cast gram_longitudinal D B hD i j

private theorem projectionVariable_partial (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (r : ℕ) (x : Index (ambient D e B C hC hCe)) :
    weightedPartial D i r (projectionVariable D B C hC hCe x) =
      if r = x.2 then MvPolynomial.C ((ambient D e B C hC hCe).G (i.castAdd e) x.1 : ℂ)
      else 0 := by
  classical
  rcases x with ⟨j,k⟩
  induction j using Fin.addCases with
  | left j =>
    simpa [projectionVariable, ambient, MvPolynomial.smul_eq_C_mul] using LatticeActualAnnihilation.annihilate_X D i j r k
  | right j =>
    simp only [projectionVariable, Fin.addCases_right, map_sum, map_smul,
      LatticeActualAnnihilation.annihilate_X, ambient, Fin.addCases_left]
    by_cases h : r = k
    · simp only [h, ↓reduceIte, smul_smul, MvPolynomial.smul_eq_C_mul,
        mul_one, ← map_mul, ← map_sum]
      congr 1
      simpa only [mul_comm] using gram_longitudinal_complex D B hD i j
    · simp [h]

/-- Compression commutes with every old positive Heisenberg direction on
every ambient polynomial. In particular transverse descendants cannot acquire
an old-current component from an unproved field-isomorphism premise. -/
theorem projection_weightedPartial (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (r : ℕ) (p : Oscillator (ambient D e B C hC hCe)) :
    polynomialProjection D B C hC hCe
        (weightedPartial (ambient D e B C hC hCe) (i.castAdd e) r p) =
      weightedPartial D i r (polynomialProjection D B C hC hCe p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C z => simp [weightedPartial, polynomialProjection]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p x hp =>
    have hx : polynomialProjection D B C hC hCe
        (weightedPartial (ambient D e B C hC hCe) (i.castAdd e) r (X x)) =
        weightedPartial D i r (polynomialProjection D B C hC hCe (X x)) := by
      rw [LatticeActualAnnihilation.annihilate_X, show polynomialProjection D B C hC hCe (X x) =
        projectionVariable D B C hC hCe x by simp [polynomialProjection],
        projectionVariable_partial D B C hC hCe hD]
      split_ifs <;> simp [MvPolynomial.smul_eq_C_mul]
    simp only [LatticeActualAnnihilation.annihilate_mul, map_add, map_mul, hp, hx]

private theorem old_current_pairing (i : Fin D.rank)
    (n : Charge (ambient D e B C hC hCe)) :
    bilinear (ambient D e B C hC hCe) (unitCharge _ (i.castAdd e)) n =
      bilinear D (unitCharge D i) (oldCharge D B C hC hCe n) +
        (Matrix.mulVec B (externalCharge D B C hC hCe n)) i := by
  classical
  rw [bilinear_unit, bilinear_unit]
  change (∑ j : Fin (D.rank+e), _) = _
  rw [Fin.sum_univ_add]
  simp [ambient, oldCharge, externalCharge, Matrix.mulVec, dotProduct]

/-- Every old current, including its shifted zero mode, passes through
longitudinal compression on arbitrary ambient polynomial states. -/
theorem projection_current_polynomial (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (n : Charge (ambient D e B C hC hCe)) (m : ℤ)
    (p : Oscillator (ambient D e B C hC hCe)) :
    polynomialProjection D B C hC hCe
        (neutralPolynomialMode (ambient D e B C hC hCe) (i.castAdd e) n m p) =
      LatticeDualCosetModule.shiftedCurrentPolynomial D
        (Matrix.mulVec B (externalCharge D B C hC hCe n)) 1 i (oldCharge D B C hC hCe n) m
        (polynomialProjection D B C hC hCe p) := by
  by_cases hm : m < 0
  · simp [neutralPolynomialMode, LatticeDualCosetModule.shiftedCurrentPolynomial,
      hm, polynomialProjection, projectionVariable]
  · by_cases hz : m = 0
    · simp [neutralPolynomialMode, LatticeDualCosetModule.shiftedCurrentPolynomial,
        hm, hz, old_current_pairing, map_smul]
    · change polynomialProjection D B C hC hCe
        ((if m < 0 then _ else if m = 0 then _ else
          (m : ℂ) • weightedPartial (ambient D e B C hC hCe) (i.castAdd e)
            (m-1).toNat) p) = _
      simp only [hm, hz, ↓reduceIte, LinearMap.smul_apply, map_smul]
      rw [projection_weightedPartial D B C hC hCe hD]
      simp [LatticeDualCosetModule.shiftedCurrentPolynomial, hm, hz, weightedPartial]

private theorem polynomialProjection_injection (p : Oscillator D) :
    polynomialProjection D B C hC hCe (polynomialInjection D B C hC hCe p) = p := by
  have h : (polynomialProjection D B C hC hCe).comp
      (polynomialInjection D B C hC hCe) = AlgHom.id ℂ (Oscillator D) := by
    ext x
    simp [polynomialProjection, polynomialInjection, projectionVariable]
  exact DFunLike.congr_fun h p

private theorem injection_single (a : Fin e → ℤ) (n : Charge D) (p : Oscillator D) :
    injection D B C hC hCe a (Finsupp.single n p) =
      Finsupp.single (liftCharge D B C hC hCe a n)
        (polynomialInjection D B C hC hCe p) := by
  simp [injection]

private theorem projection_single (a : Fin e → ℤ)
    (n : Charge (ambient D e B C hC hCe)) (p : Oscillator (ambient D e B C hC hCe)) :
    projection D B C hC hCe a (Finsupp.single n p) =
      if externalCharge D B C hC hCe n = a then
        Finsupp.single (oldCharge D B C hC hCe n) (polynomialProjection D B C hC hCe p)
      else 0 := by
  classical
  simp [projection]
  split_ifs <;> simp

/-- Statewise inner truncation, before multiplication by any rational binomial. -/
theorem compressed_high_modes (a b : Fin e → ℤ) (u v : Carrier D) (q : ℤ) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → compressed D B C hC hCe a b u (q+j) v = 0 := by
  let E := ambient D e B C hC hCe
  let U := injection D B C hC hCe a u
  let V := injection D B C hC hCe b v
  refine ⟨(-((HahnModule.of ℂ).symm (Y E U V)).order - q).toNat, ?_⟩
  intro j hj
  have hz : ((Y E U)[[q+j]]) V = 0 := by
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  change projection D B C hC hCe (a+b) (((Y E U)[[q+j]]) V) = 0
  rw [hz, map_zero]

/-- The exact proposed correction has finite support for every original state;
no ground-state or bounded-oscillator restriction is used. -/
theorem correction_finite (a b c : Fin e → ℤ) (u v w : Carrier D) (p q : ℤ) :
    Function.HasFiniteSupport (fun j : ℕ => correction D B C a b j •
      compressed D B C hC hCe a (b+c) u (p-j)
        (compressed D B C hC hCe b c v (q+j) w)) := by
  classical
  obtain ⟨N, hN⟩ := compressed_high_modes D B C hC hCe b c v w q
  apply (Finset.finite_toSet (Finset.range N)).subset
  intro j hj
  apply Finset.mem_range.mpr
  by_contra hn
  exact hj (by dsimp only; rw [hN j (by omega), map_zero, smul_zero])

end
end D5.S3.VertexAlgebra.LatticeCosetCompression
