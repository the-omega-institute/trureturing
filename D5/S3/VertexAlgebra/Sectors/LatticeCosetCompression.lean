/- GID: D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeCosetCompression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Block lattice injections and longitudinal compression of complete native fields. -/

import D5.S3.VertexAlgebra.LatticeActualStateFieldCalculus
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
set_option maxHeartbeats 800000

namespace D5.S3.VertexAlgebra.LatticeCosetCompression

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeDiscriminantTheta MvPolynomial
open scoped BigOperators VertexOperator

noncomputable section

variable (D : LatticeData) (e : ℕ)
variable (B : Matrix (Fin D.rank) (Fin e) ℤ) (C : Matrix (Fin e) (Fin e) ℤ)
variable (hC : ∀ i j, C i j = C j i) (hCe : ∀ i, Even (C i i))

/-- Old coordinates precede all external coordinates. No ambient positivity. -/
def ambient : LatticeData where
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
  eval₂AlgHom ℂ (projectionVariable D B C hC hCe)

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

/-- The chosen polynomial substitution retracts every original state. -/
theorem projection_injection (a : Fin e → ℤ) (v : Carrier D) :
    projection D B C hC hCe a (injection D B C hC hCe a v) = v := by
  have h : (projection D B C hC hCe a).comp (injection D B C hC hCe a) =
      LinearMap.id := by
    apply Finsupp.lhom_ext
    intro n p
    rw [LinearMap.comp_apply, injection_single, projection_single]
    have he : externalCharge D B C hC hCe (liftCharge D B C hC hCe a n) = a := by
      funext j
      simp [externalCharge, liftCharge]
    have ho : oldCharge D B C hC hCe (liftCharge D B C hC hCe a n) = n := by
      funext i
      simp [oldCharge, liftCharge]
    simp [he, ho, polynomialProjection_injection]
  exact DFunLike.congr_fun h v

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
  exact hj (by rw [hN j (by omega), map_zero, smul_zero])

end
end D5.S3.VertexAlgebra.LatticeCosetCompression
