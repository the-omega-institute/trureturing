/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteLineEvaluation
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteLineEvaluation
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCriticalCertificate]
   utility: none
   digest: Affine substitution controls line degree, and square-zero evaluation computes each first partial. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCriticalCertificate
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate

open MvPolynomial

abbrev F := ZMod 1009

instance : Fact (Nat.Prime 1009) := ⟨by norm_num⟩

abbrev imaginary : F := 469

theorem imaginary_sq : imaginary ^ 2 = -1 := by decide +kernel

def origin (R : Type*) [CommRing R] : Fin 5 → R := ![13, 27, 11, 25, 16]
def direction (R : Type*) [CommRing R] : Fin 5 → R := ![31, 19, 23, 17, 29]

def point {R : Type*} [CommRing R] (u : R) (i : Fin 5) : R :=
  origin R i + direction R i * u

noncomputable def affineRestriction {R : Type*} [CommRing R] :
    Slice R →+* Polynomial R :=
  eval₂Hom Polynomial.C (fun i => Polynomial.C (origin R i) +
    Polynomial.C (direction R i) * Polynomial.X)

theorem eval_affineRestriction {R : Type*} [CommRing R] (p : Slice R) (u : R) :
    (affineRestriction p).eval u = eval (point u) p := by
  change (Polynomial.evalRingHom u).comp affineRestriction p = _
  congr 1
  ext i <;> simp [affineRestriction, point, eval₂Hom_X']

theorem natDegree_affineRestriction_le {R : Type*} [CommRing R] (p : Slice R) :
    (affineRestriction p).natDegree ≤ p.totalDegree := by
  classical
  nth_rw 1 [p.as_sum]
  rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  simp only [affineRestriction, eval₂Hom_monomial]
  apply (Polynomial.natDegree_mul_le ..).trans
  rw [Polynomial.natDegree_C, zero_add]
  apply (Polynomial.natDegree_prod_le _ _).trans
  refine (Finset.sum_le_sum fun j _ => ?_).trans (le_totalDegree hm)
  apply (Polynomial.natDegree_pow_le ..).trans
  have h : (Polynomial.C (origin R j) +
      Polynomial.C (direction R j) * Polynomial.X).natDegree ≤ 1 := by
    exact (Polynomial.natDegree_add_le ..).trans (max_le (by simp)
      (by simpa using Polynomial.natDegree_C_mul_X_pow_le (direction R j) 1))
  calc
    _ ≤ m j * 1 := Nat.mul_le_mul_left _ h
    _ = _ := Nat.mul_one _

theorem distinct_points {n : ℕ} (hn : n ≤ 1009) :
    Function.Injective (fun t : Fin n => ((t : ℕ) : F)) := by
  intro x y h
  apply Fin.ext
  simpa only [ZMod.val_natCast_of_lt (x.isLt.trans_le hn),
    ZMod.val_natCast_of_lt (y.isLt.trans_le hn)] using congrArg ZMod.val h

section Jets

open TrivSqZeroExt

variable {R : Type*} [CommRing R]

private abbrev Jet (R : Type*) [CommRing R] := TrivSqZeroExt R R
private abbrev const : R →+* Jet R := TrivSqZeroExt.inlHom R R

private def withTangent (x : Fin 5 → R) (i j : Fin 5) : Jet R :=
  (x j, if j = i then 1 else 0)

private theorem jet_fst (x : Fin 5 → R) (i : Fin 5) (p : Slice R) :
    (eval₂Hom const (withTangent x i) p).fst = eval x p := by
  change ((fstHom R R R).toRingHom.comp (eval₂Hom const (withTangent x i))) p = _
  congr 1
  ext j <;> simp [eval₂Hom_X']; rfl

private theorem jet_snd (x : Fin 5 → R) (i : Fin 5) (p : Slice R) :
    (eval₂Hom const (withTangent x i) p).snd = eval x (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [eval₂Hom_C, pderiv_C, map_zero]; rfl
  | add p q hp hq => simp only [map_add, snd_add, hp, hq]
  | mul_X p j hp =>
    rw [map_mul, eval₂Hom_X', snd_mul, jet_fst, hp, pderiv_mul, map_add, map_mul,
      map_mul, eval_X, pderiv_X]
    by_cases h : j = i <;> simp [withTangent, h, smul_eq_mul, mul_comm, add_comm]

/-- Evaluate a partial using the same literal trace recurrence over dual numbers. -/
def partialValue (ι : R) (x : Fin 5 → R) (ab : Fin 4 × Fin 4) (i : Fin 5) : R :=
  (slicedObservation (const ι) (withTangent x i) ab).snd

theorem eval_partial (ι : R) (x : Fin 5 → R) (ab : Fin 4 × Fin 4) (i : Fin 5) :
    eval x (pderiv i (V ι ab)) = partialValue ι x ab i := by
  rw [← jet_snd, V, map_slicedObservation]
  simp [partialValue, eval₂Hom_X']

theorem eval_value (ι : R) (x : Fin 5 → R) (ab : Fin 4 × Fin 4) :
    eval x (V ι ab) = slicedObservation ι x ab := by
  rw [V, map_slicedObservation]
  simp

end Jets

end D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate
