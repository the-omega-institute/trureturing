/- GID: D5/S3/Arith/CMJet/JetReduction
   generality: G
   mirror-B: none(waiver:cm-jet-native-arithmetic)
   mirror-E: none(waiver:cm-jet-native-arithmetic)
   anchors: []
   utility: none
   digest: Coefficient reduction commutes with the extension derivation and its integer jets. -/

import D5.S3.Arith.CMJet.ActualRestrictedRecurrence

/-! Coefficientwise reduction of the nested CM polynomial ring. -/

noncomputable section

namespace D5.S3.Arith.CMJet.ActualRestricted

open Polynomial
open scoped Polynomial Differential

/-- The admitted coefficient reduction, with its multiplicative structure. -/
def baseReduction (p : ℕ) : Base ℤ →+* Base (ZMod p) where
  toFun := reduce p
  map_one' := by
    apply QuadraticAlgebra.ext <;>
      simp [reduce, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_zero' := by
    apply QuadraticAlgebra.ext <;> simp [reduce]
  map_add' u v := by
    apply QuadraticAlgebra.ext <;> simp [reduce]
  map_mul' u v := by
    apply QuadraticAlgebra.ext
    · simp only [reduce, QuadraticAlgebra.re_mul, Polynomial.map_add, Polynomial.map_mul]
      simp [W]
    · simp [reduce, QuadraticAlgebra.im_mul]

def zReduction (p : ℕ) : ZExt ℤ →+* ZExt (ZMod p) :=
  mapRingHom (baseReduction p)

def jetReduction (p : ℕ) : JetExt ℤ →+* JetExt (ZMod p) :=
  mapRingHom (zReduction p)

private lemma baseReduction_x (p : ℕ) : baseReduction p (x ℤ) = x (ZMod p) := by
  apply QuadraticAlgebra.ext <;> simp [baseReduction, reduce, x]

private lemma map_implicitDeriv {A B : Type*} [CommRing A] [CommRing B]
    [Differential A] [Differential B] (f : A →+* B)
    (hf : ∀ a : A, f a′ = (f a)′) (v q : A[X]) :
    (Differential.implicitDeriv v q).map f =
      Differential.implicitDeriv (v.map f) (q.map f) := by
  change (Differential.mapCoeffs q + v * q.derivative).map f =
    Differential.mapCoeffs (q.map f) + v.map f * (q.map f).derivative
  rw [Polynomial.map_add, Polynomial.map_mul, derivative_map]
  congr 1
  ext n
  simp only [coeff_map, Differential.coeff_mapCoeffs, hf]

private lemma zReduction_deriv (p : ℕ) (q : ZExt ℤ) :
    zReduction p (zDerivation ℤ q) = zDerivation (ZMod p) (zReduction p q) := by
  change (Differential.implicitDeriv (C (zSpeed ℤ)) q).map (baseReduction p) = _
  rw [map_implicitDeriv (baseReduction p) (fun a => reduce_D p a)]
  rw [Polynomial.map_C]
  have hs : baseReduction p (zSpeed ℤ) = zSpeed (ZMod p) := by
    rw [zSpeed, map_mul, map_pow, baseReduction_x, map_ofNat, zSpeed]
  rw [hs]
  rfl

theorem jetReduction_deriv (p : ℕ) (h : ℤ) (q : JetExt ℤ) :
    jetReduction p (extendedDerivation ℤ h q) =
      extendedDerivation (ZMod p) h (jetReduction p q) := by
  change (Differential.implicitDeriv (C (sSpeed ℤ h) * X) q).map (zReduction p) = _
  rw [map_implicitDeriv (zReduction p) (zReduction_deriv p)]
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
  have hs : zReduction p (sSpeed ℤ h) = sSpeed (ZMod p) h := by
    simp [sSpeed, zReduction]
  rw [hs]
  rfl

theorem jetReduction_iter (p n : ℕ) (h : ℤ) (q : JetExt ℤ) :
    jetReduction p (extendedIter ℤ h n q) =
      extendedIter (ZMod p) h n (jetReduction p q) := by
  induction n with
  | zero => simp only [extendedIter_zero]
  | succ n ih => rw [extendedIter_succ, extendedIter_succ, jetReduction_deriv, ih]

private lemma jetReduction_section (p j : ℕ) :
    jetReduction p (sectionElement ℤ j) = sectionElement (ZMod p) j := by
  simp [sectionElement, jetReduction, zReduction, baseReduction_x]

private lemma evalZ_reduction (p : ℕ) (q : ZExt ℤ) :
    (evalZ ℤ q : ZMod p) = evalZ (ZMod p) (zReduction p q) := by
  change (↑(q.eval₂ (atORingHom ℤ) 0) : ZMod p) =
    (q.map (baseReduction p)).eval₂ (atORingHom (ZMod p)) 0
  rw [eval₂_at_zero, eval₂_at_zero, coeff_map]
  exact reduce_atO p (q.coeff 0)

private lemma evalJet_reduction (p : ℕ) (q : JetExt ℤ) :
    (evalJet ℤ q : ZMod p) = evalJet (ZMod p) (jetReduction p q) := by
  change Int.castRingHom (ZMod p) (q.eval₂ (evalZ ℤ) 1) =
    (q.map (zReduction p)).eval₂ (evalZ (ZMod p)) 1
  rw [hom_eval₂, eval₂_map, map_one]
  have heq : (Int.castRingHom (ZMod p)).comp (evalZ ℤ) =
      (evalZ (ZMod p)).comp (zReduction p) := RingHom.ext (evalZ_reduction p)
  rw [heq]

/-- Casting the integer jet gives exactly the jet computed over the residue ring. -/
theorem jet_reduce_cast (p h n j : ℕ) :
    (jet h n j : ZMod p) =
      evalJet (ZMod p) (extendedIter (ZMod p) (h : ℤ) n (sectionElement (ZMod p) j)) := by
  rw [jet, evalJet_reduction, jetReduction_iter, jetReduction_section]

end D5.S3.Arith.CMJet.ActualRestricted
