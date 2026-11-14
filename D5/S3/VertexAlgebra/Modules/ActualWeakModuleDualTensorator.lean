/-
SOURCE ONLY: no elaboration, kernel check, or acceptance has been performed.
The product, its actual multiplicities, and its dual realization are the
completed pinned suppliers. All inherited source-only boundaries remain.
-/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleDualitySnakes
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleDualTensorator

open LatticeGeneratingFieldLocality LatticeDiscriminantTheta
open LatticeDualCosetModule LatticeDualCosetTransport LatticeChargedTransport
open LatticeChargedQuotientScalar (carry zeroCarry unitCharacter unitCharacter_nonzero)
open FullJacobiCurrentTransport FullJacobiIntertwiner
open ActualWeakModuleSectorCoordinates ActualWeakModuleClassification ActualWeakModuleHom
open ActualWeakModuleScalarProbes (tensorCoordinates)
open ActualWeakModuleRealization ActualWeakModuleDuality
open ActualWeakModuleUniversalField (P PairSector targetModule)
open ActualWeakModuleProductMultiplicity ActualWeakModuleProductNaturality
open ActualWeakModuleAssociator ActualWeakModulePentagon ActualWeakModuleUnits
open ActualWeakModuleUnitCoherence

open private familyMap restrict_extend from
  D5.S3.VertexAlgebra.Modules.ActualWeakModuleHom
open private restrict_identity from
  D5.S3.VertexAlgebra.Modules.ActualWeakModuleUnitCoherence
open private unitCharacter_square from
  D5.S3.VertexAlgebra.Sectors.LatticeChargedQuotientScalar

universe u v u' v'
variable {D : LatticeData}
attribute [local instance] Classical.propDecidable

-- Keep the supplied literal `by abel` headers, with exact group cancellation
-- tried before the normalization procedure that left a residual zsmul term.
local macro "abel" : tactic =>
  `(tactic| ((try dsimp only [Prod.fst, Prod.snd]); first | exact neg_add_cancel_left _ _ | abel1!))

section Scalar
variable (hD : (gramReal D).PosDef)

/-- The cap-normalized coefficient, with the original nonnormalized units. -/
def k (c d : Discriminant D) : ℂ :=
  (unitCharacter D hD (-c) * unitCharacter D hD (-d) /
    unitCharacter D hD (-(c+d))) *
    (F hD (-d) (-c) (c+d) / F hD (-c) c d)

theorem k_nonzero (c d : Discriminant D) : k hD c d ≠ 0 := by
  exact mul_ne_zero
    (div_ne_zero (mul_ne_zero (unitCharacter_nonzero D hD (-c))
      (unitCharacter_nonzero D hD (-d))) (unitCharacter_nonzero D hD (-(c+d))))
    (div_ne_zero (LatticeChargedQuotientScalar.associator_nonzero D hD _ _ _)
      (LatticeChargedQuotientScalar.associator_nonzero D hD _ _ _))

/-- This equality is the scalar comparison with the five actual cap arrows.
The full carrier comparison is a separate obligation, not an assumption here. -/
theorem k_cap_coefficient (c d : Discriminant D) :
    unitCharacter D hD (-(c+d)) * k hD c d =
      unitCharacter D hD (-c) * unitCharacter D hD (-d) *
        F hD (-d) (-c) (c+d) / F hD (-c) c d := by
  unfold k
  calc
    _ = ((unitCharacter D hD (-c) * unitCharacter D hD (-d) /
        unitCharacter D hD (-(c+d))) * unitCharacter D hD (-(c+d))) *
        (F hD (-d) (-c) (c+d) / F hD (-c) c d) := by ring
    _ = _ := by
      rw [div_mul_cancel₀ _ (unitCharacter_nonzero D hD (-(c+d)))]
      ring

theorem k_zero_left (c : Discriminant D) : k hD 0 c = unitCharacter D hD (-c) := by
  simp only [k, neg_zero, zero_add, LatticeChargedQuotientScalar.unitCharacter_zero,
    one_mul, F_unit_middle, F_unit_left, div_one,
    div_self (unitCharacter_nonzero D hD (-c))]
  <;> ring

theorem k_zero_right (c : Discriminant D) : k hD c 0 = unitCharacter D hD c := by
  have hu := unitCharacter_square D hD c
  have hn := unitCharacter_nonzero D hD c
  simp only [k, neg_zero, add_zero, LatticeChargedQuotientScalar.unitCharacter_zero,
    mul_one, div_self (unitCharacter_nonzero D hD (-c)), F_unit_left,
    F_unit_right, neg_add_cancel, LatticeChargedQuotientScalar.unitCharacter_zero, div_one,
    one_mul]
  exact (div_eq_iff hn).mpr hu.symm

/-- Three literal pentagons: (-e,-d,-c,c+d+e), (-d,-c,c+d,e),
and (-c,c,d,e). Their cancellation is the anti-monoidal defect. -/
private theorem F_reverse_defect (c d e : Discriminant D) :
    F hD c d e * F hD (-e) (-d) (d+e) * F hD (-(d+e)) (-c) (c+(d+e)) *
        F hD (-c) c d * F hD (-(c+d)) (c+d) e =
      F hD (-e) (-d) (-c) * F hD (-d) (-c) (c+d) *
        F hD (-e) (-(c+d)) (c+(d+e)) * F hD (-d) d e * F hD (-c) c (d+e) := by
  have h₁ := LatticeChargedQuotientScalar.scalar_pentagon D hD (-e) (-d) (-c) (c+(d+e))
  have h₂ := LatticeChargedQuotientScalar.scalar_pentagon D hD (-d) (-c) (c+d) e
  have h₃ := LatticeChargedQuotientScalar.scalar_pentagon D hD (-c) c d e
  have hdc : -d + -c = -(c+d) := by abel
  have hed : -e + -d = -(d+e) := by abel
  have ht : -c + (c+(d+e)) = d+e := by abel
  have hz : -c + (c+d) = d := by abel
  simp only [hdc, hed, ht, hz, neg_add_cancel,
    LatticeChargedQuotientScalar.associator_zero_left, one_mul, add_assoc] at h₁ h₂ h₃
  change F hD (-e) (-d) (-c) * F hD (-e) (-(c+d)) (c+(d+e)) *
      F hD (-d) (-c) (c+(d+e)) =
    F hD (-(d+e)) (-c) (c+(d+e)) * F hD (-e) (-d) (d+e) at h₁
  change F hD (-d) (-c) (c+d) * F hD (-d) d e * F hD (-c) (c+d) e =
    F hD (-(c+d)) (c+d) e * F hD (-d) (-c) (c+(d+e)) at h₂
  change F hD (-c) c d * F hD (-c) (c+d) e * F hD c d e =
    F hD (-c) c (d+e) at h₃
  linear_combination
    -(F hD c d e * F hD (-c) c d * F hD (-(c+d)) (c+d) e) * h₁ -
    (F hD (-e) (-d) (-c) * F hD (-e) (-(c+d)) (c+(d+e)) *
      F hD c d e * F hD (-c) c d) * h₂ +
    (F hD (-e) (-d) (-c) * F hD (-e) (-(c+d)) (c+(d+e)) *
      F hD (-d) (-c) (c+d) * F hD (-d) d e) * h₃

/-- Scalar coherence for the ORIGINAL associator and the reversed product.
No braid, hexagon, or bidual assertion is consumed. -/
theorem k_associativity (c d e : Discriminant D) :
    F hD c d e * k hD d e * k hD c (d+e) =
      F hD (-e) (-d) (-c) * k hD c d * k hD (c+d) e := by
  have hF := F_reverse_defect hD c d e
  have hne := LatticeChargedQuotientScalar.associator_nonzero D hD
  have hu := unitCharacter_nonzero D hD
  have halgebra (l a b c d r e f g h : ℂ)
      (hb : b ≠ 0) (hd : d ≠ 0) (hf : f ≠ 0) (hh : h ≠ 0)
      (H : l*a*c*f*h = r*e*g*b*d) :
      l * (a/b) * (c/d) = r * (e/f) * (g/h) := by
    field_simp [hb, hd, hf, hh]
    linear_combination H
  have hf :
      F hD c d e * (F hD (-e) (-d) (d+e) / F hD (-d) d e) *
        (F hD (-(d+e)) (-c) (c+(d+e)) / F hD (-c) c (d+e)) =
      F hD (-e) (-d) (-c) * (F hD (-d) (-c) (c+d) / F hD (-c) c d) *
        (F hD (-e) (-(c+d)) (c+(d+e)) / F hD (-(c+d)) (c+d) e) := by
    exact halgebra _ _ _ _ _ _ _ _ _ _
      (hne (-d) d e) (hne (-c) c (d+e)) (hne (-c) c d)
      (hne (-(c+d)) (c+d) e) hF
  have hfactorL (a b c d t f g h : ℂ) (hd : d ≠ 0) (ht : t ≠ 0) :
      f * ((b*c/d)*g) * ((a*d/t)*h) = (a*b*c/t) * (f*g*h) := by
    field_simp [hd, ht]
    <;> ring
  have hfactorR (a b c d t f g h : ℂ) (hd : d ≠ 0) (ht : t ≠ 0) :
      f * ((a*b/d)*g) * ((d*c/t)*h) = (a*b*c/t) * (f*g*h) := by
    field_simp [hd, ht]
    <;> ring
  let U := unitCharacter D hD (-c) * unitCharacter D hD (-d) *
    unitCharacter D hD (-e) / unitCharacter D hD (-(c+(d+e)))
  calc
    _ = U * (F hD c d e * (F hD (-e) (-d) (d+e) / F hD (-d) d e) *
        (F hD (-(d+e)) (-c) (c+(d+e)) / F hD (-c) c (d+e))) := by
      unfold k U
      exact hfactorL _ _ _ _ _ _ _ _
        (hu (-(d+e))) (hu (-(c+(d+e))))
    _ = U * (F hD (-e) (-d) (-c) * (F hD (-d) (-c) (c+d) / F hD (-c) c d) *
        (F hD (-e) (-(c+d)) (c+(d+e)) / F hD (-(c+d)) (c+d) e)) := by rw [hf]
    _ = _ := by
      unfold k U
      rw [add_assoc c d e]
      exact (hfactorR _ _ _ _ _ _ _ _
        (hu (-(c+d))) (hu (-(c+(d+e))))).symm

end Scalar

section Pairing
variable {V : Type u} {W : Type v}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Reversed algebraic dual pairing. Neither factor is assumed finite. -/
def reversePairing :
    Module.Dual ℂ W ⊗[ℂ] Module.Dual ℂ V →ₗ[ℂ] Module.Dual ℂ (V ⊗[ℂ] W) :=
  (TensorProduct.dualDistrib ℂ V W).comp
    (TensorProduct.comm ℂ (Module.Dual ℂ W) (Module.Dual ℂ V)).toLinearMap

@[simp] theorem reversePairing_tmul (ψ : Module.Dual ℂ W) (φ : Module.Dual ℂ V)
    (x : V) (y : W) :
    reversePairing (ψ ⊗ₜ[ℂ] φ) (x ⊗ₜ[ℂ] y) = φ x * ψ y := by
  simp [reversePairing]

/-- Precomposition in the two actual factors, for arbitrary algebraic tensors. -/
private theorem reversePairing_map {V' : Type u'} {W' : Type v'}
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    (f : V →ₗ[ℂ] V') (g : W →ₗ[ℂ] W')
    (ψ : Module.Dual ℂ W') (φ : Module.Dual ℂ V') (z : V ⊗[ℂ] W) :
    reversePairing (ψ ⊗ₜ[ℂ] φ) (TensorProduct.map f g z) =
      reversePairing (ψ.comp g ⊗ₜ[ℂ] φ.comp f) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul x y => simp

end Pairing

section ActualFibers
variable {X : Type u} {Y : Type v}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
variable (hD : (gramReal D).PosDef)

/-- Projection to ONE individual pair fiber of the actual normalized mu. -/
def fiberRead (s : Discriminant D) (i : Fiber (D := D) s) :
    Multiplicity (targetModule A B) s →ₗ[ℂ] PairMultiplicity A B i.val :=
  (DirectSum.component ℂ _ (fun j : Fiber (D := D) s => PairMultiplicity A B j.val) i).comp
    (mu A B hD s)

/-- Xi is a functional on the actual product multiplicity, defined by readout,
not by an asserted evaluation identity. -/
def Xi (s : Discriminant D) (i : Fiber (D := D) s) :
    Module.Dual ℂ (Multiplicity B i.val.2) ⊗[ℂ]
        Module.Dual ℂ (Multiplicity A i.val.1) →ₗ[ℂ]
      Module.Dual ℂ (Multiplicity (targetModule A B) s) :=
  (fiberRead A B hD s i).dualMap.comp reversePairing

/-- The original inverse-vacuum normalization remains visible in the readout. -/
theorem Xi_coordinate (s : Discriminant D) (i : Fiber (D := D) s)
    (w : Module.Dual ℂ (Multiplicity B i.val.2) ⊗[ℂ]
      Module.Dual ℂ (Multiplicity A i.val.1))
    (z : Multiplicity (targetModule A B) s) :
    Xi A B hD s i w z =
      epsilon D (-carry D hD i.val.1 i.val.2) (carry D hD i.val.1 i.val.2) *
        reversePairing w (tensorCoordinates (z.val.val i.val)
          (-carry D hD i.val.1 i.val.2,0)) := by
  change reversePairing w (mu A B hD s z i) = _
  rw [mu_coordinate, map_smul]
  rfl

@[simp] theorem Xi_jAt (s : Discriminant D) (i : Fiber (D := D) s)
    (w : Module.Dual ℂ (Multiplicity B i.val.2) ⊗[ℂ]
      Module.Dual ℂ (Multiplicity A i.val.1)) (z : PairMultiplicity A B i.val) :
    Xi A B hD s i w (jAt A B hD s i z) = reversePairing w z := by
  change reversePairing w ((DirectSum.component ℂ _ _ i)
    (mu A B hD s (jAt A B hD s i z))) = _
  rw [mu_jAt, DirectSum.component.lof_self]

/-- Even with the SAME total charge, a different individual pair vanishes. -/
theorem Xi_jAt_wrong (s : Discriminant D) (i j : Fiber (D := D) s)
    (hij : j ≠ i)
    (w : Module.Dual ℂ (Multiplicity B i.val.2) ⊗[ℂ]
      Module.Dual ℂ (Multiplicity A i.val.1)) (z : PairMultiplicity A B j.val) :
    Xi A B hD s i w (jAt A B hD s j z) = 0 := by
  change reversePairing w ((DirectSum.component ℂ _ _ i)
    (mu A B hD s (jAt A B hD s j z))) = 0
  rw [mu_jAt]
  change reversePairing w ((DirectSum.of (fun q : Fiber (D := D) s =>
    PairMultiplicity A B q.val) j z) i) = 0
  rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hij), map_zero]

/-- Source (r,t) in B* then A* reads precisely (-t,-r) in A then B. -/
def reverseFiber (s : Discriminant D) (i : Fiber (D := D) s) : Fiber (D := D) (-s) :=
  ⟨(-i.val.2,-i.val.1), by
    change -i.val.2 + -i.val.1 = -s
    calc
      _ = -(i.val.1 + i.val.2) := by abel
      _ = -s := congrArg Neg.neg i.property⟩

/-- Actual kappa maps remove the two dual realizations before pairing. -/
def readFunctional (s : Discriminant D) (i : Fiber (D := D) s) :
    PairMultiplicity (dualModule B) (dualModule A) i.val →ₗ[ℂ]
      DualMultiplicity (targetModule A B) s :=
  (Xi A B hD (-s) (reverseFiber s i)).comp
    (TensorProduct.map (kappa (DualMultiplicity B) i.val.1)
      (kappa (DualMultiplicity A) i.val.2))

/-- The target is the ORIGINAL contragredient multiplicity via its actual iota. -/
def dualTensorBlock (s : Discriminant D) (i : Fiber (D := D) s) :
    PairMultiplicity (dualModule B) (dualModule A) i.val →ₗ[ℂ]
      Multiplicity (dualModule (targetModule A B)) s :=
  k hD (-i.val.2) (-i.val.1) •
    (iota (DualMultiplicity (targetModule A B)) s).comp (readFunctional A B hD s i)

def dualTensorFamily :
    Families (targetModule (dualModule B) (dualModule A)) (dualModule (targetModule A B)) :=
  fun s => (DirectSum.toModule ℂ _ _ (dualTensorBlock A B hD s)).comp
    (mu (dualModule B) (dualModule A) hD s)

/-- A full all-state/all-integer-mode original ModuleHom at arbitrary original
multiplicities and independent input universes. -/
def dualTensorHom :
    ModuleHom (targetModule (dualModule B) (dualModule A)) (dualModule (targetModule A B)) :=
  extend hD (dualTensorFamily A B hD)

theorem dualTensorFamily_jAt (s : Discriminant D) (i : Fiber (D := D) s)
    (w : PairMultiplicity (dualModule B) (dualModule A) i.val) :
    dualTensorFamily A B hD s (jAt (dualModule B) (dualModule A) hD s i w) =
      k hD (-i.val.2) (-i.val.1) •
        iota (DualMultiplicity (targetModule A B)) s (readFunctional A B hD s i w) := by
  simp only [dualTensorFamily, LinearMap.comp_apply, mu_jAt, DirectSum.toModule_lof,
    dualTensorBlock, LinearMap.smul_apply, LinearMap.comp_apply] <;> rfl

/-- Raw carrier readback, with the actual source carry and target representative.
No normalization of beta_(r+t), and no finite-dimensional hypothesis. -/
theorem dualTensorHom_pair (r t : Discriminant D) (v : Carrier D)
    (w : PairMultiplicity (dualModule B) (dualModule A) (r,t)) :
    (dualTensorHom A B hD).linearMap
      (DirectSum.lof ℂ _ (PairSector (dualModule B) (dualModule A)) (r,t)
        (v ⊗ₜ[ℂ] w)) =
    k hD (-t) (-r) •
      DirectSum.lof ℂ _ (fun s => Carrier D ⊗[ℂ] DualMultiplicity (targetModule A B) s)
        (r+t) (transport D (representative D (r+t)) (carry D hD r t) v ⊗ₜ[ℂ]
          readFunctional A B hD (r+t) ⟨(r,t),rfl⟩ w) := by
  let S := targetModule (dualModule B) (dualModule A)
  let T := dualModule (targetModule A B)
  let f := dualTensorHom A B hD
  let u := transport D (representative D (r+t)) (carry D hD r t) v
  let z := jAt (dualModule B) (dualModule A) hD (r+t) ⟨(r,t),rfl⟩ w
  have hs : classified hD S (r+t) z u =
      DirectSum.lof ℂ _ (PairSector (dualModule B) (dualModule A)) (r,t)
        (v ⊗ₜ[ℂ] w) := by
    have hi := congrArg (classificationEquiv S hD)
      (classification_inverse_pair (dualModule B) (dualModule A) hD r t v w)
    exact hi.symm.trans ((classificationEquiv S hD).apply_symm_apply _)
  have hr := congrArg (fun q : Multiplicity S (r+t) →ₗ[ℂ] Multiplicity T (r+t) => q z)
    (congrFun (restrict_extend hD (dualTensorFamily A B hD)) (r+t))
  refine (congrArg f.linearMap hs.symm).trans ?_
  refine (classified_natural hD f (r+t) u z).trans ?_
  refine (congrArg (fun q => classified hD T (r+t) q u) hr).trans ?_
  let L : Multiplicity T (r+t) →ₗ[ℂ] DualCarrier (targetModule A B) :=
    (classificationEquiv T hD).toLinearMap.comp
      ((DirectSum.lof ℂ _ (fun s => Carrier D ⊗[ℂ] Multiplicity T s) (r+t)).comp
        (TensorProduct.mk ℂ (Carrier D) (Multiplicity T (r+t)) u))
  change L (dualTensorFamily A B hD (r+t) z) = _
  have hj := dualTensorFamily_jAt A B hD (r+t) ⟨(r,t),rfl⟩ w
  exact (congrArg L.toAddHom.toFun hj).trans
    ((L.map_smul (k hD (-t) (-r)) _).trans
      (congrArg (fun q => k hD (-t) (-r) • q)
        (classification_iota (DualMultiplicity (targetModule A B)) hD (r+t) _ _)))


/-- The single-charge formula exposes the epsilon for carry(r,t).
For r=-d,t=-c this is literally carry(-d,-c). -/
theorem dualTensorHom_single (r t : Discriminant D) (l : Charge D) (p : Oscillator D)
    (w : PairMultiplicity (dualModule B) (dualModule A) (r,t)) :
    (dualTensorHom A B hD).linearMap
      (DirectSum.lof ℂ _ (PairSector (dualModule B) (dualModule A)) (r,t)
        (Finsupp.single l p ⊗ₜ[ℂ] w)) =
    (k hD (-t) (-r) * epsilon D l (carry D hD r t)) •
      DirectSum.lof ℂ _ (fun s => Carrier D ⊗[ℂ] DualMultiplicity (targetModule A B) s)
        (r+t) (Finsupp.single (l+carry D hD r t) p ⊗ₜ[ℂ]
          readFunctional A B hD (r+t) ⟨(r,t),rfl⟩ w) := by
  let q := readFunctional A B hD (r+t) ⟨(r,t),rfl⟩ w
  let L : Carrier D →ₗ[ℂ] DualCarrier (targetModule A B) :=
    (DirectSum.lof ℂ _ (fun s => Carrier D ⊗[ℂ] DualMultiplicity (targetModule A B) s)
      (r+t)).comp ((TensorProduct.mk ℂ (Carrier D) _).flip q)
  refine (dualTensorHom_pair A B hD r t (Finsupp.single l p) w).trans ?_
  have ht := congrArg (fun z : Carrier D => k hD (-t) (-r) • L z)
    (transport_single D (representative D (r+t)) (carry D hD r t) l p)
  have hs := congrArg (fun z => k hD (-t) (-r) • z)
    (L.map_smul (epsilon D l (carry D hD r t))
      (Finsupp.single (l+carry D hD r t) p))
  exact ht.trans (hs.trans (smul_smul _ _ _))


/-- Cast-correct readback on the requested (-d,-c) source fiber. -/
theorem dualTensorHom_jAt (c d : Discriminant D)
    (ψ : Module.Dual ℂ (Multiplicity B d)) (φ : Module.Dual ℂ (Multiplicity A c)) :
    restrict (dualTensorHom A B hD) (-(c+d))
      (jAt (dualModule B) (dualModule A) hD (-(c+d))
        ⟨(-d,-c),by abel⟩ (dualIota B d ψ ⊗ₜ[ℂ] dualIota A c φ)) =
      k hD c d • dualIota (targetModule A B) (c+d)
        (Xi A B hD (c+d) ⟨(c,d),rfl⟩ (ψ ⊗ₜ[ℂ] φ)) := by
  let evalRaw (q : Discriminant D)
      (f : Module.Dual ℂ (Multiplicity (targetModule A B) q))
      (x : Multiplicity (targetModule A B) q) : ℂ := f.toAddHom.toFun x
  have readOn (s : Discriminant D) (i : Fiber (D := D) s)
      (ψ : DualMultiplicity B i.val.1) (φ : DualMultiplicity A i.val.2) :
      readFunctional A B hD s i
        (iota (DualMultiplicity B) i.val.1 ψ ⊗ₜ[ℂ]
          iota (DualMultiplicity A) i.val.2 φ) =
        Xi A B hD (-s) (reverseFiber s i) (ψ ⊗ₜ[ℂ] φ) := by
    as_aux_lemma =>
      let F : DualMultiplicity B i.val.1 ⊗[ℂ] DualMultiplicity A i.val.2 →ₗ[ℂ]
          DualMultiplicity (targetModule A B) s := Xi A B hD (-s) (reverseFiber s i)
      change F ((TensorProduct.map (kappa (DualMultiplicity B) i.val.1)
        (kappa (DualMultiplicity A) i.val.2))
          (iota (DualMultiplicity B) i.val.1 ψ ⊗ₜ[ℂ]
            iota (DualMultiplicity A) i.val.2 φ)) = F (ψ ⊗ₜ[ℂ] φ)
      have ht := TensorProduct.map_tmul (kappa (DualMultiplicity B) i.val.1)
        (kappa (DualMultiplicity A) i.val.2)
        (iota (DualMultiplicity B) i.val.1 ψ) (iota (DualMultiplicity A) i.val.2 φ)
      have hc := congrArg₂ (fun x y => x ⊗ₜ[ℂ] y)
        (kappa_iota (DualMultiplicity B) i.val.1 ψ)
        (kappa_iota (DualMultiplicity A) i.val.2 φ)
      exact (congrArg F ht).trans (congrArg F hc)
  have transportEvaluated {I : Type _} [Add I]
      {F : I → Type _} {G : I → Type _} {H : I → Type _} {M : I → Type _}
      (f : ∀ a b q, a+b = q → G b → F a → H q)
      (ev : ∀ q, H q → M q → ℂ)
      (c d : I) (ψ : G d) (φ : F c)
      (a b q : I) (hc : c = a) (hd : d = b)
      (hq : c+d = q) (hab : a+b = q) (x : M q) :
      ev q (f a b q hab (cast (congrArg G hd) ψ) (cast (congrArg F hc) φ)) x =
        ev q (cast (congrArg H hq) (f c d (c+d) rfl ψ φ)) x := by
    as_aux_lemma =>
      cases hc
      cases hd
      cases hq
      rfl
  let i : Fiber (D := D) (-(c+d)) := ⟨(-d,-c),by abel⟩
  let ψ' : DualMultiplicity B (-d) :=
    cast (congrArg (fun e => Module.Dual ℂ (Multiplicity B e)) (neg_neg d).symm) ψ
  let φ' : DualMultiplicity A (-c) :=
    cast (congrArg (fun e => Module.Dual ℂ (Multiplicity A e)) (neg_neg c).symm) φ
  let w := dualIota B d ψ ⊗ₜ[ℂ] dualIota A c φ
  let z := jAt (dualModule B) (dualModule A) hD (-(c+d)) i w
  have hb : dualIota B d ψ = iota (DualMultiplicity B) (-d) ψ' := by
    set_option maxHeartbeats 100000 in
      as_aux_lemma =>
        dsimp only [dualIota]
        run_tac Lean.Elab.Tactic.withMainContext do
          let target ← Lean.Elab.Tactic.getMainTarget
          let normalize (e : Lean.Expr) : Lean.MetaM (Lean.Expr × Lean.Expr × Array (Lean.Expr × Lean.Expr)) := do
            let e ← Lean.instantiateMVars e
            let mut todo := #[e]
            let mut seen : Lean.ExprSet := {}
            let mut params : Array Lean.Expr := #[]
            let mut i := 0
            while i < todo.size do
              let p := todo[i]!
              i := i+1
              if !seen.contains p then
                seen := seen.insert p
                let n := p.getAppFn.constName?.getD .anonymous
                if !p.hasLooseBVars && !p.hasFVar &&
                    (n == `Algebra.to_smulCommClass || n == `IsScalarTower.to_smulCommClass ||
                     n == `instSMulCommClassOfIsScalarTower || n == `RingHomInvPair.ids ||
                     n == `RingHomCompTriple.ids || (n.toString.splitOn "._proof_").length > 1) then
                  if ← Lean.Meta.isProof p then
                    params := params.push p
                match p with
                | .app f x => todo := (todo.push f).push x
                | .lam _ t b _ | .forallE _ t b _ => todo := (todo.push t).push b
                | .letE _ t v b _ => todo := ((todo.push t).push v).push b
                | .mdata _ b | .proj _ _ b => todo := todo.push b
                | _ => pure ()
            let mut replacements : Array (Lean.Expr × Lean.Expr) := #[]
            let mut current := e
            let mut transport ← Lean.Meta.mkEqRefl e
            for p in params do
              let tp ← Lean.Meta.inferType p
              if !(tp.isAppOf `SMulCommClass || tp.isAppOf `RingHomCompTriple ||
                  tp.isAppOf `RingHomInvPair) then
                continue
              let q ← Lean.Meta.synthInstance tp
              let q ← Lean.instantiateMVars q
              if p != q then
                let h ← Lean.Meta.mkAppM `Subsingleton.elim #[p,q]
                let step ← Lean.Meta.withLocalDeclD `comm tp fun v => do
                  let body := current.replace fun x => if x == p then some v else none
                  let motive ← Lean.Meta.mkLambdaFVars #[v] body
                  Lean.Meta.mkCongrArg motive h
                transport ← Lean.Meta.mkEqTrans transport step
                replacements := replacements.push (p,q)
                current := current.replace fun x => if x == p then some q else none
            return (current,transport,replacements)
          let (canonical,transport,_) ← normalize target
          let next ← Lean.Meta.mkFreshExprMVar canonical
          let proof ← Lean.Meta.mkEqMPR transport next
          let goal ← Lean.Elab.Tactic.getMainGoal
          goal.assign proof
          Lean.Elab.Tactic.replaceMainGoal [next.mvarId!]
        exact (LinearMap.comp_apply (iota (DualMultiplicity B) (-d)) (LinearEquiv.cast (R := ℂ) (M := (fun e => Module.Dual ℂ (Multiplicity B e))) (neg_neg d).symm).toLinearMap ψ).trans
          (congrArg (iota (DualMultiplicity B) (-d)) (LinearEquiv.cast_apply (R := ℂ) (M := (fun e => Module.Dual ℂ (Multiplicity B e)))
            (neg_neg d).symm ψ))
  have ha : dualIota A c φ = iota (DualMultiplicity A) (-c) φ' := by
    set_option maxHeartbeats 100000 in
      as_aux_lemma =>
        dsimp only [dualIota]
        run_tac Lean.Elab.Tactic.withMainContext do
          let target ← Lean.Elab.Tactic.getMainTarget
          let normalize (e : Lean.Expr) : Lean.MetaM (Lean.Expr × Lean.Expr × Array (Lean.Expr × Lean.Expr)) := do
            let e ← Lean.instantiateMVars e
            let mut todo := #[e]
            let mut seen : Lean.ExprSet := {}
            let mut params : Array Lean.Expr := #[]
            let mut i := 0
            while i < todo.size do
              let p := todo[i]!
              i := i+1
              if !seen.contains p then
                seen := seen.insert p
                let n := p.getAppFn.constName?.getD .anonymous
                if !p.hasLooseBVars && !p.hasFVar &&
                    (n == `Algebra.to_smulCommClass || n == `IsScalarTower.to_smulCommClass ||
                     n == `instSMulCommClassOfIsScalarTower || n == `RingHomInvPair.ids ||
                     n == `RingHomCompTriple.ids || (n.toString.splitOn "._proof_").length > 1) then
                  if ← Lean.Meta.isProof p then
                    params := params.push p
                match p with
                | .app f x => todo := (todo.push f).push x
                | .lam _ t b _ | .forallE _ t b _ => todo := (todo.push t).push b
                | .letE _ t v b _ => todo := ((todo.push t).push v).push b
                | .mdata _ b | .proj _ _ b => todo := todo.push b
                | _ => pure ()
            let mut replacements : Array (Lean.Expr × Lean.Expr) := #[]
            let mut current := e
            let mut transport ← Lean.Meta.mkEqRefl e
            for p in params do
              let tp ← Lean.Meta.inferType p
              if !(tp.isAppOf `SMulCommClass || tp.isAppOf `RingHomCompTriple ||
                  tp.isAppOf `RingHomInvPair) then
                continue
              let q ← Lean.Meta.synthInstance tp
              let q ← Lean.instantiateMVars q
              if p != q then
                let h ← Lean.Meta.mkAppM `Subsingleton.elim #[p,q]
                let step ← Lean.Meta.withLocalDeclD `comm tp fun v => do
                  let body := current.replace fun x => if x == p then some v else none
                  let motive ← Lean.Meta.mkLambdaFVars #[v] body
                  Lean.Meta.mkCongrArg motive h
                transport ← Lean.Meta.mkEqTrans transport step
                replacements := replacements.push (p,q)
                current := current.replace fun x => if x == p then some q else none
            return (current,transport,replacements)
          let (canonical,transport,_) ← normalize target
          let next ← Lean.Meta.mkFreshExprMVar canonical
          let proof ← Lean.Meta.mkEqMPR transport next
          let goal ← Lean.Elab.Tactic.getMainGoal
          goal.assign proof
          Lean.Elab.Tactic.replaceMainGoal [next.mvarId!]
        exact (LinearMap.comp_apply (iota (DualMultiplicity A) (-c)) (LinearEquiv.cast (R := ℂ) (M := (fun e => Module.Dual ℂ (Multiplicity A e))) (neg_neg c).symm).toLinearMap φ).trans
          (congrArg (iota (DualMultiplicity A) (-c)) (LinearEquiv.cast_apply (R := ℂ) (M := (fun e => Module.Dual ℂ (Multiplicity A e)))
            (neg_neg c).symm φ))
  have hw := congrArg₂ (fun x y => x ⊗ₜ[ℂ] y) hb ha
  have hread : readFunctional A B hD (-(c+d)) i w =
      cast (congrArg (fun e => Module.Dual ℂ (Multiplicity (targetModule A B) e))
        (neg_neg (c+d)).symm)
        (Xi A B hD (c+d) ⟨(c,d),rfl⟩ (ψ ⊗ₜ[ℂ] φ)) := by
    as_aux_lemma =>
      apply DFunLike.ext
      intro z0
      let ev : DualMultiplicity (targetModule A B) (-(c+d)) → ℂ :=
        fun ξ => evalRaw (- -(c+d)) ξ z0
      have h1 := congrArg ev
        (congrArg (readFunctional A B hD (-(c+d)) i) hw)
      have h2 := congrArg ev
        (readOn (-(c+d)) i ψ' φ')
      have h3 := transportEvaluated
        (fun a b q (hab : a+b=q)
          (ψ : Module.Dual ℂ (Multiplicity B b))
          (φ : Module.Dual ℂ (Multiplicity A a)) =>
          Xi A B hD q ⟨(a,b),hab⟩ (ψ ⊗ₜ[ℂ] φ)) evalRaw
        c d ψ φ (reverseFiber (-(c+d)) i).val.1
          (reverseFiber (-(c+d)) i).val.2 (- -(c+d))
          (neg_neg c).symm (neg_neg d).symm (neg_neg (c+d)).symm
          (reverseFiber (-(c+d)) i).property z0
      run_tac Lean.Elab.Tactic.withMainContext do
        let lctx ← Lean.instantiateLCtxMVars (← Lean.getLCtx)
        let proof (n : Lean.Name) : Lean.MetaM Lean.Expr := do
          let some d := lctx.findFromUserName? n | throwError "missing equality"
          return Lean.Expr.fvar d.fvarId
        let sides (h : Lean.Expr) : Lean.MetaM (Lean.Expr × Lean.Expr) := do
          let t ← Lean.Meta.whnf (← Lean.Meta.inferType h)
          let some (_,a,b) := t.eq? | throwError "expected equality: {t}"
          return (a,b)
        let canonicalize (h : Lean.Expr) : Lean.MetaM (Lean.Expr × Lean.Expr × Lean.Expr × Nat) := do
          let raw ← Lean.Meta.whnf (← Lean.Meta.inferType h)
          let type ← Lean.Meta.zetaReduce raw (zetaDelta := true) (zetaHave := true) (beta := true)
          let mut todo := #[type]
          let mut seen : Lean.ExprSet := {}
          let mut params : Array Lean.Expr := #[]
          let mut j := 0
          while j < todo.size do
            let p := todo[j]!
            j := j+1
            if !seen.contains p then
              seen := seen.insert p
              let n := p.getAppFn.constName?.getD .anonymous
              if !p.hasLooseBVars &&
                  (n == `Algebra.to_smulCommClass || n == `IsScalarTower.to_smulCommClass ||
                   n == `instSMulCommClassOfIsScalarTower || n == `RingHomInvPair.ids ||
                   n == `RingHomCompTriple.ids || (n.toString.splitOn "._proof_").length > 1) then
                if ← Lean.Meta.isProof p then params := params.push p
              match p with
              | .app f x => todo := (todo.push f).push x
              | .lam _ t b _ | .forallE _ t b _ => todo := (todo.push t).push b
              | .letE _ t v b _ => todo := ((todo.push t).push v).push b
              | .mdata _ b | .proj _ _ b => todo := todo.push b
              | _ => pure ()
          let mut current := type
          let mut transport ← Lean.Meta.mkEqRefl type
          let mut count := 0
          for p in params do
            let tp ← Lean.Meta.inferType p
            if !(tp.isAppOf `SMulCommClass || tp.isAppOf `RingHomCompTriple ||
                tp.isAppOf `RingHomInvPair) then continue
            let q ← Lean.instantiateMVars (← Lean.Meta.synthInstance tp)
            if p != q then
              let hpq ← Lean.Meta.mkAppM `Subsingleton.elim #[p,q]
              let step ← Lean.Meta.withLocalDeclD `scalarProof tp fun v => do
                let body := current.replace fun e => if e == p then some v else none
                let motive ← Lean.Meta.mkLambdaFVars #[v] body
                Lean.Meta.mkCongrArg motive hpq
              transport ← Lean.Meta.mkEqTrans transport step
              current := current.replace fun e => if e == p then some q else none
              count := count+1
          let proof ← Lean.Meta.mkEqMP transport h
          let some (_,a,b) := current.eq? | throwError "expected canonical scalar equality"
          return (proof,a,b,count)
        let (p1,a,b,n1) ← canonicalize (← proof `h1)
        let (p2,a2,c,n2) ← canonicalize (← proof `h2)
        let (p3,a3,d,n3) ← canonicalize (← proof `h3)
        let trans := Lean.mkConst `Eq.trans [Lean.Level.succ Lean.Level.zero]
        let tail := Lean.mkApp6 trans (Lean.mkConst `Complex) b c d p2 p3
        let full := Lean.mkApp6 trans (Lean.mkConst `Complex) a b d p1 tail
        Lean.Elab.Tactic.closeMainGoal `canonical_scalar_transitivity full
  have iotaCast {U : Type _} [AddCommGroup U] [Module ℂ U]
      (C : FullJacobiLatticeModule D U) (q : Discriminant D)
      (ξ : Module.Dual ℂ (Multiplicity C q)) :
      dualIota C q ξ = iota (DualMultiplicity C) (-q)
        (cast (congrArg (fun e => Module.Dual ℂ (Multiplicity C e)) (neg_neg q).symm) ξ) := by
    as_aux_lemma =>
      dsimp only [dualIota]
      run_tac Lean.Elab.Tactic.withMainContext do
        let target ← Lean.Elab.Tactic.getMainTarget
        let normalize (e : Lean.Expr) : Lean.MetaM (Lean.Expr × Lean.Expr × Array (Lean.Expr × Lean.Expr)) := do
          let e ← Lean.instantiateMVars e
          let mut todo := #[e]
          let mut seen : Lean.ExprSet := {}
          let mut params : Array Lean.Expr := #[]
          let mut i := 0
          while i < todo.size do
            let p := todo[i]!
            i := i+1
            if !seen.contains p then
              seen := seen.insert p
              let n := p.getAppFn.constName?.getD .anonymous
              if !p.hasLooseBVars && !p.hasFVar &&
                  (n == `Algebra.to_smulCommClass || n == `IsScalarTower.to_smulCommClass ||
                   n == `instSMulCommClassOfIsScalarTower || n == `RingHomInvPair.ids ||
                   n == `RingHomCompTriple.ids || (n.toString.splitOn "._proof_").length > 1) then
                if ← Lean.Meta.isProof p then
                  params := params.push p
              match p with
              | .app f x => todo := (todo.push f).push x
              | .lam _ t b _ | .forallE _ t b _ => todo := (todo.push t).push b
              | .letE _ t v b _ => todo := ((todo.push t).push v).push b
              | .mdata _ b | .proj _ _ b => todo := todo.push b
              | _ => pure ()
          let mut replacements : Array (Lean.Expr × Lean.Expr) := #[]
          let mut current := e
          let mut transport ← Lean.Meta.mkEqRefl e
          for p in params do
            let tp ← Lean.Meta.inferType p
            if !(tp.isAppOf `SMulCommClass || tp.isAppOf `RingHomCompTriple ||
                tp.isAppOf `RingHomInvPair) then
              continue
            let q ← Lean.Meta.synthInstance tp
            let q ← Lean.instantiateMVars q
            if p != q then
              let h ← Lean.Meta.mkAppM `Subsingleton.elim #[p,q]
              let step ← Lean.Meta.withLocalDeclD `comm tp fun v => do
                let body := current.replace fun x => if x == p then some v else none
                let motive ← Lean.Meta.mkLambdaFVars #[v] body
                Lean.Meta.mkCongrArg motive h
              transport ← Lean.Meta.mkEqTrans transport step
              replacements := replacements.push (p,q)
              current := current.replace fun x => if x == p then some q else none
          return (current,transport,replacements)
        let (canonical,transport,_) ← normalize target
        let next ← Lean.Meta.mkFreshExprMVar canonical
        let proof ← Lean.Meta.mkEqMPR transport next
        let goal ← Lean.Elab.Tactic.getMainGoal
        goal.assign proof
        Lean.Elab.Tactic.replaceMainGoal [next.mvarId!]
      exact (LinearMap.comp_apply (iota (DualMultiplicity C) (-q))
        (LinearEquiv.cast (R := ℂ) (M := fun e => Module.Dual ℂ (Multiplicity C e))
          (neg_neg q).symm).toLinearMap ξ).trans
        (congrArg (iota (DualMultiplicity C) (-q))
          (LinearEquiv.cast_apply (R := ℂ) (M := fun e => Module.Dual ℂ (Multiplicity C e))
            (neg_neg q).symm ξ))
  have hout := iotaCast (targetModule A B) (c+d)
    (Xi A B hD (c+d) ⟨(c,d),rfl⟩ (ψ ⊗ₜ[ℂ] φ))
  have hvalue := (congrArg (iota (DualMultiplicity (targetModule A B)) (-(c+d))) hread).trans hout.symm
  have hk : k hD (- -c) (- -d) = k hD c d :=
    congrArg₂ (k hD) (neg_neg c) (neg_neg d)
  have hs := (congrArg (fun a : ℂ => a • iota (DualMultiplicity (targetModule A B)) (-(c+d))
    (readFunctional A B hD (-(c+d)) i w)) hk).trans
      (congrArg (fun v => k hD c d • v) hvalue)
  have hr := congrFun (restrict_extend hD (dualTensorFamily A B hD)) (-(c+d))
  have he := DFunLike.congr_fun hr z
  have hj := dualTensorFamily_jAt A B hD (-(c+d)) i w
  apply Subtype.ext
  apply Subtype.ext
  let readValue (t : Multiplicity (dualModule (targetModule A B)) (-(c+d))) := t.val.val
  exact (congrArg readValue he).trans
    ((congrArg readValue hj).trans (congrArg readValue hs))


/-- The actual five-arrow cap composite; the associator direction is explicit. -/
def nestedEvaluation :
    ModuleHom (targetModule (targetModule (dualModule B) (dualModule A))
      (targetModule A B)) (I D) :=
  (evaluation B hD).comp
    ((productHom hD (ModuleHom.id (dualModule B)) (leftUnitIso hD B).hom).comp
      ((productHom hD (ModuleHom.id (dualModule B))
        (productHom hD (evaluation A hD) (ModuleHom.id B))).comp
        ((productHom hD (ModuleHom.id (dualModule B))
          (associatorIso (dualModule A) A B hD).inv).comp
          (associatorIso (dualModule B) (dualModule A) (targetModule A B) hD).hom)))

private theorem restrict_inverse_cap_associator (c d : Discriminant D)
    (φ : Module.Dual ℂ (Multiplicity A c)) (x : Multiplicity A c) (y : Multiplicity B d) :
    restrict (associatorIso (dualModule A) A B hD).inv d
      (jAt (dualModule A) (targetModule A B) hD d
        ⟨(-c,c+d),by abel⟩ (dualIota A c φ ⊗ₜ[ℂ] j A B hD c d (x ⊗ₜ[ℂ] y))) =
      (F hD (-c) c d)⁻¹ •
        jAt (targetModule (dualModule A) A) B hD d ⟨(0,d),zero_add d⟩
          (jAt (dualModule A) A hD 0 ⟨(-c,c),neg_add_cancel c⟩
            (dualIota A c φ ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] y) := by
  apply Subtype.ext
  apply Subtype.ext
  change alphaInverse (dualModule A) A B hD _ = _
  simpa only [jAt_val, j_val, ground, normalizedPair, LinearMap.comp_apply,
    LinearMap.flip_apply, TensorProduct.mk_apply, Submodule.coe_smul] using
    alphaInverse_normalized_fibers (dualModule A) A B hD (-c) c d 0 (c+d)
      (neg_add_cancel c) rfl (Finsupp.single 0 (1 : Oscillator D))
      (dualIota A c φ) x y

private theorem evaluation_normalized {Z : Type u'} [AddCommGroup Z] [Module ℂ Z]
    (C : FullJacobiLatticeModule D Z) (c : Discriminant D)
    (φ : Module.Dual ℂ (Multiplicity C c)) (x : Multiplicity C c) (v : Carrier D) :
    (evaluation C hD).linearMap
      (normalizedPair (dualModule C) C hD (-c) c (dualIota C c φ ⊗ₜ[ℂ] x) v) =
      (unitCharacter D hD (-c) * φ x) • transport D 0 (zeroCarry D hD) v := by
  change (evaluation C hD).linearMap
    (DirectSum.lof ℂ _ (PairSector (dualModule C) C) (-c,c)
      (transportInverse D (representative D (-c+c)) (carry D hD (-c) c) v ⊗ₜ[ℂ]
        (dualIota C c φ ⊗ₜ[ℂ] x))) = _
  rw [evaluation_pair]
  simp only [neg_add_cancel]
  have hcancel := congrArg (fun f : Carrier D →ₗ[ℂ] Carrier D => f v)
    (transportInverse_right D (representative D 0) (carry D hD (-c) c))
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hcancel
  rw [hcancel]

/-- The five ACTUAL arrows on matching four-factor generators. This computes
the coefficient before comparing it with k; v is an arbitrary carrier vector. -/
theorem nestedEvaluation_matching (c d : Discriminant D) (v : Carrier D)
    (ψ : Module.Dual ℂ (Multiplicity B d)) (φ : Module.Dual ℂ (Multiplicity A c))
    (x : Multiplicity A c) (y : Multiplicity B d) :
    (nestedEvaluation A B hD).linearMap
      (normalizedPair (targetModule (dualModule B) (dualModule A)) (targetModule A B)
        hD (-(c+d)) (c+d)
        (jAt (dualModule B) (dualModule A) hD (-(c+d)) ⟨(-d,-c),by abel⟩
          (dualIota B d ψ ⊗ₜ[ℂ] dualIota A c φ) ⊗ₜ[ℂ] j A B hD c d (x ⊗ₜ[ℂ] y)) v) =
      (unitCharacter D hD (-(c+d)) * k hD c d * φ x * ψ y) •
        transport D 0 (zeroCarry D hD) v := by
  let f0 := (associatorIso (dualModule B) (dualModule A) (targetModule A B) hD).hom.linearMap
  let f1 := (productHom hD (ModuleHom.id (dualModule B))
    (associatorIso (dualModule A) A B hD).inv).linearMap
  let f2 := (productHom hD (ModuleHom.id (dualModule B))
    (productHom hD (evaluation A hD) (ModuleHom.id B))).linearMap
  let f3 := (productHom hD (ModuleHom.id (dualModule B)) (leftUnitIso hD B).hom).linearMap
  let f4 := (evaluation B hD).linearMap
  let z0 := normalizedPair (targetModule (dualModule B) (dualModule A)) (targetModule A B)
    hD (-(c+d)) (c+d)
    (jAt (dualModule B) (dualModule A) hD (-(c+d)) ⟨(-d,-c),by abel⟩
      (dualIota B d ψ ⊗ₜ[ℂ] dualIota A c φ) ⊗ₜ[ℂ] j A B hD c d (x ⊗ₜ[ℂ] y)) v
  let z1 := normalizedPair (dualModule B) (targetModule (dualModule A) (targetModule A B))
    hD (-d) d
    (dualIota B d ψ ⊗ₜ[ℂ]
      jAt (dualModule A) (targetModule A B) hD d ⟨(-c,c+d),by abel⟩
        (dualIota A c φ ⊗ₜ[ℂ] j A B hD c d (x ⊗ₜ[ℂ] y))) v
  let z2 := normalizedPair (dualModule B) (targetModule (targetModule (dualModule A) A) B)
    hD (-d) d
    (dualIota B d ψ ⊗ₜ[ℂ]
      jAt (targetModule (dualModule A) A) B hD d ⟨(0,d),zero_add d⟩
        (jAt (dualModule A) A hD 0 ⟨(-c,c),neg_add_cancel c⟩
          (dualIota A c φ ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] y)) v
  let z3 := normalizedPair (dualModule B) (targetModule (I D) B) hD (-d) d
    (dualIota B d ψ ⊗ₜ[ℂ]
      jAt (I D) B hD d ⟨(0,d),zero_add d⟩ (eta0 hD ⊗ₜ[ℂ] y)) v
  let z4 := normalizedPair (dualModule B) B hD (-d) d
    (dualIota B d ψ ⊗ₜ[ℂ] y) v
  let z5 := transport D 0 (zeroCarry D hD) v
  have h0 : f0 z0 = F hD (-d) (-c) (c+d) • z1 := by
    change alpha (dualModule B) (dualModule A) (targetModule A B) hD z0 = _
    exact alpha_normalized_fibers (dualModule B) (dualModule A) (targetModule A B) hD
      (-d) (-c) (c+d) (-(c+d)) d (by abel) (by abel)
        v (dualIota B d ψ) (dualIota A c φ) (j A B hD c d (x ⊗ₜ[ℂ] y))
  have h1 : f1 z1 = (F hD (-c) c d)⁻¹ • z2 := by
    dsimp only [f1, z1, z2]
    simpa only [TensorProduct.map_tmul, restrict_identity,
      restrict_inverse_cap_associator, TensorProduct.tmul_smul, normalizedPair_smul] using
      (normalizedPair_input hD (ModuleHom.id (dualModule B))
        (associatorIso (dualModule A) A B hD).inv (-d) d
        (dualIota B d ψ ⊗ₜ[ℂ]
          jAt (dualModule A) (targetModule A B) hD d ⟨(-c,c+d),by abel⟩
            (dualIota A c φ ⊗ₜ[ℂ] j A B hD c d (x ⊗ₜ[ℂ] y))) v)
  have h2 : f2 z2 = (unitCharacter D hD (-c) * φ x) • z3 := by
    let capx := jAt (dualModule A) A hD 0 ⟨(-c,c),neg_add_cancel c⟩
      (dualIota A c φ ⊗ₜ[ℂ] x)
    let oldx := jAt (targetModule (dualModule A) A) B hD d ⟨(0,d),zero_add d⟩
      (capx ⊗ₜ[ℂ] y)
    let T := restrict (productHom hD (evaluation A hD) (ModuleHom.id B)) d
    let J := jAt (I D) B hD d ⟨(0,d),zero_add d⟩
    let q := unitCharacter D hD (-c) * φ x
    let N (w : PairMultiplicity (dualModule B) (targetModule (I D) B) (-d,d)) :=
      normalizedPair (dualModule B) (targetModule (I D) B) hD (-d) d w v
    have hp := normalizedPair_input hD (ModuleHom.id (dualModule B))
      (productHom hD (evaluation A hD) (ModuleHom.id B)) (-d) d
      (dualIota B d ψ ⊗ₜ[ℂ] oldx) v
    have houtermap := TensorProduct.map_tmul
      (restrict (ModuleHom.id (dualModule B)) (-d)) T (dualIota B d ψ) oldx
    have houterid := congrArg₂ (fun p t => p ⊗ₜ[ℂ] t)
      (restrict_identity (-d) (dualIota B d ψ)) (Eq.refl (T oldx))
    have he := jAt_natural hD (evaluation A hD) (ModuleHom.id B) d
      (⟨(0,d),zero_add d⟩ : Fiber (D := D) d) (capx ⊗ₜ[ℂ] y)
    have hmap := TensorProduct.map_tmul (restrict (evaluation A hD) 0)
      (restrict (ModuleHom.id B) d) capx y
    have hcoords := congrArg₂ (fun p t => p ⊗ₜ[ℂ] t)
      (evaluation_jAt A hD c φ x) (restrict_identity d y)
    have hscalar := (congrArg J (TensorProduct.smul_tmul' (R := ℂ) q (eta0 hD) y).symm).trans
      (J.map_smul q (eta0 hD ⊗ₜ[ℂ] y))
    have hinner := he.trans ((congrArg J (hmap.trans hcoords)).trans hscalar)
    have houter := (congrArg N
      (TensorProduct.tmul_smul (R := ℂ) q (dualIota B d ψ) (J (eta0 hD ⊗ₜ[ℂ] y)))).trans
      (normalizedPair_smul (dualModule B) (targetModule (I D) B) hD (-d) d q
        (dualIota B d ψ ⊗ₜ[ℂ] J (eta0 hD ⊗ₜ[ℂ] y)) v)
    exact hp.trans ((congrArg N (houtermap.trans houterid)).trans
      ((congrArg (fun t => N (dualIota B d ψ ⊗ₜ[ℂ] t)) hinner).trans houter))
  have h3 : f3 z3 = z4 := by
    let t := jAt (I D) B hD d ⟨(0,d),zero_add d⟩ (eta0 hD ⊗ₜ[ℂ] y)
    let N (w : PairMultiplicity (dualModule B) B (-d,d)) :=
      normalizedPair (dualModule B) B hD (-d) d w v
    have hp := normalizedPair_input hD (ModuleHom.id (dualModule B))
      (leftUnitIso hD B).hom (-d) d (dualIota B d ψ ⊗ₜ[ℂ] t) v
    have hm := TensorProduct.map_tmul (restrict (ModuleHom.id (dualModule B)) (-d))
      (restrict (leftUnitIso hD B).hom d) (dualIota B d ψ) t
    have hc := congrArg₂ (fun p q => p ⊗ₜ[ℂ] q)
      (restrict_identity (-d) (dualIota B d ψ))
      (restrict_leftUnit_jAt (hD := hD) (A := B) d y)
    exact hp.trans (congrArg N (hm.trans hc))
  have h4 : f4 z4 = (unitCharacter D hD (-d) * ψ y) • z5 := by
    exact evaluation_normalized hD B d ψ y v
  have hcalc {V0 : Type*} {V1 : Type*} {V2 : Type*}
      {V3 : Type*} {V4 : Type*} {V5 : Type*}
      [AddCommGroup V0] [Module ℂ V0] [AddCommGroup V1] [Module ℂ V1]
      [AddCommGroup V2] [Module ℂ V2] [AddCommGroup V3] [Module ℂ V3]
      [AddCommGroup V4] [Module ℂ V4] [AddCommGroup V5] [Module ℂ V5]
      (g0 : V0 →ₗ[ℂ] V1) (g1 : V1 →ₗ[ℂ] V2) (g2 : V2 →ₗ[ℂ] V3)
      (g3 : V3 →ₗ[ℂ] V4) (g4 : V4 →ₗ[ℂ] V5)
      (v0 : V0) (v1 : V1) (v2 : V2) (v3 : V3) (v4 : V4) (v5 : V5)
      (a0 a1 a2 a4 : ℂ)
      (q0 : g0 v0 = a0 • v1) (q1 : g1 v1 = a1 • v2)
      (q2 : g2 v2 = a2 • v3) (q3 : g3 v3 = v4) (q4 : g4 v4 = a4 • v5) :
      g4 (g3 (g2 (g1 (g0 v0)))) = (a0 * a1 * a2 * a4) • v5 := by
    simp only [q0, q1, q2, q3, q4, map_smul, smul_smul]
    congr 1 <;> ring
  unfold nestedEvaluation
  dsimp only [ModuleHom.comp, LinearMap.comp_apply]
  refine (hcalc f0 f1 f2 f3 f4 z0 z1 z2 z3 z4 z5
    (F hD (-d) (-c) (c+d)) ((F hD (-c) c d)⁻¹)
    (unitCharacter D hD (-c) * φ x) (unitCharacter D hD (-d) * ψ y)
    h0 h1 h2 h3 h4).trans ?_
  apply congrArg (fun a : ℂ => a • z5)
  rw [k_cap_coefficient]
  ring

/-- The left cap path on the SAME actual four-factor generator. -/
theorem tensorEvaluation_matching (c d : Discriminant D) (v : Carrier D)
    (ψ : Module.Dual ℂ (Multiplicity B d)) (φ : Module.Dual ℂ (Multiplicity A c))
    (x : Multiplicity A c) (y : Multiplicity B d) :
    ((evaluation (targetModule A B) hD).comp
      (productHom hD (dualTensorHom A B hD) (ModuleHom.id (targetModule A B)))).linearMap
      (normalizedPair (targetModule (dualModule B) (dualModule A)) (targetModule A B)
        hD (-(c+d)) (c+d)
        (jAt (dualModule B) (dualModule A) hD (-(c+d)) ⟨(-d,-c),by abel⟩
          (dualIota B d ψ ⊗ₜ[ℂ] dualIota A c φ) ⊗ₜ[ℂ] j A B hD c d (x ⊗ₜ[ℂ] y)) v) =
      (nestedEvaluation A B hD).linearMap
        (normalizedPair (targetModule (dualModule B) (dualModule A)) (targetModule A B)
          hD (-(c+d)) (c+d)
          (jAt (dualModule B) (dualModule A) hD (-(c+d)) ⟨(-d,-c),by abel⟩
            (dualIota B d ψ ⊗ₜ[ℂ] dualIota A c φ) ⊗ₜ[ℂ] j A B hD c d (x ⊗ₜ[ℂ] y)) v) := by
  calc
    _ = (k hD c d * (unitCharacter D hD (-(c+d)) *
        Xi A B hD (c+d) ⟨(c,d),rfl⟩ (ψ ⊗ₜ[ℂ] φ)
          (j A B hD c d (x ⊗ₜ[ℂ] y)))) •
            transport D 0 (zeroCarry D hD) v := by
      dsimp only [ModuleHom.comp, LinearMap.comp_apply]
      simp only [normalizedPair_input, TensorProduct.map_tmul, dualTensorHom_jAt]
      simp only [restrict_identity]
      simp only [← TensorProduct.smul_tmul', normalizedPair_smul, map_smul,
        evaluation_normalized, smul_smul]
    _ = (unitCharacter D hD (-(c+d)) * k hD c d * φ x * ψ y) •
        transport D 0 (zeroCarry D hD) v := by
      have hx := Xi_jAt A B hD (c+d) ⟨(c,d),rfl⟩ (ψ ⊗ₜ[ℂ] φ) (x ⊗ₜ[ℂ] y)
      dsimp only [jAt] at hx
      rw [hx, reversePairing_tmul]
      congr 1
      ring
    _ = _ := (nestedEvaluation_matching A B hD c d v ψ φ x y).symm

end ActualFibers
section Naturality
variable {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable [AddCommGroup X'] [Module ℂ X'] [AddCommGroup Y'] [Module ℂ Y']
variable {A : FullJacobiLatticeModule D X} {B : FullJacobiLatticeModule D Y}
variable {A' : FullJacobiLatticeModule D X'} {B' : FullJacobiLatticeModule D Y'}
variable (hD : (gramReal D).PosDef)

private theorem fiberRead_natural (f : ModuleHom A A') (g : ModuleHom B B')
    (s : Discriminant D) (i : Fiber (D := D) s) (z : Multiplicity (targetModule A B) s) :
    fiberRead A' B' hD s i (restrict (productHom hD f g) s z) =
      TensorProduct.map (restrict f i.val.1) (restrict g i.val.2) (fiberRead A B hD s i z) := by
  change mu A' B' hD s (restrict (productHom hD f g) s z) i = _
  rw [mu_natural]
  rfl

/-- Independent-universe naturality reads the identical individual pair fiber. -/
theorem Xi_natural (f : ModuleHom A A') (g : ModuleHom B B')
    (s : Discriminant D) (i : Fiber (D := D) s)
    (ψ : Module.Dual ℂ (Multiplicity B' i.val.2))
    (φ : Module.Dual ℂ (Multiplicity A' i.val.1))
    (z : Multiplicity (targetModule A B) s) :
    Xi A B hD s i (ψ.comp (restrict g i.val.2) ⊗ₜ[ℂ] φ.comp (restrict f i.val.1)) z =
      Xi A' B' hD s i (ψ ⊗ₜ[ℂ] φ) (restrict (productHom hD f g) s z) := by
  change reversePairing _ (fiberRead A B hD s i z) =
    reversePairing _ (fiberRead A' B' hD s i (restrict (productHom hD f g) s z))
  rw [fiberRead_natural, reversePairing_map]

private theorem kappa_dualHom (f : ModuleHom A A') (s : Discriminant D)
    (z : Multiplicity (dualModule A') s) :
    kappa (DualMultiplicity A) s (restrict (dualHom hD f) s z) =
      (kappa (DualMultiplicity A') s z).comp (restrict f (-s)) := by
  rw [dualHom, restrict_extend]
  simp only [LinearMap.comp_apply, kappa_iota]
  rfl

private theorem readFunctional_natural (f : ModuleHom A A') (g : ModuleHom B B')
    (s : Discriminant D) (i : Fiber (D := D) s)
    (w : PairMultiplicity (dualModule B') (dualModule A') i.val) :
    readFunctional A B hD s i
        (TensorProduct.map (restrict (dualHom hD g) i.val.1)
          (restrict (dualHom hD f) i.val.2) w) =
      (readFunctional A' B' hD s i w).comp (restrict (productHom hD f g) (-s)) := by
  induction w using TensorProduct.induction_on with
  | zero => ext z; simp [readFunctional]
  | add w w' hw hw' =>
      ext z
      simp only [map_add, LinearMap.add_apply, LinearMap.comp_apply, hw, hw']
  | tmul ψ φ =>
      simp only [readFunctional, LinearMap.comp_apply, TensorProduct.map_tmul,
        kappa_dualHom]
      apply LinearMap.ext
      intro z
      exact Xi_natural hD f g (-s) (reverseFiber s i)
        (kappa (DualMultiplicity B') i.val.1 ψ) (kappa (DualMultiplicity A') i.val.2 φ) z

/-- Equality of full original ModuleHom records; all four carrier universes
are independent, and no finite original multiplicity premise is used. -/
theorem dualTensorHom_natural (f : ModuleHom A A') (g : ModuleHom B B') :
    (dualHom hD (productHom hD f g)).comp (dualTensorHom A' B' hD) =
      (dualTensorHom A B hD).comp (productHom hD (dualHom hD g) (dualHom hD f)) := by
  apply (recordEquiv _ _).injective
  apply Subtype.ext
  apply DirectSum.linearMap_ext
  rintro ⟨r,t⟩
  apply TensorProduct.ext
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  change (dualHom hD (productHom hD f g)).linearMap
      ((dualTensorHom A' B' hD).linearMap
        (DirectSum.lof ℂ _ (PairSector (dualModule B') (dualModule A')) (r,t)
          (v ⊗ₜ[ℂ] w))) =
    (dualTensorHom A B hD).linearMap
      ((productHom hD (dualHom hD g) (dualHom hD f)).linearMap
        (DirectSum.lof ℂ _ (PairSector (dualModule B') (dualModule A')) (r,t)
          (v ⊗ₜ[ℂ] w)))
  let T := transport D (representative D (r+t)) (carry D hD r t) v
  let w0 := w
  let M := (dualHom hD (productHom hD f g)).linearMap
  let N := (dualTensorHom A B hD).linearMap
  have hl := congrArg M.toAddHom.toFun (dualTensorHom_pair A' B' hD r t v w0)
  have hl' := (M.map_smul (k hD (-t) (-r)) _).trans
    (congrArg (fun z => k hD (-t) (-r) • z)
      (dualHom_carrier hD (productHom hD f g) (r+t) T
        (readFunctional A' B' hD (r+t) ⟨(r,t),rfl⟩ w0)))
  have hr := congrArg N.toAddHom.toFun
    (productHom_pair hD (dualHom hD g) (dualHom hD f) r t v w0)
  have hr' := dualTensorHom_pair A B hD r t v
    (TensorProduct.map (restrict (dualHom hD g) r) (restrict (dualHom hD f) t) w0)
  have hn := readFunctional_natural hD f g (r+t) ⟨(r,t),rfl⟩ w0
  exact (hl.trans hl').trans ((hr.trans hr').trans
    (congrArg (fun φ => k hD (-t) (-r) •
      DirectSum.lof ℂ _ (fun s => Carrier D ⊗[ℂ] DualMultiplicity (targetModule A B) s)
        (r+t) (T ⊗ₜ[ℂ] φ)) hn)).symm

end Naturality

section FullCap
variable {X : Type u} {Y : Type v}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
variable (hD : (gramReal D).PosDef)

private theorem inverse_cap_associator_all (c a b : Discriminant D)
    (φ : Module.Dual ℂ (Multiplicity A c))
    (x : Multiplicity A a) (y : Multiplicity B b) :
    restrict (associatorIso (dualModule A) A B hD).inv (-c+(a+b))
      (j (dualModule A) (targetModule A B) hD (-c) (a+b)
        (dualIota A c φ ⊗ₜ[ℂ] j A B hD a b (x ⊗ₜ[ℂ] y))) =
      (F hD (-c) a b)⁻¹ •
        jAt (targetModule (dualModule A) A) B hD (-c+(a+b))
          ⟨(-c+a,b),add_assoc (-c) a b⟩
          (j (dualModule A) A hD (-c) a (dualIota A c φ ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] y) := by
  apply Subtype.ext
  apply Subtype.ext
  change alphaInverse (dualModule A) A B hD _ = _
  simpa only [jAt_val, j_val, ground, normalizedPair, LinearMap.comp_apply,
    LinearMap.flip_apply, TensorProduct.mk_apply, Submodule.coe_smul] using
    alphaInverse_normalized_fibers (dualModule A) A B hD (-c) a b (-c+a) (a+b)
      rfl rfl (Finsupp.single 0 (1 : Oscillator D)) (dualIota A c φ) x y

/-- Every mismatched individual A fiber vanishes in the five-arrow composite,
including when the two outer total charges cancel. -/
theorem nestedEvaluation_wrong_A (c d a b : Discriminant D) (ha : a ≠ c)
    (v : Carrier D) (ψ : Module.Dual ℂ (Multiplicity B d))
    (φ : Module.Dual ℂ (Multiplicity A c)) (x : Multiplicity A a) (y : Multiplicity B b) :
    (nestedEvaluation A B hD).linearMap
      (normalizedPair (targetModule (dualModule B) (dualModule A)) (targetModule A B)
        hD (-(c+d)) (a+b)
        (jAt (dualModule B) (dualModule A) hD (-(c+d)) ⟨(-d,-c),by abel⟩
          (dualIota B d ψ ⊗ₜ[ℂ] dualIota A c φ) ⊗ₜ[ℂ]
            j A B hD a b (x ⊗ₜ[ℂ] y)) v) = 0 := by
  have hz : -c+a ≠ 0 := by
    intro h
    apply ha
    have hh := congrArg (fun z => c+z) h
    simpa only [← add_assoc, add_neg_cancel, zero_add, add_zero] using hh
  unfold nestedEvaluation
  dsimp only [ModuleHom.comp, LinearMap.comp_apply]
  have hα := alpha_normalized_fibers (dualModule B) (dualModule A) (targetModule A B) hD
    (-d) (-c) (a+b) (-(c+d)) (-c+(a+b)) (by abel) rfl
      v (dualIota B d ψ) (dualIota A c φ) (j A B hD a b (x ⊗ₜ[ℂ] y))
  have hproj (z : LeftP (dualModule B) (dualModule A) (targetModule A B)) :
      (associatorIso (dualModule B) (dualModule A) (targetModule A B) hD).hom.linearMap z =
        alpha (dualModule B) (dualModule A) (targetModule A B) hD z := by
    rfl
  conv_lhs =>
    arg -1
    arg -1
    arg -1
    arg -1
    rw [hproj, hα]
  simp only [map_smul]
  rw [normalizedPair_input, TensorProduct.map_tmul, restrict_identity,
    inverse_cap_associator_all, TensorProduct.tmul_smul, normalizedPair_smul]
  simp only [map_smul]
  rw [normalizedPair_input, TensorProduct.map_tmul, restrict_identity,
    jAt_natural, TensorProduct.map_tmul, evaluation_wrong A hD (-c+a) hz]
  simp [normalizedPair]

/-- The other cross term: the inner A cap matches, but the B cap does not. -/
theorem nestedEvaluation_wrong_B (c d b : Discriminant D) (hb : b ≠ d)
    (v : Carrier D) (ψ : Module.Dual ℂ (Multiplicity B d))
    (φ : Module.Dual ℂ (Multiplicity A c)) (x : Multiplicity A c) (y : Multiplicity B b) :
    (nestedEvaluation A B hD).linearMap
      (normalizedPair (targetModule (dualModule B) (dualModule A)) (targetModule A B)
        hD (-(c+d)) (c+b)
        (jAt (dualModule B) (dualModule A) hD (-(c+d)) ⟨(-d,-c),by abel⟩
          (dualIota B d ψ ⊗ₜ[ℂ] dualIota A c φ) ⊗ₜ[ℂ]
            j A B hD c b (x ⊗ₜ[ℂ] y)) v) = 0 := by
  have hz : -d+b ≠ 0 := by
    intro h
    apply hb
    have hh := congrArg (fun z => d+z) h
    simpa only [← add_assoc, add_neg_cancel, zero_add, add_zero] using hh
  unfold nestedEvaluation
  dsimp only [ModuleHom.comp, LinearMap.comp_apply]
  have hα := alpha_normalized_fibers (dualModule B) (dualModule A) (targetModule A B) hD
    (-d) (-c) (c+b) (-(c+d)) b (by abel) (by abel)
      v (dualIota B d ψ) (dualIota A c φ) (j A B hD c b (x ⊗ₜ[ℂ] y))
  have hproj (z : LeftP (dualModule B) (dualModule A) (targetModule A B)) :
      (associatorIso (dualModule B) (dualModule A) (targetModule A B) hD).hom.linearMap z =
        alpha (dualModule B) (dualModule A) (targetModule A B) hD z := by
    rfl
  conv_lhs =>
    arg -1
    arg -1
    arg -1
    arg -1
    rw [hproj, hα]
  simp only [map_smul]
  rw [normalizedPair_input, TensorProduct.map_tmul, restrict_identity,
    restrict_inverse_cap_associator, TensorProduct.tmul_smul, normalizedPair_smul]
  simp only [map_smul]
  rw [normalizedPair_input, TensorProduct.map_tmul, restrict_identity,
    jAt_natural, TensorProduct.map_tmul, evaluation_jAt]
  simp only [restrict_identity]
  rw [← TensorProduct.smul_tmul', map_smul, TensorProduct.tmul_smul, normalizedPair_smul]
  simp only [map_smul]
  rw [normalizedPair_input, TensorProduct.map_tmul, restrict_identity, restrict_leftUnit_jAt]
  change _ • (_ • (_ • (evaluation B hD).linearMap
    (DirectSum.lof ℂ _ (PairSector (dualModule B) B) (-d,b)
      (transportInverse D (representative D (-d+b)) (carry D hD (-d) b) v ⊗ₜ[ℂ]
        (dualIota B d ψ ⊗ₜ[ℂ] y))))) = 0
  rw [evaluation_pair_wrong B hD (-d) b hz]
  simp

private theorem tensorEvaluation_wrong_total (c d a b : Discriminant D)
    (hs : -(c+d)+(a+b) ≠ 0) (v : Carrier D)
    (ψ : Module.Dual ℂ (Multiplicity B d)) (φ : Module.Dual ℂ (Multiplicity A c))
    (x : Multiplicity A a) (y : Multiplicity B b) :
    ((evaluation (targetModule A B) hD).comp
      (productHom hD (dualTensorHom A B hD) (ModuleHom.id (targetModule A B)))).linearMap
      (normalizedPair (targetModule (dualModule B) (dualModule A)) (targetModule A B)
        hD (-(c+d)) (a+b)
        (jAt (dualModule B) (dualModule A) hD (-(c+d)) ⟨(-d,-c),by abel⟩
          (dualIota B d ψ ⊗ₜ[ℂ] dualIota A c φ) ⊗ₜ[ℂ]
            j A B hD a b (x ⊗ₜ[ℂ] y)) v) = 0 := by
  change (evaluation (targetModule A B) hD).linearMap
    ((productHom hD (dualTensorHom A B hD) (ModuleHom.id (targetModule A B))).linearMap _) = 0
  rw [normalizedPair_input, TensorProduct.map_tmul, dualTensorHom_jAt, restrict_identity,
    ← TensorProduct.smul_tmul', normalizedPair_smul, map_smul]
  change k hD c d • (evaluation (targetModule A B) hD).linearMap
    (DirectSum.lof ℂ _ (PairSector (dualModule (targetModule A B)) (targetModule A B))
      (-(c+d),a+b) (_ ⊗ₜ[ℂ] _)) = 0
  rw [evaluation_pair_wrong (targetModule A B) hD (-(c+d)) (a+b) hs]
  simp

private theorem tensorEvaluation_wrong_fiber (c d : Discriminant D)
    (i : Fiber (D := D) (c+d)) (hi : i ≠ ⟨(c,d),rfl⟩)
    (v : Carrier D) (ψ : Module.Dual ℂ (Multiplicity B d))
    (φ : Module.Dual ℂ (Multiplicity A c)) (w : PairMultiplicity A B i.val) :
    ((evaluation (targetModule A B) hD).comp
      (productHom hD (dualTensorHom A B hD) (ModuleHom.id (targetModule A B)))).linearMap
      (normalizedPair (targetModule (dualModule B) (dualModule A)) (targetModule A B)
        hD (-(c+d)) (c+d)
        (jAt (dualModule B) (dualModule A) hD (-(c+d)) ⟨(-d,-c),by abel⟩
          (dualIota B d ψ ⊗ₜ[ℂ] dualIota A c φ) ⊗ₜ[ℂ] jAt A B hD (c+d) i w) v) = 0 := by
  change (evaluation (targetModule A B) hD).linearMap
    ((productHom hD (dualTensorHom A B hD) (ModuleHom.id (targetModule A B))).linearMap _) = 0
  rw [normalizedPair_input, TensorProduct.map_tmul, dualTensorHom_jAt, restrict_identity,
    ← TensorProduct.smul_tmul', normalizedPair_smul, map_smul, evaluation_normalized,
    Xi_jAt_wrong A B hD (c+d) ⟨(c,d),rfl⟩ i hi]
  simp

/-- The full four-factor comparison: no matching-fiber hypothesis is present. -/
theorem tensorEvaluation_four (c d a b : Discriminant D)
    (v : Carrier D) (ψ : Module.Dual ℂ (Multiplicity B d))
    (φ : Module.Dual ℂ (Multiplicity A c)) (x : Multiplicity A a) (y : Multiplicity B b) :
    ((evaluation (targetModule A B) hD).comp
      (productHom hD (dualTensorHom A B hD) (ModuleHom.id (targetModule A B)))).linearMap
      (normalizedPair (targetModule (dualModule B) (dualModule A)) (targetModule A B)
        hD (-(c+d)) (a+b)
        (jAt (dualModule B) (dualModule A) hD (-(c+d)) ⟨(-d,-c),by abel⟩
          (dualIota B d ψ ⊗ₜ[ℂ] dualIota A c φ) ⊗ₜ[ℂ]
            j A B hD a b (x ⊗ₜ[ℂ] y)) v) =
    (nestedEvaluation A B hD).linearMap
      (normalizedPair (targetModule (dualModule B) (dualModule A)) (targetModule A B)
        hD (-(c+d)) (a+b)
        (jAt (dualModule B) (dualModule A) hD (-(c+d)) ⟨(-d,-c),by abel⟩
          (dualIota B d ψ ⊗ₜ[ℂ] dualIota A c φ) ⊗ₜ[ℂ]
            j A B hD a b (x ⊗ₜ[ℂ] y)) v) := by
  by_cases ha : a = c
  · subst a
    by_cases hb : b = d
    · subst b
      exact tensorEvaluation_matching A B hD c d v ψ φ x y
    · rw [nestedEvaluation_wrong_B A B hD c d b hb]
      apply tensorEvaluation_wrong_total
      intro h
      apply hb
      have hh := congrArg (fun z => (c+d)+z) h
      have he : c+b = c+d := by simpa only [← add_assoc, add_neg_cancel, zero_add, add_zero] using hh
      exact add_left_cancel he
  · rw [nestedEvaluation_wrong_A A B hD c d a b ha]
    by_cases hs : a+b = c+d
    · have hi : (⟨(a,b),hs⟩ : Fiber (D := D) (c+d)) ≠ ⟨(c,d),rfl⟩ := by
        intro h
        exact ha (congrArg (fun i : Fiber (D := D) (c+d) => i.val.1) h)
      have hh := tensorEvaluation_wrong_fiber A B hD c d ⟨(a,b),hs⟩ hi v ψ φ (x ⊗ₜ[ℂ] y)
      simpa only [jAt, hs] using hh
    · apply tensorEvaluation_wrong_total
      intro h
      apply hs
      calc
        a+b = (c+d)+ (-(c+d)+(a+b)) := by abel
        _ = c+d := by rw [h, add_zero]

/-- Exhaustion of an ORIGINAL product multiplicity by all of its jAt fibers. -/
private theorem multiplicity_induction (s : Discriminant D)
    (Q : Multiplicity (targetModule A B) s → Prop) (h0 : Q 0)
    (ha : ∀ x y, Q x → Q y → Q (x+y))
    (hj : ∀ i x y, Q (jAt A B hD s i (x ⊗ₜ[ℂ] y)))
    (z : Multiplicity (targetModule A B) s) : Q z := by
  have he : ∀ t : FiberSum A B s, Q (nu A B hD s t) := by
    intro t
    induction t using DirectSum.induction_on with
    | zero => simpa only [map_zero] using h0
    | add t t' ht ht' => simpa only [map_add] using ha _ _ ht ht'
    | of i w =>
      change Q (nu A B hD s (DirectSum.lof ℂ _ _ i w))
      rw [nu_lof]
      induction w using TensorProduct.induction_on with
      | zero => simpa only [map_zero] using h0
      | add w w' hw hw' => simpa only [map_add] using ha _ _ hw hw'
      | tmul x y => exact hj i x y
  simpa only [nu_mu] using he (mu A B hD s z)

/-- Equality of the FULL original ModuleHom records. Both inner multiplicities
are exhausted independently; equal total charge never identifies pair fibers. -/
theorem dualTensorHom_evaluation :
    (evaluation (targetModule A B) hD).comp
      (productHom hD (dualTensorHom A B hD) (ModuleHom.id (targetModule A B))) =
        nestedEvaluation A B hD := by
  apply (recordEquiv _ _).injective
  apply Subtype.ext
  apply DirectSum.linearMap_ext
  rintro ⟨r,s⟩
  apply TensorProduct.ext
  intro v w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w w' hw hw' => simp only [TensorProduct.tmul_add, map_add, hw, hw']
  | tmul z t =>
    apply multiplicity_induction (dualModule B) (dualModule A) hD r
      (fun z => ((evaluation (targetModule A B) hD).comp
          (productHom hD (dualTensorHom A B hD) (ModuleHom.id (targetModule A B)))).linearMap
        (DirectSum.lof ℂ _ _ (r,s) (v ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] t))) =
        (nestedEvaluation A B hD).linearMap
          (DirectSum.lof ℂ _ _ (r,s) (v ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] t))))
      (by simp) (fun z z' hz hz' => by
        simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hz, hz']) ?_ z
    rintro ⟨⟨r₁,r₂⟩,hr⟩ ψ φ
    subst r
    apply multiplicity_induction A B hD s
      (fun t => ((evaluation (targetModule A B) hD).comp
          (productHom hD (dualTensorHom A B hD) (ModuleHom.id (targetModule A B)))).linearMap
        (DirectSum.lof ℂ _ _ (r₁+r₂,s)
          (v ⊗ₜ[ℂ] (j (dualModule B) (dualModule A) hD r₁ r₂ (ψ ⊗ₜ[ℂ] φ) ⊗ₜ[ℂ] t))) =
        (nestedEvaluation A B hD).linearMap
          (DirectSum.lof ℂ _ _ (r₁+r₂,s)
            (v ⊗ₜ[ℂ] (j (dualModule B) (dualModule A) hD r₁ r₂ (ψ ⊗ₜ[ℂ] φ) ⊗ₜ[ℂ] t))))
      (by simp) (fun t t' ht ht' => by
        simp only [TensorProduct.tmul_add, map_add, ht, ht']) ?_ t
    rintro ⟨⟨a,b⟩,hs⟩ x y
    subst s
    obtain ⟨ψ,rfl⟩ :=
      (ActualWeakModuleRealization.multiplicityEquiv (DualMultiplicity B) hD r₁).symm.surjective ψ
    obtain ⟨φ,rfl⟩ :=
      (ActualWeakModuleRealization.multiplicityEquiv (DualMultiplicity A) hD r₂).symm.surjective φ
    have hh := tensorEvaluation_four A B hD (-r₂) (-r₁) a b
      (transport D (representative D ((r₁+r₂)+(a+b)))
        (carry D hD (r₁+r₂) (a+b)) v) ψ φ x y
    simpa only [dualIota, jAt, neg_add, neg_neg, add_comm r₂ r₁,
      normalizedPair_transport] using hh

end FullCap

section FiniteInverse
variable {X : Type u} {Y : Type v}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
variable (hD : (gramReal D).PosDef)

private theorem reverseFiber_injective (s : Discriminant D) :
    Function.Injective (reverseFiber (D := D) s) := by
  intro i j hij
  apply Subtype.ext
  apply Prod.ext
  · have h := congrArg (fun z : Fiber (D := D) (-s) => -z.val.2) hij
    simpa only [reverseFiber, neg_neg] using h
  · have h := congrArg (fun z : Fiber (D := D) (-s) => -z.val.1) hij
    simpa only [reverseFiber, neg_neg] using h

/-- ALL pair fibers, finite because of the original positive Gram matrix. -/
def fiberSupport (s : Discriminant D) : Finset (Fiber (D := D) s) := by
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  letI := Fintype.ofFinite (Fiber (D := D) s)
  exact Finset.univ

@[simp] theorem mem_fiberSupport (s : Discriminant D) (i : Fiber (D := D) s) :
    i ∈ fiberSupport hD s := by
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  letI := Fintype.ofFinite (Fiber (D := D) s)
  simp [fiberSupport]

/-- An extensionality principle on the actual multiplicity, using mu/nu. -/
private theorem multiplicity_linear_ext {T : Type u'} [AddCommGroup T] [Module ℂ T]
    (s : Discriminant D)
    (f g : Multiplicity (targetModule A B) s →ₗ[ℂ] T)
    (h : ∀ i w, f (jAt A B hD s i w) = g (jAt A B hD s i w)) : f = g := by
  have he : f.comp (nu A B hD s) = g.comp (nu A B hD s) := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro w
    simpa only [LinearMap.comp_apply, nu_lof] using h i w
  apply LinearMap.ext
  intro z
  have hz := LinearMap.congr_fun he (mu A B hD s z)
  simpa only [LinearMap.comp_apply, nu_mu] using hz

variable [∀ c : Discriminant D, Module.Finite ℂ (Multiplicity A c)]
variable [∀ c : Discriminant D, Module.Finite ℂ (Multiplicity B c)]

/-- Finite reversed pairing after the two ACTUAL kappa equivalences.
Only the original A/B multiplicities are finite. -/
def finiteReverseBlock (s : Discriminant D) (i : Fiber (D := D) s) :
    PairMultiplicity (dualModule B) (dualModule A) i.val ≃ₗ[ℂ]
      Module.Dual ℂ (PairMultiplicity A B (reverseFiber s i).val) :=
  (TensorProduct.congr
    (ActualWeakModuleRealization.multiplicityEquiv (DualMultiplicity B) hD i.val.1)
    (ActualWeakModuleRealization.multiplicityEquiv (DualMultiplicity A) hD i.val.2)).trans
  ((TensorProduct.comm ℂ (DualMultiplicity B i.val.1) (DualMultiplicity A i.val.2)).trans
    (TensorProduct.dualDistribEquiv ℂ (Multiplicity A (-i.val.2))
      (Multiplicity B (-i.val.1))))

private theorem finiteReverseBlock_apply (s : Discriminant D) (i : Fiber (D := D) s)
    (w : PairMultiplicity (dualModule B) (dualModule A) i.val) :
    finiteReverseBlock A B hD s i w =
      reversePairing (TensorProduct.map (kappa (DualMultiplicity B) i.val.1)
        (kappa (DualMultiplicity A) i.val.2) w) := by
  change (TensorProduct.dualDistribEquiv ℂ _ _).toLinearMap _ = _
  rw [TensorProduct.toLinearMap_dualDistribEquiv]
  rfl

private theorem finiteReverseBlock_symm (s : Discriminant D) (i : Fiber (D := D) s)
    (Λ : Module.Dual ℂ (PairMultiplicity A B (reverseFiber s i).val)) :
    (finiteReverseBlock A B hD s i).symm Λ =
      TensorProduct.map (iota (DualMultiplicity B) i.val.1)
        (iota (DualMultiplicity A) i.val.2)
        ((TensorProduct.comm ℂ (DualMultiplicity B i.val.1)
          (DualMultiplicity A i.val.2)).symm
          ((TensorProduct.dualDistribEquiv ℂ (Multiplicity A (-i.val.2))
            (Multiplicity B (-i.val.1))).symm Λ)) := by
  rfl

private theorem readFunctional_same (s : Discriminant D) (i : Fiber (D := D) s)
    (w : PairMultiplicity (dualModule B) (dualModule A) i.val) :
    (readFunctional A B hD s i w).comp (jAt A B hD (-s) (reverseFiber s i)) =
      finiteReverseBlock A B hD s i w := by
  apply LinearMap.ext
  intro z
  change Xi A B hD (-s) (reverseFiber s i) _
    (jAt A B hD (-s) (reverseFiber s i) z) = _
  rw [Xi_jAt, finiteReverseBlock_apply]

private theorem readFunctional_other (s : Discriminant D) (i j : Fiber (D := D) s)
    (hij : j ≠ i) (w : PairMultiplicity (dualModule B) (dualModule A) i.val) :
    (readFunctional A B hD s i w).comp (jAt A B hD (-s) (reverseFiber s j)) = 0 := by
  apply LinearMap.ext
  intro z
  exact Xi_jAt_wrong A B hD (-s) (reverseFiber s i) (reverseFiber s j)
    (fun h => hij (reverseFiber_injective s h)) _ z

/-- Explicit inverse on a single component: restriction of the functional to
EVERY reversed fiber, inverse finite pairing, inverse coefficient, actual jAt. -/
def dualTensorInverseComponent (s : Discriminant D) :
    DualMultiplicity (targetModule A B) s →ₗ[ℂ]
      Multiplicity (targetModule (dualModule B) (dualModule A)) s :=
  ∑ i ∈ fiberSupport hD s,
    (k hD (-i.val.2) (-i.val.1))⁻¹ •
      (jAt (dualModule B) (dualModule A) hD s i).comp
        ((finiteReverseBlock A B hD s i).symm.toLinearMap.comp
          (jAt A B hD (-s) (reverseFiber s i)).dualMap)

private theorem dualTensorInverseComponent_block (s : Discriminant D)
    (i : Fiber (D := D) s)
    (w : PairMultiplicity (dualModule B) (dualModule A) i.val) :
    dualTensorInverseComponent A B hD s (readFunctional A B hD s i w) =
      (k hD (-i.val.2) (-i.val.1))⁻¹ •
        jAt (dualModule B) (dualModule A) hD s i w := by
  simp only [dualTensorInverseComponent, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.dualMap_apply']
  rw [Finset.sum_eq_single i]
  · rw [readFunctional_same, LinearEquiv.symm_apply_apply]
  · intro j hj hji
    rw [readFunctional_other A B hD s i j hji]
    simp
  · simp

def dualTensorInverseFamily :
    Families (dualModule (targetModule A B)) (targetModule (dualModule B) (dualModule A)) :=
  fun s => (dualTensorInverseComponent A B hD s).comp
    (kappa (DualMultiplicity (targetModule A B)) s)

def dualTensorInverseHom :
    ModuleHom (dualModule (targetModule A B)) (targetModule (dualModule B) (dualModule A)) :=
  extend hD (dualTensorInverseFamily A B hD)

private theorem dualTensorFamily_left (s : Discriminant D)
    (z : Multiplicity (targetModule (dualModule B) (dualModule A)) s) :
    dualTensorInverseFamily A B hD s (dualTensorFamily A B hD s z) = z := by
  have he : (dualTensorInverseFamily A B hD s).comp (dualTensorFamily A B hD s) =
      LinearMap.id := by
    apply multiplicity_linear_ext (dualModule B) (dualModule A) hD s
    intro i w
    simp only [LinearMap.comp_apply, dualTensorFamily_jAt, dualTensorInverseFamily,
      LinearMap.comp_apply, map_smul, kappa_iota, dualTensorInverseComponent_block,
      smul_smul, mul_inv_cancel₀ (k_nonzero hD _ _), one_smul, LinearMap.id_apply]
  exact LinearMap.congr_fun he z

private theorem dualTensorFamily_right (s : Discriminant D)
    (z : Multiplicity (dualModule (targetModule A B)) s) :
    dualTensorFamily A B hD s (dualTensorInverseFamily A B hD s z) = z := by
  apply (ActualWeakModuleRealization.multiplicityEquiv
    (DualMultiplicity (targetModule A B)) hD s).injective
  let Λ := kappa (DualMultiplicity (targetModule A B)) s z
  change kappa (DualMultiplicity (targetModule A B)) s
    (dualTensorFamily A B hD s (dualTensorInverseComponent A B hD s Λ)) = Λ
  simp only [dualTensorInverseComponent, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.dualMap_apply', map_sum, map_smul,
    dualTensorFamily_jAt, kappa_iota, smul_smul,
    inv_mul_cancel₀ (k_nonzero hD _ _), one_smul]
  have he : (∑ i ∈ fiberSupport hD s,
      readFunctional A B hD s i
        ((finiteReverseBlock A B hD s i).symm
          (Λ.comp (jAt A B hD (-s) (reverseFiber s i))))) = Λ := by
    apply multiplicity_linear_ext A B hD (-s)
    intro j w
    let i : Fiber (D := D) s := ⟨(-j.val.2,-j.val.1), by rw [← j.property]; abel⟩
    have hi : reverseFiber s i = j := by
      apply Subtype.ext
      simp only [reverseFiber, i, neg_neg]
    simp only [LinearMap.sum_apply]
    rw [Finset.sum_eq_single i]
    · rw [← hi]
      have hm := LinearMap.congr_fun
        (readFunctional_same A B hD s i
          ((finiteReverseBlock A B hD s i).symm
            (Λ.comp (jAt A B hD (-s) (reverseFiber s i))))) w
      simpa only [LinearMap.comp_apply, LinearEquiv.apply_symm_apply, hi] using hm
    · intro t ht hti
      have hn : i ≠ t := Ne.symm hti
      have hz := LinearMap.congr_fun
        (readFunctional_other A B hD s t i hn
          ((finiteReverseBlock A B hD s t).symm
            (Λ.comp (jAt A B hD (-s) (reverseFiber s t))))) w
      simpa only [LinearMap.comp_apply, hi, LinearMap.zero_apply] using hz
    · simp
  exact he

/-- Both inverse laws on ALL original vectors, by the actual classification
equivalences. No oscillator/carrier/P finiteness is used. -/
private theorem inverse_extend_apply
    (s : P (dualModule B) (dualModule A)) :
    (dualTensorInverseHom A B hD).linearMap ((dualTensorHom A B hD).linearMap s) = s := by
  have hm : (familyMap (dualTensorInverseFamily A B hD)).comp
      (familyMap (dualTensorFamily A B hD)) = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro c
    apply TensorProduct.ext
    intro v w
    simp only [LinearMap.comp_apply, familyMap, DirectSum.lmap_lof,
      TensorProduct.map_tmul, LinearMap.id_apply, dualTensorFamily_left]
  change classificationEquiv (targetModule (dualModule B) (dualModule A)) hD
    (familyMap (dualTensorInverseFamily A B hD)
      ((classificationEquiv (dualModule (targetModule A B)) hD).symm
        (classificationEquiv (dualModule (targetModule A B)) hD
          (familyMap (dualTensorFamily A B hD)
            ((classificationEquiv (targetModule (dualModule B) (dualModule A)) hD).symm s))))) = s
  rw [LinearEquiv.symm_apply_apply, ← LinearMap.comp_apply, hm,
    LinearMap.id_apply, LinearEquiv.apply_symm_apply]

private theorem extend_inverse_apply_full (s : DualCarrier (targetModule A B)) :
    (dualTensorHom A B hD).linearMap ((dualTensorInverseHom A B hD).linearMap s) = s := by
  have hm : (familyMap (dualTensorFamily A B hD)).comp
      (familyMap (dualTensorInverseFamily A B hD)) = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro c
    apply TensorProduct.ext
    intro v w
    simp only [LinearMap.comp_apply, familyMap, DirectSum.lmap_lof,
      TensorProduct.map_tmul, LinearMap.id_apply, dualTensorFamily_right]
  change classificationEquiv (dualModule (targetModule A B)) hD
    (familyMap (dualTensorFamily A B hD)
      ((classificationEquiv (targetModule (dualModule B) (dualModule A)) hD).symm
        (classificationEquiv (targetModule (dualModule B) (dualModule A)) hD
          (familyMap (dualTensorInverseFamily A B hD)
            ((classificationEquiv (dualModule (targetModule A B)) hD).symm s))))) = s
  rw [LinearEquiv.symm_apply_apply, ← LinearMap.comp_apply, hm,
    LinearMap.id_apply, LinearEquiv.apply_symm_apply]

def dualTensorIso :
    ModuleIso (targetModule (dualModule B) (dualModule A)) (dualModule (targetModule A B)) where
  linearEquiv :=
    { toLinearMap := (dualTensorHom A B hD).linearMap
      invFun := (dualTensorInverseHom A B hD).linearMap
      left_inv := inverse_extend_apply A B hD
      right_inv := extend_inverse_apply_full A B hD }
  intertwines := (dualTensorHom A B hD).intertwines

/-- Literal all-fiber carrier inverse, with no selected-fiber premise. -/
theorem dualTensorInverseHom_carrier (s : Discriminant D) (v : Carrier D)
    (Λ : DualMultiplicity (targetModule A B) s) :
    (dualTensorInverseHom A B hD).linearMap
      (DirectSum.lof ℂ _ (fun t => Carrier D ⊗[ℂ] DualMultiplicity (targetModule A B) t)
        s (v ⊗ₜ[ℂ] Λ)) =
      ∑ i ∈ fiberSupport hD s, (k hD (-i.val.2) (-i.val.1))⁻¹ •
        DirectSum.lof ℂ _ (PairSector (dualModule B) (dualModule A)) i.val
          (transportInverse D (representative D s) (carry D hD i.val.1 i.val.2) v ⊗ₜ[ℂ]
            (finiteReverseBlock A B hD s i).symm
              (Λ.comp (jAt A B hD (-s) (reverseFiber s i)))) := by
  rw [← classification_iota (DualMultiplicity (targetModule A B)) hD s Λ v,
    classified_natural, dualTensorInverseHom, restrict_extend]
  simp only [dualTensorInverseFamily, LinearMap.comp_apply, kappa_iota,
    dualTensorInverseComponent, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.dualMap_apply', classified, TensorProduct.tmul_sum,
    TensorProduct.tmul_smul, map_sum, map_smul, LinearMap.comp_apply,
    LinearMap.flip_apply, TensorProduct.mk_apply]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rcases i with ⟨⟨r,t⟩,hrt⟩
  subst s
  exact classification_j (dualModule B) (dualModule A) hD r t _ v

/-- The reciprocal epsilon from the actual inverse carry is retained. -/
theorem dualTensorInverseHom_single (s : Discriminant D) (l : Charge D) (p : Oscillator D)
    (Λ : DualMultiplicity (targetModule A B) s) :
    (dualTensorInverseHom A B hD).linearMap
      (DirectSum.lof ℂ _ (fun t => Carrier D ⊗[ℂ] DualMultiplicity (targetModule A B) t)
        s (Finsupp.single l p ⊗ₜ[ℂ] Λ)) =
      ∑ i ∈ fiberSupport hD s,
        ((k hD (-i.val.2) (-i.val.1))⁻¹ *
          (epsilon D (-carry D hD i.val.1 i.val.2) (carry D hD i.val.1 i.val.2))⁻¹ *
          epsilon D l (-carry D hD i.val.1 i.val.2)) •
        DirectSum.lof ℂ _ (PairSector (dualModule B) (dualModule A)) i.val
          (Finsupp.single (l-carry D hD i.val.1 i.val.2) p ⊗ₜ[ℂ]
            (finiteReverseBlock A B hD s i).symm
              (Λ.comp (jAt A B hD (-s) (reverseFiber s i)))) := by
  rw [dualTensorInverseHom_carrier]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [transportInverse_single, ← TensorProduct.smul_tmul', map_smul, smul_smul]
  congr 1
  ring

/-- Only the neg_neg equality transport; it adds no normalization scalar. -/
def negativeFunctional (s : Discriminant D) :
    Module.Dual ℂ (Multiplicity (targetModule A B) s) →ₗ[ℂ]
      DualMultiplicity (targetModule A B) (-s) := by
  simpa only [neg_neg] using
    (LinearMap.id : Module.Dual ℂ (Multiplicity (targetModule A B) s) →ₗ[ℂ]
      Module.Dual ℂ (Multiplicity (targetModule A B) s))

/-- The inverse tensor on the ORIGINAL (c,d) fiber: first undo finite dual
distribution, then undo the reversal, then apply both literal dualIotas. -/
def inverseFiberTensor (s : Discriminant D) (i : Fiber (D := D) s)
    (Λ : Module.Dual ℂ (Multiplicity (targetModule A B) s)) :
    PairMultiplicity (dualModule B) (dualModule A) (-i.val.2,-i.val.1) :=
  TensorProduct.map (dualIota B i.val.2) (dualIota A i.val.1)
    ((TensorProduct.comm ℂ (Module.Dual ℂ (Multiplicity B i.val.2))
      (Module.Dual ℂ (Multiplicity A i.val.1))).symm
      ((TensorProduct.dualDistribEquiv ℂ (Multiplicity A i.val.1)
        (Multiplicity B i.val.2)).symm (Λ.comp (jAt A B hD s i))))

/-- The requested readback indexed by ALL original c+d=s fibers. -/
theorem dualTensorInverseHom_negative (s : Discriminant D) (v : Carrier D)
    (Λ : Module.Dual ℂ (Multiplicity (targetModule A B) s)) :
    (dualTensorInverseHom A B hD).linearMap
      (DirectSum.lof ℂ _ (fun t => Carrier D ⊗[ℂ] DualMultiplicity (targetModule A B) t)
        (-s) (v ⊗ₜ[ℂ] negativeFunctional A B s Λ)) =
      ∑ i ∈ fiberSupport hD s, (k hD i.val.1 i.val.2)⁻¹ •
        DirectSum.lof ℂ _ (PairSector (dualModule B) (dualModule A)) (-i.val.2,-i.val.1)
          (transportInverse D (representative D (-s)) (carry D hD (-i.val.2) (-i.val.1)) v ⊗ₜ[ℂ]
            inverseFiberTensor A B hD s i Λ) := by
  rw [dualTensorInverseHom_carrier]
  symm
  apply Finset.sum_bij (fun i _ => reverseFiber s i)
  · intro i hi
    exact mem_fiberSupport hD (-s) (reverseFiber s i)
  · intro i hi j hj hij
    exact reverseFiber_injective s hij
  · intro j hj
    let i : Fiber (D := D) s := ⟨(-j.val.2,-j.val.1), by rw [← j.property]; abel⟩
    refine ⟨i, mem_fiberSupport hD s i, ?_⟩
    apply Subtype.ext
    simp only [reverseFiber, i, neg_neg]
  · intro i hi
    rcases i with ⟨⟨c,d⟩,hcd⟩
    subst s
    simp only [finiteReverseBlock_symm, negativeFunctional, inverseFiberTensor,
      reverseFiber, neg_neg, dualIota]; rfl

end FiniteInverse

section AssociatorCoherence
universe w
variable {X : Type u} {Y : Type v} {Z : Type w}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable [AddCommGroup Z] [Module ℂ Z]
variable (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
variable (C : FullJacobiLatticeModule D Z) (hD : (gramReal D).PosDef)

/-- Ground readback of the ACTUAL associator with all three equality
transports inside the actual jAt indices. -/
private theorem restrict_alpha_all (a b c ab bc q : Discriminant D)
    (hab : a+b=ab) (hbc : b+c=bc) (hq : ab+c=q)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c) :
    restrict (associatorIso A B C hD).hom q
      (jAt (targetModule A B) C hD q ⟨(ab,c),hq⟩
        (jAt A B hD ab ⟨(a,b),hab⟩ (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z)) =
      F hD a b c • jAt A (targetModule B C) hD q
        ⟨(a,bc),by rw [← hq, ← hab, ← hbc]; abel⟩
        (x ⊗ₜ[ℂ] jAt B C hD bc ⟨(b,c),hbc⟩ (y ⊗ₜ[ℂ] z)) := by
  apply Subtype.ext
  apply Subtype.ext
  change alpha A B C hD _ = _
  simpa only [jAt_val, ground, normalizedPair, LinearMap.comp_apply,
    LinearMap.flip_apply, TensorProduct.mk_apply, Submodule.coe_smul] using
    alpha_normalized_fibers A B C hD a b c ab bc hab hbc
      (Finsupp.single 0 (1 : Oscillator D)) x y z

/-- The two genuinely constructed nested functionals differ by the ORIGINAL
F. The proof exhausts BOTH levels of the actual product multiplicity and
reads literal coordinates; it does not assert a common map. -/
private theorem Xi_associator (c d e : Discriminant D)
    (φ : Module.Dual ℂ (Multiplicity A c)) (ψ : Module.Dual ℂ (Multiplicity B d))
    (χ : Module.Dual ℂ (Multiplicity C e)) :
    (Xi A (targetModule B C) hD (c+(d+e)) ⟨(c,d+e),rfl⟩
      (Xi B C hD (d+e) ⟨(d,e),rfl⟩ (χ ⊗ₜ[ℂ] ψ) ⊗ₜ[ℂ] φ)).comp
        (restrict (associatorIso A B C hD).hom (c+(d+e))) =
    F hD c d e • Xi (targetModule A B) C hD (c+(d+e))
      ⟨(c+d,e),add_assoc c d e⟩
      (χ ⊗ₜ[ℂ] Xi A B hD (c+d) ⟨(c,d),rfl⟩ (ψ ⊗ₜ[ℂ] φ)) := by
  apply multiplicity_linear_ext (targetModule A B) C hD (c+(d+e))
  rintro ⟨⟨ab,f⟩,hq⟩ w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w w' hw hw' => simp only [map_add, hw, hw']
  | tmul t z =>
    apply multiplicity_induction A B hD ab
      (fun t =>
        ((Xi A (targetModule B C) hD (c+(d+e)) ⟨(c,d+e),rfl⟩
          (Xi B C hD (d+e) ⟨(d,e),rfl⟩ (χ ⊗ₜ[ℂ] ψ) ⊗ₜ[ℂ] φ)).comp
            (restrict (associatorIso A B C hD).hom (c+(d+e))))
          (jAt (targetModule A B) C hD (c+(d+e)) ⟨(ab,f),hq⟩ (t ⊗ₜ[ℂ] z)) =
        (F hD c d e • Xi (targetModule A B) C hD (c+(d+e))
          ⟨(c+d,e),add_assoc c d e⟩
          (χ ⊗ₜ[ℂ] Xi A B hD (c+d) ⟨(c,d),rfl⟩ (ψ ⊗ₜ[ℂ] φ)))
          (jAt (targetModule A B) C hD (c+(d+e)) ⟨(ab,f),hq⟩ (t ⊗ₜ[ℂ] z)))
      (by simp) (fun t t' ht ht' => by
        simp only [TensorProduct.add_tmul, map_add, ht, ht']) ?_ t
    rintro ⟨⟨a,b⟩,hab⟩ x y
    subst ab
    simp only [LinearMap.comp_apply]
    rw [restrict_alpha_all A B C hD a b f (a+b) (b+f) (c+(d+e)) rfl rfl hq]
    by_cases ha : a = c <;> by_cases hb : b = d <;> by_cases hf : f = e
    all_goals
      simp [Xi, fiberRead, DirectSum.component, mu_coordinate, jAt_val,
        DirectSum.lof_eq_of, DFinsupp.single_apply, ground_single,
        ActualWeakModuleScalarProbes.tensorCoordinates_tmul,
        ActualWeakModuleScalarProbes.coordinate, reversePairing_tmul,
        LatticeChargedTransport.epsilon_nonzero, ha, hb, hf] <;>
        (try split_ifs) <;> simp_all [mul_comm, mul_left_comm, mul_assoc] <;> (try field_simp [hu]) <;> ring

/-- Restriction comparison on EVERY reversed pure triple. Both sides are the
actual composites from the full coherence statement. -/
private theorem K_associator_negative (c d e : Discriminant D)
    (φ : Module.Dual ℂ (Multiplicity A c)) (ψ : Module.Dual ℂ (Multiplicity B d))
    (χ : Module.Dual ℂ (Multiplicity C e)) :
    restrict (dualHom hD (associatorIso A B C hD).hom) (-(c+(d+e)))
      (restrict (dualTensorHom A (targetModule B C) hD) (-(c+(d+e)))
        (restrict (productHom hD (dualTensorHom B C hD) (ModuleHom.id (dualModule A)))
          (-(c+(d+e)))
          (jAt (targetModule (dualModule C) (dualModule B)) (dualModule A) hD
            (-(c+(d+e))) ⟨(-(d+e),-c),by abel⟩
            (jAt (dualModule C) (dualModule B) hD (-(d+e)) ⟨(-e,-d),by abel⟩
              (dualIota C e χ ⊗ₜ[ℂ] dualIota B d ψ) ⊗ₜ[ℂ] dualIota A c φ)))) =
    restrict (dualTensorHom (targetModule A B) C hD) (-(c+(d+e)))
      (restrict (productHom hD (ModuleHom.id (dualModule C)) (dualTensorHom A B hD))
        (-(c+(d+e)))
        (restrict (associatorIso (dualModule C) (dualModule B) (dualModule A) hD).hom
          (-(c+(d+e)))
          (jAt (targetModule (dualModule C) (dualModule B)) (dualModule A) hD
            (-(c+(d+e))) ⟨(-(d+e),-c),by abel⟩
            (jAt (dualModule C) (dualModule B) hD (-(d+e)) ⟨(-e,-d),by abel⟩
              (dualIota C e χ ⊗ₜ[ℂ] dualIota B d ψ) ⊗ₜ[ℂ] dualIota A c φ)))) := by
  rw [jAt_natural, TensorProduct.map_tmul, dualTensorHom_jAt, restrict_identity,
    ← TensorProduct.smul_tmul']
  simp only [map_smul]
  rw [dualTensorHom_jAt]
  simp only [map_smul]
  rw [dualHom_dualIota]
  rw [restrict_alpha_all (dualModule C) (dualModule B) (dualModule A) hD
    (-e) (-d) (-c) (-(d+e)) (-(c+d)) (-(c+(d+e))) (by abel) (by abel) (by abel)]
  simp only [map_smul]
  rw [jAt_natural, TensorProduct.map_tmul, restrict_identity, dualTensorHom_jAt,
    TensorProduct.tmul_smul]
  simp only [map_smul]
  have hK := dualTensorHom_jAt (targetModule A B) C hD (c+d) e χ
    (Xi A B hD (c+d) ⟨(c,d),rfl⟩ (ψ ⊗ₜ[ℂ] φ))
  simp only [add_assoc] at hK
  rw [hK, Xi_associator]
  simp only [map_smul, smul_smul]
  congr 1
  linear_combination k_associativity hD c d e

/-- Genuine anti-monoidal coherence on all original vectors. The actual Hom
classification is faithful; both nested source multiplicities are exhausted
before applying K_associator_negative. All three universes are independent. -/
theorem dualTensorHom_associativity :
    (dualHom hD (associatorIso A B C hD).hom).comp
      ((dualTensorHom A (targetModule B C) hD).comp
        (productHom hD (dualTensorHom B C hD) (ModuleHom.id (dualModule A)))) =
    (dualTensorHom (targetModule A B) C hD).comp
      ((productHom hD (ModuleHom.id (dualModule C)) (dualTensorHom A B hD)).comp
        (associatorIso (dualModule C) (dualModule B) (dualModule A) hD).hom) := by
  apply (recordEquiv _ _).injective
  apply (homMultiplicityEquiv _ _ hD).injective
  change restrict _ = restrict _
  funext q
  apply multiplicity_linear_ext (targetModule (dualModule C) (dualModule B)) (dualModule A) hD q
  rintro ⟨⟨r,u⟩,hqu⟩ w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w w' hw hw' => simp only [map_add, hw, hw']
  | tmul t z =>
    apply multiplicity_induction (dualModule C) (dualModule B) hD r
      (fun t =>
        restrict ((dualHom hD (associatorIso A B C hD).hom).comp
          ((dualTensorHom A (targetModule B C) hD).comp
            (productHom hD (dualTensorHom B C hD) (ModuleHom.id (dualModule A))))) q
          (jAt (targetModule (dualModule C) (dualModule B)) (dualModule A) hD q
            ⟨(r,u),hqu⟩ (t ⊗ₜ[ℂ] z)) =
        restrict ((dualTensorHom (targetModule A B) C hD).comp
          ((productHom hD (ModuleHom.id (dualModule C)) (dualTensorHom A B hD)).comp
            (associatorIso (dualModule C) (dualModule B) (dualModule A) hD).hom)) q
          (jAt (targetModule (dualModule C) (dualModule B)) (dualModule A) hD q
            ⟨(r,u),hqu⟩ (t ⊗ₜ[ℂ] z)))
      (by simp) (fun t t' ht ht' => by
        simp only [TensorProduct.add_tmul, map_add, ht, ht']) ?_ t
    rintro ⟨⟨a,b⟩,hab⟩ x y
    subst r
    subst q
    obtain ⟨χ,rfl⟩ :=
      (ActualWeakModuleRealization.multiplicityEquiv (DualMultiplicity C) hD a).symm.surjective x
    obtain ⟨ψ,rfl⟩ :=
      (ActualWeakModuleRealization.multiplicityEquiv (DualMultiplicity B) hD b).symm.surjective y
    obtain ⟨φ,rfl⟩ :=
      (ActualWeakModuleRealization.multiplicityEquiv (DualMultiplicity A) hD u).symm.surjective z
    have hh := K_associator_negative A B C hD (-u) (-b) (-a) φ ψ χ
    simpa only [dualIota, neg_add, neg_neg, jAt,
      add_comm, add_left_comm, add_assoc] using hh

end AssociatorCoherence

end D5.S3.VertexAlgebra.Modules.ActualWeakModuleDualTensorator

