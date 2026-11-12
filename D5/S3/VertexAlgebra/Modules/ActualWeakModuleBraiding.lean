/- Source-only candidate. No elaboration or native acceptance is claimed.
   The carrier below is literally ActualWeakModuleUniversalField.P.
   The two input universes are independent. No multiplicity basis is used.
   No bifunctor, unit, module pentagon or field pentagon is introduced. -/
import D5.S3.VertexAlgebra.Sectors.LatticeCosetRationalSkew
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleUniversalField
import D5.S3.VertexAlgebra.Modules.FullJacobiModuleMaps

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleBraiding
attribute [local instance] Classical.propDecidable
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeDiscriminantTheta
open FullJacobiCurrentTransport FullJacobiIntertwiner FullJacobiTensorModule FullJacobiDirectSum
open ActualWeakModuleSectorCoordinates ActualWeakModuleClassification
open ActualWeakModuleUniversalField
open LatticeCosetRationalSkew

universe u v
variable {D : LatticeData} {X : Type u} {Y : Type v}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)

/-- The phase uses literal Quotient.out representatives. -/
abbrev phase (c d : Discriminant D) : ℂ :=
  Omega D (1 : Matrix _ _ ℤ) (representative D c) (representative D d)

/-- The first tensor factor remains the original carrier, and the two
    original multiplicity factors are flipped. -/
def summandFlip (cd : Discriminant D × Discriminant D) :
    PairSector A B cd ≃ₗ[ℂ] PairSector B A (cd.2,cd.1) :=
  TensorProduct.congr (LinearEquiv.refl ℂ (Carrier D))
    (TensorProduct.comm ℂ (Multiplicity A cd.1) (Multiplicity B cd.2))

/-- Actual finite direct-sum reindexing. No replacement summand is used. -/
def braid : P A B →ₗ[ℂ] P B A :=
  DirectSum.toModule ℂ _ _ (fun cd =>
    (phase (D := D) cd.1 cd.2 • DirectSum.lof ℂ _ (PairSector B A) (cd.2,cd.1)).comp
      (summandFlip A B cd).toLinearMap)

/-- The explicit inverse has the reciprocal of the FORWARD phase. -/
def unbraid : P B A →ₗ[ℂ] P A B :=
  DirectSum.toModule ℂ _ _ (fun dc =>
    ((phase (D := D) dc.2 dc.1)⁻¹ • DirectSum.lof ℂ _ (PairSector A B) (dc.2,dc.1)).comp
      (summandFlip B A dc).toLinearMap)

@[simp] theorem braid_tag (c d : Discriminant D)
    (x : Multiplicity A c) (y : Multiplicity B d) (v : Carrier D) :
    braid A B (tag A B c d x y v) = phase (D := D) c d • tag B A d c y x v := by
  simp [braid, tag_apply, summandFlip, TensorProduct.congr_tmul]

@[simp] theorem unbraid_tag (c d : Discriminant D)
    (x : Multiplicity A c) (y : Multiplicity B d) (v : Carrier D) :
    unbraid A B (tag B A d c y x v) = (phase (D := D) c d)⁻¹ • tag A B c d x y v := by
  simp [unbraid, tag_apply, summandFlip, TensorProduct.congr_tmul]

/-- Direct-sum and algebraic-tensor generation, including empty supports. -/
theorem pair_induction (Q : P A B → Prop) (h0 : Q 0)
    (ha : ∀ x y, Q x → Q y → Q (x+y))
    (ht : ∀ c d x y v, Q (tag A B c d x y v)) (z : P A B) : Q z := by
  induction z using DirectSum.induction_on with
  | zero => exact h0
  | add x y hx hy => exact ha x y hx hy
  | of cd z =>
    rcases cd with ⟨c,d⟩
    change Q (DirectSum.lof ℂ _ (PairSector A B) (c,d) z)
    induction z using TensorProduct.induction_on with
    | zero => simpa only [map_zero] using h0
    | add x y hx hy => simpa only [map_add] using ha _ _ hx hy
    | tmul v w =>
      induction w using TensorProduct.induction_on with
      | zero => simpa only [TensorProduct.tmul_zero,map_zero] using h0
      | add x y hx hy => simpa only [TensorProduct.tmul_add,map_add] using ha _ _ hx hy
      | tmul x y => exact ht c d x y v

theorem unbraid_braid (z : P A B) : unbraid A B (braid A B z) = z := by
  apply pair_induction A B (fun z => unbraid A B (braid A B z) = z)
  · simp
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro c d x y v
    rw [braid_tag, map_smul, unbraid_tag, smul_smul,
      mul_inv_cancel₀ (Omega_ne_zero D (1 : Matrix _ _ ℤ) _ _), one_smul]

theorem braid_unbraid (z : P B A) : braid A B (unbraid A B z) = z := by
  apply pair_induction B A (fun z => braid A B (unbraid A B z) = z)
  · simp
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro d c y x v
    rw [unbraid_tag, map_smul, braid_tag, smul_smul,
      inv_mul_cancel₀ (Omega_ne_zero D (1 : Matrix _ _ ℤ) _ _), one_smul]

/-- All original states and all integer modes. The sector transport is the
    genuine equality beta_c+beta_d=beta_d+beta_c in the ORIGINAL action. -/
theorem braid_modes (h : Carrier D) (m : ℤ) (z : P A B) :
    braid A B (mode (targetModule A B) h m z) =
      mode (targetModule B A) h m (braid A B z) := by
  apply pair_induction A B (fun z => braid A B (mode (targetModule A B) h m z) =
      mode (targetModule B A) h m (braid A B z))
  · simp
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro c d x y v
    rw [target_action_tag, braid_tag, braid_tag, map_smul, target_action_tag]
    rw [add_comm (representative D c) (representative D d)]

def braidEquiv : P A B ≃ₗ[ℂ] P B A where
  toLinearMap := braid A B
  invFun := unbraid A B
  left_inv := unbraid_braid A B
  right_inv := braid_unbraid A B

/-- Genuine binary isomorphism between the original full target modules. -/
def braidIso : ModuleIso (targetModule A B) (targetModule B A) where
  linearEquiv := braidEquiv A B
  intertwines := braid_modes A B

theorem unbraid_modes (h : Carrier D) (m : ℤ) (z : P B A) :
    unbraid A B (mode (targetModule B A) h m z) =
      mode (targetModule A B) h m (unbraid A B z) :=
  (braidIso A B).inverse_intertwines h m z

/-- A consequence on every actual charge/oscillator generator, not just on
    the vacuum scalar. All original chi/cocycle conventions stay in Carrier. -/
theorem braid_single (c d : Discriminant D) (l : Charge D)
    (p : Oscillator D) (x : Multiplicity A c) (y : Multiplicity B d) :
    braid A B (DirectSum.lof ℂ _ (PairSector A B) (c,d)
      (Finsupp.single l p ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] y))) =
    phase (D := D) c d • DirectSum.lof ℂ _ (PairSector B A) (d,c)
      (Finsupp.single l p ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] x)) :=
  braid_tag A B c d x y (Finsupp.single l p)

/-- The opposite braiding is generally not the inverse. -/
theorem double_braid_tag (c d : Discriminant D)
    (x : Multiplicity A c) (y : Multiplicity B d) (v : Carrier D) :
    braid B A (braid A B (tag A B c d x y v)) =
      Complex.exp (2 * Real.pi * Complex.I *
        (LatticeCosetCanonicalIntertwiner.shift D (1 : Matrix _ _ ℤ)
          (representative D c) (representative D d) : ℂ)) • tag A B c d x y v := by
  rw [braid_tag, map_smul, braid_tag, smul_smul]
  have hp : phase (D := D) d c = phase (D := D) c d :=
    Omega_symm D (1 : Matrix _ _ ℤ) (representative D d) (representative D c)
  rw [hp]
  congr 1
  change Complex.exp _ * Complex.exp _ = _
  rw [← Complex.exp_add]
  congr 1
  ring

end D5.S3.VertexAlgebra.Modules.ActualWeakModuleBraiding
