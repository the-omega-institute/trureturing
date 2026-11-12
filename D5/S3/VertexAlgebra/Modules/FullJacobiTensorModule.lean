/- GID: D5/S3/VertexAlgebra/Modules/FullJacobiTensorModule
   generality: I
   mirror-B: none(source-only-candidate)
   mirror-E: none(source-only-candidate)
   anchors: []
   utility: Arbitrary algebraic complex multiplicity for genuine full Jacobi modules.
   status: UNCOMPILED. No native evidence is asserted for this file.
-/
import D5.S3.VertexAlgebra.Modules.FullJacobiIntertwiner
import Mathlib.LinearAlgebra.TensorProduct.Map

/-
The tensor product is algebraic. Its induction principle expresses every
input as a finite sum of simple tensors. At an addition node truncation uses
the maximum of two bounds; Jacobi uses THREE separate finite support unions.
At a simple tensor the exact original equality is mapped by m ↦ m ⊗ w.
The only module record constructed is the original sealed adapter record.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Modules.FullJacobiTensorModule
open FullJacobiCurrentTransport FullJacobiIntertwiner
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeAllStateField
open FieldNormalProduct
open scoped BigOperators VertexOperator TensorProduct
noncomputable section
universe u v w z

variable {D : LatticeData} {M : Type u} {N : Type v}
variable [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

def tensorModes (J : FullJacobiLatticeModule D M)
    (W : Type w) [AddCommGroup W] [Module ℂ W] :
    Carrier D →ₗ[ℂ] ℤ → Module.End ℂ (M ⊗[ℂ] W) where
  toFun a n := TensorProduct.map (mode J a n) LinearMap.id
  map_add' a b := by
    funext n
    simp only [mode_state_add, TensorProduct.map_add_left, Pi.add_apply]
  map_smul' c a := by
    funext n
    simp only [mode_state_smul, TensorProduct.map_smul_left, Pi.smul_apply,
      RingHom.id_apply]

/-- Finite sums of simple tensors have a finite common cutoff, even when
W has arbitrary dimension. Zero tensors and zero modules are included. -/
theorem tensorModes_truncation (J : FullJacobiLatticeModule D M)
    (W : Type w) [AddCommGroup W] [Module ℂ W]
    (a : Carrier D) (x : M ⊗[ℂ] W) :
    ∃ B : ℤ, ∀ n : ℤ, B ≤ n → tensorModes J W a n x = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul m w =>
    obtain ⟨B, hB⟩ := module_truncation J a m
    refine ⟨B, ?_⟩
    intro n hn
    change TensorProduct.map (mode J a n) LinearMap.id (m ⊗ₜ[ℂ] w) = 0
    simp only [TensorProduct.map_tmul, LinearMap.id_apply,
      hB n hn, TensorProduct.zero_tmul]
  | add x y hx hy =>
    obtain ⟨B, hB⟩ := hx
    obtain ⟨C, hC⟩ := hy
    refine ⟨max B C, ?_⟩
    intro n hn
    rw [map_add, hB n (le_trans (le_max_left B C) hn),
      hC n (le_trans (le_max_right B C) hn), zero_add]

/-- Actual Laurent-valued state-linear field, built from its coefficients. -/
def tensorField (J : FullJacobiLatticeModule D M)
    (W : Type w) [AddCommGroup W] [Module ℂ W] :
    Carrier D →ₗ[ℂ] VertexOperator ℂ (M ⊗[ℂ] W) :=
  fieldOfModes (tensorModes J W) (tensorModes_truncation J W)

@[simp] theorem tensorField_mode (J : FullJacobiLatticeModule D M)
    (W : Type w) [AddCommGroup W] [Module ℂ W] (a : Carrier D) (n : ℤ) :
    ((tensorField J W a)[[n]]) = TensorProduct.map (mode J a n) LinearMap.id :=
  fieldOfModes_mode (tensorModes J W) (tensorModes_truncation J W) a n

/-- Coefficient on a simple tensor follows from the field's definition. -/
@[simp] theorem tensorField_mode_tmul (J : FullJacobiLatticeModule D M)
    (W : Type w) [AddCommGroup W] [Module ℂ W]
    (a : Carrier D) (n : ℤ) (m : M) (w : W) :
    ((tensorField J W a)[[n]]) (m ⊗ₜ[ℂ] w) = mode J a n m ⊗ₜ[ℂ] w := by
  rw [tensorField_mode, TensorProduct.map_tmul, LinearMap.id_apply]

theorem tensorField_vacuum (J : FullJacobiLatticeModule D M)
    (W : Type w) [AddCommGroup W] [Module ℂ W] :
    tensorField J W (vacuum D) = identityField := by
  apply field_ext
  intro n
  rw [tensorField_mode]
  change (mode J (vacuum D) n).rTensor W = _
  rw [vacuum_modes, identity_field_modes]
  split_ifs <;> simp

/-- Simple tensors: map each of the three finite original families using
the coefficient identity. General tensors: take three separate finite unions
over the finite simple-tensor expression furnished by inductionOn. -/
theorem tensorField_jacobi (J : FullJacobiLatticeModule D M)
    (W : Type w) [AddCommGroup W] [Module ℂ W]
    (a b : Carrier D) (x : M ⊗[ℂ] W) (p q r : ℤ) :
    JacobiAt (tensorField J W) a b x p q r := by
  induction x using TensorProduct.inductionOn with
  | tmul m w =>
    exact (jacobiAt_module J a b m p q r).map
      ((TensorProduct.mk ℂ M W).flip w)
      (fun c n y => by
        change mode J c n y ⊗ₜ[ℂ] w =
          ((tensorField J W c)[[n]]) (y ⊗ₜ[ℂ] w)
        exact (tensorField_mode_tmul J W c n y w).symm)
  | add x y hx hy => exact hx.add hy

/-- No positivity or classification premise occurs in this construction. -/
def tensorModule (J : FullJacobiLatticeModule D M)
    (W : Type w) [AddCommGroup W] [Module ℂ W] :
    FullJacobiLatticeModule D (M ⊗[ℂ] W) where
  stateField := tensorField J W
  vacuum_field := tensorField_vacuum J W
  borcherds a b x p q r := (tensorField_jacobi J W a b x p q r).original

@[simp] theorem tensorModule_mode (J : FullJacobiLatticeModule D M)
    (W : Type w) [AddCommGroup W] [Module ℂ W] (a : Carrier D) (n : ℤ) :
    mode (tensorModule J W) a n = TensorProduct.map (mode J a n) LinearMap.id :=
  tensorField_mode J W a n

/-- Naturality simultaneously in the module and its arbitrary multiplicity.
The proof uses the constructed modes on simple tensors, then finite additivity. -/
theorem tensor_map_modes (J : FullJacobiLatticeModule D M)
    (K : FullJacobiLatticeModule D N) (f : ModuleHom J K)
    {W : Type w} {V : Type z} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup V] [Module ℂ V] (g : W →ₗ[ℂ] V)
    (a : Carrier D) (n : ℤ) (x : M ⊗[ℂ] W) :
    TensorProduct.map f.linearMap g (mode (tensorModule J W) a n x) =
      mode (tensorModule K V) a n (TensorProduct.map f.linearMap g x) := by
  induction x using TensorProduct.inductionOn with
  | tmul m w =>
    simp only [tensorModule_mode, TensorProduct.map_tmul, LinearMap.id_apply,
      f.intertwines]
  | add x y hx hy => simp only [map_add, hx, hy]

def tensorHom (J : FullJacobiLatticeModule D M) (K : FullJacobiLatticeModule D N)
    (f : ModuleHom J K) {W : Type w} {V : Type z}
    [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V]
    (g : W →ₗ[ℂ] V) : ModuleHom (tensorModule J W) (tensorModule K V) where
  linearMap := TensorProduct.map f.linearMap g
  intertwines := tensor_map_modes J K f g

/-- The source-generation theorem feeds an actual functor on weak modules. -/
def tensorHomOfGenerators (J : FullJacobiLatticeModule D M)
    (K : FullJacobiLatticeModule D N) (f : M →ₗ[ℂ] N)
    (positiveG : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hcurrent : ∀ (i : Fin D.rank) (n : ℤ) (x : M),
      f (current J i n x) = current K i n (f x))
    (hexponential : ∀ (β : Charge D) (n : ℤ) (x : M),
      f (mode J (Finsupp.single β (1 : Oscillator D)) n x) =
        mode K (Finsupp.single β (1 : Oscillator D)) n (f x))
    {W : Type w} {V : Type z} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup V] [Module ℂ V] (g : W →ₗ[ℂ] V) :
    ModuleHom (tensorModule J W) (tensorModule K V) :=
  tensorHom J K (ModuleHom.ofGenerators J K f positiveG hcurrent hexponential) g

end
end D5.S3.VertexAlgebra.Modules.FullJacobiTensorModule
