/- GID: D5/S3/VertexAlgebra/Modules/FullJacobiDirectSum
   generality: I
   mirror-B: none(source-only-candidate)
   mirror-E: none(source-only-candidate)
   anchors: []
   utility: Arbitrary dependent algebraic direct sums of genuine full Jacobi modules.
   status: UNCOMPILED. No native evidence is asserted for this file.
-/
import D5.S3.VertexAlgebra.Modules.FullJacobiIntertwiner
import Mathlib.Algebra.DirectSum.Module

/-
No finiteness assumption is made on the index type. Bounds and support
unions are taken only over the finite support of the input DFinsupp.
The literal Jacobi equality is obtained by applying each inclusion to its
original equality and adding finitely many vector equalities. Coordinate
calculations below control supports and coefficients, not a substitute axiom.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Modules.FullJacobiDirectSum
open FullJacobiCurrentTransport FullJacobiIntertwiner
open LatticeGeneratingFieldLocality LatticeAllStateField FieldNormalProduct
open scoped BigOperators VertexOperator DirectSum
noncomputable section
universe u v w

variable {D : LatticeData} {ι : Type u} {M : ι → Type v}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
local instance : DecidableEq ι := Classical.decEq ι
local instance (i : ι) : DecidableEq (M i) := Classical.decEq (M i)

def directSumModes (J : ∀ i, FullJacobiLatticeModule D (M i)) :
    Carrier D →ₗ[ℂ] ℤ → Module.End ℂ (⨁ i, M i) where
  toFun a n := DirectSum.lmap (fun i => mode (J i) a n)
  map_add' a b := by
    funext n
    apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro i
    change mode (J i) (a + b) n (x i) =
      mode (J i) a n (x i) + mode (J i) b n (x i)
    rw [mode_state_add, LinearMap.add_apply]
  map_smul' c a := by
    funext n
    apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro i
    change mode (J i) (c • a) n (x i) = c • mode (J i) a n (x i)
    rw [mode_state_smul, LinearMap.smul_apply]

/-- The supremum is over x.support, not the full index type. Its empty
value is zero, so the proof also covers an empty index type. -/
theorem directSumModes_truncation (J : ∀ i, FullJacobiLatticeModule D (M i))
    (a : Carrier D) (x : ⨁ i, M i) :
    ∃ B : ℤ, ∀ n : ℤ, B ≤ n → directSumModes J a n x = 0 := by
  classical
  choose B hB using (fun i : ι => module_truncation (J i) a (x i))
  let R : ℕ := x.support.sup (fun i => (B i).toNat)
  refine ⟨R, ?_⟩
  intro n hn
  apply DFinsupp.ext
  intro i
  change mode (J i) a n (x i) = 0
  by_cases hi : i ∈ x.support
  · have hR : (B i).toNat ≤ R :=
      Finset.le_sup (f := fun i => (B i).toNat) hi
    exact hB i n (by omega)
  · rw [DFinsupp.notMem_support_iff.mp hi, map_zero]

def directSumField (J : ∀ i, FullJacobiLatticeModule D (M i)) :
    Carrier D →ₗ[ℂ] VertexOperator ℂ (⨁ i, M i) :=
  fieldOfModes (directSumModes J) (directSumModes_truncation J)

@[simp] theorem directSumField_mode (J : ∀ i, FullJacobiLatticeModule D (M i))
    (a : Carrier D) (n : ℤ) :
    ((directSumField J a)[[n]]) = DirectSum.lmap (fun i => mode (J i) a n) :=
  fieldOfModes_mode (directSumModes J) (directSumModes_truncation J) a n

/-- The coefficient on an inclusion is derived from lmap, before Jacobi. -/
@[simp] theorem directSumField_mode_lof (J : ∀ i, FullJacobiLatticeModule D (M i))
    (a : Carrier D) (n : ℤ) (i : ι) (x : M i) :
    ((directSumField J a)[[n]]) (DirectSum.lof ℂ ι M i x) =
      DirectSum.lof ℂ ι M i (mode (J i) a n x) := by
  rw [directSumField_mode, DirectSum.lmap_lof]

@[simp] theorem directSumField_mode_component
    (J : ∀ i, FullJacobiLatticeModule D (M i))
    (a : Carrier D) (n : ℤ) (x : ⨁ i, M i) (i : ι) :
    (((directSumField J a)[[n]]) x) i = mode (J i) a n (x i) := by
  rw [directSumField_mode]
  rfl

theorem directSumField_vacuum (J : ∀ i, FullJacobiLatticeModule D (M i)) :
    directSumField J (vacuum D) = identityField := by
  apply field_ext
  intro n
  rw [directSumField_mode, identity_field_modes]
  apply LinearMap.ext
  intro x
  apply DFinsupp.ext
  intro i
  by_cases hn : n = -1 <;>
    simp [DirectSum.lmap_apply, vacuum_modes, hn]

/-- A support inclusion into a finite-coordinate union. Used separately
for the left, first and second original Jacobi families below. -/
theorem component_support_subset {α : Type*} (s : Finset ι)
    (f : α → (⨁ i, M i)) (g : ∀ i, α → M i)
    (hc : ∀ k i, f k i = g i k)
    (hz : ∀ i, i ∉ s → ∀ k, g i k = 0) :
    Function.support f ⊆ ⋃ i ∈ (s : Set ι), Function.support (g i) := by
  intro k hk
  by_contra outside
  have inside (i : ι) (hi : i ∈ s) : g i k = 0 := by
    by_contra nonzero
    exact outside (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, nonzero⟩⟩)
  apply hk
  apply DFinsupp.ext
  intro i
  rw [hc]
  by_cases hi : i ∈ s
  · exact inside i hi
  · exact hz i hi k

/-- These are three distinct support bounds. No cancellation between the
two right-hand families is used to claim finiteness. -/
theorem directSum_jacobi_supports (J : ∀ i, FullJacobiLatticeModule D (M i))
    (a b : Carrier D) (x : ⨁ i, M i) (p q r : ℤ) :
    Function.support (jacobiLeft (directSumField J) a b x p q r) ⊆
        (⋃ i ∈ (x.support : Set ι), Function.support (jacobiLeft (J i).stateField a b (x i) p q r)) ∧
    Function.support (jacobiFirst (directSumField J) a b x p q r) ⊆
        (⋃ i ∈ (x.support : Set ι), Function.support (jacobiFirst (J i).stateField a b (x i) p q r)) ∧
    Function.support (jacobiSecond (directSumField J) a b x p q r) ⊆
        (⋃ i ∈ (x.support : Set ι), Function.support (jacobiSecond (J i).stateField a b (x i) p q r)) := by
  refine ⟨component_support_subset x.support _ _ ?_ ?_,
    component_support_subset x.support _ _ ?_ ?_,
    component_support_subset x.support _ _ ?_ ?_⟩
  · intro k i
    simp only [jacobiLeft, DirectSum.smul_apply, directSumField_mode_component, mode]
  · intro i hi k
    simp only [jacobiLeft, DFinsupp.notMem_support_iff.mp hi, map_zero, smul_zero]
  · intro k i
    simp only [jacobiFirst, DirectSum.smul_apply, directSumField_mode_component, mode]
  · intro i hi k
    simp only [jacobiFirst, DFinsupp.notMem_support_iff.mp hi, map_zero, smul_zero]
  · intro k i
    simp only [jacobiSecond, DirectSum.smul_apply, directSumField_mode_component, mode]
  · intro i hi k
    simp only [jacobiSecond, DFinsupp.notMem_support_iff.mp hi, map_zero, smul_zero]

/-- Finite union support control plus a finite sum of mapped original
Jacobi equalities. In particular this proves an equality in the direct sum,
not just a statement that each coordinate would satisfy an equality. -/
theorem directSumField_jacobi (J : ∀ i, FullJacobiLatticeModule D (M i))
    (a b : Carrier D) (x : ⨁ i, M i) (p q r : ℤ) :
    JacobiAt (directSumField J) a b x p q r := by
  classical
  obtain ⟨sL, sF, sS⟩ := directSum_jacobi_supports J a b x p q r
  have hL : Function.HasFiniteSupport (jacobiLeft (directSumField J) a b x p q r) :=
    (x.support.finite_toSet.biUnion (fun i _ =>
      ((J i).borcherds a b (x i) p q r).1)).subset sL
  have hF : Function.HasFiniteSupport (jacobiFirst (directSumField J) a b x p q r) :=
    (x.support.finite_toSet.biUnion (fun i _ =>
      ((J i).borcherds a b (x i) p q r).2.1)).subset sF
  have hS : Function.HasFiniteSupport (jacobiSecond (directSumField J) a b x p q r) :=
    (x.support.finite_toSet.biUnion (fun i _ =>
      ((J i).borcherds a b (x i) p q r).2.2.1)).subset sS
  have sumJacobi : JacobiAt (directSumField J) a b
      (∑ i ∈ x.support, DirectSum.lof ℂ ι M i (x i)) p q r := by
    apply JacobiAt.sum
    intro i hi
    exact (jacobiAt_module (J i) a b (x i) p q r).map (DirectSum.lof ℂ ι M i)
      (fun c n y => (directSumField_mode_lof J c n i y).symm)
  have expansion : (∑ i ∈ x.support, DirectSum.lof ℂ ι M i (x i)) = x := by
    simpa only [DirectSum.lof_eq_of] using DirectSum.sum_support_of x
  rw [expansion] at sumJacobi
  exact ⟨hL, hF, hS, sumJacobi.2.2.2⟩

def directSumModule (J : ∀ i, FullJacobiLatticeModule D (M i)) :
    FullJacobiLatticeModule D (⨁ i, M i) where
  stateField := directSumField J
  vacuum_field := directSumField_vacuum J
  borcherds a b x p q r := (directSumField_jacobi J a b x p q r).original

@[simp] theorem directSumModule_mode (J : ∀ i, FullJacobiLatticeModule D (M i))
    (a : Carrier D) (n : ℤ) :
    mode (directSumModule J) a n = DirectSum.lmap (fun i => mode (J i) a n) :=
  directSumField_mode J a n

def inclusionHom (J : ∀ i, FullJacobiLatticeModule D (M i)) (i : ι) :
    ModuleHom (J i) (directSumModule J) where
  linearMap := DirectSum.lof ℂ ι M i
  intertwines a n x := (directSumField_mode_lof J a n i x).symm

def projectionHom (J : ∀ i, FullJacobiLatticeModule D (M i)) (i : ι) :
    ModuleHom (directSumModule J) (J i) where
  linearMap := DirectSum.component ℂ ι M i
  intertwines a n x := directSumField_mode_component J a n x i

/-- Actual maps between constructed sums, with arbitrary index set. -/
def directSumHom {N : ι → Type w}
    [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)]
    (J : ∀ i, FullJacobiLatticeModule D (M i))
    (K : ∀ i, FullJacobiLatticeModule D (N i))
    (f : ∀ i, ModuleHom (J i) (K i)) :
    ModuleHom (directSumModule J) (directSumModule K) where
  linearMap := DirectSum.lmap (fun i => (f i).linearMap)
  intertwines := by
    intro a n x
    simp only [directSumModule_mode]
    apply DFinsupp.ext
    intro i
    simp only [DirectSum.lmap_apply]
    exact (f i).intertwines a n (x i)

/-- The coproduct map used to assemble classification isomorphisms.
Its intertwining proof is a literal finite sum of the component relations. -/
def coproductHom {N : Type w} [AddCommGroup N] [Module ℂ N]
    (J : ∀ i, FullJacobiLatticeModule D (M i))
    (K : FullJacobiLatticeModule D N) (f : ∀ i, ModuleHom (J i) K) :
    ModuleHom (directSumModule J) K where
  linearMap := DirectSum.toModule ℂ ι N (fun i => (f i).linearMap)
  intertwines := by
    intro a n x
    have generators (i : ι) (y : M i) :
        DirectSum.toModule ℂ ι N (fun i => (f i).linearMap)
            (mode (directSumModule J) a n (DirectSum.lof ℂ ι M i y)) =
          mode K a n (DirectSum.toModule ℂ ι N (fun i => (f i).linearMap)
            (DirectSum.lof ℂ ι M i y)) := by
      change DirectSum.toModule ℂ ι N (fun i => (f i).linearMap)
        (((directSumField J a)[[n]]) (DirectSum.lof ℂ ι M i y)) = _
      rw [directSumField_mode_lof, DirectSum.toModule_lof, DirectSum.toModule_lof]
      exact (f i).intertwines a n y
    have expansion : (∑ i ∈ x.support, DirectSum.lof ℂ ι M i (x i)) = x := by
      simpa only [DirectSum.lof_eq_of] using DirectSum.sum_support_of x
    have sumRelation :
        DirectSum.toModule ℂ ι N (fun i => (f i).linearMap)
            (mode (directSumModule J) a n
              (∑ i ∈ x.support, DirectSum.lof ℂ ι M i (x i))) =
          mode K a n (DirectSum.toModule ℂ ι N (fun i => (f i).linearMap)
            (∑ i ∈ x.support, DirectSum.lof ℂ ι M i (x i))) := by
      simp only [map_sum]
      exact Finset.sum_congr rfl (fun i hi => generators i (x i))
    simpa only [expansion] using sumRelation

end
end D5.S3.VertexAlgebra.Modules.FullJacobiDirectSum
