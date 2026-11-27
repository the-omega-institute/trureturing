/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMatterGrading
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMatterGrading
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: Signed tensor grading and binomial lowering on the original Leech matter. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldCriticalMatter
import D5.S3.VertexAlgebra.TwistedGround.MixedJacobiFinite
import D5.S3.VertexAlgebra.LatticeActualLZeroGrading
import Mathlib.Data.Nat.Choose.Sum
import Batteries.Tactic.OpenPrivate

/-! Integer eigenspaces and lowering powers for the original matter tensor product. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.NativeBPZ

open ActualLeechHyperbolic (leechData leech_spec)
open ActualLeechOrbifoldMatter (Orbifold leechUnit)
open ActualLeechOrbifoldCriticalMatter (Matter matter hyperbolicPlane hyperbolicMatter)
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open LatticeGeneratingFieldLocality (Carrier)
open LatticeHalfFockGradedTrace (actualTensorL0 oddWeight)
open LatticePositiveEnergy (carrierBasis energy actualL0_basis actualL0_eigen_iff_grade)
open LatticeSugawaraCurrents (gramComplex sugawaraMode)

open private plane_inverse from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldCriticalMatter
open private fixedProjection from D5.S3.VertexAlgebra.TwistedGround.MixedOpposite
open private fixedSourceInclusion fixed_source_expansion actualInputBasis
  actual_input_basis_expansion actual_input_basis_energy
  from D5.S3.VertexAlgebra.TwistedGround.MixedJacobiFinite

local notation "Plane" => Carrier hyperbolicPlane
local notation "orbL" => ActualLeechOrbifoldMatter.mode
local notation "planeL" => hyperbolicMatter.mode

private theorem matter_mode_tmul (n : ℤ) (u : Orbifold) (a : Plane) :
    matter.mode n (u ⊗ₜ[ℂ] a) = (orbL n u) ⊗ₜ[ℂ] a + u ⊗ₜ[ℂ] (planeL n a) := rfl

/-- A pure tensor has the sum of the two signed integer weights. -/
theorem matter_L0_tmul (h p : ℤ) (u : Orbifold) (a : Plane)
    (hu : orbL 0 u = (h : ℂ) • u) (ha : planeL 0 a = (p : ℂ) • a) :
    matter.mode 0 (u ⊗ₜ[ℂ] a) = ((h + p : ℤ) : ℂ) • (u ⊗ₜ[ℂ] a) := by
  rw [matter_mode_tmul, hu, ha, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    Int.cast_add, add_smul]

/-- All powers of the literal critical matter L1, with both lowering orders retained. -/
theorem matter_L1_pow_tmul (s : ℕ) (u : Orbifold) (a : Plane) :
    (matter.mode 1 ^ s) (u ⊗ₜ[ℂ] a) =
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal s, s.choose q.1 •
        (((orbL 1 ^ q.1) u) ⊗ₜ[ℂ] ((planeL 1 ^ q.2) a)) := by
  let F := Module.End.rTensorAlgHom ℂ Orbifold Plane
  let G := Module.End.lTensorAlgHom ℂ Plane Orbifold
  have cross : Commute (F (orbL 1)) (G (planeL 1)) := by
    change ((orbL 1).rTensor Plane).comp ((planeL 1).lTensor Orbifold) =
      ((planeL 1).lTensor Orbifold).comp ((orbL 1).rTensor Plane)
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  change ((F (orbL 1) + G (planeL 1)) ^ s) (u ⊗ₜ[ℂ] a) = _
  rw [cross.add_pow']
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro q _
  rw [← map_pow F, ← map_pow G] <;> rfl

/-- A common pair of lowering bounds supplies a bound for the total tensor power. -/
theorem matter_L1_pow_tmul_eq_zero (A B s : ℕ) (u : Orbifold) (a : Plane)
    (hu : ∀ j : ℕ, A ≤ j → (orbL 1 ^ j) u = 0)
    (ha : ∀ j : ℕ, B ≤ j → (planeL 1 ^ j) a = 0)
    (hs : A + B ≤ s) : (matter.mode 1 ^ s) (u ⊗ₜ[ℂ] a) = 0 := by
  rw [matter_L1_pow_tmul]
  apply Finset.sum_eq_zero
  intro q hq
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
  by_cases h : A ≤ q.1
  · rw [hu q.1 h, TensorProduct.zero_tmul, nsmul_zero]
  · rw [ha q.2 (by omega), TensorProduct.tmul_zero, nsmul_zero]

private theorem orbifold_mem_span_eigen (u : Orbifold) :
    u ∈ Submodule.span ℂ {x : Orbifold | ∃ h : ℤ, orbL 0 x = (h : ℂ) • x} := by
  classical
  let S := Submodule.span ℂ {x : Orbifold | ∃ h : ℤ, orbL 0 x = (h : ℂ) • x}
  let F : LatticeInvolution.FixedCarrier leechData →ₗ[ℂ] Orbifold := LinearMap.inl ℂ _ _
  let T : HalfFock.LatticeHalfFockParityField.paritySpace leechData leechUnit (-1) →ₗ[ℂ]
      Orbifold := LinearMap.inr ℂ _ _
  change u ∈ S
  have hf : F u.1 ∈ S := by
    have expand := congrArg F (fixed_source_expansion leechData leechUnit u.1)
    rw [← expand, map_sum]
    apply S.sum_mem
    intro h _
    let x := fixedProjection leechData leechUnit h u.1
    apply Submodule.subset_span
    refine ⟨h, ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      exact (congrArg Prod.fst (ActualLeechOrbifoldMatter.mode_apply 0
        (F (fixedSourceInclusion leechData h x)))).trans
          ((actualL0_eigen_iff_grade leechData _ (actualInverse_left leechData leechUnit)
            (actualInverse_right leechData leechUnit) h x.val).mpr x.property.1)
    · apply Subtype.ext
      simpa only [F, x, LinearMap.inl_apply, Prod.smul_mk, smul_zero, Submodule.coe_zero,
        map_zero] using
        congrArg Prod.snd (ActualLeechOrbifoldMatter.mode_apply 0
          (F (fixedSourceInclusion leechData h x)))
  have ht : T u.2 ∈ S := by
    have expand := congrArg T (actual_input_basis_expansion leechData leechUnit u.2)
    rw [← expand, map_sum]
    apply S.sum_mem
    intro i _
    rw [map_smul]
    apply S.smul_mem
    apply Submodule.subset_span
    refine ⟨((oddWeight leechData i.val.1 + 3) / 2 : ℕ), ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      simpa only [T, LinearMap.inr_apply, Prod.smul_mk, smul_zero, Submodule.coe_zero,
        map_zero] using
        congrArg Prod.fst (ActualLeechOrbifoldMatter.mode_apply 0
          (T (actualInputBasis leechData leechUnit u.2 i)))
    · apply Subtype.ext
      let t := actualInputBasis leechData leechUnit u.2 i
      have ht := congrArg Prod.snd (ActualLeechOrbifoldMatter.mode_apply 0 (T t))
      change (orbL 0 (T t)).2.val = actualTensorL0 leechData leechUnit t.val at ht
      change (orbL 0 (T t)).2.val = (((((oddWeight leechData i.val.1 + 3) / 2 : ℕ) : ℤ) : ℂ) • t.val)
      simpa only [Int.cast_natCast] using
        ht.trans (actual_input_basis_energy leechData leechUnit leech_spec.1 u.2 i)
  have hsum : F u.1 + T u.2 = u := by
    rcases u with ⟨u, v⟩
    simp [F, T]
  rw [← hsum]
  exact S.add_mem hf ht

private theorem plane_mem_span_eigen (a : Plane) :
    a ∈ Submodule.span ℂ {x : Plane | ∃ h : ℤ, planeL 0 x = (h : ℂ) • x} := by
  classical
  let b := carrierBasis hyperbolicPlane
  let S := Submodule.span ℂ {x : Plane | ∃ h : ℤ, planeL 0 x = (h : ℂ) • x}
  change a ∈ S
  rw [← b.linearCombination_repr a, Finsupp.linearCombination_apply, Finsupp.sum]
  apply S.sum_mem
  intro i hi
  apply S.smul_mem
  exact Submodule.subset_span ⟨energy hyperbolicPlane i,
    actualL0_basis hyperbolicPlane (gramComplex hyperbolicPlane) plane_inverse plane_inverse i⟩

/-- Pure tensors of integer total weight `h` used to span the actual eigenspace. -/
def homogeneousMatterTensors (h : ℤ) : Set Matter :=
  {x | ∃ (p q : ℤ) (u : Orbifold) (a : Plane), p + q = h ∧
    orbL 0 u = (p : ℂ) • u ∧ planeL 0 a = (q : ℂ) • a ∧ x = u ⊗ₜ[ℂ] a}

private theorem matter_span_le_eigenspace (h : ℤ) :
    Submodule.span ℂ (homogeneousMatterTensors h) ≤ (matter.mode 0).eigenspace (h : ℂ) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p, q, u, a, rfl, hu, ha, rfl⟩
  exact Module.End.mem_eigenspace_iff.mpr (matter_L0_tmul p q u a hu ha)

private theorem matter_span_all (x : Matter) :
    x ∈ Submodule.span ℂ (⋃ h : ℤ, homogeneousMatterTensors h) := by
  let S := Submodule.span ℂ (⋃ h : ℤ, homogeneousMatterTensors h)
  change x ∈ S
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => exact S.add_mem hx hy
  | tmul u a =>
    refine Submodule.span_induction (p := fun v _ => v ⊗ₜ[ℂ] a ∈ S)
      ?_ ?_ ?_ ?_ (orbifold_mem_span_eigen u)
    · rintro v ⟨p, hp⟩
      refine Submodule.span_induction (p := fun b _ => v ⊗ₜ[ℂ] b ∈ S)
        ?_ ?_ ?_ ?_ (plane_mem_span_eigen a)
      · rintro b ⟨q, hq⟩
        exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨p + q, p, q, v, b, rfl, hp, hq, rfl⟩)
      · rw [TensorProduct.tmul_zero]
        exact S.zero_mem
      · intro b c _ _ hb hc
        rw [TensorProduct.tmul_add]
        exact S.add_mem hb hc
      · intro c b _ hb
        rw [TensorProduct.tmul_smul]
        exact S.smul_mem c hb
    · rw [TensorProduct.zero_tmul]
      exact S.zero_mem
    · intro v w _ _ hv hw
      rw [TensorProduct.add_tmul]
      exact S.add_mem hv hw
    · intro c v _ hv
      rw [← TensorProduct.smul_tmul']
      exact S.smul_mem c hv

/-- Every vector of an actual signed integer matter eigenspace is a finite
linear combination of pure tensors of that total weight. -/
theorem matter_eigenspace_eq_span (h : ℤ) :
    (matter.mode 0).eigenspace (h : ℂ) = Submodule.span ℂ (homogeneousMatterTensors h) := by
  let E := fun d : ℤ => (matter.mode 0).eigenspace (d : ℂ)
  let S := Submodule.span ℂ (homogeneousMatterTensors h)
  let U := ⨆ d ∈ ({h}ᶜ : Set ℤ), E d
  have cast_inj := Int.cast_injective (α := ℂ)
  have ind : iSupIndep E := (matter.mode 0).eigenspaces_iSupIndep.comp cast_inj
  have disj : Disjoint (E h) U := ind.disjoint_biSup (by simp)
  have hle : Submodule.span ℂ (⋃ d : ℤ, homogeneousMatterTensors d) ≤ S ⊔ U := by
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hx
    by_cases he : d = h
    · subst d
      exact Submodule.mem_sup_left (Submodule.subset_span hd)
    · have hd' : d ∈ ({h}ᶜ : Set ℤ) := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using he
      exact Submodule.mem_sup_right
        (le_iSup₂ (f := fun i (_ : i ∈ ({h}ᶜ : Set ℤ)) => E i) d hd'
          (matter_span_le_eigenspace d (Submodule.subset_span hd)))
  refine le_antisymm ?_ (matter_span_le_eigenspace h)
  intro x hx
  obtain ⟨y, hy, z, hz, hxyz⟩ := Submodule.mem_sup.mp (hle (matter_span_all x))
  have hzy : z = x - y := by rw [← hxyz, add_sub_cancel_left]
  have hzE : z ∈ E h := by
    rw [hzy]
    exact (E h).sub_mem hx (matter_span_le_eigenspace h hy)
  have hz0 : z = 0 := (Submodule.disjoint_def.mp disj) z hzE hz
  rw [hz0, add_zero] at hxyz
  exact hxyz ▸ hy

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.NativeBPZ
