/- GID: D5/S3/Quantum/Dynamics/ProductDynamicsLocalSupport
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/ProductDynamicsLocalSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Product pullbacks preserve or lower finite tensor support. -/

/- Library-search audit trail (2026-08-27):
   * `BipartiteSectorDecomposition.tensorSector` is the canonical two-factor analogue, but its
     binary tensor carrier does not state the finite-family product-dynamics result here.
   * Pinned Mathlib supplies `PiTensorProduct.map`, `map_tprod`, `mapIncl`,
     `PiTensorProduct.induction_on`, and `MultilinearMap.map_add_univ`; these are applied directly.
   * Repository and pinned-Mathlib searches found no theorem expanding finite tensor factors
     `U i sup Z i` into the sum of sectors indexed by subsets of a support finset. -/

import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.Data.Real.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped TensorProduct

namespace D5.S3.Quantum.Dynamics.ProductDynamicsLocalSupport

variable {ι : Type*} [DecidableEq ι]
variable (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module ℝ (M i)]

/-- The finite tensor sector with trace-zero directions on `S` and scalar directions elsewhere. -/
def tensorSector (U Z : ∀ i, Submodule ℝ (M i)) (S : Finset ι) :
    Submodule ℝ (⨂[ℝ] i, M i) :=
  LinearMap.range
    (PiTensorProduct.mapIncl (fun i => if i ∈ S then Z i else U i))

omit [DecidableEq ι] in
private theorem product_map_sector_mono
    (P Q : ∀ i, Submodule ℝ (M i))
    (φ : ∀ i, M i →ₗ[ℝ] M i)
    (hφ : ∀ i, Submodule.map (φ i) (P i) ≤ Q i) :
    ∀ A, A ∈ LinearMap.range (PiTensorProduct.mapIncl P) →
      PiTensorProduct.map φ A ∈ LinearMap.range (PiTensorProduct.mapIncl Q) := by
  intro A hA
  obtain ⟨a, rfl⟩ := hA
  let ψ : ∀ i, P i →ₗ[ℝ] Q i := fun i =>
    LinearMap.codRestrict (Q i) ((φ i).domRestrict (P i)) fun x =>
      hφ i ⟨x, x.property, rfl⟩
  refine ⟨PiTensorProduct.map ψ a, ?_⟩
  have hmaps :
      PiTensorProduct.mapIncl Q ∘ₗ PiTensorProduct.map ψ =
        PiTensorProduct.map φ ∘ₗ PiTensorProduct.mapIncl P := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simp [LinearMap.compMultilinearMap_apply, PiTensorProduct.mapIncl, ψ]
  exact LinearMap.congr_fun hmaps a

private theorem expanded_sector_le
    (U Z : ∀ i, Submodule ℝ (M i))
    (S : Finset ι) :
    LinearMap.range
        (PiTensorProduct.mapIncl
          (fun i => if i ∈ S then U i ⊔ Z i else U i)) ≤
      ⨆ T : {T : Finset ι // T ⊆ S}, tensorSector M U Z T.1 := by
  rintro A ⟨a, rfl⟩
  induction a using PiTensorProduct.induction_on with
  | smul_tprod r x =>
      rw [LinearMap.map_smul]
      apply Submodule.smul_mem
      simp only [PiTensorProduct.mapIncl, PiTensorProduct.map_tprod]
      have hsplit : ∀ i, ∃ z u : M i,
          z ∈ Z i ∧ u ∈ U i ∧ z + u = (x i : M i) ∧ (i ∉ S → z = 0) := by
        intro i
        by_cases hi : i ∈ S
        · have hx : (x i : M i) ∈ U i ⊔ Z i := by
            simpa only [hi, if_true] using (x i).property
          obtain ⟨u, hu, z, hz, huz⟩ := Submodule.mem_sup.mp hx
          exact ⟨z, u, hz, hu, by simpa [add_comm] using huz, fun h => (h hi).elim⟩
        · have hx : (x i : M i) ∈ U i := by
            simpa [hi] using (x i).property
          exact ⟨0, x i, Submodule.zero_mem _, hx, by simp, fun _ => rfl⟩
      choose z u hz hu hsum hzoutside using hsplit
      have htprod :
          PiTensorProduct.tprod ℝ (fun i => (x i : M i)) =
            ∑ T ∈ S.powerset, PiTensorProduct.tprod ℝ (T.piecewise z u) := by
        calc
          PiTensorProduct.tprod ℝ (fun i => (x i : M i)) =
              PiTensorProduct.tprod ℝ (S.piecewise (z + u) u) := by
                congr 1
                funext i
                by_cases hi : i ∈ S
                · simp [hi, hsum i]
                · have hui : u i = (x i : M i) := by
                    simpa [hzoutside i hi] using hsum i
                  simp [hi, hui]
          _ = ∑ T ∈ S.powerset, PiTensorProduct.tprod ℝ (T.piecewise z u) :=
            (PiTensorProduct.tprod ℝ).map_piecewise_add z u S
      change PiTensorProduct.tprod ℝ (fun i => (x i : M i)) ∈
        ⨆ T : {T : Finset ι // T ⊆ S}, tensorSector M U Z T.1
      rw [htprod]
      apply Submodule.sum_mem
      intro T hT
      let Tsub : {T : Finset ι // T ⊆ S} :=
        ⟨T, Finset.mem_powerset.mp hT⟩
      apply (le_iSup (fun R : {R : Finset ι // R ⊆ S} =>
        tensorSector M U Z R.1) Tsub)
      refine ⟨PiTensorProduct.tprod ℝ (fun i =>
        ⟨T.piecewise z u i, ?_⟩), ?_⟩
      · change T.piecewise z u i ∈ if i ∈ T then Z i else U i
        by_cases hi : i ∈ T
        · simpa [hi] using hz i
        · simpa [hi] using hu i
      · simp only [PiTensorProduct.mapIncl, PiTensorProduct.map_tprod]
        rfl
  | add a b ha hb =>
      rw [LinearMap.map_add]
      exact Submodule.add_mem _ ha hb

/-- A product Heisenberg pullback cannot create support outside `S`; if every local pullback also
preserves its trace-zero sector, it preserves the exact sector `S`. -/
private theorem product_pullback_local_support_of_sectors
    (U Z : ∀ i, Submodule ℝ (M i))
    (hdecomp : ∀ i, U i ⊔ Z i = ⊤)
    (φ : ∀ i, M i →ₗ[ℝ] M i)
    (hscalar : ∀ i, Submodule.map (φ i) (U i) ≤ U i)
    (S : Finset ι) :
    (∀ A, A ∈ tensorSector M U Z S →
      PiTensorProduct.map φ A ∈
        ⨆ T : {T : Finset ι // T ⊆ S}, tensorSector M U Z T.1) ∧
    ((∀ i, Submodule.map (φ i) (Z i) ≤ Z i) →
      ∀ A, A ∈ tensorSector M U Z S →
        PiTensorProduct.map φ A ∈ tensorSector M U Z S) := by
  constructor
  · intro A hA
    have hlocal : ∀ i,
        Submodule.map (φ i) (if i ∈ S then Z i else U i) ≤
          if i ∈ S then U i ⊔ Z i else U i := by
      intro i
      by_cases hi : i ∈ S
      · simp only [hi, if_true]
        rw [hdecomp i]
        exact le_top
      · simpa [hi] using hscalar i
    exact expanded_sector_le M U Z S
      (product_map_sector_mono M _ _ φ hlocal A hA)
  · intro hzero A hA
    have hlocal : ∀ i,
        Submodule.map (φ i) (if i ∈ S then Z i else U i) ≤
          if i ∈ S then Z i else U i := by
      intro i
      by_cases hi : i ∈ S
      · simpa [hi] using hzero i
      · simpa [hi] using hscalar i
    exact product_map_sector_mono M _ _ φ hlocal A hA

/-- A product Heisenberg pullback cannot create support outside `S`; if every local pullback also
preserves the kernels of the local traces, it preserves the exact sector `S`. -/
theorem product_pullback_local_support
    (unit : ∀ i, M i)
    (trace : ∀ i, M i →ₗ[ℝ] ℝ)
    (hunitTrace : ∀ i, trace i (unit i) = 1)
    (φ : ∀ i, M i →ₗ[ℝ] M i)
    (hunital : ∀ i, φ i (unit i) = unit i)
    (S : Finset ι) :
    let U := fun i => ℝ ∙ unit i
    let Z := fun i => LinearMap.ker (trace i)
    (∀ A, A ∈ tensorSector M U Z S →
      PiTensorProduct.map φ A ∈
        ⨆ T : {T : Finset ι // T ⊆ S}, tensorSector M U Z T.1) ∧
    ((∀ i, Submodule.map (φ i) (Z i) ≤ Z i) →
      ∀ A, A ∈ tensorSector M U Z S →
        PiTensorProduct.map φ A ∈ tensorSector M U Z S) := by
  dsimp only
  have hdecomp : ∀ i, (ℝ ∙ unit i) ⊔ LinearMap.ker (trace i) = ⊤ := by
    intro i
    apply Submodule.eq_top_iff'.mpr
    intro x
    apply Submodule.mem_sup.mpr
    refine ⟨(trace i x) • unit i, ?_, x - (trace i x) • unit i, ?_, by simp⟩
    · exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self (unit i))
    · change trace i (x - (trace i x) • unit i) = 0
      simp [hunitTrace i]
  have hscalar : ∀ i,
      Submodule.map (φ i) (ℝ ∙ unit i) ≤ ℝ ∙ unit i := by
    intro i
    rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    intro x hx
    have hx' : x = unit i := Set.mem_singleton_iff.mp hx
    subst x
    change φ i (unit i) ∈ ℝ ∙ unit i
    rw [hunital i]
    exact Submodule.mem_span_singleton_self (unit i)
  exact product_pullback_local_support_of_sectors M _ _ hdecomp φ hscalar S

end D5.S3.Quantum.Dynamics.ProductDynamicsLocalSupport
