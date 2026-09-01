/- GID: D5/S3/Quantum/Entanglement/SinglePrimeVisibleSpace
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SinglePrimeVisibleSpace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Single-factor Hermitian readout sees exactly the empty and singleton sectors. -/

import D5.S3.Quantum.Dynamics.ProductDynamicsLocalSupport
import D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/- Library-search audit trail (2026-09-02):
   * Repository exact hits provide `HermitianSpace`, `traceZeroHermitian`,
     `scalarHermitian`, and the arbitrary finite-family `tensorSector`; this module
     imports and reuses all four declarations.
   * Related repository results cover only two factors or one side of a bipartite
     readout, so none covers the present arbitrary finite family.
   * Pinned Mathlib supplies `DirectSum.IsInternal`, `DFinsupp.subtypeDomainLinearMap`,
     `Basis.piTensorProduct`, direct-sum finrank, and rank-nullity. Loogle and
     LeanSearch found no theorem packaging this low/high support decomposition. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators TensorProduct

namespace D5.S3.Quantum.Entanglement.SinglePrimeVisibleSpace

open D5.S3.Quantum.Measurement.BasisMeasurementProjection
open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
open Module

namespace ProductSupport

open D5.S3.Quantum.Dynamics.ProductDynamicsLocalSupport

variable {ι : Type*} [DecidableEq ι]
variable (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module ℝ (M i)]

private theorem sector_mono
    (P Q : ∀ i, Submodule ℝ (M i))
    (hPQ : ∀ i, P i ≤ Q i) :
    LinearMap.range (PiTensorProduct.mapIncl P) ≤
      LinearMap.range (PiTensorProduct.mapIncl Q) := by
  rintro _ ⟨x, rfl⟩
  let inclusion : ∀ i, P i →ₗ[ℝ] Q i := fun i =>
    LinearMap.codRestrict (Q i) (P i).subtype fun x => hPQ i x.property
  refine ⟨PiTensorProduct.map inclusion x, ?_⟩
  have hmaps :
      PiTensorProduct.mapIncl Q ∘ₗ PiTensorProduct.map inclusion =
        PiTensorProduct.mapIncl P := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro y
    simp [LinearMap.compMultilinearMap_apply, PiTensorProduct.mapIncl, inclusion]
  exact LinearMap.congr_fun hmaps x

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

end ProductSupport

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The source's global Hermitian tensor carrier
`Herm(H) = tensor_j Herm(H_j)` (source lines 9359-9367 and 9445-9453). -/
abbrev GlobalHermitian (d : ι → Nat) :=
  ⨂[ℝ] i, HermitianSpace (d i)

private noncomputable instance globalHermitianFiniteDimensional (d : ι → Nat) :
    FiniteDimensional ℝ (GlobalHermitian d) := by
  exact (Basis.piTensorProduct
    (fun i => Module.finBasis ℝ (HermitianSpace (d i)))).finiteDimensional_of_finite

/-- The source sector `V_S`, with a traceless Hermitian factor on `S` and a
scalar-identity factor off `S` (source lines 9456-9469). -/
def primeSector (d : ι → Nat) (S : Finset ι) :
    Submodule ℝ (GlobalHermitian d) :=
  D5.S3.Quantum.Dynamics.ProductDynamicsLocalSupport.tensorSector
    (fun i => HermitianSpace (d i))
    (fun i => scalarHermitian (d i))
    (fun i => traceZeroHermitian (d i)) S

/-- The tensor effects that are arbitrary Hermitian on factor `i` and scalar
identities on every other factor (source line 9485). -/
def singleFactorEffectSector (d : ι → Nat) (i : ι) :
    Submodule ℝ (GlobalHermitian d) :=
  LinearMap.range (PiTensorProduct.mapIncl fun j =>
    if j ∈ ({i} : Finset ι) then scalarHermitian (d j) ⊔ traceZeroHermitian (d j)
    else scalarHermitian (d j))

/-- The operational visible effect span generated by constants and all complete
single-factor Hermitian effect spaces (source lines 9483-9493). -/
def singlePrimeVisibleSpace (d : ι → Nat) :
    Submodule ℝ (GlobalHermitian d) :=
  primeSector d ∅ ⊔ ⨆ i, singleFactorEffectSector d i

/-- The readout that keeps precisely the components whose sector support has
cardinality at most one (source lines 9483-9493). -/
private noncomputable def sectorDecompositionEquiv (d : ι → Nat)
    (hInternal : DirectSum.IsInternal (primeSector d)) :
    DirectSum (Finset ι) (fun S => primeSector d S) ≃ₗ[ℝ] GlobalHermitian d :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap (primeSector d)) hInternal

def singlePrimeReadout (d : ι → Nat)
    (hInternal : DirectSum.IsInternal (primeSector d)) :
    GlobalHermitian d →ₗ[ℝ]
      DirectSum {S : Finset ι // S.card ≤ 1} (fun S => primeSector d S.1) :=
  (DFinsupp.subtypeDomainLinearMap ℝ (fun S => primeSector d S)
      (fun S => S.card ≤ 1)).comp
    ((sectorDecompositionEquiv d hInternal).symm).toLinearMap

/-- The invisible trace-zero residual is the kernel of all scalar and
single-factor sector coordinates (source lines 9509-9518). -/
def invisibleTraceZeroResidual (d : ι → Nat)
    (hInternal : DirectSum.IsInternal (primeSector d)) :
    Submodule ℝ (GlobalHermitian d) :=
  LinearMap.ker (singlePrimeReadout d hInternal)

private def lowSupport : Option ι → Finset ι
  | none => ∅
  | some i => {i}

private theorem lowSupport_injective :
    Function.Injective (lowSupport (ι := ι)) := by
  intro a b hab
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some j => simpa [lowSupport] using congrArg Finset.card hab
  | some i =>
      cases b with
      | none => simpa [lowSupport] using congrArg Finset.card hab
      | some j =>
          simp only [lowSupport, Finset.singleton_inj] at hab
          simpa [hab]

private theorem singleFactorEffectSector_eq (d : ι → Nat) (i : ι) :
    singleFactorEffectSector d i = primeSector d ∅ ⊔ primeSector d {i} := by
  let M : ι → Type := fun j => HermitianSpace (d j)
  let U := fun j => scalarHermitian (d j)
  let Z := fun j => traceZeroHermitian (d j)
  have hExpanded : singleFactorEffectSector d i ≤
      ⨆ T : {T : Finset ι // T ⊆ {i}}, primeSector d T.1 := by
    simpa [singleFactorEffectSector, primeSector, M, U, Z] using
      (ProductSupport.expanded_sector_le (M := M) U Z {i})
  have hSubsets :
      (⨆ T : {T : Finset ι // T ⊆ {i}}, primeSector d T.1) =
        primeSector d ∅ ⊔ primeSector d {i} := by
    apply le_antisymm
    · refine iSup_le fun T => ?_
      rcases Finset.subset_singleton_iff.mp T.property with h | h
      · simpa [h] using (show primeSector d T.1 ≤
            primeSector d ∅ ⊔ primeSector d {i} from le_sup_left)
      · simpa [h] using (show primeSector d T.1 ≤
            primeSector d ∅ ⊔ primeSector d {i} from le_sup_right)
    · apply sup_le
      · apply le_iSup_of_le (⟨∅, by simp⟩ : {T : Finset ι // T ⊆ {i}})
        rfl
      · apply le_iSup_of_le (⟨{i}, by simp⟩ : {T : Finset ι // T ⊆ {i}})
        rfl
  rw [hSubsets] at hExpanded
  apply le_antisymm hExpanded
  apply sup_le
  · apply ProductSupport.sector_mono
    intro j
    by_cases hji : j = i
    · subst j
      simp [primeSector]
    · simp [primeSector, hji]
  · apply ProductSupport.sector_mono
    intro j
    by_cases hji : j = i
    · subst j
      simp [primeSector]
    · simp [primeSector, hji]

private theorem low_sector_finrank (d : ι → Nat)
    (hInternal : DirectSum.IsInternal (primeSector d))
    (hSectorDim : ∀ S, Module.finrank ℝ (primeSector d S) =
      ∏ j ∈ S, (d j ^ 2 - 1)) :
    Module.finrank ℝ ↥(primeSector d ∅ ⊔ (⨆ i : ι, primeSector d {i})) =
      1 + ∑ i, (d i ^ 2 - 1) := by
  have hIndep : iSupIndep (fun o => primeSector d (lowSupport o)) :=
    hInternal.submodule_iSupIndep.comp lowSupport_injective
  have hinj : Function.Injective
      (DirectSum.coeLinearMap (fun o => primeSector d (lowSupport o))) :=
    hIndep.dfinsupp_lsum_injective
  have hrange : LinearMap.range
      (DirectSum.coeLinearMap (fun o => primeSector d (lowSupport o))) =
      primeSector d ∅ ⊔ ⨆ i, primeSector d {i} := by
    rw [DirectSum.range_coeLinearMap, iSup_option]
    rfl
  rw [← hrange, LinearMap.finrank_range_of_inj hinj, Module.finrank_directSum]
  rw [Fintype.sum_option]
  change Module.finrank ℝ (primeSector d ∅) +
      ∑ i, Module.finrank ℝ (primeSector d {i}) = _
  rw [hSectorDim ∅]
  simp only [Finset.prod_empty]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hSectorDim {i}]
  simp

private theorem globalHermitian_finrank (d : ι → Nat) :
    Module.finrank ℝ (GlobalHermitian d) = (∏ i, d i) ^ 2 := by
  let b := fun i => Module.finBasis ℝ (HermitianSpace (d i))
  rw [Module.finrank_eq_card_basis (Basis.piTensorProduct b), Fintype.card_pi]
  simp only [Fintype.card_fin]
  simp_rw [hermitian_space_finrank]
  rw [← Finset.prod_pow]

private theorem low_readout_surjective (d : ι → Nat)
    (hInternal : DirectSum.IsInternal (primeSector d)) :
    Function.Surjective (singlePrimeReadout d hInternal) := by
  intro y
  let low : Finset ι → Prop := fun S => S.card ≤ 1
  let extend : DirectSum {S : Finset ι // low S} (fun S => primeSector d S.1) →ₗ[ℝ]
      DirectSum (Finset ι) (fun S => primeSector d S) :=
    DirectSum.toModule ℝ {S : Finset ι // low S}
      (DirectSum (Finset ι) (fun S => primeSector d S)) fun S =>
        DirectSum.lof ℝ (Finset ι) (fun T => primeSector d T) S.1
  let z := extend y
  refine ⟨sectorDecompositionEquiv d hInternal z, ?_⟩
  simp only [singlePrimeReadout, LinearMap.comp_apply]
  change DFinsupp.subtypeDomain (fun S : Finset ι => S.card ≤ 1)
      ((sectorDecompositionEquiv d hInternal).symm
        (sectorDecompositionEquiv d hInternal z)) = y
  rw [(sectorDecompositionEquiv d hInternal).symm_apply_apply]
  change DFinsupp.subtypeDomain low (extend y) = y
  have hextend_single (S : {S : Finset ι // low S})
      (value : primeSector d S.1) :
      extend (DFinsupp.single S value) =
        DirectSum.of (fun T => primeSector d T) S.1 value := by
    change DirectSum.toModule ℝ {S : Finset ι // low S}
        (DirectSum (Finset ι) (fun T => primeSector d T))
        (fun S => DirectSum.lof ℝ (Finset ι) (fun T => primeSector d T) S.1)
        (DirectSum.lof ℝ {S : Finset ι // low S}
          (fun S => primeSector d S.1) S value) = _
    rw [DirectSum.toModule_lof]
    rfl
  induction y using DFinsupp.induction with
  | h0 => simp [extend]
  | ha S value rest hrestS hvalue ih =>
      rw [map_add, DFinsupp.subtypeDomain_add, ih]
      congr 1
      apply DFinsupp.ext
      intro T
      rw [DFinsupp.subtypeDomain_apply, hextend_single]
      by_cases hST : S = T
      · subst T
        rw [DirectSum.of_eq_same, DFinsupp.single_eq_same]
      · rw [DirectSum.of_eq_of_ne]
        · exact (DFinsupp.single_eq_of_ne
            (β := fun R : {R : Finset ι // low R} => primeSector d R.1)
            (fun h => hST h.symm)).symm
        · intro hval
          apply hST
          exact Subtype.ext hval.symm

private theorem residual_eq_high_sectors (d : ι → Nat)
    (hInternal : DirectSum.IsInternal (primeSector d)) :
    invisibleTraceZeroResidual d hInternal =
      ⨆ S : {S : Finset ι // 2 ≤ S.card}, primeSector d S.1 := by
  let high : Submodule ℝ (GlobalHermitian d) :=
    ⨆ S : {S : Finset ι // 2 ≤ S.card}, primeSector d S.1
  apply le_antisymm
  · intro x hx
    have hxLow : ∀ S : Finset ι, S.card ≤ 1 →
        (sectorDecompositionEquiv d hInternal).symm x S = 0 := by
      intro S hS
      have hx' := hx
      change singlePrimeReadout d hInternal x = 0 at hx'
      have hcomponent := DFunLike.congr_fun hx' (⟨S, hS⟩ : {T : Finset ι // T.card ≤ 1})
      change DFinsupp.subtypeDomain (fun T : Finset ι => T.card ≤ 1)
          ((sectorDecompositionEquiv d hInternal).symm x) ⟨S, hS⟩ = 0 at hcomponent
      rw [DFinsupp.subtypeDomain_apply] at hcomponent
      exact hcomponent
    have hcoe : ∀ z : DirectSum (Finset ι) (fun S => primeSector d S),
        (∀ S, S.card ≤ 1 → z S = 0) → DirectSum.coeLinearMap (primeSector d) z ∈ high := by
      intro z
      induction z using DFinsupp.induction with
      | h0 => simp
      | ha S value rest hrestS hvalue ih =>
          intro hz
          have hS : 2 ≤ S.card := by
            by_contra hnot
            have hlow : S.card ≤ 1 := by omega
            have := hz S hlow
            simp [hrestS] at this
            exact hvalue this
          have hrestLow : ∀ T, T.card ≤ 1 → rest T = 0 := by
            intro T hT
            have hne : S ≠ T := by
              intro hEq
              subst T
              omega
            have := hz T hT
            simpa [DFinsupp.single_apply, hne] using this
          rw [map_add]
          apply Submodule.add_mem
          · change DirectSum.coeLinearMap (primeSector d)
                (DirectSum.of (fun T => primeSector d T) S value) ∈ high
            rw [DirectSum.coeLinearMap_of]
            exact (le_iSup (fun T : {T : Finset ι // 2 ≤ T.card} =>
              primeSector d T.1) ⟨S, hS⟩) value.property
          · exact ih hrestLow
    have hxRecompose : DirectSum.coeLinearMap (primeSector d)
        ((sectorDecompositionEquiv d hInternal).symm x) = x := by
      exact (sectorDecompositionEquiv d hInternal).apply_symm_apply x
    rw [← hxRecompose]
    exact hcoe ((sectorDecompositionEquiv d hInternal).symm x) hxLow
  · refine iSup_le fun S => ?_
    intro x hx
    change singlePrimeReadout d hInternal x = 0
    apply DFinsupp.ext
    intro T
    have hne : S.1 ≠ T.1 := by
      intro hEq
      have := S.property
      rw [hEq] at this
      omega
    have hcomponent := hInternal.ofBijective_coeLinearMap_of_mem_ne hne hx
    change DFinsupp.subtypeDomain (fun R : Finset ι => R.card ≤ 1)
        ((sectorDecompositionEquiv d hInternal).symm x) T = 0
    rw [DFinsupp.subtypeDomain_apply]
    simpa only [sectorDecompositionEquiv] using hcomponent

/-- Complete single-prime Hermitian effects see exactly the scalar and singleton
sectors. Their invisible trace-zero residual is exactly the sum of sectors supported
on at least two prime factors, with the two dimensions stated in theorem 119.1. -/
theorem single_prime_visible_space
    (d : ι → Nat)
    (hInternal : DirectSum.IsInternal (primeSector d))
    (hSectorDim : ∀ S, Module.finrank ℝ (primeSector d S) =
      ∏ j ∈ S, (d j ^ 2 - 1)) :
    singlePrimeVisibleSpace d = primeSector d ∅ ⊔ ⨆ i, primeSector d {i} ∧
      Module.finrank ℝ (singlePrimeVisibleSpace d) =
        1 + ∑ i, (d i ^ 2 - 1) ∧
      Module.finrank ℝ (invisibleTraceZeroResidual d hInternal) =
        (∏ i, d i) ^ 2 - 1 - ∑ i, (d i ^ 2 - 1) ∧
      invisibleTraceZeroResidual d hInternal =
        ⨆ S : {S : Finset ι // 2 ≤ S.card}, primeSector d S.1 := by
  have hVisible : singlePrimeVisibleSpace d =
      primeSector d ∅ ⊔ ⨆ i, primeSector d {i} := by
    rw [singlePrimeVisibleSpace]
    apply le_antisymm
    · apply sup_le le_sup_left
      refine iSup_le fun i => ?_
      rw [singleFactorEffectSector_eq]
      exact sup_le le_sup_left
        (le_sup_of_le_right (le_iSup (fun j => primeSector d {j}) i))
    · apply sup_le le_sup_left
      refine iSup_le fun i => le_trans ?_ le_sup_right
      apply le_iSup_of_le i
      rw [singleFactorEffectSector_eq]
      exact le_sup_right
  have hVisibleDim : Module.finrank ℝ (singlePrimeVisibleSpace d) =
      1 + ∑ i, (d i ^ 2 - 1) := by
    rw [hVisible]
    exact low_sector_finrank d hInternal hSectorDim
  have hResidualDim : Module.finrank ℝ (invisibleTraceZeroResidual d hInternal) =
      (∏ i, d i) ^ 2 - 1 - ∑ i, (d i ^ 2 - 1) := by
    have hlowSum :
        (∑ S : {S : Finset ι // S.card ≤ 1}, Module.finrank ℝ (primeSector d S.1)) =
          1 + ∑ i, (d i ^ 2 - 1) := by
      let lowEquiv : Option ι ≃ {S : Finset ι // S.card ≤ 1} :=
        Equiv.ofBijective
          (fun o => ⟨lowSupport o, by cases o <;> simp [lowSupport]⟩)
          ⟨fun a b h => lowSupport_injective (congrArg Subtype.val h), fun S => by
            by_cases hEmpty : S.1 = ∅
            · exact ⟨none, Subtype.ext (by simpa [lowSupport] using hEmpty.symm)⟩
            · have hpos : 0 < S.1.card :=
                Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hEmpty)
              have hcard : S.1.card = 1 := by omega
              obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
              exact ⟨some i, Subtype.ext (by simpa [lowSupport] using hi.symm)⟩⟩
      rw [← lowEquiv.sum_comp]
      simp_rw [hSectorDim]
      rw [Fintype.sum_option]
      change (∏ j ∈ (∅ : Finset ι), (d j ^ 2 - 1)) +
          ∑ i, ∏ j ∈ ({i} : Finset ι), (d j ^ 2 - 1) = _
      simp
    let f := singlePrimeReadout d hInternal
    change Module.finrank ℝ (LinearMap.ker f) = _
    have hsurj : Function.Surjective f := by
      simpa only [f] using low_readout_surjective d hInternal
    have hrank := LinearMap.finrank_range_add_finrank_ker
      (K := ℝ)
      (V := GlobalHermitian d)
      (V₂ := DirectSum {S : Finset ι // S.card ≤ 1}
        (fun S => primeSector d S.1)) f
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top,
      Module.finrank_directSum, hlowSum, globalHermitian_finrank d] at hrank
    omega
  exact ⟨hVisible, hVisibleDim, hResidualDim,
    residual_eq_high_sectors d hInternal⟩

/-- Reverse probe for assertion A4: the public theorem implies that every sector
with support cardinality at least two lies in the readout kernel. -/
example
    (d : ι → Nat)
    (hInternal : DirectSum.IsInternal (primeSector d))
    (hSectorDim : ∀ S, Module.finrank ℝ (primeSector d S) =
      ∏ j ∈ S, (d j ^ 2 - 1))
    (S : Finset ι) (hS : 2 ≤ S.card) :
    primeSector d S ≤ invisibleTraceZeroResidual d hInternal := by
  have h := (single_prime_visible_space d hInternal hSectorDim).2.2.2
  rw [h]
  exact le_iSup (fun T : {T : Finset ι // 2 ≤ T.card} => primeSector d T.1) ⟨S, hS⟩

/-- Trivialization probe for assertion A3: when every local Hilbert dimension is
one, the public residual-dimension formula specializes to zero. -/
example
    (d : ι → Nat)
    (hInternal : DirectSum.IsInternal (primeSector d))
    (hSectorDim : ∀ S, Module.finrank ℝ (primeSector d S) =
      ∏ j ∈ S, (d j ^ 2 - 1))
    (hUnit : ∀ i, d i = 1) :
    Module.finrank ℝ (invisibleTraceZeroResidual d hInternal) = 0 := by
  have h := (single_prime_visible_space d hInternal hSectorDim).2.2.1
  simpa [hUnit] using h

#print axioms single_prime_visible_space

end D5.S3.Quantum.Entanglement.SinglePrimeVisibleSpace
