/- GID: D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnTensor
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SubspaceCodes/MRDDensityColumnTensor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-field MRD density: tensor argument. -/
/-
admission_basis: escape-witness
escape_witness: D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor.tensor_dimension_equality
question_answered: https://github.com/the-omega-institute/trureturing/issues/26598
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27411
Direct frozen declaration identities (not module pins):
none
Per-declaration proof_shape; escape_witness; consumers:
MRDDensityTensor.rectangle: proof_shape=bind-only; escape_witness=none; consumers=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityTuples.weightedFrameMoment, MRDDensityTensor.rectangle_le_kernel_iff, MRDDensityTensor.rectangle_map, MRDDensityTensor.rectangle_mono, MRDDensityTensor.rectangle_range, MRDDensityTensor.rectangle_top_ker, MRDDensityTensor.tensor_detect_left
MRDDensityTensor.rectangle_range: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityTensor.rectangle_finrank, MRDDensityTensor.rectangle_inf_right
MRDDensityTensor.rectangle_mono: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityTensor.tensor_dimension_lower_bound
MRDDensityTensor.rectangle_finrank: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityTensor.tensor_dimension_lower_bound
MRDDensityTensor.rectangle_top_ker: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityTensor.rectangle_inf_right
MRDDensityTensor.rectangle_map: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityTensor.rectangle_inf_right
MRDDensityTensor.rectangle_inf_right: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityTensor.tensor_dimension_lower_bound
MRDDensityTensor.sum_dimension_lower_bound: proof_shape=content; escape_witness=MRDDensityTensor.sum_dimension_lower_bound; consumers=MRDDensityTensor.tensor_dimension_lower_bound
MRDDensityTensor.tensor_dimension_lower_bound: proof_shape=content; escape_witness=MRDDensityTensor.tensor_dimension_lower_bound; consumers=MRDDensityTensor.tensor_dimension_equality, MRDDensityTensor.tensor_direct_frames
MRDDensityTensor.tensor_detect_left: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityTensor.independent_rectangle_separation
MRDDensityTensor.independent_rectangle_separation: proof_shape=content; escape_witness=MRDDensityTensor.independent_rectangle_separation; consumers=MRDDensityTensor.tensor_dimension_equality
MRDDensityTensor.tensor_dimension_equality: proof_shape=content; escape_witness=MRDDensityTensor.tensor_dimension_equality; consumers=MRDDensityTensor.tensor_dimension_strict
MRDDensityTensor.tensor_dimension_strict: proof_shape=content; escape_witness=MRDDensityTensor.tensor_dimension_equality; consumers=MRDDensityTensor.tensor_frames_strict
MRDDensityTensor.tensor_frames_strict: proof_shape=content; escape_witness=MRDDensityTensor.tensor_dimension_equality; consumers=MRDDensityTuples.tuple_tensor_surplus
MRDDensityCounting.rank_factorization: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityCounting.bounded_rank_map_count
MRDDensityCounting.bounded_rank_map_count: proof_shape=content; escape_witness=MRDDensityCounting.bounded_rank_map_count; consumers=MRDDensityTuples.tuple_rank_count
MRDDensityTuples.block_independent_of_joint: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityTensor.tensor_direct_frames
MRDDensityTuples.joint_range: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityTensor.tensor_direct_frames, MRDDensityTuples.tuple_tensor_surplus
MRDDensityTuples.joint_injective_iff: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityTensor.tensor_direct_frames, MRDDensityTuples.joint_rank_lt, MRDDensityTuples.tuple_direct_count
MRDDensityTuples.joint_rank_lt: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityTuples.nondirect_tensor_weight_sum
MRDDensityTuples.tuple_rank_count: proof_shape=content; escape_witness=MRDDensityTuples.tuple_rank_count; consumers=MRDDensityTuples.nondirect_tensor_weight_sum
MRDDensityTuples.tuple_tensor_surplus: proof_shape=content; escape_witness=MRDDensityTensor.tensor_dimension_equality; consumers=MRDDensityTuples.nondirect_tensor_weight_sum
MRDDensityMoments.nondirect_sum_le: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityTuples.nondirect_tensor_weight_sum
MRDDensityTensor.blockMap: proof_shape=bind-only; escape_witness=none; consumers=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityMoments.frame_incidence_product, D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.blocks_probability, D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.generator_block, MRDDensityTensor.rectangle_le_kernel_iff
MRDDensityTensor.rectangle_le_kernel_iff: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityTensor.tensor_constraints_iff
MRDDensityTensor.tensor_constraints_iff: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityTensor.tensor_event_fraction
MRDDensityTensor.tensor_event_fraction: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityTuples.frame_incidence_average
MRDDensityTensor.finrank_sup_le_sum: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityTensor.tensor_direct_frames
MRDDensityTensor.tensor_direct_frames: proof_shape=content; escape_witness=MRDDensityTensor.tensor_direct_frames; consumers=MRDDensityTuples.frame_weight_decomposition
MRDDensityTuples.tuple_direct_count: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityTuples.frame_weight_decomposition
MRDDensityTuples.nondirectTuples: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityTuples.frame_weight_decomposition, MRDDensityTuples.nondirect_tensor_weight_sum
MRDDensityTuples.nondirect_tensor_weight_sum: proof_shape=content; escape_witness=MRDDensityTensor.tensor_dimension_equality; consumers=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityTuples.weighted_frame_moment_limit
MRDDensityTuples.frameTuples: proof_shape=bind-only; escape_witness=none; consumers=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityMoments.frame_incidence_product, D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityTuples.weightedFrameMoment, MRDDensityTuples.frame_incidence_average, MRDDensityTuples.frame_weight_decomposition
MRDDensityTuples.frame_weight_decomposition: proof_shape=content; escape_witness=MRDDensityTuples.frame_weight_decomposition; consumers=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityTuples.weighted_frame_moment_limit
MRDDensityTuples.frame_incidence_average: proof_shape=bind-only; escape_witness=none; consumers=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityMoments.kernel_frame_moment_limit
-/

import D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling
import Mathlib.Algebra.BigOperators.Field
import Mathlib.RingTheory.Flat.Basic

open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityModel
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityCounting

open scoped TensorProduct
open Module TensorProduct

namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor
variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]

noncomputable def rectangle (U : Submodule K E) (V : Submodule K F) :
    Submodule K (E ⊗[K] F) :=
  Submodule.map₂ (TensorProduct.mk K E F) U V

private theorem rectangle_range (U : Submodule K E) (V : Submodule K F) :
    rectangle U V = LinearMap.range (TensorProduct.mapIncl U V) := by
  exact (TensorProduct.range_mapIncl U V).symm

private theorem rectangle_mono {U U' : Submodule K E} {V V' : Submodule K F}
    (hU : U ≤ U') (hV : V ≤ V') : rectangle U V ≤ rectangle U' V' := by
  exact Submodule.map₂_le_map₂ hU hV

private theorem rectangle_finrank [FiniteDimensional K E] [FiniteDimensional K F]
    (U : Submodule K E) (V : Submodule K F) :
    finrank K ↥(rectangle U V) = finrank K U * finrank K V := by
  rw [rectangle_range, LinearMap.finrank_range_of_inj]
  · exact Module.finrank_tensorProduct
  · exact Module.Flat.tensorProduct_mapIncl_injective_of_right U V

private theorem rectangle_top_ker (V : Submodule K F) :
    rectangle (⊤ : Submodule K E) V = LinearMap.ker (LinearMap.lTensor E V.mkQ) := by
  rw [lTensor_mkQ]
  rw [LinearMap.lTensor, TensorProduct.range_map]
  simp only [LinearMap.range_id, Submodule.range_subtype]
  rfl

private theorem rectangle_map {E' F' : Type*} [AddCommGroup E'] [Module K E']
    [AddCommGroup F'] [Module K F'] (f : E →ₗ[K] E') (g : F →ₗ[K] F')
    (U : Submodule K E) (V : Submodule K F) :
    (rectangle U V).map (TensorProduct.map f g) = rectangle (U.map f) (V.map g) := by
  unfold rectangle
  rw [Submodule.map_map₂, Submodule.map₂_map_map]
  rfl

private theorem rectangle_inf_right (U : Submodule K E) (V W : Submodule K F) :
    rectangle U V ⊓ rectangle (⊤ : Submodule K E) W = rectangle U (V ⊓ W) := by
  let a := TensorProduct.mapIncl U V
  let b := LinearMap.lTensor E W.mkQ
  let h := W.mkQ.comp V.subtype
  let c := LinearMap.rTensor (F ⧸ W) U.subtype
  have hc : Function.Injective c :=
    Module.Flat.rTensor_preserves_injective_linearMap U.subtype U.subtype_injective
  have hab : b.comp a = c.comp (LinearMap.lTensor U h) := by
    exact AlgebraTensorModule.ext fun x => congrFun rfl
  have hker : LinearMap.ker (b.comp a) = LinearMap.ker (LinearMap.lTensor U h) := by
    rw [hab]
    ext z
    change c ((LinearMap.lTensor U h) z) = 0 ↔ (LinearMap.lTensor U h) z = 0
    constructor
    · intro hz
      apply hc
      simpa using hz
    · intro hz
      simp [hz]
  have hex := Module.Flat.lTensor_exact U h.exact_subtype_ker_map
  have hker' : LinearMap.ker (LinearMap.lTensor U h) =
      LinearMap.range (LinearMap.lTensor U (LinearMap.ker h).subtype) :=
    hex.linearMap_ker_eq
  have hrect : LinearMap.range (LinearMap.lTensor U (LinearMap.ker h).subtype) =
      rectangle (⊤ : Submodule K U) (LinearMap.ker h) := by
    rw [LinearMap.lTensor, TensorProduct.range_map]
    simp only [LinearMap.range_id, Submodule.range_subtype]
    rfl
  have hkh : (LinearMap.ker h).map V.subtype = V ⊓ W := by
    have hh : LinearMap.ker h = W.comap V.subtype := by
      ext x
      simp [h, LinearMap.mem_ker]
    rw [hh, Submodule.map_comap_subtype]
  rw [rectangle_range, rectangle_top_ker]
  change LinearMap.range a ⊓ LinearMap.ker b = _
  rw [← Submodule.map_top a, Submodule.map_inf_eq_map_inf_comap, top_inf_eq]
  change (LinearMap.ker (b.comp a)).map a = _
  rw [hker, hker', hrect]
  change (rectangle (⊤ : Submodule K U) (LinearMap.ker h)).map
    (TensorProduct.map U.subtype V.subtype) = _
  rw [rectangle_map, Submodule.map_top, Submodule.range_subtype, hkh]

private theorem sum_dimension_lower_bound
    {K E F ι : Type*} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]
    [DecidableEq ι] (T : ι → Submodule K E) (V : ι → Submodule K F) (r : ℕ)
    (hT : ∀ i, finrank K ↥(T i) = r * finrank K ↥(V i))
    (hI : ∀ (s : Finset ι) (i : ι), i ∉ s →
      finrank K ↥(s.sup T ⊓ T i : Submodule K E) ≤
        r * finrank K ↥(s.sup V ⊓ V i : Submodule K F))
    (s : Finset ι) : r * finrank K ↥(s.sup V) ≤ finrank K ↥(s.sup T) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty, Finset.sup_empty, finrank_bot, finrank_bot, Nat.mul_zero]
  | @insert i s hi ih =>
    rw [Finset.sup_insert, Finset.sup_insert]
    have ht := Submodule.finrank_sup_add_finrank_inf_eq (s.sup T) (T i)
    have hv := Submodule.finrank_sup_add_finrank_inf_eq (s.sup V) (V i)
    have hv' := congrArg (fun n : ℕ => r * n) hv
    rw [Nat.mul_add, Nat.mul_add] at hv'
    rw [hT i] at ht
    have hbound := hI s i hi
    rw [sup_comm (T i), sup_comm (V i)]
    omega

private theorem tensor_dimension_lower_bound
    {ι : Type*} [FiniteDimensional K E] [FiniteDimensional K F] [DecidableEq ι]
    (U : ι → Submodule K E) (V : ι → Submodule K F) (r : ℕ)
    (hU : ∀ i, finrank K ↥(U i) = r) (s : Finset ι) :
    r * finrank K ↥(s.sup V) ≤ finrank K ↥(s.sup fun i => rectangle (U i) (V i)) := by
  apply sum_dimension_lower_bound (fun i => rectangle (U i) (V i)) V r
  · intro i
    rw [rectangle_finrank, hU]
  · intro t i _
    have ht : t.sup (fun j => rectangle (U j) (V j)) ≤ rectangle ⊤ (t.sup V) := by
      apply Finset.sup_le
      intro j hj
      exact rectangle_mono le_top (Finset.le_sup hj)
    have hi : t.sup (fun j => rectangle (U j) (V j)) ⊓ rectangle (U i) (V i) ≤
        rectangle (U i) ((t.sup V) ⊓ V i) := by
      rw [inf_comm (t.sup _), inf_comm (t.sup V), ← rectangle_inf_right]
      exact inf_le_inf_left _ ht
    have hdim := Submodule.finrank_mono hi
    rwa [rectangle_finrank, hU i] at hdim

private theorem tensor_detect_left (U : Submodule K E) {H : Type*}
    [AddCommGroup H] [Module K H] (u : E) (v : H) (hv : v ≠ 0)
    (h : u ⊗ₜ[K] v ∈ rectangle U (⊤ : Submodule K H)) : u ∈ U := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K hv
  let c : E ⊗[K] H →ₗ[K] E :=
    (TensorProduct.rid K E).toLinearMap.comp (φ.lTensor E)
  have hc : rectangle U (⊤ : Submodule K H) ≤ U.comap c := by
    apply Submodule.map₂_le.mpr
    intro x hx y _
    change c (x ⊗ₜ[K] y) ∈ U
    simpa [c] using U.smul_mem (φ y) hx
  have hh := hc h
  change c (u ⊗ₜ[K] v) ∈ U at hh
  simpa [c, hφ] using hh

private theorem independent_rectangle_separation
    {ι : Type*} [DecidableEq ι] [FiniteDimensional K E]
    (U : Submodule K E) (Us : ι → Submodule K E) (Vs : ι → Submodule K F)
    (W : Submodule K F) (hVs : iSupIndep Vs)
    (hU : ∀ i, finrank K ↥(Us i) = finrank K U)
    (hneq : ∀ i, Us i ≠ U) (hW : W ≤ ⨆ i, Vs i)
    (hrect : rectangle U W ≤ ⨆ i, rectangle (Us i) (Vs i)) : W = ⊥ := by
  classical
  let l : (Π₀ i, Vs i) →ₗ[K] F := DFinsupp.lsum ℕ (fun i => (Vs i).subtype)
  obtain ⟨g, hg⟩ := l.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hVs.dfinsupp_lsum_injective)
  have hgl (x : Π₀ i, Vs i) : g (l x) = x := LinearMap.congr_fun hg x
  have hgV (i : ι) (x : Vs i) : g x = DFinsupp.single i x := by
    simpa [l] using hgl (DFinsupp.single i x)
  apply eq_bot_iff.mpr
  intro v hv
  have hcoord : ∀ i : ι, (g v) i = 0 := by
    intro i
    by_contra hn
    let ri : F →ₗ[K] Vs i := (DFinsupp.lapply i).comp g
    have hmap : (⨆ j, rectangle (Us j) (Vs j)) ≤
        (rectangle (Us i) (⊤ : Submodule K (Vs i))).comap (ri.lTensor E) := by
      apply iSup_le
      intro j
      apply Submodule.map₂_le.mpr
      intro x hx y hy
      change x ⊗ₜ[K] ri y ∈ rectangle (Us i) ⊤
      by_cases hji : j = i
      · subst j
        exact Submodule.apply_mem_map₂ _ hx (Submodule.mem_top)
      · have hriy : ri y = 0 := by
          change (g y) i = 0
          rw [hgV j ⟨y, hy⟩]
          simp [DFinsupp.single_apply, hji, Ne.symm hji]
        simp [hriy, rectangle]
    have hle : U ≤ Us i := by
      intro u hu
      have hz := hmap (hrect (Submodule.apply_mem_map₂ _ hu hv))
      change u ⊗ₜ[K] ri v ∈ rectangle (Us i) ⊤ at hz
      exact tensor_detect_left (Us i) u (ri v) hn hz
    exact hneq i (Submodule.eq_of_le_of_finrank_eq hle (hU i).symm).symm
  have hgv : g v = 0 := DFinsupp.ext hcoord
  have hvr : v ∈ LinearMap.range l := by
    simpa [l, ← Submodule.iSup_eq_range_dfinsupp_lsum Vs] using hW hv
  obtain ⟨z, hz⟩ := hvr
  have hz0 : z = 0 := by
    rw [← hgl z, hz, hgv]
  simpa [← hz, hz0] using (show (0 : F) ∈ (⊥ : Submodule K F) from Submodule.zero_mem _)

private theorem tensor_dimension_equality
    {ι : Type*} [FiniteDimensional K E] [FiniteDimensional K F] [DecidableEq ι]
    (U : ι → Submodule K E) (V : ι → Submodule K F) (r : ℕ)
    (hU : ∀ i, finrank K ↥(U i) = r) (hinj : Function.Injective U) (s : Finset ι) :
    finrank K ↥(s.sup fun i => rectangle (U i) (V i)) = r * finrank K ↥(s.sup V) ↔
      s.SupIndep V := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty, Finset.sup_empty, finrank_bot, finrank_bot, Nat.mul_zero]
    simp
  | @insert i s hi ih =>
    let Ts : Submodule K (E ⊗[K] F) := s.sup fun j => rectangle (U j) (V j)
    let Ws : Submodule K F := s.sup V
    let Ti := rectangle (U i) (V i)
    have hinc : Ts ⊓ Ti ≤ rectangle (U i) (Ws ⊓ V i) := by
      have ht : Ts ≤ rectangle ⊤ Ws := by
        apply Finset.sup_le
        intro j hj
        exact rectangle_mono le_top (Finset.le_sup hj)
      rw [inf_comm Ts, inf_comm Ws, ← rectangle_inf_right]
      exact inf_le_inf_left _ ht
    have hI := Submodule.finrank_mono hinc
    rw [rectangle_finrank, hU i] at hI
    have ht := Submodule.finrank_sup_add_finrank_inf_eq Ts Ti
    have hv := Submodule.finrank_sup_add_finrank_inf_eq Ws (V i)
    have hv' := congrArg (fun n : ℕ => r * n) hv
    rw [Nat.mul_add, Nat.mul_add] at hv'
    have hTi : finrank K Ti = r * finrank K ↥(V i) := by
      dsimp [Ti]
      rw [rectangle_finrank, hU i]
    rw [hTi] at ht
    have hprev := tensor_dimension_lower_bound U V r hU s
    change r * finrank K Ws ≤ finrank K Ts at hprev
    constructor
    · intro heq
      rw [Finset.sup_insert, Finset.sup_insert, sup_comm (rectangle (U i) (V i)),
        sup_comm (V i)] at heq
      change finrank K ↥(Ts ⊔ Ti) = r * finrank K ↥(Ws ⊔ V i) at heq
      have hp : finrank K Ts = r * finrank K Ws := by omega
      have hIeq : finrank K ↥(Ts ⊓ Ti : Submodule K (E ⊗[K] F)) =
          r * finrank K ↥(Ws ⊓ V i : Submodule K F) := by omega
      have hpV : s.SupIndep V := ih.mp hp
      have hsubeq : Ts ⊓ Ti = rectangle (U i) (Ws ⊓ V i) := by
        apply Submodule.eq_of_le_of_finrank_eq hinc
        simpa [rectangle_finrank, hU i] using hIeq
      have hzero : Ws ⊓ V i = ⊥ := by
        apply independent_rectangle_separation (U i) (fun j : s => U j)
          (fun j : s => V j) (Ws ⊓ V i) hpV.independent
        · intro j
          rw [hU, hU]
        · intro j h
          exact hi (hinj h ▸ j.property)
        · simpa only [Ts, Ws, iSup_subtype, Finset.sup_eq_iSup] using
            (inf_le_left : Ws ⊓ V i ≤ Ws)
        · have hle : rectangle (U i) (Ws ⊓ V i) ≤ Ts := by
            rw [← hsubeq]
            exact inf_le_left
          simpa only [Ts, Ws, iSup_subtype, Finset.sup_eq_iSup] using hle
      exact hpV.insert (disjoint_iff.mpr (by simpa [inf_comm] using hzero))
    · intro hV
      have hpV : s.SupIndep V := hV.subset (Finset.subset_insert _ _)
      have hdV : Disjoint (V i) Ws := hV (Finset.subset_insert _ _) (Finset.mem_insert_self _ _) hi
      have hdT : Disjoint Ts Ti := by
        apply disjoint_iff.mpr
        apply le_antisymm _ bot_le
        calc
          Ts ⊓ Ti ≤ rectangle (U i) (Ws ⊓ V i) := hinc
          _ = ⊥ := by simp [hdV.symm.eq_bot, rectangle]
      have hp := ih.mpr hpV
      rw [Finset.sup_insert, Finset.sup_insert, sup_comm (rectangle (U i) (V i)),
        sup_comm (V i)]
      change finrank K ↥(Ts ⊔ Ti) = r * finrank K ↥(Ws ⊔ V i)
      have ht' : finrank K ↥(Ts ⊔ Ti) = finrank K Ts + r * finrank K ↥(V i) := by
        rw [hdT.eq_bot, finrank_bot, Nat.add_zero] at ht
        exact ht
      have hv'' : finrank K ↥(Ws ⊔ V i) = finrank K Ws + finrank K ↥(V i) := by
        rw [hdV.symm.eq_bot, finrank_bot, Nat.add_zero] at hv
        exact hv
      rw [ht', hv'', Nat.mul_add]
      simpa only [Ts, Ws] using congrArg (fun n => n + r * finrank K ↥(V i)) hp

private theorem tensor_dimension_strict
    {ι : Type*} [FiniteDimensional K E] [FiniteDimensional K F] [DecidableEq ι]
    (U : ι → Submodule K E) (V : ι → Submodule K F) (r : ℕ)
    (hU : ∀ i, finrank K ↥(U i) = r) (hinj : Function.Injective U) (s : Finset ι)
    (hV : ¬ s.SupIndep V) :
    r * finrank K ↥(s.sup V) + 1 ≤ finrank K ↥(s.sup fun i => rectangle (U i) (V i)) := by
  have hl := tensor_dimension_lower_bound U V r hU s
  have hn := (tensor_dimension_equality U V r hU hinj s).not.mpr hV
  omega

private theorem tensor_frames_strict
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [FiniteDimensional K E] [FiniteDimensional K F]
    (U : ι → Submodule K E) (r : ℕ) (hU : ∀ i, finrank K ↥(U i) = r)
    (hinj : Function.Injective U) (k : ι → ℕ) (v : ∀ i, Fin (k i) → F)
    (hv : ∀ i, LinearIndependent K (v i))
    (hbad : ¬ LinearIndependent K (fun j : Σ i, Fin (k i) => v j.1 j.2)) :
    r * finrank K ↥(Finset.univ.sup (fun i => Submodule.span K (Set.range (v i)))) + 1 ≤
      finrank K ↥(Finset.univ.sup (fun i => rectangle (U i) (Submodule.span K (Set.range (v i))))) := by
  apply tensor_dimension_strict U (fun i => Submodule.span K (Set.range (v i))) r hU hinj
  intro h
  apply hbad
  apply linearIndependent_iUnion_finite hv
  intro i t ht hi
  have h' := (iSupIndep_iff_supIndep_univ.mpr h)
  exact h'.disjoint_biSup hi

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor
open Module
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityCounting
variable {K E F : Type*} [Field K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

private theorem rank_factorization (s : ℕ) (f : E →ₗ[K] F)
    (hf : finrank K ↥(LinearMap.range f) ≤ s) :
    ∃ (a : E →ₗ[K] (Fin s → K)) (b : (Fin s → K) →ₗ[K] F), b.comp a = f := by
  have hs : finrank K ↥(LinearMap.range f) ≤ finrank K (Fin s → K) := by simpa using hf
  obtain ⟨i, hi⟩ := (finrank_le_iff_exists_linearMap).mp hs
  obtain ⟨j, hj⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
  refine ⟨i.comp f.rangeRestrict, (LinearMap.range f).subtype.comp j, ?_⟩
  ext x
  change (j (i (f.rangeRestrict x)) : F) = f x
  rw [show j (i (f.rangeRestrict x)) = f.rangeRestrict x from congrArg
    (fun z : ↥(LinearMap.range f) →ₗ[K] ↥(LinearMap.range f) => z (f.rangeRestrict x)) hj]
  rfl

private theorem bounded_rank_map_count [Fintype K] (s : ℕ) :
    Nat.card {f : E →ₗ[K] F // finrank K ↥(LinearMap.range f) ≤ s} ≤
      Fintype.card K ^ (s * (finrank K E + finrank K F)) := by
  classical
  let p : ((E →ₗ[K] (Fin s → K)) × ((Fin s → K) →ₗ[K] F)) →
      {f : E →ₗ[K] F // finrank K ↥(LinearMap.range f) ≤ s} := fun ab =>
    ⟨ab.2.comp ab.1, le_trans (Submodule.finrank_mono (LinearMap.range_comp_le_range _ _))
      (by simpa using LinearMap.finrank_range_le ab.2)⟩
  have hp : Function.Surjective p := by
    rintro ⟨f, hf⟩
    obtain ⟨a, b, hab⟩ := rank_factorization s f hf
    exact ⟨(a,b), Subtype.ext hab⟩
  letI : Finite E := Nat.finite_of_card_ne_zero (by
    rw [Module.natCard_eq_pow_finrank (K := K), Nat.card_eq_fintype_card]
    exact pow_ne_zero _ Fintype.card_ne_zero)
  letI : Finite F := Nat.finite_of_card_ne_zero (by
    rw [Module.natCard_eq_pow_finrank (K := K), Nat.card_eq_fintype_card]
    exact pow_ne_zero _ Fintype.card_ne_zero)
  letI : Finite (E →ₗ[K] (Fin s → K)) := Finite.of_injective
    (fun f : E →ₗ[K] (Fin s → K) => (f : E → (Fin s → K))) DFunLike.coe_injective
  letI : Finite ((Fin s → K) →ₗ[K] F) := Finite.of_injective
    (fun f : (Fin s → K) →ₗ[K] F => (f : (Fin s → K) → F)) DFunLike.coe_injective
  have hc := Nat.card_le_card_of_surjective p hp
  rw [Nat.card_prod, Module.natCard_eq_pow_finrank (K := K) (V := E →ₗ[K] (Fin s → K)),
    Module.natCard_eq_pow_finrank (K := K) (V := (Fin s → K) →ₗ[K] F),
    Module.finrank_linearMap (R := K) (S := K),
    Module.finrank_linearMap (R := K) (S := K),
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
    Nat.card_eq_fintype_card (α := K), ← pow_add] at hc
  convert hc using 1
  congr 1
  ring

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityCounting
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityCounting
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTuples
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityCounting Module
variable {K E D ι : Type*} [Field K] [Fintype K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup D] [Module K D] [FiniteDimensional K D]
  [Fintype ι] [DecidableEq ι]

private theorem block_independent_of_joint (k : ι → ℕ) (v : ∀ i, Fin (k i) → D)
    (h : LinearIndependent K (fun j : Σ i, Fin (k i) => v j.1 j.2)) :
    ∀ i, LinearIndependent K (v i) := by
  intro i
  exact h.comp (fun j => (⟨i,j⟩ : Σ i, Fin (k i)))
    (fun _ _ h => eq_of_heq (Sigma.mk.inj h).2)

private theorem joint_range (k : ι → ℕ) (v : ∀ i, Fin (k i) → D) :
    LinearMap.range ((Pi.basisFun K (Σ i, Fin (k i))).constr K (fun j : Σ i, Fin (k i) => v j.1 j.2)) =
      Finset.univ.sup (fun i => Submodule.span K (Set.range (v i))) := by
  rw [Basis.constr_range]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨i,j⟩,rfl⟩
    have ht : Submodule.span K (Set.range (v i)) ≤
        Finset.univ.sup (fun i => Submodule.span K (Set.range (v i))) := Finset.le_sup (f := fun i => Submodule.span K (Set.range (v i))) (Finset.mem_univ i)
    exact ht (Submodule.subset_span (Set.mem_range_self j))
  · apply Finset.sup_le
    intro i hi
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact Submodule.subset_span ⟨⟨i,j⟩,rfl⟩

private theorem joint_injective_iff (k : ι → ℕ) (v : ∀ i, Fin (k i) → D) :
    Function.Injective ((Pi.basisFun K (Σ i, Fin (k i))).constr K (fun j : Σ i, Fin (k i) => v j.1 j.2)) ↔
      LinearIndependent K (fun j : Σ i, Fin (k i) => v j.1 j.2) := by
  let b := Pi.basisFun K (Σ i, Fin (k i))
  have he : ((Pi.basisFun K (Σ i, Fin (k i))).constr K (fun j : Σ i, Fin (k i) => v j.1 j.2)) ∘ b = (fun j : Σ i, Fin (k i) => v j.1 j.2) := by
    funext j
    exact b.constr_basis K _ j
  constructor
  · intro h
    rw [← he]
    exact b.linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr h)
  · intro h
    apply LinearMap.ker_eq_bot.mp
    rw [← he] at h
    have hd := Submodule.range_ker_disjoint h
    simpa only [b.span_eq, top_inf_eq] using hd.eq_bot

private theorem joint_rank_lt (k : ι → ℕ) (v : ∀ i, Fin (k i) → D)
    (hv : ¬ LinearIndependent K (fun j : Σ i, Fin (k i) => v j.1 j.2)) :
    finrank K ↥(LinearMap.range ((Pi.basisFun K (Σ i, Fin (k i))).constr K (fun j : Σ i, Fin (k i) => v j.1 j.2))) < ∑ i, k i := by
  have hker : finrank K ↥(LinearMap.ker ((Pi.basisFun K (Σ i, Fin (k i))).constr K (fun j : Σ i, Fin (k i) => v j.1 j.2))) ≠ 0 := by
    intro h
    apply hv
    apply (joint_injective_iff (K := K) k v).mp
    exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp h)
  have h := ((Pi.basisFun K (Σ i, Fin (k i))).constr K (fun j : Σ i, Fin (k i) => v j.1 j.2)).finrank_range_add_finrank_ker
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sigma, Fintype.card_fin] at h
  omega

private theorem tuple_rank_count (k : ι → ℕ) (s : ℕ) :
    Nat.card {v : (∀ i, Fin (k i) → D) // finrank K ↥(LinearMap.range ((Pi.basisFun K (Σ i, Fin (k i))).constr K (fun j : Σ i, Fin (k i) => v j.1 j.2))) ≤ s} ≤
      Fintype.card K ^ (s * ((∑ i, k i) + finrank K D)) := by
  let e : (∀ i, Fin (k i) → D) ≃ (((Σ i, Fin (k i)) → K) →ₗ[K] D) :=
    (Equiv.piCurry (fun i (_ : Fin (k i)) => D)).symm.trans
      ((Pi.basisFun K (Σ i, Fin (k i))).constr K).toEquiv
  let e' : {v : (∀ i, Fin (k i) → D) // finrank K ↥(LinearMap.range ((Pi.basisFun K (Σ i, Fin (k i))).constr K (fun j : Σ i, Fin (k i) => v j.1 j.2))) ≤ s} ≃
      {f : ((Σ i, Fin (k i)) → K) →ₗ[K] D // finrank K ↥(LinearMap.range f) ≤ s} :=
    Equiv.subtypeEquiv e (fun _ => Iff.rfl)
  rw [Nat.card_congr e']
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_sigma, Fintype.card_fin] using
    (bounded_rank_map_count (K := K) (E := (Σ i, Fin (k i)) → K) (F := D) s)

private theorem tuple_tensor_surplus
    (U : ι → Submodule K E) (r : ℕ) (hU : ∀ i, finrank K ↥(U i) = r)
    (hinj : Function.Injective U) (k : ι → ℕ) (v : ∀ i, Fin (k i) → D)
    (hv : ∀ i, LinearIndependent K (v i))
    (hbad : ¬ LinearIndependent K (fun j : Σ i, Fin (k i) => v j.1 j.2)) :
    r * finrank K ↥(LinearMap.range ((Pi.basisFun K (Σ i, Fin (k i))).constr K (fun j : Σ i, Fin (k i) => v j.1 j.2))) + 1 ≤
      finrank K ↥(Finset.univ.sup (fun i => rectangle (U i) (Submodule.span K (Set.range (v i))))) := by
  rw [joint_range]
  exact tensor_frames_strict U r hU hinj k v hv hbad

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTuples
open Module
open scoped Classical BigOperators
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityCounting
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTuples
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityCounting
variable {K E F : Type*} [Field K] [Fintype K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityCounting
open scoped BigOperators
open Finset
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityCounting
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTuples
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityMoments
private theorem nondirect_sum_le {α : Type*} [DecidableEq α]
    (S : Finset α) (rank : α → ℕ) (w : α → ℝ) (q : ℝ) (hq : 1 < q)
    (r m R : ℕ) (h_rank : ∀ x ∈ S, rank x < R)
    (hcard : ∀ s < R, ((S.filter (fun x => rank x = s)).card : ℝ) ≤
      q ^ (s * R + r * m * s))
    (hweight : ∀ x ∈ S, w x ≤ (q ^ (m * (r * rank x + 1)))⁻¹) :
    (∑ x ∈ S, w x) ≤ (∑ s ∈ range R, q ^ (s * R)) * (q ^ m)⁻¹ := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hfib : (∑ s ∈ range R, ∑ x ∈ S.filter (fun x => rank x = s), w x) =
      ∑ x ∈ S, w x := by
    apply sum_fiberwise_of_maps_to
    intro x hx
    exact mem_range.mpr (h_rank x hx)
  rw [← hfib, sum_mul]
  apply sum_le_sum
  intro s hs
  have hw : (∑ x ∈ S.filter (fun x => rank x = s), w x) ≤
      ((S.filter (fun x => rank x = s)).card : ℝ) * (q ^ (m * (r*s+1)))⁻¹ := by
    simpa only [nsmul_eq_mul] using sum_le_card_nsmul
      (S.filter (fun x => rank x = s)) w ((q ^ (m*(r*s+1)))⁻¹) (by
        intro x hx
        obtain ⟨hx, hsx⟩ := mem_filter.mp hx
        simpa only [hsx] using hweight x hx)
  apply hw.trans
  apply (mul_le_mul_of_nonneg_right (hcard s (mem_range.mp hs))
    (inv_nonneg.mpr (pow_nonneg hq0.le _))).trans_eq
  rw [show m * (r*s+1) = r*m*s+m by ring, pow_add, pow_add]
  field_simp [ne_of_gt hq0] <;> ring

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityMoments
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityCounting
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTuples
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityMoments
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor
variable {K E D F : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup D] [Module K D]
  [AddCommGroup F] [Module K F]

noncomputable def blockMap (g : (E ⊗[K] D) →ₗ[K] F) (U : Submodule K E) :
    D →ₗ[K] (U →ₗ[K] F) :=
  ((TensorProduct.curry g).comp U.subtype).flip

private theorem rectangle_le_kernel_iff (g : (E ⊗[K] D) →ₗ[K] F)
    (U : Submodule K E) (V : Submodule K D) :
    rectangle U V ≤ LinearMap.ker g ↔ V ≤ LinearMap.ker (blockMap g U) := by
  constructor
  · intro h y hy
    apply LinearMap.ext
    intro u
    exact h (Submodule.apply_mem_map₂ (TensorProduct.mk K E D) u.property hy)
  · intro h
    apply Submodule.map₂_le.mpr
    intro x hx y hy
    exact LinearMap.congr_fun (h hy) ⟨x,hx⟩

private theorem tensor_constraints_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : (E ⊗[K] D) →ₗ[K] F) (U : ι → Submodule K E)
    (k : ι → ℕ) (v : ∀ i, Fin (k i) → D) :
    (Finset.univ.sup (fun i => rectangle (U i) (Submodule.span K (Set.range (v i))))) ≤
      LinearMap.ker g ↔ ∀ i j, blockMap g (U i) (v i j) = 0 := by
  simp only [Finset.sup_le_iff, Finset.mem_univ, forall_const, rectangle_le_kernel_iff]
  constructor
  · intro h i j
    exact h i (Submodule.subset_span (Set.mem_range_self j))
  · intro h i
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact h i j

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityCounting
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTuples
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityMoments
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityCounting Module
variable {K E D : Type*} [Field K] [Fintype K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup D] [Module K D] [FiniteDimensional K D]
private theorem tensor_event_fraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (U : ι → Submodule K E) (k : ι → ℕ) (v : ∀ i, Fin (k i) → D) :
    (Nat.card {g : (E ⊗[K] D) →ₗ[K] (Fin m → K) // ∀ i j, blockMap g (U i) (v i j) = 0} : ℝ) /
      (Nat.card ((E ⊗[K] D) →ₗ[K] (Fin m → K)) : ℝ) =
      ((Fintype.card K : ℝ) ^
        (finrank K ↥(Finset.univ.sup (fun i => rectangle (U i) (Submodule.span K (Set.range (v i))))) * m))⁻¹ := by
  let T := Finset.univ.sup (fun i => rectangle (U i) (Submodule.span K (Set.range (v i))))
  let e : {g : (E ⊗[K] D) →ₗ[K] (Fin m → K) // ∀ i j, blockMap g (U i) (v i j) = 0} ≃
      {g : (E ⊗[K] D) →ₗ[K] (Fin m → K) // T ≤ LinearMap.ker g} :=
    Equiv.subtypeEquivRight (fun g => (tensor_constraints_iff g U k v).symm)
  rw [Nat.card_congr e]
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
    (annihilating_map_fraction (K := K) (E := E ⊗[K] D) (F := Fin m → K) T)
end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityCounting
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTuples
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityMoments
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor
variable {K E D : Type*} [Field K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup D] [Module K D] [FiniteDimensional K D]
theorem finrank_sup_le_sum {ι : Type*} [DecidableEq ι]
    (V : ι → Submodule K E) (s : Finset ι) :
    finrank K ↥(s.sup V) ≤ ∑ i ∈ s, finrank K ↥(V i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sup_insert, Finset.sum_insert hi]
    have h := Submodule.finrank_sup_add_finrank_inf_eq (V i) (s.sup V)
    omega

private theorem tensor_direct_frames [Fintype K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : ι → Submodule K E) (r : ℕ) (hU : ∀ i, finrank K ↥(U i) = r)
    (k : ι → ℕ) (v : ∀ i, Fin (k i) → D)
    (hv : LinearIndependent K (fun j : Σ i, Fin (k i) => v j.1 j.2)) :
    finrank K ↥(Finset.univ.sup (fun i => rectangle (U i) (Submodule.span K (Set.range (v i))))) =
      r * (∑ i, k i) := by
  have hvi (i : ι) : LinearIndependent K (v i) :=
    D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTuples.block_independent_of_joint k v hv i
  have hw : finrank K ↥(Finset.univ.sup (fun i => Submodule.span K (Set.range (v i)))) = ∑ i, k i := by
    rw [← D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTuples.joint_range]
    have hr := LinearMap.finrank_range_of_inj (D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTuples.joint_injective_iff (K := K) k v |>.mpr hv)
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_sigma, Fintype.card_fin] using hr
  apply le_antisymm
  · apply (finrank_sup_le_sum (fun i => rectangle (U i) (Submodule.span K (Set.range (v i)))) Finset.univ).trans_eq
    simp only [rectangle_finrank, hU, finrank_span_eq_card (hvi _), Fintype.card_fin]
    rw [Finset.mul_sum]
  · simpa only [hw] using tensor_dimension_lower_bound U (fun i => Submodule.span K (Set.range (v i))) r hU Finset.univ

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityCounting
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTuples
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityMoments
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTuples
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityCounting Module
variable {K E D ι : Type*} [Field K] [Fintype K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup D] [Module K D] [FiniteDimensional K D]
  [Fintype ι] [DecidableEq ι]
private theorem tuple_direct_count (k : ι → ℕ) :
    Nat.card {v : (∀ i, Fin (k i) → D) //
      LinearIndependent K (fun j : Σ i, Fin (k i) => v j.1 j.2)} =
      Nat.card {f : ((Σ i, Fin (k i)) → K) →ₗ[K] D // Function.Injective f} := by
  let e : (∀ i, Fin (k i) → D) ≃ (((Σ i, Fin (k i)) → K) →ₗ[K] D) :=
    (Equiv.piCurry (fun i (_ : Fin (k i)) => D)).symm.trans
      ((Pi.basisFun K (Σ i, Fin (k i))).constr K).toEquiv
  let e' : {v : (∀ i, Fin (k i) → D) //
      LinearIndependent K (fun j : Σ i, Fin (k i) => v j.1 j.2)} ≃
      {f : ((Σ i, Fin (k i)) → K) →ₗ[K] D // Function.Injective f} :=
    Equiv.subtypeEquiv e (fun v => (joint_injective_iff (K := K) k v).symm)
  exact Nat.card_congr e'

noncomputable def nondirectTuples [Fintype D] (k : ι → ℕ) : Finset (∀ i, Fin (k i) → D) := by
  classical
  exact Finset.univ.filter (fun v => (∀ i, LinearIndependent K (v i)) ∧
    ¬ LinearIndependent K (fun j : Σ i, Fin (k i) => v j.1 j.2))

theorem nondirect_tensor_weight_sum [Fintype D]
    (U : ι → Submodule K E) (r m : ℕ) (hU : ∀ i, finrank K ↥(U i) = r)
    (hinj : Function.Injective U) (hD : finrank K D = r*m) (k : ι → ℕ) :
    (∑ v ∈ nondirectTuples (K := K) (D := D) k, ((Fintype.card K : ℝ)^(
      m * finrank K ↥(Finset.univ.sup (fun i => rectangle (U i) (Submodule.span K (Set.range (v i)))))))⁻¹) ≤
      (∑ s ∈ Finset.range (∑ i, k i), (Fintype.card K : ℝ)^(s*(∑ i, k i))) *
        ((Fintype.card K : ℝ)^m)⁻¹ := by
  classical
  let S := nondirectTuples (K := K) (D := D) k
  let rank (v : ∀ i, Fin (k i) → D) := finrank K ↥(LinearMap.range ((Pi.basisFun K (Σ i, Fin (k i))).constr K (fun j : Σ i, Fin (k i) => v j.1 j.2)))
  have hq : (1 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.one_lt_card (α := K)
  have hq0 : (0 : ℝ) < Fintype.card K := lt_trans zero_lt_one hq
  apply D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityMoments.nondirect_sum_le S rank _ _ hq r m (∑ i,k i)
  · intro v hv
    exact joint_rank_lt k v (Finset.mem_filter.mp hv).2.2
  · intro s hs
    let e : {v // v ∈ S.filter (fun v => rank v=s)} →
        {v : (∀ i, Fin (k i) → D) // rank v ≤ s} :=
      fun v => ⟨v.val, (Finset.mem_filter.mp v.property).2.le⟩
    have he : Function.Injective e := by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun z : {v : (∀ i, Fin (k i) → D) // rank v ≤ s} => z.val) h
    have hc := Nat.card_le_card_of_injective e he
    have hc' := hc.trans (tuple_rank_count (K := K) (D := D) k s)
    have hcR : ((S.filter (fun v => rank v=s)).card : ℝ) ≤
        (Fintype.card K : ℝ)^(s*((∑ i,k i)+finrank K D)) := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, Nat.cast_pow] using
        (show (Nat.card {v // v ∈ S.filter (fun v => rank v=s)} : ℝ) ≤
          (Fintype.card K : ℝ)^(s*((∑ i,k i)+finrank K D)) by exact_mod_cast hc')
    simpa only [hD, show s*((∑ i,k i)+r*m)=s*(∑ i,k i)+r*m*s by ring] using hcR
  · intro v hv
    have hp := tuple_tensor_surplus U r hU hinj k v
      (Finset.mem_filter.mp hv).2.1 (Finset.mem_filter.mp hv).2.2
    apply inv_anti₀ (pow_pos hq0 _)
    apply pow_le_pow_right₀ hq.le
    exact Nat.mul_le_mul_left m hp

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTuples
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityCounting
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTuples
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityMoments
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTuples
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityCounting Module
variable {K E D ι : Type*} [Field K] [Fintype K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup D] [Module K D] [FiniteDimensional K D] [Fintype D]
  [Fintype ι] [DecidableEq ι]

noncomputable def frameTuples (k : ι → ℕ) : Finset (∀ i, Fin (k i) → D) := by
  classical
  exact Finset.univ.filter (fun v => ∀ i, LinearIndependent K (v i))


theorem frame_weight_decomposition
    (U : ι → Submodule K E) (r m : ℕ) (hU : ∀ i, finrank K ↥(U i) = r)
    (hD : finrank K D = r*m) (k : ι → ℕ) :
    (∑ v ∈ frameTuples (K := K) (D := D) k, ((Fintype.card K : ℝ)^(
      m * finrank K ↥(Finset.univ.sup (fun i => rectangle (U i) (Submodule.span K (Set.range (v i)))))))⁻¹) =
      (Nat.card {f : ((Σ i, Fin (k i)) → K) →ₗ[K] D // Function.Injective f} : ℝ) /
        (Nat.card (((Σ i, Fin (k i)) → K) →ₗ[K] D) : ℝ) +
      (∑ v ∈ nondirectTuples (K := K) (D := D) k, ((Fintype.card K : ℝ)^(
        m * finrank K ↥(Finset.univ.sup (fun i => rectangle (U i) (Submodule.span K (Set.range (v i)))))))⁻¹) := by
  classical
  let p (v : ∀ i, Fin (k i) → D) := LinearIndependent K (fun j : Σ i, Fin (k i) => v j.1 j.2)
  let w (v : ∀ i, Fin (k i) → D) : ℝ := ((Fintype.card K : ℝ)^(
      m * finrank K ↥(Finset.univ.sup (fun i => rectangle (U i) (Submodule.span K (Set.range (v i)))))))⁻¹
  have hdir : (frameTuples (K := K) (D := D) k).filter p = Finset.univ.filter p := by
    ext v
    simp only [frameTuples, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨And.right, fun h => ⟨block_independent_of_joint k v h,h⟩⟩
  have hbad : (frameTuples (K := K) (D := D) k).filter (fun v => ¬p v) = nondirectTuples (K := K) (D := D) k := by
    simp only [frameTuples, nondirectTuples, Finset.filter_filter, p]
  have hsum : (∑ v ∈ Finset.univ.filter p, w v) =
      ((Finset.univ.filter p).card : ℝ) * ((Fintype.card K : ℝ)^(m*(r*(∑ i,k i))))⁻¹ := by
    calc
      _ = ∑ _v ∈ Finset.univ.filter p, ((Fintype.card K : ℝ)^(m*(r*(∑ i,k i))))⁻¹ := by
        apply Finset.sum_congr rfl
        intro v hv
        unfold w
        rw [tensor_direct_frames U r hU k v (Finset.mem_filter.mp hv).2]
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hc : (Finset.univ.filter p).card = Nat.card {v : (∀ i, Fin (k i) → D) // p v} := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hc, tuple_direct_count (K := K) k] at hsum
  have hden : (Nat.card (((Σ i, Fin (k i)) → K) →ₗ[K] D) : ℝ) =
      (Fintype.card K : ℝ)^(m*(r*(∑ i,k i))) := by
    rw [Module.natCard_eq_pow_finrank (K := K), Nat.card_eq_fintype_card (α := K), Nat.cast_pow,
      Module.finrank_linearMap, Module.finrank_fintype_fun_eq_card,
      Fintype.card_sigma, show (∑ i, Fintype.card (Fin (k i))) = ∑ i,k i by simp]
    rw [hD]
    congr 1
    ring
  have hs := Finset.sum_filter_add_sum_filter_not (frameTuples (K := K) (D := D) k) p w
  rw [hdir,hbad,hsum,← hden,← div_eq_mul_inv] at hs
  exact hs.symm

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTuples
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityCounting
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTuples
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityMoments
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTuples
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityCounting Module
variable {K E D ι : Type*} [Field K] [Fintype K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup D] [Module K D] [FiniteDimensional K D] [Fintype D]
  [Fintype ι] [DecidableEq ι]
theorem frame_incidence_average (m : ℕ)
    [Fintype ((E ⊗[K] D) →ₗ[K] (Fin m → K))]
    (U : ι → Submodule K E) (k : ι → ℕ) :
    ((∑ g : (E ⊗[K] D) →ₗ[K] (Fin m → K),
        ∑ v ∈ frameTuples (K := K) (D := D) k,
          (if ∀ i j, blockMap g (U i) (v i j) = 0 then (1 : ℝ) else 0)) /
      (Nat.card ((E ⊗[K] D) →ₗ[K] (Fin m → K)) : ℝ)) =
      ∑ v ∈ frameTuples (K := K) (D := D) k, ((Fintype.card K : ℝ)^(
        m * finrank K ↥(Finset.univ.sup (fun i => rectangle (U i) (Submodule.span K (Set.range (v i)))))))⁻¹ := by
  classical
  simp_rw [Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  rw [← Finset.sum_div]
  have hc : (∑ g : (E ⊗[K] D) →ₗ[K] (Fin m → K),
      (if ∀ i j, blockMap g (U i) (v i j) = 0 then (1 : ℝ) else 0)) =
      (Nat.card {g : (E ⊗[K] D) →ₗ[K] (Fin m → K) // ∀ i j, blockMap g (U i) (v i j) = 0} : ℝ) := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_eq_sum_ones,
      Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro g hg
    split_ifs <;> norm_num
  rw [hc]
  simpa only [Nat.mul_comm] using tensor_event_fraction m U k v
end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTuples
