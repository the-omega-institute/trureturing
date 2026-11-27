/- GID: D5/S3/Zeros/GRH/Lib/PadicHodge/BlochKato/CocycleContinuity
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicHodge/BlochKato/CocycleContinuity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicHodge.BlochKato.CocycleContinuity. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicHodge/BlochKato/CocycleContinuity.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicHodge.Crystalline.Jumps
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Bloch–Kato finite local condition: rank formula and size of its annihilator (known
result; see Lib.PadicHodge.BlochKato.BlochKato).

This file: Filtered de Rham frame; extensions by crystalline cocycles are admissible; such cocycles
are continuous. -/


variable {p} [ThePrime p] {Γ R T C : Type} [Group Γ] [CommRing R] [Algebra ℤ_[p] R] [AddCommGroup T]
  [Module R T] [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T] [AddCommGroup C] [Module R C]
  [OverGp Γ p] {ρ : Representation R Γ T}
open Algebra Submodule Classical Matrix IsScalarTower Finset Function NonarchimedeanGroup algebraMap

/-- Hodge decomposition: for j of open image, T potentially crystalline with finite Z_p-basis e,
there are integers k_i, the jumps of T over Z_p, and a Z_p-linear automorphism of B_dR^ι
turning `coordAction` into the coordinatewise action and mapping (B_dR^+)^ι onto ∏
t^(−k_i)B_dR^+. -/
lemma IsPotCrys.exists_hodge_basis {ι} [Fintype ι] (h : IsPotCrys ρ) e : ∃ k, ∃ N : (ι → BdR)
  ≃ₗ[ℤ_[p]] ι → BdR, HasJumps (overZp ρ) (ofId ..) (univ.1.map k) ∧ (∀ g y, N (coordAction ρ e g
  y) = toGp g • N y) ∧ (∀ b, (∃ x : ι → BdRPlus, N ((↑) ∘ x) = b) ↔ ∀ i, b i ∈ hodgeFil (-k i)) ∧
  ∃ W : _ˣ, ∀ g, (repMatrix ρ e g).map (↑) * toGp g • hodgeMatrix W.1 k = hodgeMatrix W k := by
  choose U u using exists_GL_col_mem_of_span _ ((top_le_span_fixed (ρ :=
    overZp ..) e h (ofId ..)).trans (span_le.2 fun v ⟨_, u, w⟩ ↦
    (is_nonarchimedean _ u).rec fun U M ↦ (span_subset_span ..) (mem_span_fixed toGp (coordAction
    (B := BdR) ρ e) (by simp [coordAction, funext_iff, mulVec_eq_sum, mul_sum, mul_left_comm,
    Algebra.smul_def]) (by simp [comp_def, ← algebraMap_apply] at w; tauto)
    (InfiniteGalois.fixingSubgroup_fixedField ⟨_, U.isClosed⟩).le)))
  choose Y W k P _ E H _ using _root_.exists_hodge_frame Γ le_top U.isUnit fun g ↦ ext_col (u · g)
  have M : IsUnit _ := ⟨U * Y.toGL.map _, E⟩
  refine let L := DistribMulAction.toLinearEquiv _ _ M.unit; ⟨k, L.symm,
      And.left (hasJumps_of_rows e (.map _ P.unit)⁻¹ _ (.of_forall
      (inv_mul_apply_of_isHodgeTateFrame <| isHodgeTateFrame_of_hodgeMatrix <| H ·))), fun g ↦
    L.surjective.forall.2 fun b ↦ ?_, fun b ↦ P.smul_bijective.2.exists.trans ?_, P.unit, H⟩ <;>
    simp [L.symm_apply_eq, mem_hodgeFil, skolem, ← funext_iff, ← M.smul_left_cancel (y := b)]
  simpa [L, funext_iff, coordAction, ↓← mulVec_mulVec, mulVec_apply_eq_sum, smul_sum]
    using congr($(H g) *ᵥ toGp g • b)
  simp [L, funext_iff, hodgeMatrix, mulVec_apply_eq_sum]; field_simp

open Filter Module LinearMap PadicInt crysCocycles
variable (a : C →ₗ[R] crysCocycles ρ) [Free ℤ_[p] T]

/-- The extension of the trivial module C by T along an R-linear map a: C → Z_f(T): the
representation on T × C with g(x, e) = (gx + a(e)(g), e). -/
@[local simp] noncomputable def extensionRep : Representation R Γ (T × C) := ⟨⟨fun g ↦
  ((ρ g).coprod (proj g ∘ₗ (crysCocycles ρ).subtype ∘ₗ a)).prod (snd ..), by
  ext <;> simp; simpa using apply_mul (a _).2 1 1⟩, by
  intros; ext <;> simp [apply_mul (a _).2, add_comm]⟩

/-- If `IsAdmissible` holds for ρ and F, it holds, with the same F, for the extension of the
trivial module C by T defined by an R-linear family a of crystalline cocycles. -/
lemma isAdmissible_extensionRep [Module ℤ_[p] C] [IsScalarTower ℤ_[p] R C]
    {F} (h : IsAdmissible ρ F) : IsAdmissible (extensionRep a) F :=
  isAdmissible_of_one_tmul_mem_span fun (l, x) ↦ (a x).2.rec fun y e ↦
  (sub_mem_iff_left _ (h.baseChange_mem_span_fixedPeriods (f := inl ..) (by simp) (1 ⊗ₜ l + y))).1
  (subset_span (.of_forall fun g ↦ by rw [map_sub, tensorAction_periodTensorMap (R := R), map_add,
  ← add_eq_of_eq_sub (e g)] <;>
  simp [tensorAction, periodTensorMap, ← sub_sub, ← TensorProduct.tmul_sub]))

/-- Let T be finite over R and free over Z_p, and a: C → Z_f(T) be R-linear. For u ≠ 0, the
multiplicity of the jump u at γ in the extension `extensionRep` a is at most that in T. -/
lemma jump_extension_le [Module.Finite R T] {γ u} (hu : u ≠ 0) : jump (extensionRep a) γ u ≤ jump ρ
  γ u := finrank_le_finrank_of_injective (.of_ker (hodgeTateMaps.pull (inl ..) (by simp)) fun f
  e ↦ by ext; apply
  tate_eq_zero_of_chi_twist (neg_ne_zero.2 hu) (nhds_one_le_map_nearOne Γ ((f.2 _).mono fun _
  ↦ (·.symm.trans (by simpa [← sub_mem_ker_iff, Prod.sub_def] using! congr($e.1 _))))))

/-- Let T be finite free over Z_p and potentially crystalline. For c in Z_f(T) and every m, the
value c(g) lies in p^m T for all g with j(g) near 1. -/
lemma crysCocycles.eventually_eq_pow_smul [Module.Finite ℤ_[p] T] (h : IsPotCrys ρ)
    {c} (hc : c ∈ crysCocycles ρ) m : ∀ᶠ g in nearOne Γ, ∃ y, c g = p ^ m • y := by
  have e := finBasis ℤ_[p] T
  obtain ⟨χ : Continuous cyclotomicGp, _ : NormSMulClass ℤ_[p] ℂ_[p], P, k, H, -⟩ :=
    continuous_cycChar p, ⟨(norm_smul ·.1)⟩, IsPotCrys.exists_isHodgeTateFrame (e.prod (.singleton
    Unit _)) (isAdmissible_extensionRep (ρ := overZp ..) (id.smulRight ⟨_, hc⟩) h) (ofId ..)
  filter_upwards [H, Eventually.all fun i ↦ ((by fun_prop : ContinuousAt (fun g ↦ ‖∑ a, P (.inl i)
    a * (cyclotomicGp g ^ (-k a)).1 • g • P⁻¹ a (.inr ())‖) 1).eventually_le_const (u := (p : ℝ) ^
    (-m : ℤ)) (by simp [← Matrix.mul_apply, NeZero.pos])).comap toGp] with g H
  simp [↓← inv_mul_apply_of_isHodgeTateFrame H, ← Matrix.mul_apply, toMatrix_apply,
    algebraMap_eq_smul_one, dvd_def,
    -_root_.zpow_neg, skolem, norm_smul, norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton,
    e.equivFun.surjective.exists, e.ext_elem_iff]
