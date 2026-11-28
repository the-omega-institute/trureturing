/- GID: D5/S3/Zeros/GRH/Lib/PadicHodge/Limit/LocalLimit
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicHodge/Limit/LocalLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicHodge.Limit.LocalLimit. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicHodge/Limit/LocalLimit.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicHodge.Limit.HodgeTateProjectors
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Limits of crystalline representations with bounded weights are crystalline. The hypothesis here
is a uniform limit of traces with unbounded coefficients and ranks, and crystallinity is Liu's
theorem for the image of the group ring. Limit formulas for weight multiplicities and killing
polynomials are also proved. Source: T. Liu, Torsion p-adic Galois representations and a conjecture
of Fontaine, Ann. Sci. ENS 40 (2007) 633–674; L. Berger, Limites de représentations cristallines,
Compositio Math. 140 (2004) 1473–1498; for the passage from traces to the image of the group ring P.
Wake, C. Wang-Erickson, Deformation conditions for pseudorepresentations, Forum Math. Sigma 7
(2019).

This file: Uniform limits of traces keep crystallinity, Hodge-Tate weights and killing
polynomials. -/

attribute [-simp] map_eq_zero isUnit_map_iff
open Matrix Polynomial MonoidAlgebra Finset Module Metric IsUltrametricDist Submodule Set
  hodgeTateMaps TensorProduct Function LinearMap Amax Classical Filter

/-- Let tr r (r continuous, with `IsTraceNondeg`) be a uniform limit of combinations of traces of
continuous representations unramified or crystalline at A, finitely many in all or all with jumps J.
So is r; jump multiplicities and, under coefficientwise uniform convergence, killing polynomials of
bounded degree pass to r.

Known result: Limits of crystalline representations with bounded weights are crystalline. -/
lemma local_clauses_of_trace_limit {ℓ} [ThePrime ℓ] [PadicIso ℓ] {E m I : Type} [Field E]
  [EmbeddedNumberField E] [Fintype m] {r : GalRep ℓ E m} {A} (hr : Continuous r) (hn : IsTraceNondeg
  r) R {R' J} {ι : I → Type} [∀ η, Fintype (ι η)] F [NeBot F] (a J' : ∀ _ _, _) (ρ : ∀ η, ι η →
  PadicRep _ ℓ) (hc : ∀ η i, Continuous (ρ η i).rep) (hU : ∀ η i, IsGoodAt (ρ η i).rep A) (hJ :
  ∀ η i, JumpsRelAt (ρ η i).rep A R' (J' η i)) (hS : Finite I ∨ ∀ η i, HasJumpsAt (ρ η i).rep A J)
  (T : TendstoUniformly (fun η g ↦ ∑ i, a η i * ((ρ η i).rep g).1.trace) (r · |>.1.trace) F) (h' :
  ∀ τ u (x : ∀ _ _, ℕ) (n : ℕ), (∀ η i, R' ((J' η i τ).count u) (x η i)) → F.Tendsto (fun η ↦ ∑ i,
  a η i * x η i) (nhds n) → R ((J τ).count u) n) : IsGoodAt r A ∧ JumpsRelAt r A R J ∧
  ∀ ⦃s N P⦄ ⦃Q : ∀ _ _, _⦄, natDegree P < N → (∀ η i, natDegree (Q η i) < N ∧ PolyKillsAt
  (ρ η i).rep A s (Q η i)) → (∀ l, TendstoUniformly (fun η g ↦ ∑ i, a η i * (Q η i).coeff l *
  ((ρ η i).rep g).1.trace) (fun g ↦ P.coeff l * (r g).1.trace) F) → PolyKillsAt r A s P := by
  let W b c := TendstoUniformly (fun η g ↦ ∑ x, (a * c) η x * ((ρ η x).rep g).1.trace)
    ((b * ·.1.trace) ∘ r) F
  obtain ⟨⟨t₀⟩, T : W 1 1⟩ := F.nonempty_of_neBot, by simpa [W]
  have B {b c} (H : W b c) η hη := (tendstoUniformly_iff.1 H η hη).mono fun n h y ↦ show
    b * (groupRingHom ⟨r⟩ y).trace - ∑ x, (a * c) n x * (groupRingHom _ y).trace ∈ ball 0 η by
    simpa [lift_apply, Finsupp.sum, mul_sum, univ.sum_comm, smul_sub, smul_sum, -mem_ball] using!
      sum_mem (S := ball_openAddSubgroup _ hη) fun g _ ↦ balanced_ball_zero.smul_mem
      (y.coeff g).2 (mem_ball_zero_iff.2 (mem_ball_iff_norm.1 (h g)))
  -- a linear relation that holds in all `ρ θ x` holds in `r`
  have Z S {b c : ℕ → _} (H : ∀ {l}, W (b l) (c l)) (y : ∀ _ _, _) (h : ∀ θ x, ∑ l ∈ S, c l θ x •
      groupRingHom (ρ θ x) _ = 0) {M} (e : ∀ θ, M = ∑ l ∈ S, b l • groupRingHom ⟨r⟩ (y θ l)) :
    M = 0 := hn _ (by simp (maxDischargeDepth := 9) [e t₀, lift_apply, Finsupp.sum, sum_mem,
    smul_of_tower_mem, mem_span_of_mem]) fun g ↦ (tendsto_const_nhds_iff.1 ((tendsto_finsetSum S
    fun l _ ↦ tendsto_nhds.2 (B (@H l) · · |>.mono fun θ h ↦ h (y θ l * .single g 1))).congr
    fun θ ↦ by simpa [e θ, sum_mul, mul_sum, mul_assoc, S.sum_comm] using
    congr(∑ x, _ * ($(h θ x) * ((ρ θ x).rep g).1).trace))).trans sum_const_zero
  obtain ⟨p, g, hg⟩ := @PadicInt.maximalIdeal_eq_span_p ℓ, skolem.1 exists_gp_eq_algHom
  let Δ := decompGroup Gal(Ω/E) A
  let X η := Option.elim' ⟨r⟩ (ρ η)
  refine ⟨⟨fun l s b ↦ by simpa using (Z {0} T (fun _ _ ↦ .single s 1 - 1) (by simp
    [(hU ..).1, *]) fun _ ↦ rfl), @fun l ↦ ?_⟩, fun l γ _ b w ↦ h' _ w _ _ (hJ · · b w) ?_, fun s n
    P Q hP h O ↦ ⟨fun l ↦ Z (range n) @O (fun _ ↦ (.single s 1 ^ ·)) (by simp [(h ..).2.1, *,
    ← aeval_eq_sum_range']) (by simp [aeval_eq_sum_range' hP]), @fun l m k w ↦ ?_⟩⟩ <;> (
    choose L q u _ _ hs hu _ U using fun η ↦ exists_finite_groupRing_quotient Δ (τ :=
      X η) (·.rec hr (hc η))
    have b η : ∀ᶠ k in cofinite, ∀ o γ, jump (decompRep (X η o).rep A) γ k = 0 := exists_jump_bound
      (ρ := actionRep _ (L η) (.domRestrict ((lift _ _ _).symm (q η)) _)).rec fun _ h ↦ (finite_Icc
      ..).subset (h · ∘ mt fun e o γ ↦ jump_eq_zero_iff.2 fun f a ↦ f.ext fun v ↦ (congrArg f (by
      simp [asSemilinear])).trans congr($(jump_eq_zero_iff.1 e _
      (pull (asSemilinear (applyVec (u _ o)) (v, γ)) (by simp [hu, asSemilinear]) ⟨_, a⟩).2) 1))
    have ⟨d, hd⟩ := ((hS.elim (fun _ ↦ .all b) fun H ↦ ((b t₀).and (∑ τ, J
      τ).finite_toSet.compl_mem_cofinite).mono fun k h η ↦ (·.rec (h.1 none) fun x γ ↦ by
      simp at h; erw [← H η x (hg γ)]; simp [*])).image Int.natAbs).bddAbove
    let α := singleHom.comp (((Units.coeHom _).comp (χ⁻¹ ^ d)).prod Δ.subtype)
    have ew {σ} g x : viaGroupRing α σ g x =
      (χ g ^ (-d : ℤ)).1 • decompRep σ.rep A g x := by simp [α]
    have K η o c : IsCrystalline .. ∧ IsCrystallineUpTo (2 * d) (viaGroupRing α (X η o)) := ⟨c,
      c.tate_twist _ ew, fun γ u h ↦ by have := hd ⟨u -
      d, by simp [← jump_twist_cyclotomicGp _ ew]; tauto, rfl⟩; omega⟩
    choose C H using fun θ o ↦ K θ o (o.rec (.tate_twist (isCrystalline_of_trace_limit α hr hn (X :=
      ρ) (K · · (hU ..).2 |>.2) hc (B T · · |>.exists.imp fun _ b y z ↦
      le_of_lt (by simpa [z] using! b y))) d (by simp [α, smul_smul, ← mul_pow])) (hU θ · |>.2)))
  use C t₀ none
  have N {x} : ‖γ x‖ = ‖x‖ := by simp [*, ← smul_coe_Cp]
  choose t z hz S using (exists_uniform_trace_sum_eq_jump _ _ (w - -d)).imp fun t S θ ↦
    S (finBasis ..) 1 (U θ (H θ))
  choose y hy using (hs · <| finBasis ℤ_[ℓ] _ ·)
  refine tendsto_nhds.2 fun ε e ↦ (exists_pos_mul_lt e ‖t‖).elim fun δ ⟨e, k⟩ ↦ (B T δ e).mono fun θ
    h ↦ k.trans_le' (.trans_eq' (norm_mul_le_of_le le_rfl (norm_tsum_le_of_forall_le_of_nonneg e.le
    fun s ↦ (norm_mul_le_of_le (hz θ s) N.le).trans (by simpa using (h (y θ s)).le))) ?_)
  have S o := S θ γ ⟨.toHomUnits _⟩ (u θ o) (by simp [hu]) (by simp) (H θ o).1.isPotCrys
  simpa [← hy, hu, mul_sub, mul_sum, sum_comm (γ := ι _), mul_left_comm (γ _), dist_eq_norm', ← N,
    ↓jump_twist_cyclotomicGp _ ew] using! congr(‖$(S none) - ∑ x, γ (a θ x) * $(S x)‖)
  -- the powers of a Weil element have bounded denominators; linear forms on `Amax` read them
  obtain ⟨⟨δ, D, S⟩, ⟨c⟩⟩ := Lift.uniform_period_bound Δ _, p ▸ nonempty_adicBasis _ p
  choose Y V using fun θ N ↦ span_le (p := (periodTensorMap _ _ id).range.comap (.restrictScalars _
    _ ∘ₗ periodTensorMap _ _ id)).2 (fun y a ↦ ⟨_,
    .symm ((linearFrob_apply (U θ (H θ)).1.isPotCrys (w.pow N) (fixedPeriods.map (by simp)
    ((nearOne _).univ_mem' a))).trans (tensorAction_periodTensorMap (fun _ ↦ id_apply _) ..))⟩)
    (nsmul_mem ((S (finBasis ..) (U θ (H θ))).1 1) ((ℓ ^ (k * d)) ^ (n - N)))
  choose G hG using (Y · · |>.exists_finset)
  choose M V E using fun θ o {Q} (h : natDegree Q < n) v ↦ show ∃ M, periodTensorMap _ _ id M = (δ •
    (ℓ ^ _ :
    Bcris) ^ n) • Q.eval₂ (coefEnd (PadicAlgCl ℓ) _) (linearFrob (decompRep (X θ o).rep A) ..) _ ∧
    ∀ f, lift (lsmul .. ∘ₗ f) M = (∑ N ∈ range n, Q.coeff N • groupRingHom _ (surjInv (hs θ) (lift
    (lsmul .. ∘ₗ f) (Y θ N)))) *ᵥ v from ⟨∑ N ∈ range n, lTensor _ (Q.coeff N • applyVec (u θ o) v)
    (Y θ N), by simpa +contextual [eval₂_eq_sum_range' _ h, smul_sum, periodTensorMap,
    hG, smul_comm _ δ, tmul_eq_smul_one_tmul δ, ← Nat.cast_smul_eq_nsmul Bcris, smul_smul,
    ← pow_add, mem_range_le, _root_.smul_pow, ↓linearFrob_pow (H
    ..).1.isPotCrys w, ↓linearFrob_twist_cyclotomicGp (C ..).isPotCrys w d ew, ↓map_nsmul]
    using congr(∑ N ∈ range n, (coefEnd ..) _ ($((congrArg _ (V θ N)).trans (baseChange_linearFrob
    (U θ (H θ)).1.isPotCrys (w.pow N) (H θ o).1.isPotCrys (applyVec (u θ o) v) (by simp [hu]) _)))),
    by simp [← hu, hG, surjInv_eq, sum_mulVec, smul_sum, smul_comm (Q.coeff _)]⟩
  have Z f := Z _ @O _ (fun θ x ↦ ext_iff_mulVec.2 fun v ↦ by
    erw [← E θ x (h ..).1,
      periodTensorMap_injective (a₂ := 0) ((V ..).trans (((h ..).2.2 w).2 ▸ smul_zero _))]
    simp; rfl) fun θ ↦ ext_iff_mulVec.2 fun v ↦ (E t₀ none hP v f).symm.trans
    (periodTensorMap_injective (V t₀ none hP v ▸ V θ none hP v) ▸ E ..)
  use (C t₀ none).isPotCrys, (isBaseChange ..).algHom_ext _ _ fun v ↦ ?_
  simpa [D.ne_zero, Algebra.smul_def δ, (NeZero.of_faithfulSMul ℚ_[ℓ] _ ℓ).1,
    tensor_eq_zero_of_separating c.eq_zero_of_coord _
    fun f ↦ (E ..).trans (Z _ ▸ zero_mulVec v)] using! (V t₀ none hP v).symm
