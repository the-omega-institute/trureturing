/- GID: D5/S3/Zeros/GRH/Lib/PadicComparison/CrystallineFrobenius/DenseRelation
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicComparison/CrystallineFrobenius/DenseRelation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicComparison.CrystallineFrobenius.DenseRelation. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicComparison/CrystallineFrobenius/DenseRelation.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Shimura.AbelianScheme.Specialisation
import D5.S3.Zeros.GRH.Lib.Cohomology.Etale.EllAdicCohomology
import D5.S3.Zeros.GRH.Lib.Cohomology.ProjectiveLine.NormalizationPullback
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Congruence relation for the crystalline Frobenius (known result; see
Lib.PadicComparison.CrystallineFrobenius.CrystallineCohomology).

Part of: Descent of torsion étale cohomology along v-covers; excision, transfer, limits (known
result; see Lib.Cohomology.Etale.ContinuityAtlas).

This file: Transfer: rational cohomology of the base is the invariants of a Galois cover. Relation
among field points of special fibre holds locally modulo z on tests. -/

open CategoryTheory AlgebraicGeometry Fintype Set Fint

/-- Transfer: for W, Y proper over R, Ω the algebraic closure of ℚ as an R-algebra and c: W → Y
a covering with finite group Δ (`IsGaloisCovering`), c^*: V^n(Y) → V^n(W) is injective and
its image contains every Δ-invariant class. -/
lemma ellAdicCohom.transfer {R} [Algebra R.1 Ω] {W Y c Δ a} [IsProper W.hom] [IsProper Y.hom]
    (h : @IsGaloisCovering R Y W c Δ a) ℓ [ThePrime ℓ] n : let V := ellAdicCohom R Ω n
  (⇑(V.map c.op)).Injective ∧
    ∀ y, (∀ g, V.map (a g).asHom.op y = y) → y ∈ range (V.map c.op) := by
  obtain ⟨_, m, l, ν, e, _, _, k⟩ :=
    exists_transfer_map (h.1 · ▸ ((geomPoints _ Ω ⋙ onTests).4 ..).symm)
  dsimp [ellAdicCohom] at *
  let N := (card Δ : ℚ)⁻¹ • ellAdicPull n ν
  refine (k _ (((isProperOver_pointsToBase _).baseChange _).hasCohomDenseImage_of_surjective
    ((isProperOver_pointsToBase _).baseChange _) fun k _ _ y ↦ (exists_point_over _ (h.2.1 _)).rec
    fun x hx ↦ ⟨⟨(_, _), .trans congr(⟨Spec.preimage $(hx ▸ by simp)⟩) y.2⟩, congr(⟨(⟨$hx⟩, _),
    _⟩)⟩) (((isProperOver_pointsToBase _).baseChange _).isCohomDense_of_coincidences (fun g ↦
    cech.proj ((geomPoints ..).2 c) 1 g.1 ≫ (geomPoints ..).2 (a g.2).asHom) fun z B x H ↦
    (@h.3 _ _ (z.1
    0).1.2.1.1.toAlgebra.charZero_of_charZero _ _ congr($(z.2 ..).1.1.1)).exists.imp' .mulRight fun
    d h i ↦ (@H (0, _) (1, i) congr(⟨(⟨$(a.map_mul .. ▸ h =≫ _)⟩, $(z.2 ..).1.2),
    _⟩)).symm)).bijective_ellAdicPull.imp (.of_comp (f := N) ∘ (funext ?_).subst) fun C y _ ↦
    (C (N y)).imp fun _ _ ↦ (e ▸ ellAdicPull.comp
    ..).symm.trans ?_ <;> simp [N, ellAdicPull.comp, ← Nat.cast_smul_eq_nsmul ℚ, *]

open Ideal CommRingCat Finset Quotient Spec ULift Fact Pi

/-- Let R be noetherian, W, Y proper, p ∈ 𝔴, ∑ n_i[Frob^{a_i}u_i(x)] = 0 at field points killing 𝔴.
For some M: if z in O_C has p ∣ z^j and z^{M+1} dividing 𝔴O_C, the relation modulo (p, z) holds
locally everywhere on p-adic points of W. -/
lemma exists_cancels_frobPow_locally {p} [ThePrime p] {R} [CommRing R] [Algebra R OC] {W Y : Over
  (Spec ⟨R⟩)} {I} [Fintype I] n a (u : I → (W ⟶ Y)) [IsNoetherianRing R] [IsProper Y.hom] [IsProper
  W.hom] (𝔴 : Ideal R) (hp : ↑p ∈ 𝔴) (h : CongruenceRelation n 𝔴 p a u) : ∃ M, ∀ z j,
  (p : OC) ∣ z ^ j → (∀ c ∈ 𝔴, z ^ (M + 1) ∣ algebraMap R _ c) →
  ∀ c (x : (testPoints.obj W).obj c) m, IsMaximal m → ∃ b ∉ m, ∀ D [CommRing D] e ρ, IsUnit (ρ b) →
  ρ (c.structureMap z) = 0 → Cancels n fun i ↦ map (ofHom ((@frobPow p D _ _ e
  (a i)).comp ρ)) ≫ x.1.left ≫ (u i).left := have ⟨T, t, _, ht⟩ := exists_finiteType_atlas W.hom
  have := isLocallyNoetherian_Spec.1 (LocallyOfFiniteType.isLocallyNoetherian (t ≫ W.hom))
  let α := 𝔴.map (Spec.preimage (t ≫ W.hom)).1
  have ⟨Z, hZ⟩ := PrimeSpectrum.exists_primeSpectrum_prod_le (T ⧸ α) ⊥
  let q (l : Z) := l.1.1.under T
  ⟨_, fun z j hj hw c x m _ ↦ (ht _ c.isTest.2 x.1.1).elim fun β hb ↦ by
  choose τ hτ using fun i ↦ show ∃ l, ∀ r ∈ q l, c.structureMap z i ∣ β r i by
    let σ := (evalRingHom _ i).comp c.structureMap
    by_contra! r; choose r h₁ h₂ using r
    exact Nat.lt_irrefl _
      ((pow_dvd_pow_iff (by simpa [·, IsCell.p_ne_zero] using map_dvd σ (hw _ hp))
      (mt (isUnit_of_dvd_unit (by simpa using map_dvd σ hj) ∘ .pow _) out)).1 ((mem_span_singleton.1
      (map_le_of_le_comap (K := (span {_}).comap ((evalRingHom ..).comp β.1)) (fun r hr ↦
      mem_span_singleton.2 ((map_pow σ .. ▸ map_dvd σ (hw r hr)).trans congr($(map_injective (a₁ :=
      _ ≫ _) (.trans (by simp) ((hb =≫ _).trans x.1.w))) r i).symm.dvd)) (eq_zero_iff_mem.1 (by
      with_unfolding_all exact (map_prod ..).trans ((Z.map_univ _ ▸ hZ) (prod_mem_prod
        fun _ _ ↦ h₁ _)))))).trans (by simpa using! prod_dvd_prod_of_dvd _ _ fun _ _ ↦
      (ValuationRing.dvd_total ..).resolve_left (h₂ _))))
  refine by_contra fun N ↦ m.one_notMem ((funext (by simp) : ∑ t, ((if τ · = t then 1 else 0) :
    c.ProdRing) = 1) ▸ sum_mem fun l _ ↦ by_contra (N ⟨_, ·, fun _ _ e ρ hk hρ ↦ ?_⟩))
  have h𝔴 : α ≤ q l := le_comap_of_map_le (by simp)
  have E := by simpa using eq_zero_iff_mem.2 (h𝔴 (mem_map_of_mem _ hp))
  convert ((@h (q l).ResidueField _ (.of_eq_zero out (natCast_eq_zero_of_algebra
    E _)) (map (ofHom (algebraMap ..)) ≫ t) (by simpa using! le_comap_of_map_le h𝔴)).mono (v' := fun
    i ↦ map (ofHom ((frobPow E (a i)).comp (Ideal.Quotient.mk _))) ≫ t ≫ (u i).left) fun _ _ j ↦
    up_injective ((isProperOver_pointsToBase Y.hom).ext_of_jointly_injective ![ofHom
    (algebraMap _ (q l).ResidueField)] (by simp) fun _ ↦
    up_inj.2 ?_)).mono fun _ _ ↦ (map (ofHom (lift _ (ρ.comp β.hom) fun r hr ↦ zero_dvd_iff.1 (hρ ▸
    hk.dvd_mul_left.1 (map_mul ρ .. ▸ map_dvd _ (pi_dvd_iff.2 fun i ↦ by
      erw [Pi.mul_apply]
      split <;> simp [*, hτ i r]))))) ≫= ·) using 2
  all_goals (try convert j) <;> simp [← hb, ← map_comp_assoc, -map_comp] <;> congr 2 with <;> aesop⟩
