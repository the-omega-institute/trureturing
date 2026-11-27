/- GID: D5/S3/Zeros/GRH/Lib/Cohomology/Hodge/PointClass
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Cohomology/Hodge/PointClass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Cohomology.Hodge.PointClass. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Cohomology/Hodge/PointClass.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Cohomology.WoodsHole.IsolatedCoincidences
import D5.S3.Zeros.GRH.Lib.Cohomology.Hodge.GrothendieckSymbol
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Class of the diagonal and Künneth surjectivity in Hodge cohomology (Grothendieck
symbols) (known result; see Lib.Cohomology.Hodge.FixedPointFormula).

This file: Class of a rational point in Hodge cohomology; independence of choices, excision,
sums. -/

open CategoryTheory Classical Function Ideal TrivSqZeroExt relFreeAb

seal H.map

attribute [local simp] Field.toIsField mem_offPoints_iff isOpenSub_offPoints ComesFromPoints

variable {k} [Field k] {X X' d e R R'} {U : Subfunctor X} {g m} {ξ :
  HodgeH (relFreeAb U) d} (a : EtaleChart e X) {z : X (.of k k)}

/-- For a chart with ring R and e coordinates, and f ∈ R^d, the universal point gives an
equivalence for Hodge coefficients from (h_{(R,R^e)}, locus where some f_i is a unit) to
(Spec R, locus where f generates the unit ideal). -/
lemma EtaleChart.isCohomEquiv_univPoint : ∃ μ : a.R ⟶ HodgeTest.sqZeroExt ⟨_, Fin e⟩,
  LeftInverse fst μ ∧ ∀ {d f S}, S = (@unimodular k _ d).preimage (pointMap ⟨f⟩) →
  ∃ h, IsCohomEquiv hodgeCoeff (map (U' := someUnitLocus (c := ⟨_, _⟩) f) (𝟙 _) h ≫ map (U :=
  S.whisker _) (pointMap ⟨μ⟩) le_rfl) := a.exists_univPoint.imp fun _ ⟨s, j⟩ ↦
  (forall_and.1 j).elim fun j _ ↦ ⟨s, @fun _ f _ e ↦ funext (s ∘' f) ▸ e ▸ ⟨fun _ _ ⟨i, h⟩ ↦
  projSpace.span_eq_top_of_isUnit i (isUnit_iff_isUnit_fst.2 h), Iff.mpr (IsCohomEquiv.comp_iff
  (isCohomEquiv_of_le _ (isCohomEquiv_someUnitLocus <| by apply unimodular.2 ·.baseProj ·.2)))
  (relFreeAb.excision _ .of_top_le (m := mono_of_app_injective j) rfl)⟩⟩

lemma EtaleChart.symbolClass_eq_of_cutsOutLocus {f g : Fin d → a.R} {P x} (D : CutsOutLocus _ P x f)
  (F : CutsOutLocus X' P x g) : symbolClass.map (relFreeAb.map _ D.preimage_fieldLocus_not.le) =
  symbolClass.map (relFreeAb.map _ F.preimage_fieldLocus_not.le) := by
  have hg : _ = span (.range g) := eq_of_forall_ge_iff
    (·.mk_ker ▸ (D _ (CommAlgCat.ofHom (Quotient.mkₐ ..))).trans (F ..).symm)
  choose M hM using fun _ ↦ mem_span_range_iff_exists_fun.1 (hg ▸ mem_span_range_self)
  obtain ⟨⟨μ : _ →ₐ[k] TrivSqZeroExt a.R (_ → a.R)⟩, e : LeftInverse _ μ,
    V⟩ := a.isCohomEquiv_univPoint
  apply ((V D.preimage_fieldLocus_not).2 _).1; erw [← H.map_comp,
    symbolClass_transformation (f := μ ∘ f) (g := μ ∘ g) _ _ _ M M _ (funext
    _).symm, one_smul, H.map_comp] <;>
    first | tauto | (simp [comp_def, e _] <;> assumption) | rw [hg]
  simp [← hM, snd_sum, e _, Ideal.sum_mem, mul_mem_right, mem_span_range_self]

/-- Excision for Hodge cohomology: let u: X' → X be injective on points with open image, and let
every field-valued point outside the image lie in an open subfunctor contained in U. Then u
induces bijections Hdg^n(X, U) → Hdg^n(X', u⁻¹U) for all n. -/
lemma hodge_excision {u : X' ⟶ X} [Mono u] (ho : IsOpenSub (.range u)) (H : ∀ K, IsField K.1 →
  ∀ x ∉ Subfunctor.range u K, ∃ O, IsOpenSub O ∧ x ∈ O K ∧ O ≤ U) {U'} (e : U' = U.preimage u) :
  IsCohomEquiv hodgeCoeff (HodgeTest.sqZeroExt.whiskerLeft (map _ e.le)) := excision (U := U.whisker
  _) ((restrictAlong _).map u) (hasZariskiDescent_hodgeCoeff (isLocallyEverything_of_open_cover
  (byCases (by tauto) <| .imp (by tauto) ∘ H · · ·))) congr(.whisker $e _)

@[local simp ←] lemma HodgeH.map_comp {N N' M} (α : M ⟶ N') β (x : @HodgeH k _ N d) :
    x.map (α ≫ β) = (x.map β).map α := .symm (H.map_comp ..).symm

@[simp] lemma HodgeH.map_zero {N} : ξ.map (N' := N) 0 = 0 := ((H.mapHom ..).flip ξ).map_zero

/-- g ∈ R^d cuts out P at y ∈ X(R), y maps the complement V of that locus into U, and y^*ξ =
m·[dg/g] in Hdg^d(Spec R, V). -/
def IsLocalSymbol ξ y P g (m : k) := ∃ᵉ (D : CutsOutLocus X P y g) (h), HodgeH.map (map (pointMap
  (A := R) y) (U := U) h) ξ = m • .map (map _ D.preimage_fieldLocus_not.le) (@symbolClass k _ d)

lemma IsLocalSymbol.map {y P} (h : IsLocalSymbol ξ y P g m) φ :
    IsLocalSymbol ξ (@X.map R R' φ y) P (φ ∘ g) m := ⟨(by simpa [span_le] using h.1 · <| φ ≫ ·), by
  rw! (transparency := .all) [← pointMap_comp _ (pointMap y)]
  exact ⟨_, by simpa using! congr($(h.2.2).map (relFreeAb.map _ le_rfl))⟩⟩

/-- Every z ∈ s lies in some chart on which d functions g generate the ideal of z and ξ ∈
Hdg^d(X, U) restricts to n(z)·[dg/g]. -/
def IsPointSum (s : Set _) (n : _ → k) (ξ : HodgeH (relFreeAb U) d) := ∀ z ∈ s, ∃ᵉ (a :
  EtaleChart d X) (g), z ∈ a.locus _ ∧ IsLocalSymbol ξ a.point (ComesFromPoints {z}) g (n z)

/-- The class of a k-point z: the image in Hdg^d(X) of a chosen class in Hdg^d(X, X∖z) with
local multiplicity 1 at z (`IsPointSum`), arbitrary if none exists. -/
noncomputable def pointClass d (z : X _) :=
  HodgeH.map (q := d) (π (offPoints {z})) (epsilon (IsPointSum {z} 1))

lemma exists_isOpenSub_le_offPoints [IsSepFunctor X] (h : z ∈ U _) ⦃K⦄ (hK : IsField K.1) ⦃x⦄ (n :
  x ∉ U K) :
  ∃ O, IsOpenSub O ∧ x ∈ O K ∧ O ≤ offPoints {z} := by have := U.map (V := K) structureMap h; aesop

/-- Let X be separated over a field k, a an e-dimensional chart containing z ∈ X(k), g functions
cutting out z on a. Some ξ ∈ Hdg^e(X, X∖z) restricts to [dg/g] on a and satisfies `IsPointSum` for
{z} with multiplicity 1. -/
lemma EtaleChart.exists_isLocalSymbol [IsSepFunctor X] {g} (h : CutsOutLocus X (ComesFromPoints {z})
  a.point g) (w : z ∈ a.locus _) : ∃ ξ : HodgeH (relFreeAb (offPoints {z})) e, IsLocalSymbol ξ
  a.point (ComesFromPoints {z}) g 1 ∧ IsPointSum {z} 1 ξ := ((hodge_excision a.isOpenSub
  (exists_isOpenSub_le_offPoints w) rfl e).2 _).imp fun _ l ↦ (⟨·, by rintro _ ⟨⟩; tauto⟩) ⟨h, _, l⟩

lemma IsPointSum.map_eq_smul_pointClass [IsSepFunctor X] {n ξ} (h : IsPointSum {z} n ξ) :
  .map (π (offPoints {z})) ξ = n z • pointClass d z := by
  have ⟨a, g, hz, h⟩ := h z rfl
  have ⟨b, g₀, e, h'⟩ := epsilon_spec ⟨_, (a.exists_isLocalSymbol h.1 hz).choose_spec.2⟩ _ rfl
  have ⟨c, E⟩ := a.exists_locus_eq_inf b; have ⟨⟨_, e₁⟩, _, e₂⟩ := E ▸ c.point_mem_locus
  obtain ⟨⟨D, _, h⟩, F, _, u⟩ := e₁ ▸ h.map _, e₂ ▸ h'.map _
  rw [c.symbolClass_eq_of_cutsOutLocus D F, ← u.trans (one_smul ..), ← map_smul] at h
  simp [(hodge_excision c.isOpenSub (exists_isOpenSub_le_offPoints (by aesop)) rfl _).1 h,
    pointClass]

/-- Let X be separated, s a finite set of k-points, U = X∖s. If ξ ∈ Hdg^d(X, U) has local
multiplicity n(z) ∈ k at each z ∈ s (`IsPointSum`), its image in Hdg^d(X) is Σ_{z∈s} n(z)·cl(z). -/
lemma IsPointSum.map_eq_sum_pointClass [IsSepFunctor X] {s : Finset _} {n} (h :
  IsPointSum s n ξ) (e : U = offPoints s) : .map (π _) ξ = ∑ z ∈ s, n z • pointClass d z := by
  induction' s using Finset.induction with z s hz ih generalizing U
  simp [(freeAb.hom_ext fun _ _ ↦ mk_eq_zero (e ▸ nofun) : π U = 0)]
  cases show U = offPoints {z} ⊓ offPoints s by aesop (add simp [offPoints, fieldLocus])
  obtain ⟨x, y : HodgeH .., E : y.map (relFreeAb.map _ (by simp)) = _⟩ :=
    ((hodge_excision (u := (offPoints s).ι) (by simp) (exists_isOpenSub_le_offPoints (z :=
    z) (by simpa)) (by ext _ ⟨⟩; apply_rules [and_iff_left]) d).2 (ξ.map (map _
    le_rfl))).imp fun x E ↦ ((LongExactSeq.contravariant
    ((shortExact_triple ..).2.map_of_exact (restrictAlong _)) _).exact_f_g d (ξ - .map (map
    (𝟙 _) (by simp)) x)).1 ((HodgeH.map _).sub_mem_ker_iff.2 (by simpa using! E.symm))
  have O {t A B l l' x y} t' (e : ξ = .map (map (𝟙 X) (U := A) l) x + .map (map (𝟙 X) (U := B)
      l') y) : B = offPoints t' → t = ↑(insert z s) \ t' → IsPointSum t n x := by
    rintro rfl rfl w o; peel 4 h w o.1
    exact ⟨_, by simpa [e, -ComesFromPoints, (hom_ext fun _ _ ↦ mk_eq_zero fun K _ l ↦
      (mem_offPoints_iff l).1 (X.map_comp_apply .. ▸ by_contra (exists_isOpenSub_le_offPoints (z :=
      w) (by aesop) l · |>.elim (by tauto))) : map _ this.1 ≫ map _ l' = 0)] using this.2⟩
  cases add_eq_of_eq_sub' E
  simp [hz, ih (O _ (add_comm ..) rfl _), (O s rfl _ _).map_eq_smul_pointClass, π_map]
