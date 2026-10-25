/- GID: D5/S3/Topology/Measures/SignedSplitSuccessorOrdered
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/SignedSplitSuccessorOrdered
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Adaptive signed columns and inherited or birth reference reservoirs -/

import D5.S3.Topology.Measures.SignedSplitSuccessorSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace D5.S3.Topology.Measures.SignedSplitSuccessor

universe u v w

variable {K : Type u} [TopologicalSpace K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]
variable {L : Type v} [TopologicalSpace L] [T2Space L]
  [MeasurableSpace L] [BorelSpace L]

private lemma apply_error_of_finite_marginal {C : Type*} [Fintype C]
    (f : K → (C → Bool)) (hf : Continuous f) (s t : SignedMeasure K)
    (eps : ℝ)
    (hsmall : (SignedMeasure.totalVariation (s.map f - t.map f)).real univ < eps)
    (A : Set K)
    (hA : ∀ x y, f x = f y → (x ∈ A ↔ y ∈ A)) : |s A - t A| < eps := by
  classical
  let D : Set (C → Bool) := f '' A
  have hpre : f ⁻¹' D = A := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact (hA y x hxy).mp hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hm : MeasurableSet D := (isClopen_discrete D).isClosed.measurableSet
  have heval : (s.map f - t.map f) D = s A - t A := by
    rw [_root_.sub_apply, VectorMeasure.map_apply _ hf.measurable hm,
      VectorMeasure.map_apply _ hf.measurable hm, hpre]
  calc
    |s A - t A| = |(s.map f - t.map f) D| := congrArg abs heval.symm
    _ ≤ (SignedMeasure.totalVariation (s.map f - t.map f)).real D := by
      simpa only [Real.norm_eq_abs] using (show SignedMeasure (C → Bool) from s.map f - t.map f).norm_le_totalVariation D
    _ ≤ (SignedMeasure.totalVariation (s.map f - t.map f)).real univ :=
      measureReal_mono (subset_univ D) (measure_ne_top _ _)
    _ < eps := hsmall

/-- Literal finite-depth data; a completed column has one index for every actual row. -/
structure OrderedHistory (Rows : Type w) (K : Type u) [TopologicalSpace K] (q : ℕ) where
  n : Fin q → ℕ
  H : Fin q → TopologicalSpace.Clopens K
  F : Fin q → Finset (TopologicalSpace.Clopens K)
  m : Rows → Fin q → ℕ

/-- One new column, with its clopen tests fixed before its auxiliary choices. -/
structure OrderedColumn (Rows : Type w) (K : Type u) [TopologicalSpace K] where
  n : ℕ
  H : TopologicalSpace.Clopens K
  F : Finset (TopologicalSpace.Clopens K)
  m : Rows → ℕ

/-- Appending uses the literal old data, with no retuning of an earlier entry. -/
def OrderedHistory.append {Rows : Type w} {q : ℕ}
    (h : OrderedHistory Rows K q) (c : OrderedColumn Rows K) : OrderedHistory Rows K (q + 1) where
  n := Fin.snoc h.n c.n
  H := Fin.snoc h.H c.H
  F := Fin.snoc h.F c.F
  m := fun r => Fin.snoc (h.m r) (c.m r)

/-- Exact truncation of all four data families. -/
def OrderedHistory.restrict {Rows : Type w} {q : ℕ}
    (h : OrderedHistory Rows K (q + 1)) : OrderedHistory Rows K q where
  n := fun j => h.n j.castSucc
  H := fun j => h.H j.castSucc
  F := fun j => h.F j.castSucc
  m := fun r j => h.m r j.castSucc

/-- The simultaneous geometric and measured obligations of one literal extension. -/
def OrderedColumn.Spec {Rows : Type w} {q : ℕ}
    (code : Rows → ℕ) (h : OrderedHistory Rows K q)
    (B : ℕ → TopologicalSpace.Clopens K) (S : Set ℕ)
    (p : K → L) (V : ℕ → Set L) (nu : ℕ → SignedMeasure L) (v : Measure K)
    (Base : Rows → Type v)
    [∀ r, TopologicalSpace (Base r)] [∀ r, MeasurableSpace (Base r)]
    (pR : ∀ r, K → Base r) (VR : ∀ r, ℕ → Set (Base r))
    (nuR : ∀ r, ℕ → SignedMeasure (Base r)) (muR : Rows → SignedMeasure K)
    (pool : Rows → Set ℕ) (c : OrderedColumn Rows K) : Prop := by
  classical
  exact
      (h.append c).restrict = h ∧
      c.n ∈ S ∧ (∀ j, h.n j < c.n) ∧
      (∃ A : Finset Rows, (∀ r, r ∈ A ↔ code r < q) ∧
        ∃ R : TopologicalSpace.Clopens K,
          (R : Set K) = ⋃ r ∈ A, ⋃ j : Fin q, pR r ⁻¹' VR r (h.m r j) ∧
          (c.H : Set K) ⊆ p ⁻¹' V c.n \ R ∧
          (∃ D : Set L, IsClopen D ∧ D ⊆ V c.n ∧ (c.H : Set K) = p ⁻¹' D \ R) ∧
          (∀ x y, p x ∈ V c.n → p y ∈ V c.n → p x = p y →
            (x ∈ c.H ↔ y ∈ c.H)) ∧
          c.F = (Finset.univ.biUnion h.F) ∪ {B q, c.H, R}) ∧
      (∀ t : SignedMeasure K, t.map p = nu c.n →
        t.totalVariation univ = (nu c.n).totalVariation univ →
        (13 : ℝ) / 48 < t c.H ∧ (1 : ℝ) / 6 < t c.H) ∧
      ∀ r, c.m r ∈ pool r ∧ (∀ j, h.m r j < c.m r) ∧
        v.real (pR r ⁻¹' VR r (c.m r)) <
          (1 : ℝ) / 128 * (1 / 2 : ℝ) ^ code r * (1 / 2 : ℝ) ^ q ∧
        (∀ A ∈ c.F, ∀ x y,
          pR r x ∈ VR r (c.m r) → pR r y ∈ VR r (c.m r) → pR r x = pR r y →
          (x ∈ A ↔ y ∈ A)) ∧
        ∀ t : SignedMeasure K, t.map (pR r) = nuR r (c.m r) →
          t.totalVariation univ = (nuR r (c.m r)).totalVariation univ →
          (SignedMeasure.totalVariation
            (t.map (fun x (A : {A // A ∈ c.F}) => (A.val : Set K).boolIndicator x) -
              (muR r).map (fun x (A : {A // A ∈ c.F}) => (A.val : Set K).boolIndicator x))).real univ < (1 / 2 : ℝ) ^ q ∧
          ∀ A : Set K,
            (∀ x y, (∀ C ∈ c.F, x ∈ C ↔ y ∈ C) → (x ∈ A ↔ y ∈ A)) →
            |t A - muR r A| < (1 / 2 : ℝ) ^ q

/-- One measured dynamic column is constructed in the order
old history, finite exclusion, target index, literal target slice, clopen tests,
then independently one auxiliary index in every actual row. The input fibre
conditions concern the original separating coordinates, not all clopens or a
moving finite marginal. -/
theorem exists_ordered_signed_column [CompactSpace L] [ZeroDimensionalSpace L]
    {Rows : Type w} {Γ : Type*} {q : ℕ}
    (code : Rows → ℕ) (hcode : Function.Injective code)
    (h : OrderedHistory Rows K q)
    (coord : Γ → C(K, Bool))
    (hsep : Function.Injective (fun x : K => fun c => coord c x))
    (B : ℕ → TopologicalSpace.Clopens K)
    (S : Set ℕ) (hS : S.Infinite) (p : K → L) (hp : Continuous p)
    (V : ℕ → Set L) (hV : ∀ n, IsClopen (V n))
    (nu : ℕ → SignedMeasure L) (s : ℕ → SignedMeasure K)
    (hsmap : ∀ n, (s n).map p = nu n)
    (hsmass : ∀ n, (s n).totalVariation univ = (nu n).totalVariation univ)
    (hnull : ∀ n, (nu n).totalVariation (V n)ᶜ = 0)
    (hposreg : ∀ n, Measure.Regular (nu n).toJordanDecomposition.posPart)
    (hnegreg : ∀ n, Measure.Regular (nu n).toJordanDecomposition.negPart)
    (hpos : ∀ n, (1 : ℝ) / 2 ≤ (nu n).toJordanDecomposition.posPart.real univ)
    (hE : ∀ c, ∀ᶠ n in atTop ⊓ 𝓟 S, ∀ x y,
      p x ∈ V n → p y ∈ V n → p x = p y → coord c x = coord c y)
    (v : Measure K) [IsFiniteMeasure v]
    (href : ∀ A : Set K, IsClopen A →
      Tendsto (fun n => (s n).totalVariation.real A)
        (atTop ⊓ 𝓟 S) (𝓝 (v.real A)))
    (Base : Rows → Type v)
    [∀ r, TopologicalSpace (Base r)] [∀ r, T2Space (Base r)]
    [∀ r, MeasurableSpace (Base r)] [∀ r, BorelSpace (Base r)]
    (pR : ∀ r, K → Base r) (hpR : ∀ r, Continuous (pR r))
    (VR : ∀ r, ℕ → Set (Base r)) (hVR : ∀ r n, IsClopen (VR r n))
    (nuR : ∀ r, ℕ → SignedMeasure (Base r))
    (sR : Rows → ℕ → SignedMeasure K) (muR : Rows → SignedMeasure K)
    (hsRmap : ∀ r n, (sR r n).map (pR r) = nuR r n)
    (hsRmass : ∀ r n, (sR r n).totalVariation univ = (nuR r n).totalVariation univ)
    (hRnull : ∀ r n, (nuR r n).totalVariation (VR r n)ᶜ = 0)
    (pool : Rows → Set ℕ) (hpool : ∀ r, (pool r).Infinite)
    (hRE : ∀ r c, ∀ᶠ n in atTop ⊓ 𝓟 (pool r), ∀ x y,
      pR r x ∈ VR r n → pR r y ∈ VR r n → pR r x = pR r y →
        coord c x = coord c y)
    (hRref : ∀ r, Tendsto
      (fun n => (NormPreservingLifts.signedFunctional (sR r n)).toWeakDual)
      (atTop ⊓ 𝓟 (pool r)) (𝓝 (NormPreservingLifts.signedFunctional (muR r)).toWeakDual))
    (hRdis : ∀ r, Pairwise (fun n m => Disjoint (pR r ⁻¹' VR r n) (pR r ⁻¹' VR r m)))
    (hsmall : ∀ r (j : Fin q), v.real (pR r ⁻¹' VR r (h.m r j)) ≤
      (1 : ℝ) / 128 * (1 / 2 : ℝ) ^ code r * (1 / 2 : ℝ) ^ (j : ℕ)) :
    ∃ c : OrderedColumn Rows K,
      c.Spec code h B S p V nu v Base pR VR nuR muR pool := by
  classical
  let A : Finset Rows := ((Set.finite_Iio q).preimage hcode.injOn).toFinset
  have hA (r : Rows) : r ∈ A ↔ code r < q := by simp [A]
  let W : Rows → ℕ → Set K := fun r j =>
    if hj : j < q then pR r ⁻¹' VR r (h.m r ⟨j, hj⟩) else ∅
  have hW : ∀ r j, IsClopen (W r j) := by
    intro r j
    dsimp only [W]
    split_ifs with hj
    · exact (hVR r _).preimage (hpR r)
    · exact isClopen_empty
  have hWsmall : ∀ r ∈ A, ∀ j < q,
      v.real (W r j) < (1 : ℝ) / 64 * (1 / 2 : ℝ) ^ code r * (1 / 2 : ℝ) ^ j := by
    intro r _ j hj
    have hb : 0 < (1 / 2 : ℝ) ^ code r * (1 / 2 : ℝ) ^ j := by positivity
    have hs := hsmall r ⟨j, hj⟩
    dsimp only [W]
    rw [dite_eq_left hj]
    dsimp only at hs
    nlinarith
  obtain ⟨n, hnS, hnM, H, hH, hsub, hliteral, hHE, hlarge⟩ :=
    exists_target_after_finite_exclusion code hcode A q S hS p hp V hV nu s
      hsmap hsmass hnull hposreg hnegreg hpos W hW
      (fun r _ j _ => eventually_clopen_fibre (atTop ⊓ 𝓟 S) coord hsep p V hE (hW r j))
      v (fun r _ j _ => href (W r j) (hW r j)) hWsmall (Finset.univ.sup h.n)
  let R : TopologicalSpace.Clopens K :=
    ⟨⋃ r ∈ A, ⋃ j ∈ Finset.range q, W r j,
      isClopen_biUnion_finset (fun r _ => isClopen_biUnion_finset (fun j _ => hW r j))⟩
  let Hc : TopologicalSpace.Clopens K := ⟨H, hH⟩
  let F : Finset (TopologicalSpace.Clopens K) :=
    (Finset.univ.biUnion h.F) ∪ {B q, Hc, R}
  let test : {A // A ∈ F} → C(K, Bool) := fun A =>
    ⟨(A.val : Set K).boolIndicator,
      (continuous_boolIndicator_iff_isClopen _).mpr A.val.isClopen⟩
  have hex (r : Rows) := exists_auxiliary_index (pool r) (hpool r) (pR r) (hpR r)
    (VR r) (hVR r) (nuR r) (sR r) (muR r) (hsRmap r) (hsRmass r) (hRnull r) test
    (fun A => by
      filter_upwards [eventually_clopen_fibre (atTop ⊓ 𝓟 (pool r)) coord hsep
        (pR r) (VR r) (hRE r) A.val.isClopen] with k hk
      intro x y hx hy hxy
      have heq := hk x y hx hy hxy
      change (A.val : Set K).boolIndicator x = (A.val : Set K).boolIndicator y
      simp only [Set.boolIndicator, heq])
    (hRref r) v (hRdis r) (Finset.univ.sup (h.m r))
    ((1 / 2 : ℝ) ^ q) ((1 : ℝ) / 128 * (1 / 2 : ℝ) ^ code r * (1 / 2 : ℝ) ^ q)
    (by positivity) (by positivity)
  choose m hmPool hmM hmSmall hmE hmMarginal using hex
  let c : OrderedColumn Rows K := ⟨n, Hc, F, m⟩
  refine ⟨c, ?_, hnS, ?_, ⟨A, hA, R, ?_, hsub, hliteral, hHE, rfl⟩, hlarge, ?_⟩
  · cases h
    simp only [OrderedHistory.append, OrderedHistory.restrict, Fin.snoc_castSucc]
  · intro j
    exact (Finset.le_sup (s := Finset.univ) (f := h.n) (Finset.mem_univ j)).trans_lt hnM
  · ext x
    simp only [R, TopologicalSpace.Clopens.coe_mk, mem_iUnion, Finset.mem_range, W]
    constructor
    · rintro ⟨r, hr, j, hj, hx⟩
      exact ⟨r, hr, ⟨j, hj⟩, by simpa only [dite_eq_left hj] using hx⟩
    · rintro ⟨r, hr, j, hx⟩
      exact ⟨r, hr, j.val, j.isLt, by simpa only [dite_eq_left j.isLt] using hx⟩
  · intro r
    refine ⟨hmPool r, ?_, hmSmall r, ?_, ?_⟩
    · intro j
      exact (Finset.le_sup (s := Finset.univ) (f := h.m r)
        (Finset.mem_univ j)).trans_lt (hmM r)
    · intro A hAF x y hx hy hxy
      have hb := hmE r ⟨A, hAF⟩ x y hx hy hxy
      change (A : Set K).boolIndicator x = (A : Set K).boolIndicator y at hb
      change x ∈ (A : Set K) ↔ y ∈ (A : Set K)
      rw [(A : Set K).mem_iff_boolIndicator x, (A : Set K).mem_iff_boolIndicator y, hb]
    · intro t htmap htmass
      refine ⟨(hmMarginal r t htmap htmass).1, ?_⟩
      intro A hgen
      let f : K → ({A // A ∈ F} → Bool) := fun x C => test C x
      have hf : Continuous f := continuous_pi (fun C => (test C).continuous)
      apply apply_error_of_finite_marginal f hf t (muR r) ((1 / 2 : ℝ) ^ q)
        (hmMarginal r t htmap htmass).1 A
      intro x y hxy
      apply hgen x y
      intro C hCF
      have hb := congrFun hxy ⟨C, hCF⟩
      change (C : Set K).boolIndicator x = (C : Set K).boolIndicator y at hb
      change x ∈ (C : Set K) ↔ y ∈ (C : Set K)
      rw [(C : Set K).mem_iff_boolIndicator x, (C : Set K).mem_iff_boolIndicator y, hb]

lemma map_mass_through_factor {X : Type*} [MeasurableSpace X]
    (f : X → K) (hf : Measurable f) (g : K → L) (hg : Measurable g)
    (t : SignedMeasure X) (nu : SignedMeasure L)
    (hmap : t.map (g ∘ f) = nu) (hmass : t.totalVariation univ = nu.totalVariation univ) :
    (t.map f).map g = nu ∧ (SignedMeasure.totalVariation (t.map f)) univ = nu.totalVariation univ := by
  have hmid : (t.map f).map g = nu := by
    ext A hA
    rw [VectorMeasure.map_apply _ hg hA, VectorMeasure.map_apply _ hf (hg hA)]
    have h := congrArg (fun r : SignedMeasure L => r A) hmap
    rw [VectorMeasure.map_apply _ (hg.comp hf) hA] at h
    exact h
  have hupper := VectorMeasure.variation_map_le (μ := t) (φ := f) univ
  have hlower := VectorMeasure.variation_map_le (μ := t.map f) (φ := g) univ
  simp only [← SignedMeasure.totalVariation_eq_variation,
    Measure.map_apply hf MeasurableSet.univ, preimage_univ] at hupper
  simp only [← SignedMeasure.totalVariation_eq_variation, hmid,
    Measure.map_apply hg MeasurableSet.univ, preimage_univ] at hlower
  exact ⟨hmid, le_antisymm (hupper.trans hmass.le) hlower⟩

lemma apply_eq_inter_of_null_compl {X : Type*} [MeasurableSpace X]
    (t : SignedMeasure X) {A W : Set X} (hA : MeasurableSet A) (hW : MeasurableSet W)
    (hnull : t.totalVariation Wᶜ = 0) : t A = t (A ∩ W) := by
  have hz : t (A \ W) = 0 := t.null_of_totalVariation_zero
    (measure_mono_null (fun _ hx => hx.2) hnull)
  have hsplit := VectorMeasure.of_add_of_sdiff (v := t) (hA.inter hW) hA
    (inter_subset_left : A ∩ W ⊆ A)
  have heq : A \ (A ∩ W) = A \ W := by ext x; simp only [Set.mem_sdiff, mem_inter_iff]; tauto
  rw [heq, hz, add_zero] at hsplit
  exact hsplit.symm

lemma bool_eq_of_true_iff (a b : Bool) (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

/-- Inherited reservoirs exist only on old rows. The new row uses its signed
cluster pool and has no inherited parity reservoir at this stage. -/
noncomputable def ordinaryPool {Rows Γ : Type*} (newRow : Rows)
    (oldJ : ∀ r, r ≠ newRow → Γ → Set ℕ)
    (oldN : ∀ r, r ≠ newRow → Γ → Fin 2 → Set ℕ)
    (birthS : Γ → Set ℕ) (rho : ℕ → Γ) (r : Rows) (q : ℕ) : Set ℕ := by
  classical
  exact if hr : r = newRow then birthS (rho q)
    else oldJ r hr (rho q) ∩ oldN r hr (rho q) ⟨q % 2, Nat.mod_lt q (by decide)⟩

/-- Old signed references have no value on the new row before its cluster is chosen. -/
noncomputable def ordinaryReference {Rows Γ : Type*} (newRow : Rows)
    (oldMu : ∀ r, r ≠ newRow → Γ → SignedMeasure K)
    (birthMu : Γ → SignedMeasure K) (r : Rows) (d : Γ) : SignedMeasure K := by
  classical
  exact if hr : r = newRow then birthMu d else oldMu r hr d


end D5.S3.Topology.Measures.SignedSplitSuccessor
