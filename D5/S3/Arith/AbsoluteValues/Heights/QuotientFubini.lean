/- GID: D5/S3/Arith/AbsoluteValues/Heights/QuotientFubini
   generality: G
   mirror-B: D5/B/S3/Arith/AbsoluteValues/Heights/QuotientFubini
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A quotient-space integration bound controls measure of lattice translates. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Prod

public section

open MeasureTheory Measure Module Set

open scoped ENNReal Pointwise

namespace ZLattice

section Lattice

variable {G : Type*} [NormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G]




end Lattice

section Descent

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- **The descent from a lattice to a sublattice** (the equivalence of (6) with (7) and (8) in
Cassels' proof of his Chapter VIII, Theorem IV). If two points of `A` are congruent modulo `L` only
when they are congruent modulo the sublattice `Λ`, then the measure of the image of `A` in `E ⧸ L`
equals the measure of its image in `E ⧸ Λ`: the covering `E ⧸ Λ → E ⧸ L` is injective there.

Both measures are read off against fundamental domains — `FΛ` for `Λ`, `FL` for `L`, each given by
its exact form `∀ x, ∃! v, ↑v + x ∈ ·` — and the proof exhibits `(FΛ ∩ (A + Λ)) ∪ (FL \ (A + L))`
as a third fundamental domain, for `L`. ⚠ This is where `μ FL ≠ ⊤` is used, and it is the only
finiteness hypothesis in the file. -/
theorem measure_inter_add_eq_of_separated (μ : Measure E) [μ.IsAddLeftInvariant]
    {Λ L : Submodule ℤ E} [Countable Λ] [Countable L] (hΛL : Λ ≤ L) {FΛ FL : Set E}
    (hΛ : ∀ x : E, ∃! v : Λ, (v : E) + x ∈ FΛ) (hL : ∀ x : E, ∃! v : L, (v : E) + x ∈ FL)
    (hmΛ : MeasurableSet FΛ) (hmL : MeasurableSet FL) (hfin : μ FL ≠ ⊤) {A : Set E}
    (hA : MeasurableSet A) (hsep : ∀ x ∈ A, ∀ y ∈ A, x - y ∈ L → x - y ∈ Λ) :
    μ (FΛ ∩ (A + (Λ : Set E))) = μ (FL ∩ (A + (L : Set E))) := by
  have : VAddInvariantMeasure L E μ := inferInstanceAs (VAddInvariantMeasure L.toAddSubgroup E μ)
  set SΛ : Set E := A + (Λ : Set E) with hSΛ
  set SL : Set E := A + (L : Set E) with hSL
  have hsub : SΛ ⊆ SL := Set.add_subset_add_left fun l hl ↦ hΛL hl
  have hmSΛ : MeasurableSet SΛ := (open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal ZLattice in (fun {G : Type _} [instG1 : NormedAddCommGroup G] [instG2 : MeasurableSpace G] [instG3 : BorelSpace G] (M : Submodule ℤ G) [Countable M] {A : Set G}
        (hA : MeasurableSet A) => (show MeasurableSet (A + (M : Set G)) from by
      have h : A + (M : Set G) = ⋃ l : M, (fun x ↦ x - (l : G)) ⁻¹' A := by
        ext x
        simp only [Set.mem_add, Set.mem_iUnion, Set.mem_preimage]
        exact ⟨fun ⟨a, ha, l, hl, he⟩ ↦ ⟨⟨l, hl⟩, by simp only [← he]; simpa using ha⟩,
          fun ⟨l, hx⟩ ↦ ⟨x - (l : G), hx, l, l.2, by abel⟩⟩
      rw [h]
      exact MeasurableSet.iUnion fun l ↦ hA.preimage (measurable_id.sub_const _))))) Λ hA
  have hmSL : MeasurableSet SL := (open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal ZLattice in (fun {G : Type _} [instG1 : NormedAddCommGroup G] [instG2 : MeasurableSpace G] [instG3 : BorelSpace G] (M : Submodule ℤ G) [Countable M] {A : Set G}
        (hA : MeasurableSet A) => (show MeasurableSet (A + (M : Set G)) from by
      have h : A + (M : Set G) = ⋃ l : M, (fun x ↦ x - (l : G)) ⁻¹' A := by
        ext x
        simp only [Set.mem_add, Set.mem_iUnion, Set.mem_preimage]
        exact ⟨fun ⟨a, ha, l, hl, he⟩ ↦ ⟨⟨l, hl⟩, by simp only [← he]; simpa using ha⟩,
          fun ⟨l, hx⟩ ↦ ⟨x - (l : G), hx, l, l.2, by abel⟩⟩
      rw [h]
      exact MeasurableSet.iUnion fun l ↦ hA.preimage (measurable_id.sub_const _))))) L hA
  set D : Set E := (FΛ ∩ SΛ) ∪ (FL \ SL) with hD
  have hfd : IsAddFundamentalDomain L D μ := by
    refine IsAddFundamentalDomain.mk' ((hmΛ.inter hmSΛ).union (hmL.diff hmSL)).nullMeasurableSet
      fun x ↦ ?_
    by_cases hx : x ∈ SL
    · have hmemL : ∀ v : L, (v : E) + x ∈ SL := fun v ↦ ((open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal ZLattice in (fun {G : Type _} [instG1 : NormedAddCommGroup G] (M : Submodule ℤ G) {A : Set G} {v : G} (hv : v ∈ M) (x : G) => (show v + x ∈ A + (M : Set G) ↔ x ∈ A + (M : Set G) from by
        constructor
        · rintro ⟨a, ha, l, hl, h⟩
          refine ⟨a, ha, l - v, Submodule.sub_mem _ hl hv, ?_⟩
          simp only at h ⊢
          linear_combination (norm := abel) h
        · rintro ⟨a, ha, l, hl, rfl⟩
          exact ⟨a, ha, v + l, Submodule.add_mem _ hv hl, by simp; abel⟩)))) L v.2 x).2 hx
      have hiff : ∀ y : E, y ∈ SL → (y ∈ D ↔ y ∈ FΛ ∩ SΛ) := fun y hy ↦ by
        simp only [hD, Set.mem_union, Set.mem_sdiff, hy, not_true_eq_false, and_false, or_false]
      have huniq2 : ∀ v v' : L, (v : E) + x ∈ FΛ ∩ SΛ → (v' : E) + x ∈ FΛ ∩ SΛ → v = v' := by
        intro v v' h1 h2
        obtain ⟨a₁, ha₁, c₁, hc₁, he₁⟩ := h1.2
        obtain ⟨a₂, ha₂, c₂, hc₂, he₂⟩ := h2.2
        have he₁' : a₁ + c₁ = (v : E) + x := he₁
        have he₂' : a₂ + c₂ = (v' : E) + x := he₂
        have hd1 : a₁ - a₂ = ((v : E) - (v' : E)) - (c₁ - c₂) := by
          linear_combination (norm := abel) he₁' - he₂'
        have hdiff : a₁ - a₂ ∈ L := by
          rw [hd1]
          exact Submodule.sub_mem _ (Submodule.sub_mem _ v.2 v'.2)
            (hΛL (Submodule.sub_mem _ hc₁ hc₂))
        have hs := hsep a₁ ha₁ a₂ ha₂ hdiff
        have hw : (v : E) - (v' : E) ∈ Λ := by
          have hd2 : (v : E) - (v' : E) = (a₁ - a₂) + (c₁ - c₂) := by
            linear_combination (norm := abel) he₂' - he₁'
          rw [hd2]
          exact Submodule.add_mem _ hs (Submodule.sub_mem _ hc₁ hc₂)
        obtain ⟨u', -, huq⟩ := hΛ ((v' : E) + x)
        have e1 : (⟨(v : E) - (v' : E), hw⟩ : Λ) = u' := by
          refine huq _ ?_
          change ((v : E) - (v' : E)) + ((v' : E) + x) ∈ FΛ
          rw [show ((v : E) - (v' : E)) + ((v' : E) + x) = (v : E) + x from by abel]
          exact h1.1
        have e2 : (0 : Λ) = u' := by
          refine huq _ ?_
          change ((0 : Λ) : E) + ((v' : E) + x) ∈ FΛ
          simpa using h2.1
        have h4 : (v : E) - (v' : E) = 0 := by
          have h5 := congrArg (fun z : Λ ↦ (z : E)) (e1.trans e2.symm)
          simpa using h5
        exact Subtype.ext (sub_eq_zero.1 h4)
      obtain ⟨a, ha, l, hl, hx'⟩ := hx
      have hx'' : a + l = x := hx'
      obtain ⟨u, hu, -⟩ := hΛ a
      have hex : ∃ v : L, (v : E) + x ∈ FΛ ∩ SΛ := by
        refine ⟨⟨(u : E) - l, Submodule.sub_mem _ (hΛL u.2) hl⟩, ?_⟩
        change ((u : E) - l) + x ∈ FΛ ∩ SΛ
        rw [show ((u : E) - l) + x = (u : E) + a from by rw [← hx'']; abel]
        exact ⟨hu, ⟨a, ha, (u : E), u.2, add_comm _ _⟩⟩
      obtain ⟨v₀, hv₀⟩ := hex
      exact ⟨v₀, (hiff _ (hmemL _)).2 hv₀, fun v hv ↦ huniq2 v v₀ ((hiff _ (hmemL v)).1 hv) hv₀⟩
    · have hmemL : ∀ v : L, (v : E) + x ∉ SL := fun v h ↦ hx (((open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal ZLattice in (fun {G : Type _} [instG1 : NormedAddCommGroup G] (M : Submodule ℤ G) {A : Set G} {v : G} (hv : v ∈ M) (x : G) => (show v + x ∈ A + (M : Set G) ↔ x ∈ A + (M : Set G) from by
        constructor
        · rintro ⟨a, ha, l, hl, h⟩
          refine ⟨a, ha, l - v, Submodule.sub_mem _ hl hv, ?_⟩
          simp only at h ⊢
          linear_combination (norm := abel) h
        · rintro ⟨a, ha, l, hl, rfl⟩
          exact ⟨a, ha, v + l, Submodule.add_mem _ hv hl, by simp; abel⟩)))) L v.2 x).1 h)
      have hiff : ∀ v : L, ((v : E) + x ∈ D ↔ (v : E) + x ∈ FL) := by
        intro v
        have h1 : (v : E) + x ∉ SΛ := fun h ↦ hmemL v (hsub h)
        rw [hD]
        simp only [Set.mem_union, Set.mem_sdiff]
        constructor
        · rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact absurd h h1
          · exact h
        · exact fun h ↦ Or.inr ⟨h, hmemL v⟩
      obtain ⟨u, hu, huniq⟩ := hL x
      exact ⟨u, (hiff u).2 hu, fun v hv ↦ huniq v ((hiff v).1 hv)⟩
  have hdisj : Disjoint (FΛ ∩ SΛ) (FL \ SL) :=
    Set.disjoint_left.2 fun y hy hy' ↦ hy'.2 (hsub hy.2)
  have hunion : μ D = μ (FΛ ∩ SΛ) + μ (FL \ SL) := measure_union hdisj (hmL.diff hmSL)
  have hFL : μ FL = μ (FL ∩ SL) + μ (FL \ SL) := (measure_inter_add_sdiff FL hmSL).symm
  have hDeq : μ D = μ FL :=
    hfd.measure_eq (IsAddFundamentalDomain.mk' hmL.nullMeasurableSet hL)
  have hlt : μ (FL \ SL) ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono Set.sdiff_subset)
  rw [hunion, hFL] at hDeq
  exact (ENNReal.add_left_inj hlt).mp hDeq

end Descent

section Product

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]
  [BorelSpace W] [FiniteDimensional ℝ W]

/-- A lattice in `V` sits in `V × W` as the sublattice `Λ × 0`, and it is countable there. -/
private instance countable_prod_bot (Λ : Submodule ℤ V) [Countable Λ] :
    Countable (Λ.prod (⊥ : Submodule ℤ W)) := by
  refine Function.Injective.countable
    (f := fun p : Λ.prod (⊥ : Submodule ℤ W) ↦ (⟨p.1.1, p.2.1⟩ : Λ)) ?_
  intro p q hpq
  have h1 : p.1.1 = q.1.1 := congrArg Subtype.val hpq
  have h2 : p.1.2 = 0 := p.2.2
  have h3 : q.1.2 = 0 := q.2.2
  exact Subtype.ext (Prod.ext h1 (h2.trans h3.symm))


/-- **The scaling estimate** (Cassels, Chapter VIII, §4.2, the displays (12) and (14) in the proof
of Theorem IV). For a convex set `A` and `s ≥ 1`, the quotient measure of `s • A` over `Λ × 0` is at
least `s ^ dim W` times that of `A`.

The factor is `s ^ dim W` and not `s ^ dim (V × W)` because the Fubini decomposition scales only
the `W`-direction: on each slice the dilation is replaced by a translation, which the quotient
measure over `Λ` does not see. ⚠ The translating vector depends on the slice, so no map of `V × W`
realizes this comparison; see the implementation notes. -/
theorem measure_inter_add_prod_smul_le (μV : Measure V) [μV.IsAddHaarMeasure] (μW : Measure W)
    [μW.IsAddHaarMeasure] (Λ : Submodule ℤ V) [Countable Λ] {F : Set V}
    (hF : ∀ x : V, ∃! v : Λ, (v : V) + x ∈ F) (hFm : MeasurableSet F) {A : Set (V × W)}
    (hAm : MeasurableSet A) (hAc : Convex ℝ A) {s : ℝ} (hs : 1 ≤ s) :
    ENNReal.ofReal (s ^ finrank ℝ W) * (μV.prod μW)
        ((F ×ˢ (univ : Set W)) ∩ (A + ((Λ.prod (⊥ : Submodule ℤ W)) : Set (V × W)))) ≤
      (μV.prod μW) ((F ×ˢ (univ : Set W)) ∩
        ((s • A) + ((Λ.prod (⊥ : Submodule ℤ W)) : Set (V × W)))) := by
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le one_pos hs
  have hsAm : MeasurableSet (s • A) := hAm.const_smul₀ s
  rw [(open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal ZLattice in (fun {V W : Type _} [instV1 : NormedAddCommGroup V] [instV2 : NormedSpace ℝ V] [instV3 : MeasurableSpace V] [instV4 : BorelSpace V] [instV5 : FiniteDimensional ℝ V] [instW1 : NormedAddCommGroup W] [instW2 : NormedSpace ℝ W] [instW3 : MeasurableSpace W] [instW4 : BorelSpace W] [instW5 : FiniteDimensional ℝ W] (μV : Measure V) [μV.IsAddHaarMeasure] (μW : Measure W)
        [μW.IsAddHaarMeasure] (Λ : Submodule ℤ V) [Countable Λ] {F : Set V} (hFm : MeasurableSet F)
        {X : Set (V × W)} (hX : MeasurableSet X) => (show (μV.prod μW) ((F ×ˢ (univ : Set W)) ∩ (X + ((Λ.prod (⊥ : Submodule ℤ W)) : Set (V × W))))
          = ∫⁻ z, μV (F ∩ ({y | (y, z) ∈ X} + (Λ : Set V))) ∂μW from by
      rw [Measure.prod_apply_symm ((hFm.prod MeasurableSet.univ).inter
        ((open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal ZLattice in (fun {G : Type _} [instG1 : NormedAddCommGroup G] [instG2 : MeasurableSpace G] [instG3 : BorelSpace G] (M : Submodule ℤ G) [Countable M] {A : Set G}
              (hA : MeasurableSet A) => (show MeasurableSet (A + (M : Set G)) from by
            have h : A + (M : Set G) = ⋃ l : M, (fun x ↦ x - (l : G)) ⁻¹' A := by
              ext x
              simp only [Set.mem_add, Set.mem_iUnion, Set.mem_preimage]
              exact ⟨fun ⟨a, ha, l, hl, he⟩ ↦ ⟨⟨l, hl⟩, by simp only [← he]; simpa using ha⟩,
                fun ⟨l, hx⟩ ↦ ⟨x - (l : G), hx, l, l.2, by abel⟩⟩
            rw [h]
            exact MeasurableSet.iUnion fun l ↦ hA.preimage (measurable_id.sub_const _))))) _ hX))]
      exact lintegral_congr fun z ↦ by rw [(open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal ZLattice in (fun {V W : Type _} [instV1 : NormedAddCommGroup V] [instW1 : NormedAddCommGroup W] (Λ : Submodule ℤ V) (X : Set (V × W)) (z : W) {F : Set V} => (show (fun y ↦ (y, z)) ⁻¹' ((F ×ˢ (univ : Set W)) ∩
                (X + ((Λ.prod (⊥ : Submodule ℤ W)) : Set (V × W))))
              = F ∩ ({y | (y, z) ∈ X} + (Λ : Set V)) from by
          ext y
          simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true,
            Set.mem_add, Set.mem_ofPred_eq, SetLike.mem_coe, Submodule.mem_prod, Submodule.mem_bot]
          refine and_congr Iff.rfl ⟨?_, ?_⟩
          · rintro ⟨p, hp, l, ⟨hl₁, hl₂⟩, he⟩
            refine ⟨p.1, ?_, l.1, hl₁, ?_⟩
            · have hz : p.2 = z := by
                have := congrArg Prod.snd he
                simpa [hl₂] using this
              rwa [← hz]
            · have := congrArg Prod.fst he
              simpa using this
          · rintro ⟨a, ha, l, hl, he⟩
            exact ⟨(a, z), ha, (l, 0), ⟨hl, rfl⟩, by simp [he]⟩)))) Λ X z])))) μV μW Λ hFm hAm,
    (open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal ZLattice in (fun {V W : Type _} [instV1 : NormedAddCommGroup V] [instV2 : NormedSpace ℝ V] [instV3 : MeasurableSpace V] [instV4 : BorelSpace V] [instV5 : FiniteDimensional ℝ V] [instW1 : NormedAddCommGroup W] [instW2 : NormedSpace ℝ W] [instW3 : MeasurableSpace W] [instW4 : BorelSpace W] [instW5 : FiniteDimensional ℝ W] (μV : Measure V) [μV.IsAddHaarMeasure] (μW : Measure W)
          [μW.IsAddHaarMeasure] (Λ : Submodule ℤ V) [Countable Λ] {F : Set V} (hFm : MeasurableSet F)
          {X : Set (V × W)} (hX : MeasurableSet X) => (show (μV.prod μW) ((F ×ˢ (univ : Set W)) ∩ (X + ((Λ.prod (⊥ : Submodule ℤ W)) : Set (V × W))))
            = ∫⁻ z, μV (F ∩ ({y | (y, z) ∈ X} + (Λ : Set V))) ∂μW from by
        rw [Measure.prod_apply_symm ((hFm.prod MeasurableSet.univ).inter
          ((open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal ZLattice in (fun {G : Type _} [instG1 : NormedAddCommGroup G] [instG2 : MeasurableSpace G] [instG3 : BorelSpace G] (M : Submodule ℤ G) [Countable M] {A : Set G}
                (hA : MeasurableSet A) => (show MeasurableSet (A + (M : Set G)) from by
              have h : A + (M : Set G) = ⋃ l : M, (fun x ↦ x - (l : G)) ⁻¹' A := by
                ext x
                simp only [Set.mem_add, Set.mem_iUnion, Set.mem_preimage]
                exact ⟨fun ⟨a, ha, l, hl, he⟩ ↦ ⟨⟨l, hl⟩, by simp only [← he]; simpa using ha⟩,
                  fun ⟨l, hx⟩ ↦ ⟨x - (l : G), hx, l, l.2, by abel⟩⟩
              rw [h]
              exact MeasurableSet.iUnion fun l ↦ hA.preimage (measurable_id.sub_const _))))) _ hX))]
        exact lintegral_congr fun z ↦ by rw [(open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal ZLattice in (fun {V W : Type _} [instV1 : NormedAddCommGroup V] [instW1 : NormedAddCommGroup W] (Λ : Submodule ℤ V) (X : Set (V × W)) (z : W) {F : Set V} => (show (fun y ↦ (y, z)) ⁻¹' ((F ×ˢ (univ : Set W)) ∩
                  (X + ((Λ.prod (⊥ : Submodule ℤ W)) : Set (V × W))))
                = F ∩ ({y | (y, z) ∈ X} + (Λ : Set V)) from by
            ext y
            simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true,
              Set.mem_add, Set.mem_ofPred_eq, SetLike.mem_coe, Submodule.mem_prod, Submodule.mem_bot]
            refine and_congr Iff.rfl ⟨?_, ?_⟩
            · rintro ⟨p, hp, l, ⟨hl₁, hl₂⟩, he⟩
              refine ⟨p.1, ?_, l.1, hl₁, ?_⟩
              · have hz : p.2 = z := by
                  have := congrArg Prod.snd he
                  simpa [hl₂] using this
                rwa [← hz]
              · have := congrArg Prod.fst he
                simpa using this
            · rintro ⟨a, ha, l, hl, he⟩
              exact ⟨(a, z), ha, (l, 0), ⟨hl, rfl⟩, by simp [he]⟩)))) Λ X z])))) μV μW Λ hFm hsAm]
  set f : W → ℝ≥0∞ := fun z ↦ μV (F ∩ ({y | (y, z) ∈ s • A} + (Λ : Set V))) with hf
  have hsubst : ∫⁻ z, f z ∂μW = ENNReal.ofReal (s ^ finrank ℝ W) * ∫⁻ z, f (s • z) ∂μW := by
    have hne : s ≠ 0 := hs0.ne'
    have hmap : μW.map (fun z : W ↦ s • z) = ENNReal.ofReal |(s ^ finrank ℝ W)⁻¹| • μW :=
      map_addHaar_smul μW hne
    have h1 : ∫⁻ z, f z ∂(μW.map (fun z : W ↦ s • z)) = ∫⁻ z, f (s • z) ∂μW := by
      simpa using lintegral_map_equiv (μ := μW) f (MeasurableEquiv.smul₀ s hne)
    rw [hmap, lintegral_smul_measure,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (s ^ finrank ℝ W)⁻¹)] at h1
    rw [← h1, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      mul_inv_cancel₀ (by positivity)]
    simp
  rw [hsubst]
  refine mul_le_mul_right (lintegral_mono fun z ↦ ?_) _
  set X : Set V := {y | (y, z) ∈ A} with hX
  have hXm : MeasurableSet X := hAm.preimage measurable_prodMk_right
  have hXc : Convex ℝ X := by
    intro y₁ h₁ y₂ h₂ a b ha hb hab
    change (a • y₁ + b • y₂, z) ∈ A
    rw [show (a • y₁ + b • y₂, z) = a • (y₁, z) + b • (y₂, z) from
      Prod.ext rfl (show z = a • z + b • z by rw [← add_smul, hab, one_smul])]
    exact hAc h₁ h₂ ha hb hab
  have hfz : f (s • z) = μV (F ∩ ((s • X) + (Λ : Set V))) := by
    rw [hf]
    simp only
    rw [(open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal ZLattice in (fun {V W : Type _} [instV1 : NormedAddCommGroup V] [instV2 : NormedSpace ℝ V] [instW1 : NormedAddCommGroup W] [instW2 : NormedSpace ℝ W] (A : Set (V × W)) {s : ℝ} (hs : s ≠ 0) (z : W) => (show {y | (y, s • z) ∈ s • A} = s • {y | (y, z) ∈ A} from by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_smul_set]
        constructor
        · rintro ⟨p, hp, he⟩
          have h₂ : s • p.2 = s • z := congrArg Prod.snd he
          have h₂' : p.2 = z := smul_right_injective W hs h₂
          exact ⟨p.1, by rwa [← h₂'], congrArg Prod.fst he⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨(x, z), hx, rfl⟩)))) A hs0.ne' z, ← hX]
  rw [hfz]
  rcases Set.eq_empty_or_nonempty X with hemp | ⟨y₀, hy₀⟩
  · rw [hemp, Set.empty_add, Set.smul_set_empty, Set.empty_add]
  · refine (open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal ZLattice in (fun {V : Type _} [instV1 : NormedAddCommGroup V] [instV2 : NormedSpace ℝ V] [instV3 : MeasurableSpace V] [instV4 : BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (Λ : Submodule ℤ V)
        [Countable Λ] {F : Set V} (hF : ∀ x : V, ∃! v : Λ, (v : V) + x ∈ F) (hFm : MeasurableSet F)
        {X Y : Set V} (hY : MeasurableSet Y) {c : V} (hsub : ∀ y ∈ X, y + c ∈ Y) => (show μ (F ∩ (X + (Λ : Set V))) ≤ μ (F ∩ (Y + (Λ : Set V))) from by
      have : VAddInvariantMeasure Λ V μ := inferInstanceAs (VAddInvariantMeasure Λ.toAddSubgroup V μ)
      set Fc : Set V := (fun y ↦ y + (-c)) ⁻¹' F with hFc
      have hFcm : MeasurableSet Fc := hFm.preimage (measurable_id.add_const _)
      have hFcfd : ∀ x : V, ∃! v : Λ, (v : V) + x ∈ Fc := by
        intro x
        obtain ⟨u, hu, huq⟩ := hF (x + (-c))
        refine ⟨u, ?_, fun w hw ↦ huq w ?_⟩
        · change ((u : V) + x) + (-c) ∈ F
          rw [show ((u : V) + x) + (-c) = (u : V) + (x + (-c)) from by abel]
          exact hu
        · change (w : V) + (x + (-c)) ∈ F
          rw [show (w : V) + (x + (-c)) = ((w : V) + x) + (-c) from by abel]
          exact hw
      have hstep : μ (F ∩ (X + (Λ : Set V)))
          = μ (Fc ∩ ((fun y ↦ y + (-c)) ⁻¹' (X + (Λ : Set V)))) := by
        rw [hFc, ← Set.preimage_inter]
        exact (measure_preimage_add_right μ (-c) _).symm
      rw [hstep]
      have hsub' : (fun y ↦ y + (-c)) ⁻¹' (X + (Λ : Set V)) ⊆ Y + (Λ : Set V) := by
        rintro y ⟨a, ha, l, hl, he⟩
        refine ⟨a + c, hsub a ha, l, hl, ?_⟩
        simp only at he ⊢
        linear_combination (norm := abel) he
      refine le_trans (measure_mono (Set.inter_subset_inter_right _ hsub')) (le_of_eq ?_)
      have h1 : IsAddFundamentalDomain Λ F μ := IsAddFundamentalDomain.mk' hFm.nullMeasurableSet hF
      have h2 : IsAddFundamentalDomain Λ Fc μ :=
        IsAddFundamentalDomain.mk' hFcm.nullMeasurableSet hFcfd
      rw [Set.inter_comm Fc, Set.inter_comm F]
      exact h2.measure_set_eq h1 ((open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal ZLattice in (fun {G : Type _} [instG1 : NormedAddCommGroup G] [instG2 : MeasurableSpace G] [instG3 : BorelSpace G] (M : Submodule ℤ G) [Countable M] {A : Set G}
            (hA : MeasurableSet A) => (show MeasurableSet (A + (M : Set G)) from by
          have h : A + (M : Set G) = ⋃ l : M, (fun x ↦ x - (l : G)) ⁻¹' A := by
            ext x
            simp only [Set.mem_add, Set.mem_iUnion, Set.mem_preimage]
            exact ⟨fun ⟨a, ha, l, hl, he⟩ ↦ ⟨⟨l, hl⟩, by simp only [← he]; simpa using ha⟩,
              fun ⟨l, hx⟩ ↦ ⟨x - (l : G), hx, l, l.2, by abel⟩⟩
          rw [h]
          exact MeasurableSet.iUnion fun l ↦ hA.preimage (measurable_id.sub_const _))))) Λ hY) ((open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal ZLattice in (fun {G : Type _} [instG1 : NormedAddCommGroup G] (M : Submodule ℤ G) {Y : Set G} (g : M) => (show (fun x ↦ g +ᵥ x) ⁻¹' (Y + (M : Set G)) = Y + (M : Set G) from by
          ext x
          constructor
          · rintro ⟨a, ha, l, hl, he⟩
            have he' : a + l = (g : G) + x := he
            refine ⟨a, ha, l - (g : G), Submodule.sub_mem _ hl g.2, ?_⟩
            change a + (l - (g : G)) = x
            linear_combination (norm := abel) he'
          · rintro ⟨a, ha, l, hl, rfl⟩
            refine ⟨a, ha, (g : G) + l, Submodule.add_mem _ g.2 hl, ?_⟩
            change a + ((g : G) + l) = (g : G) + (a + l)
            abel)))) Λ))))) μV Λ hF hFm (hXm.const_smul₀ s) (c := (s - 1) • y₀) ?_
    intro y hy
    rw [show y + (s - 1) • y₀ = s • (s⁻¹ • y + (1 - s⁻¹) • y₀) from by
      rw [smul_add, smul_smul, mul_inv_cancel₀ hs0.ne', one_smul, smul_smul,
        show s * (1 - s⁻¹) = s - 1 from by field_simp]]
    refine Set.smul_mem_smul_set (hXc hy hy₀ (by positivity) ?_ (by ring))
    simp only [sub_nonneg]
    rw [inv_le_one₀ hs0]
    exact hs

end Product

section Space

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E]


omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The lattice and its copy inside its own span are `ℤ`-linearly equivalent. -/
private def comapSpanEquiv (Λ : Submodule ℤ E) :
    (ZLattice.comap ℝ Λ (Submodule.span ℝ (Λ : Set E)).subtype) ≃ₗ[ℤ] Λ :=
  Submodule.comapSubtypeEquivOfLe
    (show Λ ≤ (Submodule.span ℝ (Λ : Set E)).restrictScalars ℤ from
      fun _ hx ↦ Submodule.subset_span hx)


/-- **The scaling estimate for a lattice of arbitrary rank in a single space**, with the slab
produced rather than assumed: some measurable set `F` is a fundamental domain for `Λ` and, for
every convex `A` and every `s ≥ 1`, the quotient measure of `s • A` modulo `Λ` is at least
`s ^ (n - rank Λ)` times that of `A`.

This is Cassels' normalization of his Chapter VIII, Theorem IV made intrinsic: he transforms the
lattice to `ℤ ^ n` linearly, and the transformation is here the choice of a complement `W` of the
span of `Λ`, along which the fundamental parallelepiped of `Λ` in that span is extended to the
slab `F`. The exponent is `dim W`. -/
theorem exists_isAddFundamentalDomain_measure_smul_le (μ : Measure E) [μ.IsAddHaarMeasure]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] :
    ∃ F : Set E, MeasurableSet F ∧ (∀ x : E, ∃! v : Λ, (v : E) + x ∈ F) ∧
      ∀ A : Set E, MeasurableSet A → Convex ℝ A → ∀ s : ℝ, 1 ≤ s →
        ENNReal.ofReal (s ^ (finrank ℝ E - finrank ℤ Λ)) * μ (F ∩ (A + (Λ : Set E))) ≤
          μ (F ∩ ((s • A) + (Λ : Set E))) := by
  have hcount : Countable Λ := (open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal ZLattice in (fun {E : Type _} [instE1 : NormedAddCommGroup E] [instE2 : NormedSpace ℝ E] [instE3 : FiniteDimensional ℝ E] (Λ : Submodule ℤ E) [DiscreteTopology Λ] => (show Countable Λ from by
      letI hdisc : DiscreteTopology (ZLattice.comap ℝ Λ (Submodule.span ℝ (Λ : Set E)).subtype) :=
        ZLattice.comap_discreteTopology ℝ Λ continuous_subtype_val Subtype.val_injective
      letI hzl : IsZLattice ℝ (ZLattice.comap ℝ Λ (Submodule.span ℝ (Λ : Set E)).subtype) :=
        ⟨(open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal ZLattice in (fun {E : Type _} [instE1 : NormedAddCommGroup E] [instE2 : NormedSpace ℝ E] (Λ : Submodule ℤ E) => (show Submodule.span ℝ ((ZLattice.comap ℝ Λ (Submodule.span ℝ (Λ : Set E)).subtype) :
                Set ↥(Submodule.span ℝ (Λ : Set E))) = ⊤ from by exact (Submodule.span_span_coe_preimage (R := ℝ) (s := (Λ : Set E))))))) Λ⟩
      letI : Countable (ZLattice.comap ℝ Λ (Submodule.span ℝ (Λ : Set E)).subtype) :=
        _root_.instCountable_of_discrete_submodule _
      exact Countable.of_equiv (ZLattice.comap ℝ Λ (Submodule.span ℝ (Λ : Set E)).subtype)
        (Submodule.comapSubtypeEquivOfLe (show Λ ≤ (Submodule.span ℝ (Λ : Set E)).restrictScalars ℤ from fun _ hx ↦ Submodule.subset_span hx)).toEquiv)))) Λ
  set V : Submodule ℝ E := Submodule.span ℝ (Λ : Set E) with hV
  obtain ⟨W, hcompl⟩ := V.exists_isCompl
  set e : (↥V × ↥W) ≃L[ℝ] E :=
    (Submodule.prodEquivOfIsCompl V W hcompl).toContinuousLinearEquiv with he
  have hea : ∀ p : ↥V × ↥W, e p = (p.1 : E) + (p.2 : E) := fun _ ↦ rfl
  set Λ' : Submodule ℤ ↥V := ZLattice.comap ℝ Λ V.subtype with hΛ'
  have hmemΛ' : ∀ y : ↥V, y ∈ Λ' ↔ (y : E) ∈ Λ := fun _ ↦ Iff.rfl
  have hΛV : ∀ v : E, v ∈ Λ → v ∈ V := fun _ hv ↦ Submodule.subset_span hv
  have hdisc : DiscreteTopology Λ' :=
    ZLattice.comap_discreteTopology ℝ Λ continuous_subtype_val Subtype.val_injective
  have hzl : IsZLattice ℝ Λ' := ⟨(open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal ZLattice in (fun {E : Type _} [instE1 : NormedAddCommGroup E] [instE2 : NormedSpace ℝ E] (Λ : Submodule ℤ E) => (show Submodule.span ℝ ((ZLattice.comap ℝ Λ (Submodule.span ℝ (Λ : Set E)).subtype) :
          Set ↥(Submodule.span ℝ (Λ : Set E))) = ⊤ from by exact (Submodule.span_span_coe_preimage (R := ℝ) (s := (Λ : Set E))))))) Λ⟩
  have hcount' : Countable Λ' := inferInstance
  -- the fundamental parallelepiped of `Λ` inside its span
  have hmodfin : Module.Finite ℤ Λ' := ZLattice.module_finite ℝ Λ'
  have hfree : Module.Free ℤ Λ' := ZLattice.module_free ℝ Λ'
  set bZ : Basis (Module.Free.ChooseBasisIndex ℤ Λ') ℤ Λ' := Module.Free.chooseBasis ℤ Λ' with hbZ
  set bR : Basis (Module.Free.ChooseBasisIndex ℤ Λ') ℝ ↥V := bZ.ofZLatticeBasis ℝ Λ' with hbR
  set FV : Set ↥V := ZSpan.fundamentalDomain bR with hFVdef
  have hFVm : MeasurableSet FV := ZSpan.fundamentalDomain_measurableSet bR
  have hFVfd : ∀ y : ↥V, ∃! v : Λ', (v : ↥V) + y ∈ FV := fun y ↦
    (bZ.ofZLatticeBasis_span ℝ) ▸
      (ZSpan.exist_unique_vadd_mem_fundamentalDomain bR y)
  -- the slab in `E`
  set F : Set E := e '' (FV ×ˢ (univ : Set ↥W)) with hFdef
  have hmemF : ∀ y : E, y ∈ F ↔ (e.symm y).1 ∈ FV := by
    intro y
    rw [hFdef]
    exact ⟨fun ⟨p, hp, hpy⟩ ↦ by simpa [← hpy] using hp.1,
      fun hy ↦ ⟨e.symm y, ⟨hy, Set.mem_univ _⟩, by simp⟩⟩
  have hFm : MeasurableSet F := by
    rw [show F = (e.symm : E → ↥V × ↥W) ⁻¹' (FV ×ˢ (univ : Set ↥W)) from by
      ext y; rw [hmemF y]; simp]
    exact (hFVm.prod MeasurableSet.univ).preimage e.symm.continuous.measurable
  have hπ : ∀ (v : Λ) (x : E),
      (e.symm ((v : E) + x)).1 = (⟨(v : E), hΛV _ v.2⟩ : ↥V) + (e.symm x).1 := by
    intro v x
    have hev : e.symm (v : E) = ((⟨(v : E), hΛV _ v.2⟩ : ↥V), (0 : ↥W)) := by
      refine e.injective ?_
      rw [ContinuousLinearEquiv.apply_symm_apply, hea]
      simp
    rw [map_add, hev]
    rfl
  have hFfd : ∀ x : E, ∃! v : Λ, (v : E) + x ∈ F := by
    intro x
    obtain ⟨u, hu, huq⟩ := hFVfd (e.symm x).1
    have huΛ : ((u : ↥V) : E) ∈ Λ := u.2
    refine ⟨⟨((u : ↥V) : E), huΛ⟩, ?_, ?_⟩
    · change ((u : ↥V) : E) + x ∈ F
      rw [hmemF, hπ ⟨((u : ↥V) : E), huΛ⟩ x,
        show (⟨((u : ↥V) : E), hΛV _ huΛ⟩ : ↥V) = (u : ↥V) from Subtype.ext rfl]
      exact hu
    · intro w hw
      have hw2 : (w : E) + x ∈ F := hw
      rw [hmemF, hπ w x] at hw2
      have hw' : (⟨⟨(w : E), hΛV _ w.2⟩, w.2⟩ : Λ') = u := huq _ hw2
      exact Subtype.ext (congrArg (fun z : Λ' ↦ ((z : ↥V) : E)) hw')
  refine ⟨F, hFm, hFfd, ?_⟩
  intro A hAm hAc s hs
  -- the transport of the Haar measure to the product
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0∞, ∀ S : Set E, MeasurableSet S →
      μ S = c * ((addHaar : Measure ↥V).prod (addHaar : Measure ↥W)) (e ⁻¹' S) := by
    set ν : Measure (↥V × ↥W) := μ.map e.symm with hν
    have hνHaar : ν.IsAddHaarMeasure := e.symm.isAddHaarMeasure_map μ
    obtain ⟨c, hcν⟩ : ∃ c : ℝ≥0∞, ν = c • ((addHaar : Measure ↥V).prod (addHaar : Measure ↥W)) :=
      ⟨addHaarScalarFactor ν ((addHaar : Measure ↥V).prod (addHaar : Measure ↥W)),
        isAddLeftInvariant_eq_smul _ _⟩
    refine ⟨c, fun S hS ↦ ?_⟩
    have h1 : ν (e ⁻¹' S) = μ S := by
      rw [hν, Measure.map_apply e.symm.continuous.measurable
        (hS.preimage e.continuous.measurable)]
      congr 1
      ext y
      simp
    rw [← h1, hcν]
    simp
  -- the transport of the sets
  have hpreadd : ∀ X Y : Set E, e ⁻¹' (X + Y) = (e ⁻¹' X) + (e ⁻¹' Y) := by
    intro X Y
    ext p
    simp only [Set.mem_preimage, Set.mem_add]
    constructor
    · rintro ⟨x, hx, y, hy, hxy⟩
      refine ⟨e.symm x, by simpa using hx, e.symm y, by simpa using hy, ?_⟩
      rw [← map_add, hxy]
      exact e.symm_apply_apply p
    · rintro ⟨p₁, h₁, p₂, h₂, rfl⟩
      exact ⟨e p₁, h₁, e p₂, h₂, (map_add e p₁ p₂).symm⟩
  have hpresmul : ∀ (t : ℝ) (X : Set E), e ⁻¹' (t • X) = t • (e ⁻¹' X) := by
    intro t X
    ext p
    simp only [Set.mem_preimage, Set.mem_smul_set]
    constructor
    · rintro ⟨a, ha, hae⟩
      refine ⟨e.symm a, by simpa using ha, ?_⟩
      rw [← map_smul, hae]
      exact e.symm_apply_apply p
    · rintro ⟨q, hq, rfl⟩
      exact ⟨e q, hq, (map_smul e t q).symm⟩
  have hpreΛ : e ⁻¹' (Λ : Set E) = ((Λ'.prod (⊥ : Submodule ℤ ↥W)) : Set (↥V × ↥W)) := by
    ext p
    simp only [Set.mem_preimage, SetLike.mem_coe, Submodule.mem_prod, Submodule.mem_bot, hea]
    constructor
    · intro hp
      have hpV : (p.1 : E) + (p.2 : E) ∈ V := hΛV _ hp
      have h2 : (p.2 : E) ∈ V := by
        rw [show (p.2 : E) = ((p.1 : E) + (p.2 : E)) - (p.1 : E) from by abel]
        exact Submodule.sub_mem _ hpV p.1.2
      have h3 : p.2 = 0 := by
        have hmem : (p.2 : E) ∈ V ⊓ W := ⟨h2, p.2.2⟩
        rw [hcompl.inf_eq_bot] at hmem
        exact Subtype.ext (by simpa using hmem)
      refine ⟨(hmemΛ' p.1).2 ?_, h3⟩
      rw [show ((p.1 : ↥V) : E) = (p.1 : E) + (p.2 : E) from by
        rw [show (p.2 : E) = 0 from by rw [h3]; simp]; abel]
      exact hp
    · rintro ⟨h1, h2⟩
      rw [show (p.2 : E) = 0 from by rw [h2]; simp, add_zero]
      exact (hmemΛ' p.1).1 h1
  have hpreF : e ⁻¹' F = FV ×ˢ (univ : Set ↥W) := by
    ext p
    rw [Set.mem_preimage, hmemF]
    simp
  -- the rank bookkeeping
  have hr1 : finrank ℤ Λ = finrank ℝ ↥V := by
    rw [← ZLattice.rank ℝ Λ']
    exact ((comapSpanEquiv Λ).finrank_eq).symm
  have hr2 : finrank ℝ ↥V + finrank ℝ ↥W = finrank ℝ E :=
    Submodule.finrank_add_eq_of_isCompl hcompl
  have hrank : finrank ℝ E - finrank ℤ Λ = finrank ℝ ↥W := by omega
  -- the comparison, transported
  have hsAm : MeasurableSet (s • A) := hAm.const_smul₀ s
  rw [hc _ (hFm.inter ((open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal ZLattice in (fun {G : Type _} [instG1 : NormedAddCommGroup G] [instG2 : MeasurableSpace G] [instG3 : BorelSpace G] (M : Submodule ℤ G) [Countable M] {A : Set G}
        (hA : MeasurableSet A) => (show MeasurableSet (A + (M : Set G)) from by
      have h : A + (M : Set G) = ⋃ l : M, (fun x ↦ x - (l : G)) ⁻¹' A := by
        ext x
        simp only [Set.mem_add, Set.mem_iUnion, Set.mem_preimage]
        exact ⟨fun ⟨a, ha, l, hl, he⟩ ↦ ⟨⟨l, hl⟩, by simp only [← he]; simpa using ha⟩,
          fun ⟨l, hx⟩ ↦ ⟨x - (l : G), hx, l, l.2, by abel⟩⟩
      rw [h]
      exact MeasurableSet.iUnion fun l ↦ hA.preimage (measurable_id.sub_const _))))) Λ hAm)),
    hc _ (hFm.inter ((open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal ZLattice in (fun {G : Type _} [instG1 : NormedAddCommGroup G] [instG2 : MeasurableSpace G] [instG3 : BorelSpace G] (M : Submodule ℤ G) [Countable M] {A : Set G}
          (hA : MeasurableSet A) => (show MeasurableSet (A + (M : Set G)) from by
        have h : A + (M : Set G) = ⋃ l : M, (fun x ↦ x - (l : G)) ⁻¹' A := by
          ext x
          simp only [Set.mem_add, Set.mem_iUnion, Set.mem_preimage]
          exact ⟨fun ⟨a, ha, l, hl, he⟩ ↦ ⟨⟨l, hl⟩, by simp only [← he]; simpa using ha⟩,
            fun ⟨l, hx⟩ ↦ ⟨x - (l : G), hx, l, l.2, by abel⟩⟩
        rw [h]
        exact MeasurableSet.iUnion fun l ↦ hA.preimage (measurable_id.sub_const _))))) Λ hsAm)), Set.preimage_inter, Set.preimage_inter,
    hpreF, hpreadd, hpreΛ, hpreadd, hpreΛ, hpresmul, hrank, mul_left_comm]
  exact mul_le_mul_right (measure_inter_add_prod_smul_le _ _ Λ' hFVfd hFVm
    (hAm.preimage e.continuous.measurable) (hAc.linear_preimage e.toLinearEquiv.toLinearMap) hs) c

/-- **Cassels' Chapter VIII, Theorem IV, in one step** (the display (14) of his proof). For a
convex set `A` on which congruence modulo the lattice `L` is congruence modulo the sublattice `Λ`,
dilating by `s ≥ 1` multiplies the measure of the image in `E ⧸ L` by at least
`s ^ (n - rank Λ)`.

This is the inductive step of Weyl's proof of the upper bound in Minkowski's second theorem: the
separation hypotheses are Cassels' Lemma 2 applied to `A = t • B`, and the exponent decreases by
one each time `t` passes a successive minimum. -/
theorem pow_mul_measure_inter_add_le (μ : Measure E) [μ.IsAddHaarMeasure] {Λ L : Submodule ℤ E}
    [DiscreteTopology Λ] [DiscreteTopology L] (hΛL : Λ ≤ L) {FL : Set E}
    (hL : ∀ x : E, ∃! v : L, (v : E) + x ∈ FL) (hmL : MeasurableSet FL) (hfin : μ FL ≠ ⊤)
    {A : Set E} (hAm : MeasurableSet A) (hAc : Convex ℝ A) {s : ℝ} (hs : 1 ≤ s)
    (hsepA : ∀ x ∈ A, ∀ y ∈ A, x - y ∈ L → x - y ∈ Λ)
    (hsepB : ∀ x ∈ s • A, ∀ y ∈ s • A, x - y ∈ L → x - y ∈ Λ) :
    ENNReal.ofReal (s ^ (finrank ℝ E - finrank ℤ Λ)) * μ (FL ∩ (A + (L : Set E))) ≤
      μ (FL ∩ ((s • A) + (L : Set E))) := by
  have hcΛ : Countable Λ := (open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal ZLattice in (fun {E : Type _} [instE1 : NormedAddCommGroup E] [instE2 : NormedSpace ℝ E] [instE3 : FiniteDimensional ℝ E] (Λ : Submodule ℤ E) [DiscreteTopology Λ] => (show Countable Λ from by
      letI hdisc : DiscreteTopology (ZLattice.comap ℝ Λ (Submodule.span ℝ (Λ : Set E)).subtype) :=
        ZLattice.comap_discreteTopology ℝ Λ continuous_subtype_val Subtype.val_injective
      letI hzl : IsZLattice ℝ (ZLattice.comap ℝ Λ (Submodule.span ℝ (Λ : Set E)).subtype) :=
        ⟨(open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal ZLattice in (fun {E : Type _} [instE1 : NormedAddCommGroup E] [instE2 : NormedSpace ℝ E] (Λ : Submodule ℤ E) => (show Submodule.span ℝ ((ZLattice.comap ℝ Λ (Submodule.span ℝ (Λ : Set E)).subtype) :
                Set ↥(Submodule.span ℝ (Λ : Set E))) = ⊤ from by exact (Submodule.span_span_coe_preimage (R := ℝ) (s := (Λ : Set E))))))) Λ⟩
      letI : Countable (ZLattice.comap ℝ Λ (Submodule.span ℝ (Λ : Set E)).subtype) :=
        _root_.instCountable_of_discrete_submodule _
      exact Countable.of_equiv (ZLattice.comap ℝ Λ (Submodule.span ℝ (Λ : Set E)).subtype)
        (Submodule.comapSubtypeEquivOfLe (show Λ ≤ (Submodule.span ℝ (Λ : Set E)).restrictScalars ℤ from fun _ hx ↦ Submodule.subset_span hx)).toEquiv)))) Λ
  have hcL : Countable L := (open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal ZLattice in (fun {E : Type _} [instE1 : NormedAddCommGroup E] [instE2 : NormedSpace ℝ E] [instE3 : FiniteDimensional ℝ E] (Λ : Submodule ℤ E) [DiscreteTopology Λ] => (show Countable Λ from by
      letI hdisc : DiscreteTopology (ZLattice.comap ℝ Λ (Submodule.span ℝ (Λ : Set E)).subtype) :=
        ZLattice.comap_discreteTopology ℝ Λ continuous_subtype_val Subtype.val_injective
      letI hzl : IsZLattice ℝ (ZLattice.comap ℝ Λ (Submodule.span ℝ (Λ : Set E)).subtype) :=
        ⟨(open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal ZLattice in (fun {E : Type _} [instE1 : NormedAddCommGroup E] [instE2 : NormedSpace ℝ E] (Λ : Submodule ℤ E) => (show Submodule.span ℝ ((ZLattice.comap ℝ Λ (Submodule.span ℝ (Λ : Set E)).subtype) :
                Set ↥(Submodule.span ℝ (Λ : Set E))) = ⊤ from by exact (Submodule.span_span_coe_preimage (R := ℝ) (s := (Λ : Set E))))))) Λ⟩
      letI : Countable (ZLattice.comap ℝ Λ (Submodule.span ℝ (Λ : Set E)).subtype) :=
        _root_.instCountable_of_discrete_submodule _
      exact Countable.of_equiv (ZLattice.comap ℝ Λ (Submodule.span ℝ (Λ : Set E)).subtype)
        (Submodule.comapSubtypeEquivOfLe (show Λ ≤ (Submodule.span ℝ (Λ : Set E)).restrictScalars ℤ from fun _ hx ↦ Submodule.subset_span hx)).toEquiv)))) L
  obtain ⟨F, hFm, hFfd, hscale⟩ := exists_isAddFundamentalDomain_measure_smul_le μ Λ
  have hsAm : MeasurableSet (s • A) := hAm.const_smul₀ s
  rw [← measure_inter_add_eq_of_separated μ hΛL hFfd hL hFm hmL hfin hAm hsepA,
    ← measure_inter_add_eq_of_separated μ hΛL hFfd hL hFm hmL hfin hsAm hsepB]
  exact hscale A hAm hAc s hs

end Space

end ZLattice
