/- GID: D5/S3/Arith/DiophantineApproximation/DisjointVariables
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/DisjointVariables
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Polynomials in disjoint variable sets have multiplicative product height. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import D5.S3.Arith.AbsoluteValues.Heights.GaussLemma
public import Mathlib.Algebra.MvPolynomial.Rename

@[expose] public section

noncomputable section

namespace MvPolynomial

open Height

variable {σ τ υ : Type*}

section Coeff

variable {R : Type*} [CommSemiring R]

/-- **The coefficients of a product in disjoint variables are the pairwise products of the
coefficients.** The antidiagonal of `Finsupp.sumElim m n` meets the two supports in the single
point `(mapDomain Sum.inl m, mapDomain Sum.inr n)`, so no sum survives. -/
theorem coeff_sumElim_rename_mul_rename (f : MvPolynomial σ R) (g : MvPolynomial τ R)
    (m : σ →₀ ℕ) (n : τ →₀ ℕ) :
    (AddMonoidAlgebra.coeff (rename Sum.inl f * rename Sum.inr g)) (Finsupp.sumElim m n) = (AddMonoidAlgebra.coeff f) m * (AddMonoidAlgebra.coeff g) n := by
  classical
  have hsum : Finsupp.mapDomain (Sum.inl : σ → σ ⊕ τ) m
      + Finsupp.mapDomain (Sum.inr : τ → σ ⊕ τ) n = Finsupp.sumElim m n :=
    (Finsupp.sumElim_eq_add m n).symm
  have key : ∀ p ∈ Finset.antidiagonal (Finsupp.sumElim m n),
      p ≠ (Finsupp.mapDomain (Sum.inl : σ → σ ⊕ τ) m,
        Finsupp.mapDomain (Sum.inr : τ → σ ⊕ τ) n) →
      (rename Sum.inl f).coeff p.1 * (rename Sum.inr g).coeff p.2 = 0 := by
    intro p hp hne
    rw [Finset.mem_antidiagonal] at hp
    by_contra hc
    obtain ⟨u, hu, -⟩ := coeff_rename_ne_zero (Sum.inl : σ → σ ⊕ τ) f p.1 (left_ne_zero_of_mul hc)
    obtain ⟨w, hw, -⟩ := coeff_rename_ne_zero (Sum.inr : τ → σ ⊕ τ) g p.2 (right_ne_zero_of_mul hc)
    rw [← hu, ← hw, ← Finsupp.sumElim_eq_add] at hp
    have hp' : (u, w) = (m, n) := Finsupp.sumFinsuppEquivProdFinsupp.symm.injective hp
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp' 
    exact hne (Prod.ext hu.symm hw.symm)
  change AddMonoidAlgebra.coeff (rename Sum.inl f * rename Sum.inr g) (Finsupp.sumElim m n) = f.coeff m * g.coeff n
  rw [coeff_mul, Finset.sum_eq_single_of_mem
      (f := fun p : (σ ⊕ τ →₀ ℕ) × (σ ⊕ τ →₀ ℕ) ↦
        (rename Sum.inl f).coeff p.1 * (rename Sum.inr g).coeff p.2)
      _ (Finset.mem_antidiagonal.mpr hsum) key,
    coeff_rename_mapDomain _ Sum.inl_injective, coeff_rename_mapDomain _ Sum.inr_injective]

end Coeff

section LocalFactor

variable {K : Type*} [Field K]

end LocalFactor

section Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

/-- **Bombieri–Gubler, Proposition 1.6.2.** The height of a product of polynomials in disjoint
sets of variables is the product of the heights, exactly. -/
theorem mulHeight_rename_inl_mul_rename_inr {f : MvPolynomial σ K} {g : MvPolynomial τ K}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    (rename Sum.inl f * rename Sum.inr g).mulHeight = f.mulHeight * g.mulHeight := by
  have hmulHeight {x : (σ →₀ ℕ) →₀ K} {y : (τ →₀ ℕ) →₀ K}
      {z : (σ ⊕ τ →₀ ℕ) →₀ K} {e : (σ →₀ ℕ) × (τ →₀ ℕ) → (σ ⊕ τ →₀ ℕ)}
      (he : Function.Injective e) (hmul : ∀ p : (σ →₀ ℕ) × (τ →₀ ℕ), z (e p) = x p.1 * y p.2)
      (hzero : ∀ c, c ∉ Set.range e → z c = 0) (hx : x ≠ 0) (hy : y ≠ 0) :
      z.mulHeight = x.mulHeight * y.mulHeight := by
    have hinj : Function.Injective fun p : x.support × y.support ↦ e (p.1.val, p.2.val) := by
      intro p q h
      have h' := he h
      exact Prod.ext (Subtype.ext (congrArg Prod.fst h')) (Subtype.ext (congrArg Prod.snd h'))
    have hcov : ∀ c ∈ z.support,
        c ∈ Set.range fun p : x.support × y.support ↦ e (p.1.val, p.2.val) := by
      intro c hc
      have hc' : z c ≠ 0 := Finsupp.mem_support_iff.mp hc
      obtain ⟨p, rfl⟩ : c ∈ Set.range e := by
        by_contra h
        exact hc' (hzero c h)
      rw [hmul p] at hc'
      exact ⟨⟨⟨p.1, Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hc')⟩,
        ⟨p.2, Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hc')⟩⟩, rfl⟩
    have h1 : z.mulHeight
        = Height.mulHeight fun p : x.support × y.support ↦ z (e (p.1.val, p.2.val)) :=
      (open scoped Classical NumberField in (open Height Module Matrix Set Finsupp in (fun {K : Type _} [instK : Field K] [instH : Height.AdmissibleAbsValues K] {α : Type _} {ι : Type _} [Finite ι] (x : α →₀ K) (f : ι → α)
            (hf : Function.Injective f) (hx : ∀ a ∈ x.support, a ∈ Set.range f) => (show x.mulHeight = Height.mulHeight fun i ↦ x (f i) from by
          have hbij : Function.Bijective
              (fun i : Function.support (fun i ↦ x (f i)) ↦
                (⟨f i.val, Finsupp.mem_support_iff.mpr i.prop⟩ : x.support)) := by
            refine ⟨fun i j h ↦ Subtype.ext (hf (congrArg Subtype.val h)), fun ⟨a, ha⟩ ↦ ?_⟩
            obtain ⟨i, rfl⟩ := hx a ha
            exact ⟨⟨i, Finsupp.mem_support_iff.mp ha⟩, rfl⟩
          rw [Height.mulHeight_eq_mulHeight_restrict_support fun i ↦ x (f i), Finsupp.mulHeight,
            ← Height.mulHeight_comp_equiv (Equiv.ofBijective _ hbij)]
          rfl)))) z _ hinj hcov
    have h2 : (fun p : x.support × y.support ↦ z (e (p.1.val, p.2.val)))
        = fun p : x.support × y.support ↦ x p.1.val * y p.2.val :=
      funext fun p ↦ hmul _
    have h3 : Height.mulHeight (fun p : x.support × y.support ↦ x p.1.val * y p.2.val)
        = Height.mulHeight (fun i : x.support ↦ x i.val)
          * Height.mulHeight (fun i : y.support ↦ y i.val) :=
      Height.mulHeight_fun_mul_eq ((fun {x : _ →₀ K} (hx : x ≠ 0) ↦ (show (fun i : x.support ↦ x i.val) ≠ 0 from by
        obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hx
        exact Function.ne_iff.mpr ⟨⟨i, hi⟩, Finsupp.mem_support_iff.mp hi⟩)) hx) ((fun {x : _ →₀ K} (hx : x ≠ 0) ↦ (show (fun i : x.support ↦ x i.val) ≠ 0 from by
        obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hx
        exact Function.ne_iff.mpr ⟨⟨i, hi⟩, Finsupp.mem_support_iff.mp hi⟩)) hy)
    rw [h1, h2, h3, ← (open scoped Classical NumberField in (open Height Module Matrix Set Finsupp in (fun {K : Type _} [instK : Field K] [instH : Height.AdmissibleAbsValues K] {α : Type _} {s : Finset α} (x : α →₀ K) (hx : x.support ⊆ s) => (show x.mulHeight = Height.mulHeight fun i : s ↦ x i.val from ((open scoped Classical NumberField in (open Height Module Matrix Set Finsupp in (fun {K : Type _} [instK : Field K] [instH : Height.AdmissibleAbsValues K] {α : Type _} {ι : Type _} [Finite ι] (x : α →₀ K) (f : ι → α)
            (hf : Function.Injective f) (hx : ∀ a ∈ x.support, a ∈ Set.range f) => (show x.mulHeight = Height.mulHeight fun i ↦ x (f i) from by
          have hbij : Function.Bijective
              (fun i : Function.support (fun i ↦ x (f i)) ↦
                (⟨f i.val, Finsupp.mem_support_iff.mpr i.prop⟩ : x.support)) := by
            refine ⟨fun i j h ↦ Subtype.ext (hf (congrArg Subtype.val h)), fun ⟨a, ha⟩ ↦ ?_⟩
            obtain ⟨i, rfl⟩ := hx a ha
            exact ⟨⟨i, Finsupp.mem_support_iff.mp ha⟩, rfl⟩
          rw [Height.mulHeight_eq_mulHeight_restrict_support fun i ↦ x (f i), Finsupp.mulHeight,
            ← Height.mulHeight_comp_equiv (Equiv.ofBijective _ hbij)]
          rfl)))) x) Subtype.val Subtype.val_injective fun _ ha ↦ ⟨⟨_, hx ha⟩, rfl⟩)))) x (Finset.Subset.refl _),
      ← (open scoped Classical NumberField in (open Height Module Matrix Set Finsupp in (fun {K : Type _} [instK : Field K] [instH : Height.AdmissibleAbsValues K] {α : Type _} {s : Finset α} (x : α →₀ K) (hx : x.support ⊆ s) => (show x.mulHeight = Height.mulHeight fun i : s ↦ x i.val from ((open scoped Classical NumberField in (open Height Module Matrix Set Finsupp in (fun {K : Type _} [instK : Field K] [instH : Height.AdmissibleAbsValues K] {α : Type _} {ι : Type _} [Finite ι] (x : α →₀ K) (f : ι → α)
              (hf : Function.Injective f) (hx : ∀ a ∈ x.support, a ∈ Set.range f) => (show x.mulHeight = Height.mulHeight fun i ↦ x (f i) from by
            have hbij : Function.Bijective
                (fun i : Function.support (fun i ↦ x (f i)) ↦
                  (⟨f i.val, Finsupp.mem_support_iff.mpr i.prop⟩ : x.support)) := by
              refine ⟨fun i j h ↦ Subtype.ext (hf (congrArg Subtype.val h)), fun ⟨a, ha⟩ ↦ ?_⟩
              obtain ⟨i, rfl⟩ := hx a ha
              exact ⟨⟨i, Finsupp.mem_support_iff.mp ha⟩, rfl⟩
            rw [Height.mulHeight_eq_mulHeight_restrict_support fun i ↦ x (f i), Finsupp.mulHeight,
              ← Height.mulHeight_comp_equiv (Equiv.ofBijective _ hbij)]
            rfl)))) x) Subtype.val Subtype.val_injective fun _ ha ↦ ⟨⟨_, hx ha⟩, rfl⟩)))) y (Finset.Subset.refl _)]

  change Finsupp.mulHeight (AddMonoidAlgebra.coeff (rename Sum.inl f * rename Sum.inr g))
    = Finsupp.mulHeight (AddMonoidAlgebra.coeff f) * Finsupp.mulHeight (AddMonoidAlgebra.coeff g)
  exact hmulHeight (x := AddMonoidAlgebra.coeff f) (y := AddMonoidAlgebra.coeff g)
    (z := AddMonoidAlgebra.coeff (rename Sum.inl f * rename Sum.inr g))
    (e := fun p : (σ →₀ ℕ) × (τ →₀ ℕ) ↦ Finsupp.sumElim p.1 p.2) Finsupp.sumFinsuppEquivProdFinsupp.symm.injective
    (fun p ↦ coeff_sumElim_rename_mul_rename f g p.1 p.2)
    (fun c hc ↦ absurd (Finsupp.sumFinsuppEquivProdFinsupp.symm.surjective c) (by simpa using hc))
    (fun h ↦ hf (AddMonoidAlgebra.coeff_injective
      (by simpa only [AddMonoidAlgebra.coeff_zero] using h)))
    (fun h ↦ hg (AddMonoidAlgebra.coeff_injective
      (by simpa only [AddMonoidAlgebra.coeff_zero] using h)))

/-- **The form Layer 2.7 consumes.** Two polynomials embedded into one set of variables along
injections with disjoint ranges have the product of their heights. -/
theorem mulHeight_rename_mul_rename_of_disjoint {u : σ → υ} {w : τ → υ}
    (hu : Function.Injective u) (hw : Function.Injective w)
    (hd : Disjoint (Set.range u) (Set.range w)) {f : MvPolynomial σ K} {g : MvPolynomial τ K}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    (rename u f * rename w g).mulHeight = f.mulHeight * g.mulHeight := by
  have hrename {e : σ ⊕ τ → υ} (he : Function.Injective e)
      (P : MvPolynomial (σ ⊕ τ) K) : (rename e P).mulHeight = P.mulHeight := by
    have hinj : Function.Injective fun m : (AddMonoidAlgebra.coeff P).support ↦ Finsupp.mapDomain e m.val :=
      fun m n h ↦ Subtype.ext (Finsupp.mapDomain_injective he h)
    have hcov : ∀ d ∈ (AddMonoidAlgebra.coeff (rename e P)).support,
        d ∈ Set.range fun m : (AddMonoidAlgebra.coeff P).support ↦ Finsupp.mapDomain e m.val := by
      intro d hd
      obtain ⟨u, hu, hu0⟩ := coeff_rename_ne_zero e P d (Finsupp.mem_support_iff.mp hd)
      exact ⟨⟨u, Finsupp.mem_support_iff.mpr hu0⟩, hu⟩
    have hfun : (fun m : (AddMonoidAlgebra.coeff P).support ↦ (AddMonoidAlgebra.coeff (rename e P)) (Finsupp.mapDomain e m.val))
        = fun m : (AddMonoidAlgebra.coeff P).support ↦ (AddMonoidAlgebra.coeff P) m.val :=
      funext fun m ↦ coeff_rename_mapDomain e he P m.val
    change Finsupp.mulHeight (AddMonoidAlgebra.coeff (rename e P)) = Finsupp.mulHeight (AddMonoidAlgebra.coeff P)
    rw [(open scoped Classical NumberField in (open Height Module Matrix Set Finsupp in (fun {K : Type _} [instK : Field K] [instH : Height.AdmissibleAbsValues K] {α : Type _} {ι : Type _} [Finite ι] (x : α →₀ K) (f : ι → α)
          (hf : Function.Injective f) (hx : ∀ a ∈ x.support, a ∈ Set.range f) => (show x.mulHeight = Height.mulHeight fun i ↦ x (f i) from by
        have hbij : Function.Bijective
            (fun i : Function.support (fun i ↦ x (f i)) ↦
              (⟨f i.val, Finsupp.mem_support_iff.mpr i.prop⟩ : x.support)) := by
          refine ⟨fun i j h ↦ Subtype.ext (hf (congrArg Subtype.val h)), fun ⟨a, ha⟩ ↦ ?_⟩
          obtain ⟨i, rfl⟩ := hx a ha
          exact ⟨⟨i, Finsupp.mem_support_iff.mp ha⟩, rfl⟩
        rw [Height.mulHeight_eq_mulHeight_restrict_support fun i ↦ x (f i), Finsupp.mulHeight,
          ← Height.mulHeight_comp_equiv (Equiv.ofBijective _ hbij)]
        rfl)))) _ _ hinj hcov, hfun,
      (open scoped Classical NumberField in (open Height Module Matrix Set Finsupp in (fun {K : Type _} [instK : Field K] [instH : Height.AdmissibleAbsValues K] {α : Type _} {s : Finset α} (x : α →₀ K) (hx : x.support ⊆ s) => (show x.mulHeight = Height.mulHeight fun i : s ↦ x i.val from ((open scoped Classical NumberField in (open Height Module Matrix Set Finsupp in (fun {K : Type _} [instK : Field K] [instH : Height.AdmissibleAbsValues K] {α : Type _} {ι : Type _} [Finite ι] (x : α →₀ K) (f : ι → α)
              (hf : Function.Injective f) (hx : ∀ a ∈ x.support, a ∈ Set.range f) => (show x.mulHeight = Height.mulHeight fun i ↦ x (f i) from by
            have hbij : Function.Bijective
                (fun i : Function.support (fun i ↦ x (f i)) ↦
                  (⟨f i.val, Finsupp.mem_support_iff.mpr i.prop⟩ : x.support)) := by
              refine ⟨fun i j h ↦ Subtype.ext (hf (congrArg Subtype.val h)), fun ⟨a, ha⟩ ↦ ?_⟩
              obtain ⟨i, rfl⟩ := hx a ha
              exact ⟨⟨i, Finsupp.mem_support_iff.mp ha⟩, rfl⟩
            rw [Height.mulHeight_eq_mulHeight_restrict_support fun i ↦ x (f i), Finsupp.mulHeight,
              ← Height.mulHeight_comp_equiv (Equiv.ofBijective _ hbij)]
            rfl)))) x) Subtype.val Subtype.val_injective fun _ ha ↦ ⟨⟨_, hx ha⟩, rfl⟩)))) (AddMonoidAlgebra.coeff P) (Finset.Subset.refl _)]

  have hren : rename u f * rename w g =
      rename (Sum.elim u w) (rename Sum.inl f * rename Sum.inr g) := by
    rw [map_mul, rename_rename, rename_rename, Sum.elim_comp_inl, Sum.elim_comp_inr]
  rw [hren,
    hrename (Sum.elim_injective.mpr
      ⟨hu, hw, fun a b h ↦ Set.disjoint_left.mp hd ⟨a, rfl⟩ ⟨b, h.symm⟩⟩),
    mulHeight_rename_inl_mul_rename_inr hf hg]

end Height

end MvPolynomial

section Examples

open Height MvPolynomial

end Examples

end
