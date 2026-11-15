/- GID: D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTensorReflection
   generality: E
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/EmbeddedTensorReflection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.TensorProduct.Prod, mathlib/module/Mathlib.RepresentationTheory.Intertwining]
   utility: none
   digest: Tensor reflection along arbitrary faithful finite additive embeddings, with the original relative witnesses. -/

import D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrResidueCriterion
import D5.S3.FiniteGroups.GroupAlgebra.EmbeddedPolynomialCancellation
import D5.S3.FiniteGroups.GroupAlgebra.EmbeddedOriginalClassification
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
Recurrence provenance: Elmer--Kadr, Proof of Corollary 1.3,
DOI 10.1007/s13366-026-00855-9 / arXiv:2510.07939v1.
The theorem restricts the original signed polynomial contragredients along
an arbitrary faithful finite additive embedding E →+ K. The coefficient
field need not be finite, and the group has its own independent universe.
Intermediate relative-projective factors retain the original unrestricted
X/P witnesses in the field universe. The recurrence and its boundary cases
are adapted from ElmerKadrTensorReflection; this is not a novelty claim.

This source is prepared for native compilation; no build or kernel acceptance
is claimed by the source-only implementation attempt.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.EmbeddedTensorReflection

open D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrTensorCounterexample
open D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrPositiveCriterion
open D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrResidueCriterion
open scoped TensorProduct DirectSum

universe uK uG uE

section ActualEquivalences

variable {K A B C D : Type uK} {G : Type uG} [Field K] [Group G]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C] [AddCommGroup D] [Module K D]

private def prodCongr {ρ : Representation K G A} {σ : Representation K G B}
    {τ : Representation K G C} {υ : Representation K G D}
    (e : ρ.Equiv σ) (f : τ.Equiv υ) : (ρ.prod τ).Equiv (σ.prod υ) :=
  Representation.Equiv.mk (e.toLinearEquiv.prodCongr f.toLinearEquiv) fun c => by
    apply LinearMap.ext
    intro x
    exact Prod.ext (LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' c) x.1)
      (LinearMap.congr_fun (f.toIntertwiningMap.isIntertwining' c) x.2)

private def tensorCongr {ρ : Representation K G A} {σ : Representation K G B}
    {τ : Representation K G C} {υ : Representation K G D}
    (e : ρ.Equiv σ) (f : τ.Equiv υ) : (ρ.tprod τ).Equiv (σ.tprod υ) :=
  Representation.Equiv.mk (TensorProduct.congr e.toLinearEquiv f.toLinearEquiv)
    fun c => by
      apply TensorProduct.ext'
      intro x y
      change e (ρ c x) ⊗ₜ[K] f (τ c y) = σ c (e x) ⊗ₜ[K] υ c (f y)
      exact congrArg₂ (fun a b => a ⊗ₜ[K] b)
        (LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' c) x)
        (LinearMap.congr_fun (f.toIntertwiningMap.isIntertwining' c) y)

private def prodComm (ρ : Representation K G A) (σ : Representation K G B) :
    (ρ.prod σ).Equiv (σ.prod ρ) :=
  Representation.Equiv.mk (LinearEquiv.prodComm K A B) fun _ => by
    apply LinearMap.ext
    intro x
    rfl

private def tensorProdRight (ρ : Representation K G A)
    (σ : Representation K G B) (τ : Representation K G C) :
    (ρ.tprod (σ.prod τ)).Equiv ((ρ.tprod σ).prod (ρ.tprod τ)) :=
  Representation.Equiv.mk (TensorProduct.prodRight K K A B C) fun _ => by
    apply TensorProduct.ext'
    intro x y
    simp only [LinearMap.comp_apply, Representation.tprod_apply,
      TensorProduct.map_tmul, TensorProduct.prodRight_tmul] <;> rfl

private def tensorProdLeft (ρ : Representation K G A)
    (σ : Representation K G B) (τ : Representation K G C) :
    ((ρ.prod σ).tprod τ).Equiv ((ρ.tprod τ).prod (σ.tprod τ)) :=
  Representation.Equiv.mk (TensorProduct.prodLeft K K A B C) fun _ => by
    apply TensorProduct.ext'
    rintro ⟨x, y⟩ z
    simp only [LinearMap.comp_apply, Representation.tprod_apply,
      TensorProduct.map_tmul, TensorProduct.prodLeft_tmul] <;> rfl

end ActualEquivalences

section OriginalWitnessCalculus

variable {K M A B C D : Type uK} {G : Type uG} [Field K] [Group G]
  [AddCommGroup M] [Module K M] [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C]
  [AddCommGroup D] [Module K D]
  (τ : Representation K G M)
  {ρ : Representation K G A} {σ : Representation K G B}
  {υ : Representation K G C} {ξ : Representation K G D}

-- These are the original retract/decomposition constructions with only
-- the group-universe parameter separated from the field universe.
private theorem relativeProjective_transport (e : ρ.Equiv σ)
    (hρ : RelativeProjective τ (Rep.of ρ)) : RelativeProjective τ (Rep.of σ) := by
  obtain ⟨X, i, r, hri⟩ := hρ
  refine ⟨X, i.comp e.symm.toIntertwiningMap, e.toIntertwiningMap.comp r, ?_⟩
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change e (r (i (e.symm x))) = x
  have hx := congrArg (fun k => k (e.symm x)) hri
  change r (i (e.symm x)) = e.symm x at hx
  rw [hx, e.apply_symm_apply]

private theorem relativeStableIso_of_decomposition
    (ρ : Representation K G A) (σ : Representation K G B)
    (κ : Representation K G C) (e : σ.Equiv (ρ.prod κ))
    (hκ : RelativeProjective τ (Rep.of κ)) : RelativeStableIso τ ρ σ := by
  let inS := Representation.IntertwiningMap.inl K ρ κ
  let prS := Representation.IntertwiningMap.fst K ρ κ
  let inR := Representation.IntertwiningMap.inr K ρ κ
  let prR := Representation.IntertwiningMap.snd K ρ κ
  let f := e.symm.toIntertwiningMap.comp inS
  let g := prS.comp e.toIntertwiningMap
  have hgf : g.comp f = .id ρ := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change (e (e.symm (x, 0))).1 = x
    rw [e.apply_symm_apply]
  refine ⟨f, g, ?_, ?_⟩
  · rw [hgf, sub_self]
    exact relativeFactors_zero τ ρ ρ
  · refine ⟨Rep.of κ, hκ, prR.comp e.toIntertwiningMap,
      -(e.symm.toIntertwiningMap.comp inR), ?_⟩
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change -e.symm (0, (e x).2) = e.symm ((e x).1, 0) - x
    apply e.injective
    rw [map_neg, map_sub]
    change -e.toLinearEquiv (e.toLinearEquiv.symm (0, (e x).2)) =
      e.toLinearEquiv (e.toLinearEquiv.symm ((e x).1, 0)) - e.toLinearEquiv x
    rw [e.toLinearEquiv.apply_symm_apply, e.toLinearEquiv.apply_symm_apply]
    apply Prod.ext <;> simp

private theorem projective_prod
    (hρ : RelativeProjective τ (Rep.of ρ))
    (hσ : RelativeProjective τ (Rep.of σ)) :
    RelativeProjective τ (Rep.of (ρ.prod σ)) := by
  obtain ⟨X, i, r, hri⟩ := hρ
  obtain ⟨Y, j, s, hsj⟩ := hσ
  let e := tensorProdLeft X.ρ Y.ρ τ
  let I := (i.comp (Representation.IntertwiningMap.fst K ρ σ)).prod
    (j.comp (Representation.IntertwiningMap.snd K ρ σ))
  let R := (r.comp (Representation.IntertwiningMap.fst K (X.ρ.tprod τ) (Y.ρ.tprod τ))).prod
    (s.comp (Representation.IntertwiningMap.snd K (X.ρ.tprod τ) (Y.ρ.tprod τ)))
  refine ⟨Rep.of (X.ρ.prod Y.ρ), e.symm.toIntertwiningMap.comp I,
    R.comp e.toIntertwiningMap, ?_⟩
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  rintro ⟨x, y⟩
  change R (e (e.symm (i x, j y))) = (x, y)
  rw [e.apply_symm_apply]
  exact Prod.ext (congrArg (fun k => k x) hri) (congrArg (fun k => k y) hsj)

private theorem projective_lTensor (υ : Representation K G C)
    (hρ : RelativeProjective τ (Rep.of ρ)) :
    RelativeProjective τ (Rep.of (υ.tprod ρ)) := by
  obtain ⟨X, i, r, hri⟩ := hρ
  let e := Representation.TensorProduct.assoc υ X.ρ τ
  refine ⟨Rep.of (υ.tprod X.ρ),
    e.symm.toIntertwiningMap.comp (i.lTensor υ),
    (r.lTensor υ).comp e.toIntertwiningMap, ?_⟩
  apply Representation.IntertwiningMap.ext
  apply TensorProduct.ext'
  intro x y
  change (r.lTensor υ) (e (e.symm (x ⊗ₜ[K] i y))) = x ⊗ₜ[K] y
  rw [e.apply_symm_apply]
  change x ⊗ₜ[K] r (i y) = x ⊗ₜ[K] y
  rw [show r (i y) = y from congrArg (fun k => k y) hri]

private theorem factors_neg {f : ρ.IntertwiningMap σ}
    (hf : RelativeFactors τ f) : RelativeFactors τ (-f) := by
  obtain ⟨P, hP, a, b, hab⟩ := hf
  refine ⟨P, hP, a, -b, ?_⟩
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change -(b (a x)) = -(f x)
  rw [show b (a x) = f x from congrArg (fun k => k x) hab]

private theorem factors_add {f g : ρ.IntertwiningMap σ}
    (hf : RelativeFactors τ f) (hg : RelativeFactors τ g) :
    RelativeFactors τ (f + g) := by
  obtain ⟨P, hP, a, b, hab⟩ := hf
  obtain ⟨Q, hQ, c, d, hcd⟩ := hg
  refine ⟨Rep.of (P.ρ.prod Q.ρ), projective_prod τ hP hQ, a.prod c,
    b.comp (Representation.IntertwiningMap.fst K P.ρ Q.ρ) +
      d.comp (Representation.IntertwiningMap.snd K P.ρ Q.ρ), ?_⟩
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change b (a x) + d (c x) = f x + g x
  rw [show b (a x) = f x from congrArg (fun k => k x) hab,
    show d (c x) = g x from congrArg (fun k => k x) hcd]

private theorem factors_lTensor {f : ρ.IntertwiningMap σ}
    (hf : RelativeFactors τ f) (υ : Representation K G C) :
    RelativeFactors τ (f.lTensor υ) := by
  obtain ⟨P, hP, a, b, hab⟩ := hf
  refine ⟨Rep.of (υ.tprod P.ρ), projective_lTensor τ υ hP,
    a.lTensor υ, b.lTensor υ, ?_⟩
  apply Representation.IntertwiningMap.ext
  apply TensorProduct.ext'
  intro x y
  change x ⊗ₜ[K] b (a y) = x ⊗ₜ[K] f y
  rw [show b (a y) = f y from congrArg (fun k => k y) hab]

theorem relativeStableIso_of_equiv (e : ρ.Equiv σ) :
    RelativeStableIso τ ρ σ := by
  refine ⟨e.toIntertwiningMap, e.symm.toIntertwiningMap, ?_, ?_⟩
  · have hz : e.symm.toIntertwiningMap.comp e.toIntertwiningMap - .id ρ = 0 := by
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      change e.symm (e x) - x = 0
      rw [e.symm_apply_apply, sub_self]
    rw [hz]
    exact relativeFactors_zero τ ρ ρ
  · have hz : e.toIntertwiningMap.comp e.symm.toIntertwiningMap - .id σ = 0 := by
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      change e (e.symm x) - x = 0
      rw [e.apply_symm_apply, sub_self]
    rw [hz]
    exact relativeFactors_zero τ σ σ

private theorem stable_refl (ρ : Representation K G A) : RelativeStableIso τ ρ ρ :=
  relativeStableIso_of_equiv τ (Representation.Equiv.refl ρ)

private theorem stable_symm (h : RelativeStableIso τ ρ σ) : RelativeStableIso τ σ ρ := by
  obtain ⟨f, g, hgf, hfg⟩ := h
  exact ⟨g, f, hfg, hgf⟩

-- Shared sandwich outputs are left-associated; the pointwise change steps
-- below normalize composition directly, retaining the original P witnesses.
theorem stable_trans (h : RelativeStableIso τ ρ σ)
    (h' : RelativeStableIso τ σ υ) : RelativeStableIso τ ρ υ := by
  obtain ⟨f, g, hgf, hfg⟩ := h
  obtain ⟨f', g', hg'f', hf'g'⟩ := h'
  refine ⟨f'.comp f, g.comp g', ?_, ?_⟩
  · have hh := factors_add τ (ElmerKadrPolynomialCancellation.factors_sandwich τ hg'f' g f) hgf
    convert hh using 1
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change g (g' (f' (f x))) - x = g (g' (f' (f x)) - f x) + (g (f x) - x)
    rw [map_sub]
    abel
  · have hh := factors_add τ (ElmerKadrPolynomialCancellation.factors_sandwich τ hfg f' g') hf'g'
    convert hh using 1
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change f' (f (g (g' x))) - x = f' (f (g (g' x)) - g' x) + (f' (g' x) - x)
    rw [map_sub]
    abel

theorem stable_lTensor (h : RelativeStableIso τ ρ σ)
    (υ : Representation K G C) : RelativeStableIso τ (υ.tprod ρ) (υ.tprod σ) := by
  obtain ⟨f, g, hgf, hfg⟩ := h
  refine ⟨f.lTensor υ, g.lTensor υ, ?_, ?_⟩
  · convert factors_lTensor τ hgf υ using 1
    apply Representation.IntertwiningMap.ext
    apply TensorProduct.ext'
    intro x y
    change x ⊗ₜ[K] g (f y) - x ⊗ₜ[K] y = x ⊗ₜ[K] (g (f y) - y)
    rw [TensorProduct.tmul_sub]
  · convert factors_lTensor τ hfg υ using 1
    apply Representation.IntertwiningMap.ext
    apply TensorProduct.ext'
    intro x y
    change x ⊗ₜ[K] f (g y) - x ⊗ₜ[K] y = x ⊗ₜ[K] (f (g y) - y)
    rw [TensorProduct.tmul_sub]

private theorem stable_rTensor (h : RelativeStableIso τ ρ σ)
    (υ : Representation K G C) : RelativeStableIso τ (ρ.tprod υ) (σ.tprod υ) :=
  stable_trans τ
    (relativeStableIso_of_equiv τ (Representation.TensorProduct.comm ρ υ))
    (stable_trans τ (stable_lTensor τ h υ)
      (relativeStableIso_of_equiv τ (Representation.TensorProduct.comm υ σ)))

private theorem stable_tensor (h : RelativeStableIso τ ρ σ)
    (h' : RelativeStableIso τ υ ξ) : RelativeStableIso τ (ρ.tprod υ) (σ.tprod ξ) :=
  stable_trans τ (stable_rTensor τ h υ) (stable_lTensor τ h' σ)

private theorem stable_prod (h : RelativeStableIso τ ρ σ)
    (h' : RelativeStableIso τ υ ξ) : RelativeStableIso τ (ρ.prod υ) (σ.prod ξ) := by
  obtain ⟨f, g, hgf, hfg⟩ := h
  obtain ⟨f', g', hg'f', hf'g'⟩ := h'
  let F := (f.comp (Representation.IntertwiningMap.fst K ρ υ)).prod
    (f'.comp (Representation.IntertwiningMap.snd K ρ υ))
  let G := (g.comp (Representation.IntertwiningMap.fst K σ ξ)).prod
    (g'.comp (Representation.IntertwiningMap.snd K σ ξ))
  refine ⟨F, G, ?_, ?_⟩
  · have hh := factors_add τ
      (ElmerKadrPolynomialCancellation.factors_sandwich τ hgf (Representation.IntertwiningMap.inl K ρ υ)
        (Representation.IntertwiningMap.fst K ρ υ))
      (ElmerKadrPolynomialCancellation.factors_sandwich τ hg'f' (Representation.IntertwiningMap.inr K ρ υ)
        (Representation.IntertwiningMap.snd K ρ υ))
    convert hh using 1
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    rintro ⟨x, y⟩
    change (g (f x), g' (f' y)) - (x, y) =
      (g (f x) - x, 0) + (0, g' (f' y) - y)
    exact Prod.ext (by simp) (by simp)
  · have hh := factors_add τ
      (ElmerKadrPolynomialCancellation.factors_sandwich τ hfg (Representation.IntertwiningMap.inl K σ ξ)
        (Representation.IntertwiningMap.fst K σ ξ))
      (ElmerKadrPolynomialCancellation.factors_sandwich τ hf'g' (Representation.IntertwiningMap.inr K σ ξ)
        (Representation.IntertwiningMap.snd K σ ξ))
    convert hh using 1
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    rintro ⟨x, y⟩
    change (f (g x), f' (g' y)) - (x, y) =
      (f (g x) - x, 0) + (0, f' (g' y) - y)
    exact Prod.ext (by simp) (by simp)

private theorem stable_of_projectives
    (hρ : RelativeProjective τ (Rep.of ρ))
    (hσ : RelativeProjective τ (Rep.of σ)) : RelativeStableIso τ ρ σ := by
  refine ⟨0, 0, ?_, ?_⟩
  · have hid : RelativeFactors τ (.id ρ) := by
      refine ⟨Rep.of ρ, hρ, .id ρ, .id ρ, ?_⟩
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      rfl
    simpa only [Representation.IntertwiningMap.zero_comp, zero_sub] using factors_neg τ hid
  · have hid : RelativeFactors τ (.id σ) := by
      refine ⟨Rep.of σ, hσ, .id σ, .id σ, ?_⟩
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      rfl
    simpa only [Representation.IntertwiningMap.zero_comp, zero_sub] using factors_neg τ hid

end OriginalWitnessCalculus

section PolynomialSteps

variable {K : Type uK} [Field K]

/-- The Fin 1 sum in the saved full-residue decomposition is the actual
single polynomial factor. All reindexing is on the original direct sum. -/
def expectedOne (i j : ℕ) :
    (expectedAction (K := K) i j 1).Equiv (dualAction K (i + j - 1)) := by
  let f := firstProjection (K := K) i j 1 (by decide)
  let g := firstInclusion (K := K) i j 1 (by decide)
  -- Prove this identity on the original Fin 1 sum directly: the old
  -- theorem was stated in a finite-field section, while f/g themselves
  -- are actual maps over every field.
  have hfg : f.comp g = .id _ := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact DirectSum.component.lof_self (R := K) (ι := Fin 1)
      (M := fun ell : Fin 1 => DualPower K (i + j - (2 * ell.val + 1)))
      ⟨0, by decide⟩ x
  exact Representation.Equiv.mk
    { toFun := f
      invFun := g
      left_inv := fun x => by
        apply DFinsupp.ext
        intro ell
        have he : ell = (⟨0, by decide⟩ : Fin 1) := Subsingleton.elim _ _
        subst ell
        change f (g (f x)) = f x
        exact congrArg (fun k => k (f x)) hfg
      right_inv := fun x => congrArg (fun k => k x) hfg
      map_add' := f.map_add
      map_smul' := fun c x => f.map_smul c x }
    f.isIntertwining'

/-- Only V_2 tensor V_m is split in the recurrence. Its binomial is m,
and its actual kernel factor V_1 tensor V_(m-1) is removed by the unit. -/
private def two_split_field (m : ℕ) (hm : 0 < m) (hc : (m : K) ≠ 0) :
    ((dualAction K 2).tprod (dualAction K m)).Equiv
      ((dualAction K (m + 1)).prod (dualAction K (m - 1))) := by
  have hb : ((2 + m - 2).choose (2 - 1) : K) ≠ 0 := by
    simpa only [show 2 + m - 2 = m by omega,
      show 2 - 1 = 1 from rfl, Nat.choose_one_right] using hc
  have hn : 2 + m - 1 = m + 1 := by omega
  let e : ((dualAction K 2).tprod (dualAction K m)).Equiv
      ((dualAction K (m + 1)).prod
        ((dualAction K 1).tprod (dualAction K (m - 1)))) := by
    have hs := tensor_split (K := K) 2 m (by decide) hm hb
    rw [hn] at hs
    exact hs
  exact e.trans (prodCongr (Representation.Equiv.refl _)
    (tensorUnitLeft (dualAction K (m - 1))))

end PolynomialSteps

section EmbeddingArithmetic

variable {K : Type uK} [Field K]
  {E : Type uE} [AddGroup E] [Fintype E] [Nontrivial E]
  (α : E →+ K) (hα : Function.Injective α)
  {p : ℕ} [Fact p.Prime] [CharP K p]

include hα in
/-- Divisibility is used before estimating the top block. In particular
 a+1=card(E)/p and the actual V_card(E) summand are retained. -/
private theorem full_block_bound (a u : ℕ) (h : p * a + u < Fintype.card E) :
    a + 1 ≤ Fintype.card E / p := by
  have hq : p * (Fintype.card E / p) = Fintype.card E :=
    Nat.mul_div_cancel' (EmbeddedOriginalClassification.prime_dvd_card_embedding
      (p := p) α hα)
  by_contra hn
  have ha : Fintype.card E / p ≤ a := by omega
  have hm := Nat.mul_le_mul_left p ha
  omega

private theorem residue_cast_ne_zero (a r : ℕ) (hr : 0 < r) (hrp : r < p) :
    ((p * a + r : ℕ) : K) ≠ 0 := by
  intro hz
  have hc : (r : K) = 0 := by
    simpa only [Nat.cast_add, Nat.cast_mul, CharP.cast_eq_zero K p,
      zero_mul, zero_add] using hz
  have hpr : p ∣ r := (CharP.cast_eq_zero_iff K p r).mp hc
  have hm : r % p = 0 := Nat.mod_eq_zero_of_dvd hpr
  rw [Nat.mod_eq_of_lt hrp] at hm
  omega

end EmbeddingArithmetic

section RestrictedPolynomialSteps

variable {K : Type uK} [Field K]
  {E : Type uE} [AddGroup E] (α : E →+ K)

/-- Restrict the proved field-level splitting. Equivariance is not assumed. -/
private def two_split (m : ℕ) (hm : 0 < m) (hc : (m : K) ≠ 0) :
    (Representation.tprod ((dualAction K 2).comp α.toMultiplicative)
      ((dualAction K m).comp α.toMultiplicative)).Equiv
      (Representation.prod ((dualAction K (m + 1)).comp α.toMultiplicative)
        ((dualAction K (m - 1)).comp α.toMultiplicative)) :=
  EmbeddedOriginalClassification.restrictEquiv α.toMultiplicative
    (two_split_field (K := K) m hm hc)

/-- The actual tensor unit for any E-representation, with E and K in
independent universes. The one-dimensional polynomial equivalence is
restricted; its tensor and the actual Mathlib unitor retain equivariance. -/
private def embeddedUnitLeft {A : Type uK} [AddCommGroup A] [Module K A]
    (ρ : Representation K (Multiplicative E) A) :
    (Representation.tprod ((dualAction K 1).comp α.toMultiplicative) ρ).Equiv ρ := by
  let e : Representation.Equiv ((dualAction K 1).comp α.toMultiplicative)
      (Representation.trivial K (Multiplicative E) K) :=
    EmbeddedOriginalClassification.restrictEquiv α.toMultiplicative
      (dualOneEquiv (K := K))
  exact (tensorCongr e (Representation.Equiv.refl ρ)).trans
    (Representation.TensorProduct.lid K ρ)

private def embeddedUnitRight {A : Type uK} [AddCommGroup A] [Module K A]
    (ρ : Representation K (Multiplicative E) A) :
    (Representation.tprod ρ ((dualAction K 1).comp α.toMultiplicative)).Equiv ρ :=
  (Representation.TensorProduct.comm ρ
    ((dualAction K 1).comp α.toMultiplicative)).trans (embeddedUnitLeft α ρ)

/-- Restrict the original field-level retract, retaining the very same X,
i and r as linear maps. No finiteness condition on any witness is added. -/
private theorem multiple_tensor_projective
    {p : ℕ} [Fact p.Prime] [CharP K p] (s a m : ℕ) (ha : a ≤ s) :
    RelativeProjective
      ((PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s).comp
        α.toMultiplicative)
      (Rep.of (Representation.tprod ((dualAction K (p * a)).comp α.toMultiplicative)
        ((dualAction K m).comp α.toMultiplicative))) :=
  EmbeddedOriginalClassification.restrict_relativeProjective α.toMultiplicative
    (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s)
    (multiple_tensor_relativeProjective (K := K) (p := p) s a m ha)

end RestrictedPolynomialSteps

section SingleFactorRecurrence

variable {K : Type uK} [Field K]
  {E : Type uE} [AddGroup E] [Fintype E] [Nontrivial E]
  (α : E →+ K) (hα : Function.Injective α)
  {p : ℕ} [Fact p.Prime] [CharP K p]

local notation "V" => fun d : ℕ => MonoidHom.comp (dualAction K d) α.toMultiplicative
local notation "W" => MonoidHom.comp (dualAction K (p - 1)) α.toMultiplicative
local notation "M" =>
  MonoidHom.comp (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p)
    (Fintype.card E / p)) α.toMultiplicative

/-- The low-factor decomposition is used once, at (0,a,p-1,1).
There is no high-digit carry hypothesis: choose(a,0)=1. -/
private theorem single_base (a : ℕ) (hp : 3 ≤ p)
    (ha : a + 1 ≤ Fintype.card E / p) :
    RelativeStableIso M (Representation.tprod W (V (p * a + 1))) (V (p * a + p - 1)) := by
  obtain ⟨eK⟩ := residue_decomposition (K := K) (p := p) 0 a (p - 1) 1
    (by omega) (by decide) (by omega) (by simp)
  have e := EmbeddedOriginalClassification.restrictEquiv α.toMultiplicative eK
  have ht : min (p - 1) 1 = 1 := by omega
  have htop : (p - 1) + (p * a + 1) - 1 = p * a + p - 1 := by omega
  have e' : (Representation.tprod W (V (p * a + 1))).Equiv
      (Representation.prod (V (p * a + p - 1))
        (Representation.tprod (V (p - 2)) (V (p * a)))) := by
    have hlow : p - 1 - 1 = p - 2 := by omega
    have e₀ : (Representation.tprod W (V (p * a + 1))).Equiv
        (Representation.prod
          ((expectedAction (K := K) (p - 1) (p * a + 1) 1).comp α.toMultiplicative)
          (Representation.tprod (V (p - 2)) (V (p * a)))) := by
      rw [show p * 0 + (p - 1) = p - 1 by omega, ht, hlow,
        show p * a + 1 - 1 = p * a by omega] at e
      exact e
    have e₁ := e₀.trans (prodCongr
      (EmbeddedOriginalClassification.restrictEquiv α.toMultiplicative
        (expectedOne (K := K) (p - 1) (p * a + 1)))
      (Representation.Equiv.refl _))
    rw [htop] at e₁
    exact e₁
  have hP := relativeProjective_transport M
    (Representation.TensorProduct.comm (V (p * a)) (V (p - 2)))
    (multiple_tensor_projective α (K := K) (p := p)
      (Fintype.card E / p) a (p - 2) (by omega))
  exact stable_symm M (relativeStableIso_of_decomposition M _ _ _ e' hP)

omit [Fact p.Prime] [CharP K p] in
/-- One tensor step, before deleting boundary terms or cancelling a positive
polynomial factor. No split is applied at residue zero. -/
private theorem recurrence_pair (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmc : (m : K) ≠ 0) (hnc : (n : K) ≠ 0)
    (h : RelativeStableIso M (Representation.tprod W (V m)) (V n)) :
    RelativeStableIso M
      (Representation.prod (Representation.tprod W (V (m + 1)))
        (Representation.tprod W (V (m - 1))))
      (Representation.prod (V (n - 1)) (V (n + 1))) := by
  let l := (tensorCongr (Representation.Equiv.refl W) (two_split α (K := K) m hm hmc)).trans
    (tensorProdRight W (V (m + 1)) (V (m - 1)))
  let r := (two_split α (K := K) n hn hnc).trans
    (prodComm (V (n + 1)) (V (n - 1)))
  let e := (Representation.TensorProduct.assoc W (V m) (V 2)).trans
    (tensorCongr (Representation.Equiv.refl W)
      (Representation.TensorProduct.comm (V m) (V 2)))
  exact stable_trans M (relativeStableIso_of_equiv M l.symm)
    (stable_trans M (relativeStableIso_of_equiv M e.symm)
      (stable_trans M (stable_rTensor M h (V 2))
        (stable_trans M (relativeStableIso_of_equiv M
          (Representation.TensorProduct.comm (V n) (V 2)))
          (relativeStableIso_of_equiv M r))))

/-- At u=2, BOTH deleted terms are actual original-relative-projectives:
V_pa (including zero) and V_p(a+1) (including V_q). -/
private theorem single_two (a : ℕ) (hp : 3 ≤ p)
    (ha : a + 1 ≤ Fintype.card E / p) :
    RelativeStableIso M (Representation.tprod W (V (p * a + 2))) (V (p * a + p - 2)) := by
  have h1c : ((p * a + 1 : ℕ) : K) ≠ 0 :=
    residue_cast_ne_zero (K := K) (p := p) a 1 (by decide) (by omega)
  have hrc : ((p * a + p - 1 : ℕ) : K) ≠ 0 := by
    have he : p * a + p - 1 = p * a + (p - 1) := by omega
    rw [he]
    exact residue_cast_ne_zero (K := K) (p := p) a (p - 1) (by omega) (by omega)
  have hs := recurrence_pair α (K := K) (p := p) (p * a + 1) (p * a + p - 1)
    (by omega) (by omega) h1c hrc (single_base α a hp ha)
  have hs' : RelativeStableIso M
      (Representation.prod (Representation.tprod W (V (p * a + 2)))
        (Representation.tprod W (V (p * a))))
      (Representation.prod (V (p * a + p - 2)) (V (p * (a + 1)))) := by
    have he : p * (a + 1) = p * a + p := by ring
    rw [show p * a + 1 + 1 = p * a + 2 by omega,
      show p * a + 1 - 1 = p * a by omega,
      show p * a + p - 1 - 1 = p * a + p - 2 by omega,
      show p * a + p - 1 + 1 = p * a + p by omega, ← he] at hs
    exact hs
  have hL := relativeProjective_transport M
    (Representation.TensorProduct.comm (V (p * a)) W)
    (multiple_tensor_projective α (K := K) (p := p)
      (Fintype.card E / p) a (p - 1) (by omega))
  have hR := relativeProjective_transport M
    (embeddedUnitRight α (V (p * (a + 1))))
    (multiple_tensor_projective α (K := K) (p := p)
      (Fintype.card E / p) (a + 1) 1 ha)
  have hleft := relativeStableIso_of_decomposition M
    (Representation.tprod W (V (p * a + 2)))
    (Representation.prod (Representation.tprod W (V (p * a + 2)))
      (Representation.tprod W (V (p * a))))
    (Representation.tprod W (V (p * a))) (Representation.Equiv.refl _) hL
  have hright := relativeStableIso_of_decomposition M
    (V (p * a + p - 2)) (Representation.prod (V (p * a + p - 2)) (V (p * (a + 1))))
    (V (p * (a + 1))) (Representation.Equiv.refl _) hR
  exact stable_trans M hleft (stable_trans M hs' (stable_symm M hright))

include hα in
/-- Strong induction on the low digit. The only cancellation is of the
specific positive polynomial C=V_(pa+p-u+2), with all bounds supplied here. -/
private theorem single_of_block (a u : ℕ) (hp : 3 ≤ p)
    (ha : a + 1 ≤ Fintype.card E / p) (hu : 1 ≤ u) (hup : u < p) :
    RelativeStableIso M (Representation.tprod W (V (p * a + u))) (V (p * a + p - u)) := by
  revert hu hup
  induction u using Nat.strong_induction_on with
  | h u ih =>
    intro hu hup
    by_cases h1 : u = 1
    · subst u
      exact single_base α a hp ha
    by_cases h2 : u = 2
    · subst u
      exact single_two α a hp ha
    have hu3 : 3 ≤ u := by omega
    have hq : p * (Fintype.card E / p) = Fintype.card E :=
      Nat.mul_div_cancel' (EmbeddedOriginalClassification.prime_dvd_card_embedding (p := p) α hα)
    have hblock : p * a + p ≤ Fintype.card E := by
      have hh := Nat.mul_le_mul_left p ha
      rw [Nat.mul_add, Nat.mul_one, hq] at hh
      exact hh
    let m := p * a + u - 1
    let n := p * a + p - u + 1
    have hm : 0 < m := by dsimp [m]; omega
    have hn : 0 < n := by dsimp [n]; omega
    have hmc : (m : K) ≠ 0 := by
      have he : m = p * a + (u - 1) := by dsimp [m]; omega
      rw [he]
      exact residue_cast_ne_zero (K := K) (p := p) a (u - 1) (by omega) (by omega)
    have hnc : (n : K) ≠ 0 := by
      have he : n = p * a + (p - u + 1) := by dsimp [n]; omega
      rw [he]
      exact residue_cast_ne_zero (K := K) (p := p) a (p - u + 1)
        (by omega) (by omega)
    have hprev : RelativeStableIso M (Representation.tprod W (V m)) (V n) := by
      have he : p * a + (u - 1) = m := by dsimp [m]; omega
      have he' : p * a + p - (u - 1) = n := by dsimp [n]; omega
      have hs := ih (u - 1) (by omega) (by omega) (by omega)
      rw [he, he'] at hs
      exact hs
    have hpair := recurrence_pair α (K := K) (p := p) m n hm hn hmc hnc hprev
    let d := p * a + p - u + 2
    have hpair' : RelativeStableIso M
        (Representation.prod (Representation.tprod W (V (p * a + u)))
          (Representation.tprod W (V (p * a + (u - 2)))))
        (Representation.prod (V (p * a + p - u)) (V d)) := by
      have he1 : m + 1 = p * a + u := by dsimp [m]; omega
      have he2 : m - 1 = p * a + (u - 2) := by dsimp [m]; omega
      have he3 : n - 1 = p * a + p - u := by rfl
      have he4 : n + 1 = d := by rfl
      rw [he1, he2, he3, he4] at hpair
      exact hpair
    have hcommon : RelativeStableIso M (Representation.tprod W (V (p * a + (u - 2)))) (V d) := by
      have he : p * a + p - (u - 2) = d := by dsimp [d]; omega
      have hs := ih (u - 2) (by omega) (by omega) (by omega)
      rw [he] at hs
      exact hs
    have hreplace : RelativeStableIso M
        (Representation.prod (Representation.tprod W (V (p * a + u))) (V d))
        (Representation.prod (Representation.tprod W (V (p * a + u)))
          (Representation.tprod W (V (p * a + (u - 2))))) :=
      stable_prod M (stable_refl M _) (stable_symm M hcommon)
    have hcancel := stable_trans M hreplace hpair'
    have hd : 0 < d := by dsimp [d]; omega
    have hdsize : d + 1 ≤ Fintype.card E := by dsimp [d]; omega
    have hdchar : (d : K) ≠ 0 := by
      have he : d = p * a + (p - u + 2) := by dsimp [d]; omega
      rw [he]
      exact residue_cast_ne_zero (K := K) (p := p) a (p - u + 2)
        (by omega) (by omega)
    exact EmbeddedPolynomialCancellation.polynomial_summand_cancellation α hα
      (K := K) (p := p) (Fintype.card E / p) d hd hdsize hdchar
      (Representation.tprod W (V (p * a + u))) (V (p * a + p - u)) hcancel

include hα in
/-- Single-factor recurrence for every original index below q. The
characteristic-two branch is the actual tensor unit equivalence. -/
theorem single_factor_reflection (a u : ℕ) (hu : 1 ≤ u) (hup : u < p)
    (hi : p * a + u < Fintype.card E) :
    RelativeStableIso M (Representation.tprod W (V (p * a + u))) (V (p * a + p - u)) := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  by_cases hp2 : p = 2
  · have hu1 : u = 1 := by omega
    have hw : p - 1 = 1 := by omega
    have hr : p * a + p - u = p * a + u := by omega
    rw [hw, hr]
    exact relativeStableIso_of_equiv M (embeddedUnitLeft α (V (p * a + u)))
  exact single_of_block α hα a u (by omega) (full_block_bound α hα a u hi) hu hup

include hα in
/-- Derived only AFTER the complete single-factor induction. -/
theorem reflection_square : RelativeStableIso M (Representation.tprod W W) (V 1) := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpq : p ≤ Fintype.card E :=
    Nat.le_of_dvd Fintype.card_pos
      (EmbeddedOriginalClassification.prime_dvd_card_embedding (p := p) α hα)
  have hs := single_factor_reflection α hα (K := K) (p := p) 0 (p - 1)
    (by omega) (by omega) (by simp only [Nat.mul_zero, Nat.zero_add]; omega)
  have hidx : p * 0 + (p - 1) = p - 1 := by omega
  have href : p * 0 + p - (p - 1) = 1 := by omega
  rw [hidx, href] at hs
  exact hs

end SingleFactorRecurrence

section TwoFactorReflection

variable {K : Type uK} [Field K]
  {E : Type uE} [AddGroup E] [Fintype E] [Nontrivial E]
  (α : E →+ K) (hα : Function.Injective α)
  {p : ℕ} [Fact p.Prime] [CharP K p]

local notation "V" => fun d : ℕ => MonoidHom.comp (dualAction K d) α.toMultiplicative
local notation "W" => MonoidHom.comp (dualAction K (p - 1)) α.toMultiplicative
local notation "M" =>
  MonoidHom.comp (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p)
    (Fintype.card E / p)) α.toMultiplicative

include hα in
/-- Full two-factor reflection along the actual faithful embedding.
Zero original factors and reflected p-multiple factors use the original
relative-projective retracts; no bound on either total index is imposed. -/
theorem tensor_reflection (a b u v : ℕ) (hu : u < p) (hv : v < p)
    (hi : p * a + u < Fintype.card E) (hj : p * b + v < Fintype.card E) :
    RelativeStableIso
      ((PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p)
        (Fintype.card E / p)).comp α.toMultiplicative)
      (Representation.tprod ((dualAction K (p * a + p - u)).comp α.toMultiplicative)
        ((dualAction K (p * b + p - v)).comp α.toMultiplicative))
      (Representation.tprod ((dualAction K (p * a + u)).comp α.toMultiplicative)
        ((dualAction K (p * b + v)).comp α.toMultiplicative)) := by
  have ha := full_block_bound α hα (K := K) (p := p) a u hi
  have hb := full_block_bound α hα (K := K) (p := p) b v hj
  by_cases hu0 : u = 0
  · subst u
    have hR : RelativeProjective M
        (Rep.of (Representation.tprod (V (p * a + p)) (V (p * b + p - v)))) := by
      have hs := multiple_tensor_projective α (K := K) (p := p)
        (Fintype.card E / p) (a + 1) (p * b + p - v) ha
      rw [show p * (a + 1) = p * a + p by ring] at hs
      exact hs
    have hL := multiple_tensor_projective α (K := K) (p := p)
      (Fintype.card E / p) a (p * b + v) (by omega)
    simpa only [Nat.add_zero, Nat.sub_zero] using stable_of_projectives M hR hL
  by_cases hv0 : v = 0
  · subst v
    have hR : RelativeProjective M
        (Rep.of (Representation.tprod (V (p * a + p - u)) (V (p * b + p)))) := by
      have hP := multiple_tensor_projective α (K := K) (p := p)
        (Fintype.card E / p) (b + 1) (p * a + p - u) hb
      have hP' := relativeProjective_transport M
        (Representation.TensorProduct.comm (V (p * (b + 1))) (V (p * a + p - u))) hP
      rw [show p * (b + 1) = p * b + p by ring] at hP'
      exact hP'
    have hL := relativeProjective_transport M
      (Representation.TensorProduct.comm (V (p * b)) (V (p * a + u)))
      (multiple_tensor_projective α (K := K) (p := p)
        (Fintype.card E / p) b (p * a + u) (by omega))
    simpa only [Nat.add_zero, Nat.sub_zero] using stable_of_projectives M hR hL
  have hI := single_factor_reflection α hα (K := K) (p := p) a u (by omega) hu hi
  have hJ := single_factor_reflection α hα (K := K) (p := p) b v (by omega) hv hj
  let I := V (p * a + u)
  let J := V (p * b + v)
  -- The middle two factors are exchanged by actual equivariant equivalences.
  let inner := (Representation.TensorProduct.assoc I W J).symm.trans
    ((tensorCongr (Representation.TensorProduct.comm I W)
      (Representation.Equiv.refl J)).trans (Representation.TensorProduct.assoc W I J))
  let shuffle :
      (Representation.tprod (Representation.tprod W I) (Representation.tprod W J)).Equiv
        (Representation.tprod (Representation.tprod W W) (Representation.tprod I J)) :=
    ((Representation.TensorProduct.assoc W I (Representation.tprod W J)).trans
      (tensorCongr (Representation.Equiv.refl W) inner)).trans
        (Representation.TensorProduct.assoc W W (Representation.tprod I J)).symm
  have hT := stable_symm M (stable_tensor M hI hJ)
  exact stable_trans M hT
    (stable_trans M (relativeStableIso_of_equiv M shuffle)
      (stable_trans M
        (stable_rTensor M (reflection_square α hα (K := K) (p := p))
          (Representation.tprod I J))
        (relativeStableIso_of_equiv M (embeddedUnitLeft α (Representation.tprod I J)))))

end TwoFactorReflection

end D5.S3.FiniteGroups.GroupAlgebra.EmbeddedTensorReflection
