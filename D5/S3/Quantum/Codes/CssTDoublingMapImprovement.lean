/- GID: D5/S3/Quantum/Codes/CssTDoublingMapImprovement
   generality: G
   mirror-B: D5/B/S3/Quantum/Codes/CssTDoublingMapImprovement
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: A cyclic binary doubling map gives a CSS extension of greater distance than identity. -/

module

public import Mathlib.InformationTheory.Hamming
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
public import Mathlib.Tactic

/-! A binary circulant improves the distance of an admissible CSS-T doubling construction. -/

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Module

namespace D5.S3.Quantum.Codes.CssTDoublingMapImprovement

/-- The infimum of the weights in the two nontrivial CSS quotient legs. -/
noncomputable def cssDistance {ι : Type*} [Fintype ι]
    (C₂ C₁ : Submodule (ZMod 2) (ι → ZMod 2)) : ℕ :=
  sInf ({d | ∃ x, x ∈ C₁ ∧ x ∉ C₂ ∧ hammingNorm x = d} ∪
    {d | ∃ z, z ∈ C₂.orthogonalBilin (dotProductBilin (ZMod 2) (ZMod 2)) ∧
      z ∉ C₁.orthogonalBilin (dotProductBilin (ZMod 2) (ZMod 2)) ∧ hammingNorm z = d})

/-- The extension code consists of pairs `(x, φ x)` with `x` in the subcode. -/
def extension {n : ℕ} {C C₁ : Submodule (ZMod 2) (Fin n → ZMod 2)}
    (h : C ≤ C₁) (φ : C₁ →ₗ[ZMod 2] (Fin n → ZMod 2)) :
    Submodule (ZMod 2) (Fin n ⊕ Fin n → ZMod 2) :=
  (φ ∘ₗ Submodule.inclusion h).graph.map
    ((LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin n) (ZMod 2) (ZMod 2)).symm.toLinearMap
      ∘ₗ C.subtype.prodMap (LinearMap.id : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)))

/-- The triple-product parity condition characterizing an admissible CSS-T extension. -/
def admissible {n : ℕ} (C₂ C₁ : Submodule (ZMod 2) (Fin n → ZMod 2))
    (h : C₂ ≤ C₁) (φ : C₁ →ₗ[ZMod 2] (Fin n → ZMod 2)) : Prop :=
  ∀ (x y : C₁) (z : C₂),
    (∑ i, x.val i * y.val i * z.val i) +
      (∑ i, φ x i * φ y i * φ ⟨z.val, h z.property⟩ i) = 0

/-- An admissible extension can strictly improve distance at equal length and dimension. -/
def claim : Prop :=
  ∃ (n : ℕ) (C₂ C₁ : Submodule (ZMod 2) (Fin n → ZMod 2)) (h : C₂ ≤ C₁),
    finrank (ZMod 2) C₂ < finrank (ZMod 2) C₁ ∧
      ∃ φ : C₁ →ₗ[ZMod 2] (Fin n → ZMod 2), admissible C₂ C₁ h φ ∧
        cssDistance (extension h φ) (extension (le_refl C₁) φ) >
          cssDistance (extension h C₁.subtype) (extension (le_refl C₁) C₁.subtype)

noncomputable section

private lemma rank_strict : finrank (ZMod 2) (LinearMap.range ((LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)).comp (LinearMap.ker
        (LinearMap.lsum (ZMod 2) (fun _ : Fin 13 => ZMod 2) (ZMod 2) (fun _ =>
        LinearMap.id))).subtype)) < finrank (ZMod 2) (LinearMap.range (LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))) := by
  have hn : (LinearMap.lsum (ZMod 2) (fun _ : Fin 13 => ZMod 2) (ZMod 2) (fun _ => LinearMap.id))
      ≠ 0 := by
    intro h
    have : (LinearMap.lsum (ZMod 2) (fun _ : Fin 13 => ZMod 2) (ZMod 2) (fun _ => LinearMap.id))
        (Pi.single 0 1) = 0 := congrArg (fun f => f (Pi.single 0 1)) h
    rw [LinearMap.lsum_piSingle] at this
    exact one_ne_zero this
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hn
  have hi : Function.Injective ((LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)).comp (LinearMap.ker
        (LinearMap.lsum (ZMod 2) (fun _ : Fin 13 => ZMod 2) (ZMod 2) (fun _ =>
        LinearMap.id))).subtype) := by
    intro x y h
    exact Subtype.ext ((LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
      (Prod.snd_surjective.comp (finProdFinEquiv (m := 2) (n := 13)).symm.surjective)) h)
  have h₁ := LinearMap.finrank_range_of_inj (LinearMap.funLeft_injective_of_surjective (ZMod 2)
      (ZMod 2) _
      (Prod.snd_surjective.comp (finProdFinEquiv (m := 2) (n := 13)).symm.surjective))
  have h₂ := LinearMap.finrank_range_of_inj hi
  change finrank (ZMod 2) (LinearMap.ker (LinearMap.lsum (ZMod 2) (fun _ : Fin 13 => ZMod 2) (ZMod
      2) (fun _ => LinearMap.id))) + 1 = finrank (ZMod 2) (Fin 13 → ZMod 2) at hk
  change finrank (ZMod 2) (LinearMap.range (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))) = finrank (ZMod 2) (Fin 13 → ZMod
        2) at h₁
  change finrank (ZMod 2) (LinearMap.range ((LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)).comp (LinearMap.ker
        (LinearMap.lsum (ZMod 2) (fun _ : Fin 13 => ZMod 2) (ZMod 2) (fun _ =>
        LinearMap.id))).subtype)) = finrank (ZMod 2) (LinearMap.ker (LinearMap.lsum (ZMod 2) (fun
        _ : Fin 13 => ZMod 2) (ZMod 2) (fun _ => LinearMap.id))) at h₂
  omega

private lemma admissible_witness : admissible (LinearMap.range ((LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)).comp (LinearMap.ker
        (LinearMap.lsum (ZMod 2) (fun _ : Fin 13 => ZMod 2) (ZMod 2) (fun _ =>
        LinearMap.id))).subtype)) (LinearMap.range (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))) (LinearMap.range_comp_le_range
        (LinearMap.ker (LinearMap.lsum (ZMod 2) (fun _ : Fin 13 => ZMod 2) (ZMod 2) (fun _ =>
        LinearMap.id))).subtype (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))) (((LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)).comp (LinearMap.id +
        LinearMap.funLeft (ZMod 2)
          (ZMod 2) (fun i : Fin 13 => i + 1) +
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 2) :
      (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2))).comp
    (LinearEquiv.ofInjective (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))
        (LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
      (Prod.snd_surjective.comp (finProdFinEquiv (m := 2) (n :=
          13)).symm.surjective))).symm.toLinearMap) := by
  rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩ ⟨_, ⟨z, hz⟩, rfl⟩
  change (∑ i, (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) x i * (LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) y i * (LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) z i) +
    (∑ i, (((LinearMap.funLeft (ZMod
        2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)).comp (LinearMap.id +
        LinearMap.funLeft (ZMod 2)
          (ZMod 2) (fun i : Fin 13 => i + 1) +
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 2) :
      (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2))).comp
    (LinearEquiv.ofInjective (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))
        (LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
      (Prod.snd_surjective.comp (finProdFinEquiv (m := 2) (n :=
          13)).symm.surjective))).symm.toLinearMap) ⟨(LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) x, _⟩ i *
      (((LinearMap.funLeft (ZMod 2)
          (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)).comp (LinearMap.id +
        LinearMap.funLeft (ZMod 2)
          (ZMod 2) (fun i : Fin 13 => i + 1) +
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 2) :
      (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2))).comp
    (LinearEquiv.ofInjective (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))
        (LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
      (Prod.snd_surjective.comp (finProdFinEquiv (m := 2) (n :=
          13)).symm.surjective))).symm.toLinearMap) ⟨(LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) y, _⟩ i *
      (((LinearMap.funLeft (ZMod 2)
          (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)).comp (LinearMap.id +
        LinearMap.funLeft (ZMod 2)
          (ZMod 2) (fun i : Fin 13 => i + 1) +
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 2) :
      (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2))).comp
    (LinearEquiv.ofInjective (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))
        (LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
      (Prod.snd_surjective.comp (finProdFinEquiv (m := 2) (n :=
          13)).symm.surjective))).symm.toLinearMap) ⟨(LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) z, _⟩ i) = 0
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [
    ← (finProdFinEquiv (m := 2) (n := 13)).sum_comp _,
    Fintype.sum_prod_type, Fin.sum_univ_two,
    ← (finProdFinEquiv (m := 2) (n := 13)).sum_comp _,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [LinearMap.funLeft_apply, Equiv.symm_apply_apply,
    CharTwo.add_self_eq_zero]

private lemma cyclic_kernel (x : Fin 13 → ZMod 2) (h : (LinearMap.id + LinearMap.funLeft (ZMod 2)
    (ZMod 2) (fun i : Fin 13 => i + 1) +
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 2) :
      (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2)) x = 0) : x = 0 := by
  have hz (i : Fin 13) : x i + x (i + 1) + x (i + 2) = 0 := congrFun h i
  have hp (i : Fin 13) : x (i + 3) = x i := by
    have hh := hz (i + 1)
    rw [show i + 1 + 1 = i + 2 by rw [add_assoc]; rfl,
      show i + 1 + 2 = i + 3 by rw [add_assoc]; rfl] at hh
    have he : x i = x (i + 1) + x (i + 2) :=
      CharTwo.add_eq_zero.mp ((add_assoc _ _ _).symm.trans (hz i))
    have hf : x (i + 1) + x (i + 2) = x (i + 3) := CharTwo.add_eq_zero.mp hh
    exact (he.trans hf).symm
  have horbit (k : ℕ) : x (k • (3 : Fin 13)) = x 0 := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simpa only [succ_nsmul] using (hp (k • (3 : Fin 13))).trans ih
  have hc (i : Fin 13) : x i = x 0 := by
    have hi : (9 * i.val) • (3 : Fin 13) = i := by fin_cases i <;> decide
    rw [← hi]
    exact horbit _
  have hzero : x 0 = 0 := by
    have hh := hz 0
    rw [hc (0 + 1), hc (0 + 2), CharTwo.add_self_eq_zero, zero_add] at hh
    exact hh
  funext i
  exact (hc i).trans hzero

private lemma x_weight_bound (x : Fin 13 → ZMod 2) (hx : (LinearMap.lsum (ZMod 2) (fun _ : Fin 13
    => ZMod 2) (ZMod 2) (fun _ => LinearMap.id)) x ≠ 0) :
    8 ≤ hammingNorm (Sum.elim ((LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) x) ((LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) ((LinearMap.id +
        LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 1) +
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 2) :
      (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2)) x))) := by
  have hn : x ≠ 0 := by intro h; exact hx (h ▸ (LinearMap.lsum (ZMod 2) (fun _ : Fin 13 => ZMod 2)
      (ZMod 2) (fun _ => LinearMap.id)).map_zero)
  have ha : (LinearMap.id + LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 1) +
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 2) :
      (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2)) x ≠ 0 := fun h => hn
        (cyclic_kernel x h)
  have hp : 0 < hammingNorm x := hammingNorm_pos_iff.mpr hn
  have hq := hammingNorm_pos_iff.mpr ha
  have ht : hammingNorm x ≠ 2 := by
    intro h
    apply hx
    change (∑ i, x i) = 0
    have hp : (∑ i, x i) = (hammingNorm x : ZMod 2) := by
      rw [hammingNorm, Finset.card_filter, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : x i = 0
      · rw [hi]; norm_num
      · rw [show x i = 1 from Fin.eq_one_of_ne_zero (x i) hi]; norm_num
    rw [hp, h]
    decide
  have hw : hammingNorm (Sum.elim ((LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) x) ((LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) ((LinearMap.id +
        LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 1) +
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 2) :
      (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2)) x))) =
      2 * (hammingNorm x + hammingNorm ((LinearMap.id + LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i
          : Fin 13 => i + 1) +
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 2) :
      (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2)) x)) := by
    rw [hammingNorm, Finset.card_filter, Fintype.sum_sum_type,
      ← (finProdFinEquiv (m := 2) (n := 13)).sum_comp _,
      Fintype.sum_prod_type, Fin.sum_univ_two,
      ← (finProdFinEquiv (m := 2) (n := 13)).sum_comp _,
      Fintype.sum_prod_type, Fin.sum_univ_two]
    simp only [Sum.elim_inl, Sum.elim_inr,
      LinearMap.funLeft_apply, Equiv.symm_apply_apply]
    rw [← Finset.card_filter, ← Finset.card_filter]
    change hammingNorm x + hammingNorm x +
      (hammingNorm ((LinearMap.id + LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 1) +
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 2) :
      (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2)) x) + hammingNorm ((LinearMap.id
        + LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 1) +
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 2) :
      (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2)) x)) = _
    omega
  rw [hw]
  by_cases hs : hammingNorm x = 1
  · let f := Finsupp.equivFunOnFinite.symm x
    have hf : f.support.card = 1 := by
      have he : f.support = Finset.univ.filter (fun i => x i ≠ 0) := by
        ext i
        simp only [Finsupp.mem_support_iff, Finset.mem_filter, Finset.mem_univ, true_and]
        rfl
      exact he ▸ hs
    obtain ⟨i, hi, he⟩ := Finsupp.card_support_eq_one.mp hf
    rw [Fin.eq_one_of_ne_zero (f i) hi] at he
    have hx : x = Pi.single i 1 :=
      (congrArg (fun g : Fin 13 →₀ ZMod 2 => (g : Fin 13 → ZMod 2)) he).trans
        (Finsupp.single_eq_pi_single i 1)
    subst x
    have hw : hammingNorm ((LinearMap.id + LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 =>
        i + 1) +
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 2) :
      (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2)) (Pi.single i 1)) = 3 := by
      fin_cases i <;> decide
    omega
  · omega

private lemma transpose_dot (x w : (Fin 13 → ZMod 2)) :
    dotProduct ((LinearMap.id + LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 1) +
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 2) :
      (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2)) x) w = dotProduct x (fun i => w i + w
          (i - 1) + w (i - 2)) := by
  change (∑ i, (x i + x (i + 1) + x (i + 2)) * w i) =
    ∑ i, x i * (w i + w (i - 1) + w (i - 2))
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  have h₁ := (dotProduct_comp_equiv_symm x w (Equiv.addRight (1 : Fin 13))).symm
  have h₂ := (dotProduct_comp_equiv_symm x w (Equiv.addRight (2 : Fin 13))).symm
  simp only [dotProduct, Function.comp_apply, Equiv.coe_addRight, Equiv.addRight_symm] at h₁ h₂
  simp only [sub_eq_add_neg]
  rw [h₁, h₂]

private lemma transpose_weight (w : Fin 13 → ZMod 2) :
    hammingNorm (fun i => w i + w (i - 1) + w (i - 2)) ≤ 3 *
        hammingNorm w := by
  have h₁ : hammingNorm (w + fun i => w (i - 1)) ≤
      hammingNorm w + hammingNorm (fun i => w (i - 1)) := by
    have h := hammingDist_triangle (-w) 0 (fun i => w (i - 1))
    rw [hammingDist_zero_right, hammingDist_zero_left,
      hammingDist_eq_hammingNorm, neg_neg] at h
    have hn : -w = w := by ext i; exact CharTwo.neg_eq _
    rw [hn] at h
    exact h
  have h₂ : hammingNorm (fun i => w i + w (i - 1) + w (i - 2)) ≤
      hammingNorm (w + fun i => w (i - 1)) + hammingNorm (fun i => w (i - 2)) := by
    have h := hammingDist_triangle (-(w + fun i => w (i - 1))) 0 (fun i => w (i - 2))
    rw [hammingDist_zero_right, hammingDist_zero_left,
      hammingDist_eq_hammingNorm, neg_neg] at h
    have hn : -(w + fun i => w (i - 1)) = (w + fun i => w (i - 1)) := by
      ext i
      exact CharTwo.neg_eq _
    rw [hn] at h
    exact h
  have h₃ := (Equiv.subRight (1 : Fin 13)).sum_comp
    (fun i => if w i ≠ 0 then (1 : ℕ) else 0)
  have h₄ := (Equiv.subRight (2 : Fin 13)).sum_comp
    (fun i => if w i ≠ 0 then (1 : ℕ) else 0)
  rw [← Finset.card_filter, ← Finset.card_filter] at h₃ h₄
  change hammingNorm (fun i => w (i - 1)) = hammingNorm w at h₃
  change hammingNorm (fun i => w (i - 2)) = hammingNorm w at h₄
  omega

private lemma weight_block_sums (z : Fin 26 ⊕ Fin 26 → ZMod 2) :
    hammingNorm ((fun i => (z) (Sum.inl ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) +
        (fun i => (z) (Sum.inl ((finProdFinEquiv (m :=
        2) (n := 13)) (1, i))))) + hammingNorm ((fun i => (z) (Sum.inr ((finProdFinEquiv (m :=
        2) (n := 13)) (0, i)))) + (fun i =>
        (z) (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) ≤ hammingNorm z := by
  have h₁ : hammingNorm ((fun i => (z) (Sum.inl ((finProdFinEquiv (m := 2) (n := 13)) (0,
      i)))) +
      (fun i => (z) (Sum.inl ((finProdFinEquiv (m
      := 2) (n := 13)) (1, i))))) ≤
      hammingNorm (fun i => z (Sum.inl
          ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) + hammingNorm (fun i => z (Sum.inl
              ((finProdFinEquiv (m := 2) (n :=
          13)) (1, i)))) := by
    have h := hammingDist_triangle (-(fun i =>
        z (Sum.inl ((finProdFinEquiv (m := 2) (n := 13)) (0, i))))) 0 (fun i => z (Sum.inl
            ((finProdFinEquiv (m := 2) (n := 13)) (1,
        i))))
    rw [hammingDist_zero_right, hammingDist_zero_left,
      hammingDist_eq_hammingNorm, neg_neg] at h
    have hn : -(fun i => z (Sum.inl
        ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) = (fun i => z (Sum.inl
            ((finProdFinEquiv (m := 2) (n := 13)) (0, i))))
        := by ext i; exact CharTwo.neg_eq _
    rw [hn] at h
    exact h
  have h₂ : hammingNorm ((fun i => (z) (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (0,
      i)))) +
      (fun i => (z) (Sum.inr ((finProdFinEquiv (m
      := 2) (n := 13)) (1, i))))) ≤
      hammingNorm (fun i => z (Sum.inr
          ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) + hammingNorm (fun i => z (Sum.inr
              ((finProdFinEquiv (m := 2) (n :=
          13)) (1, i)))) := by
    have h := hammingDist_triangle (-(fun i =>
        z (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (0, i))))) 0 (fun i => z (Sum.inr
            ((finProdFinEquiv (m := 2) (n := 13)) (1,
        i))))
    rw [hammingDist_zero_right, hammingDist_zero_left,
      hammingDist_eq_hammingNorm, neg_neg] at h
    have hn : -(fun i => z (Sum.inr
        ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) = (fun i => z (Sum.inr
            ((finProdFinEquiv (m := 2) (n := 13)) (0, i))))
        := by ext i; exact CharTwo.neg_eq _
    rw [hn] at h
    exact h
  calc
    _ ≤ hammingNorm (fun i => z (Sum.inl
        ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) + hammingNorm (fun i => z (Sum.inl
            ((finProdFinEquiv (m := 2) (n := 13)) (1,
        i)))) +
        (hammingNorm (fun i => z (Sum.inr
            ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) + hammingNorm (fun i => z
                (Sum.inr ((finProdFinEquiv (m := 2) (n :=
            13)) (1, i))))) := Nat.add_le_add h₁ h₂
    _ = hammingNorm z := by
      symm
      rw [hammingNorm, Finset.card_filter, Fintype.sum_sum_type,
        ← (finProdFinEquiv (m := 2) (n := 13)).sum_comp _,
        Fintype.sum_prod_type, Fin.sum_univ_two,
        ← (finProdFinEquiv (m := 2) (n := 13)).sum_comp _,
        Fintype.sum_prod_type, Fin.sum_univ_two]
      rw [hammingNorm, Finset.card_filter, hammingNorm, Finset.card_filter,
        hammingNorm, Finset.card_filter, hammingNorm, Finset.card_filter]

private lemma graph_dot (f : (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2))
    (x : Fin 13 → ZMod 2) (z : Fin 26 ⊕ Fin 26 → ZMod 2) :
    dotProduct (Sum.elim ((LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) x) ((LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) (f x))) z =
      dotProduct x ((fun i => (z) (Sum.inl ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) +
          (fun i => (z) (Sum.inl ((finProdFinEquiv
          (m := 2) (n := 13)) (1, i))))) + dotProduct (f x) ((fun i => (z) (Sum.inr
          ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) + (fun i => (z) (Sum.inr
              ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) := by
  have h := sumElim_dotProduct_sumElim ((LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) x) (z ∘ Sum.inl)
    ((LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) (f x)) (z ∘ Sum.inr)
  rw [Sum.elim_comp_inl_inr] at h
  rw [show dotProduct (Sum.elim ((LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) x) ((LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) (f x))) z = _ from h]
  change (∑ i, (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) x i * z (Sum.inl i)) +
    (∑ i, (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) (f x) i * z (Sum.inr i)) = _
  rw [← (finProdFinEquiv (m := 2) (n := 13)).sum_comp _,
    Fintype.sum_prod_type, Fin.sum_univ_two,
    ← (finProdFinEquiv (m := 2) (n := 13)).sum_comp _,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [LinearMap.funLeft_apply, Equiv.symm_apply_apply]
  change (∑ i, x i * (fun i => z (Sum.inl
      ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) i) + (∑ i, x i * (fun i => z (Sum.inl
          ((finProdFinEquiv (m := 2) (n := 13)) (1,
      i)))) i) +
    ((∑ i, f x i * (fun i => z (Sum.inr
        ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) i) + (∑ i, f x i * (fun i => z
            (Sum.inr ((finProdFinEquiv (m := 2) (n := 13))
        (1, i)))) i)) = _
  rw [dotProduct_add, dotProduct_add]
  rfl

private lemma syndrome_one (z : Fin 26 ⊕ Fin 26 → ZMod 2)
    (h₂ : z ∈ (extension (LinearMap.range_comp_le_range (LinearMap.ker (LinearMap.lsum (ZMod 2)
        (fun _ : Fin 13 => ZMod 2) (ZMod 2) (fun _ => LinearMap.id))).subtype (LinearMap.funLeft
        (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))) (((LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)).comp (LinearMap.id +
        LinearMap.funLeft (ZMod 2)
          (ZMod 2) (fun i : Fin 13 => i + 1) +
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 2) :
      (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2))).comp
    (LinearEquiv.ofInjective (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))
        (LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
      (Prod.snd_surjective.comp (finProdFinEquiv (m := 2) (n :=
          13)).symm.surjective))).symm.toLinearMap)).orthogonalBilin
      (dotProductBilin (ZMod 2) (ZMod 2)))
    (h₁ : z ∉ (extension (le_refl (LinearMap.range (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)))) (((LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)).comp (LinearMap.id +
        LinearMap.funLeft (ZMod 2)
          (ZMod 2) (fun i : Fin 13 => i + 1) +
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 2) :
      (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2))).comp
    (LinearEquiv.ofInjective (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))
        (LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
      (Prod.snd_surjective.comp (finProdFinEquiv (m := 2) (n :=
          13)).symm.surjective))).symm.toLinearMap)).orthogonalBilin
      (dotProductBilin (ZMod 2) (ZMod 2))) :
    (((fun i => (z) (Sum.inl ((finProdFinEquiv (m := 2) (n :=
        13)) (0, i)))) + (fun i => (z)
        (Sum.inl ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) + (fun i => ((fun i =>
            (z) (Sum.inr ((finProdFinEquiv (m :=
        2) (n := 13)) (0, i)))) + (fun i =>
        (z) (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) i + ((fun i =>
            (z) (Sum.inr ((finProdFinEquiv (m :=
        2) (n := 13)) (0, i)))) + (fun i =>
        (z) (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) (i - 1) + ((fun i
            => (z) (Sum.inr ((finProdFinEquiv (m :=
        2) (n := 13)) (0, i)))) + (fun i =>
        (z) (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) (i - 2))) = fun _ =>
            1 := by
  have horth (x : Fin 13 → ZMod 2) (hx : (LinearMap.lsum (ZMod 2) (fun _ : Fin 13 => ZMod 2) (ZMod
      2) (fun _ => LinearMap.id)) x = 0) : dotProduct x (((fun i => (z) (Sum.inl
          ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) + (fun i => (z) (Sum.inl
          ((finProdFinEquiv (m := 2) (n := 13))
      (1, i))))) + (fun i => ((fun i
      => (z) (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) + (fun i => (z)
          (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (1,
      i))))) i + ((fun i
      => (z) (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) + (fun i => (z)
          (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (1,
      i))))) (i - 1) + ((fun i
      => (z) (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) + (fun i => (z)
          (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (1,
      i))))) (i - 2))) = 0 := by
    rw [dotProduct_add, ← transpose_dot, ← graph_dot]
    apply h₂
    unfold extension
    rw [LinearMap.graph_eq_range_prod, ← LinearMap.range_comp]
    refine ⟨⟨(LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) x, ⟨⟨x, hx⟩, rfl⟩⟩, ?_⟩
    change (LinearEquiv.sumArrowLequivProdArrow _ _ (ZMod 2) (ZMod 2)).symm
      ((LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) x, (((LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)).comp (LinearMap.id +
        LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 1) + LinearMap.funLeft (ZMod 2)
        (ZMod 2) (fun i : Fin 13 => i + 2) : (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod
        2))).comp
    (LinearEquiv.ofInjective (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))
        (LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
      (Prod.snd_surjective.comp (finProdFinEquiv (m := 2) (n :=
          13)).symm.surjective))).symm.toLinearMap) ⟨(LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) x, _⟩) = (Sum.elim
        ((LinearMap.funLeft
        (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) x) ((LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) ((LinearMap.id +
        LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 1) + LinearMap.funLeft (ZMod 2)
        (ZMod 2) (fun i : Fin 13 => i + 2) : (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2))
        x)))
    funext i
    cases i with
    | inl j => rw [LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl]; rfl
    | inr j =>
      rw [LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr]
      exact congrFun (congrArg (fun y => (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) ((LinearMap.id + LinearMap.funLeft
        (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 1) + LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i :
        Fin 13 => i + 2) : (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2)) y))
        ((LinearEquiv.ofInjective (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))
        (LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
      (Prod.snd_surjective.comp (finProdFinEquiv (m := 2) (n :=
          13)).symm.surjective))).symm_apply_apply x)) j
  have hc (i : Fin 13) : (((fun i => (z) (Sum.inl
      ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) + (fun i => (z) (Sum.inl
          ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) +
      (fun i => ((fun i => (z) (Sum.inr
      ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) + (fun i => (z) (Sum.inr
          ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) i + ((fun i => (z) (Sum.inr
      ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) + (fun i => (z) (Sum.inr
          ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) (i - 1) + ((fun i => (z)
          (Sum.inr
      ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) + (fun i => (z) (Sum.inr
          ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) (i - 2))) i
      = (((fun i => (z) (Sum.inl ((finProdFinEquiv (m := 2) (n
      := 13)) (0, i)))) + (fun i => (z)
      (Sum.inl ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) + (fun i => ((fun i => (z)
          (Sum.inr ((finProdFinEquiv (m := 2) (n
      := 13)) (0, i)))) + (fun i => (z)
      (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) i + ((fun i => (z)
          (Sum.inr ((finProdFinEquiv (m := 2) (n
      := 13)) (0, i)))) + (fun i => (z)
      (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) (i - 1) + ((fun i => (z)
          (Sum.inr ((finProdFinEquiv (m := 2) (n
      := 13)) (0, i)))) + (fun i => (z)
      (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) (i - 2))) 0 := by
    have hp : (LinearMap.lsum (ZMod 2) (fun _ : Fin 13 => ZMod 2) (ZMod 2) (fun _ =>
        LinearMap.id)) (Pi.single i 1 + Pi.single 0 1) = 0 := by
      rw [map_add, LinearMap.lsum_piSingle, LinearMap.lsum_piSingle]
      decide
    have hh := horth _ hp
    rw [add_dotProduct, single_one_dotProduct, single_one_dotProduct] at hh
    exact CharTwo.add_eq_zero.mp hh
  have hn : (((fun i => (z) (Sum.inl ((finProdFinEquiv (m := 2) (n
      := 13)) (0, i)))) + (fun i => (z)
      (Sum.inl ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) + (fun i => ((fun i => (z)
          (Sum.inr ((finProdFinEquiv (m := 2) (n
      := 13)) (0, i)))) + (fun i => (z)
      (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) i + ((fun i => (z)
          (Sum.inr ((finProdFinEquiv (m := 2) (n
      := 13)) (0, i)))) + (fun i => (z)
      (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) (i - 1) + ((fun i => (z)
          (Sum.inr ((finProdFinEquiv (m := 2) (n
      := 13)) (0, i)))) + (fun i => (z)
      (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) (i - 2))) 0 ≠ 0 := by
    intro hz
    apply h₁
    intro v hv
    unfold extension at hv
    rw [LinearMap.graph_eq_range_prod, ← LinearMap.range_comp] at hv
    obtain ⟨⟨_, x, rfl⟩, rfl⟩ := hv
    simp only [LinearMap.comp_apply, LinearMap.prod_apply, LinearMap.prodMap_apply,
      Function.prod_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap,
      Submodule.subtype_apply, Submodule.inclusion_apply]
    erw [(LinearEquiv.ofInjective
      (LinearMap.funLeft (ZMod 2) (ZMod 2)
        (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))
      (LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
        (Prod.snd_surjective.comp
          (finProdFinEquiv (m := 2) (n := 13)).symm.surjective))).symm_apply_apply x]
    change dotProduct (Sum.elim ((LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) x) ((LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) ((LinearMap.id +
        LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 1) +
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 2) :
      (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2)) x))) z = 0
    rw [graph_dot, transpose_dot, ← dotProduct_add]
    have he : (((fun i => (z) (Sum.inl ((finProdFinEquiv (m :=
        2) (n := 13)) (0, i)))) + (fun i =>
        (z) (Sum.inl ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) + (fun i => ((fun i
            => (z) (Sum.inr ((finProdFinEquiv
        (m := 2) (n := 13)) (0, i)))) + (fun
        i => (z) (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) i + ((fun i
            => (z) (Sum.inr ((finProdFinEquiv
        (m := 2) (n := 13)) (0, i)))) + (fun
        i => (z) (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) (i - 1) +
            ((fun i => (z) (Sum.inr ((finProdFinEquiv
        (m := 2) (n := 13)) (0, i)))) + (fun
        i => (z) (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) (i - 2))) = 0
            := funext
        (fun i => (hc i).trans hz)
    rw [he, dotProduct_zero]
  have ho : (((fun i => (z) (Sum.inl ((finProdFinEquiv (m := 2) (n
      := 13)) (0, i)))) + (fun i => (z)
      (Sum.inl ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) + (fun i => ((fun i => (z)
          (Sum.inr ((finProdFinEquiv (m := 2) (n
      := 13)) (0, i)))) + (fun i => (z)
      (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) i + ((fun i => (z)
          (Sum.inr ((finProdFinEquiv (m := 2) (n
      := 13)) (0, i)))) + (fun i => (z)
      (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) (i - 1) + ((fun i => (z)
          (Sum.inr ((finProdFinEquiv (m := 2) (n
      := 13)) (0, i)))) + (fun i => (z)
      (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) (i - 2))) 0 = 1 :=
      Fin.eq_one_of_ne_zero _ hn
  exact funext (fun i => (hc i).trans ho)

private lemma z_weight_bound (z : Fin 26 ⊕ Fin 26 → ZMod 2)
    (h₂ : z ∈ (extension (LinearMap.range_comp_le_range (LinearMap.ker (LinearMap.lsum (ZMod 2)
        (fun _ : Fin 13 => ZMod 2) (ZMod 2) (fun _ => LinearMap.id))).subtype (LinearMap.funLeft
        (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))) (((LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)).comp (LinearMap.id +
        LinearMap.funLeft (ZMod 2)
          (ZMod 2) (fun i : Fin 13 => i + 1) +
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 2) :
      (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2))).comp
    (LinearEquiv.ofInjective (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))
        (LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
      (Prod.snd_surjective.comp (finProdFinEquiv (m := 2) (n :=
          13)).symm.surjective))).symm.toLinearMap)).orthogonalBilin
      (dotProductBilin (ZMod 2) (ZMod 2)))
    (h₁ : z ∉ (extension (le_refl (LinearMap.range (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)))) (((LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)).comp (LinearMap.id +
        LinearMap.funLeft (ZMod 2)
          (ZMod 2) (fun i : Fin 13 => i + 1) +
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 2) :
      (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2))).comp
    (LinearEquiv.ofInjective (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))
        (LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
      (Prod.snd_surjective.comp (finProdFinEquiv (m := 2) (n :=
          13)).symm.surjective))).symm.toLinearMap)).orthogonalBilin
      (dotProductBilin (ZMod 2) (ZMod 2))) :
    5 ≤ hammingNorm z := by
  have hs := syndrome_one z h₂ h₁
  have he : ((fun i => (z) (Sum.inl ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) + (fun i
      => (z) (Sum.inl ((finProdFinEquiv (m := 2) (n :=
      13)) (1, i))))) = fun i => 1 + (fun i => ((fun i => (z) (Sum.inr ((finProdFinEquiv (m
          := 2) (n := 13)) (0, i)))) + (fun i => (z) (Sum.inr ((finProdFinEquiv (m := 2)
      (n := 13)) (1, i))))) i + ((fun i => (z) (Sum.inr ((finProdFinEquiv (m := 2) (n :=
          13)) (0, i)))) + (fun i => (z) (Sum.inr ((finProdFinEquiv (m := 2)
      (n := 13)) (1, i))))) (i - 1)
      + ((fun i => (z) (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) + (fun i =>
          (z) (Sum.inr ((finProdFinEquiv (m := 2)
      (n := 13)) (1, i))))) (i - 2)) i := by
    funext i
    have hi := congrFun hs i
    change ((fun i => (z) (Sum.inl ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) + (fun i =>
        (z) (Sum.inl ((finProdFinEquiv (m := 2) (n :=
        13)) (1, i))))) i + (fun i => ((fun i => (z) (Sum.inr ((finProdFinEquiv (m := 2) (n
            := 13)) (0, i)))) + (fun i => (z) (Sum.inr ((finProdFinEquiv (m := 2) (n
        := 13)) (1, i))))) i + ((fun i => (z) (Sum.inr ((finProdFinEquiv (m := 2) (n :=
            13)) (0, i)))) + (fun i => (z) (Sum.inr ((finProdFinEquiv (m := 2) (n
        := 13)) (1, i))))) (i - 1) + ((fun i => (z) (Sum.inr ((finProdFinEquiv (m := 2) (n
            := 13)) (0, i)))) + (fun i => (z) (Sum.inr ((finProdFinEquiv (m := 2) (n
        := 13)) (1, i))))) (i -
        2)) i = 1 at hi
    exact CharTwo.add_eq_iff_eq_add.mp hi
  have hb := weight_block_sums z
  have hc := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun i => (fun i => ((fun i => (z) (Sum.inr ((finProdFinEquiv (m := 2)
        (n := 13)) (0, i)))) + (fun i => (z) (Sum.inr ((finProdFinEquiv (m := 2) (n
        := 13)) (1, i))))) i + ((fun i => (z) (Sum.inr ((finProdFinEquiv (m := 2) (n :=
            13)) (0, i)))) + (fun i => (z) (Sum.inr ((finProdFinEquiv (m := 2) (n
        := 13)) (1, i))))) (i - 1) + ((fun i => (z) (Sum.inr ((finProdFinEquiv (m := 2) (n
            := 13)) (0, i)))) + (fun i => (z) (Sum.inr ((finProdFinEquiv (m := 2) (n
        := 13)) (1, i))))) (i -
        2)) i = 0)
  have hflip (i : Fin 13) :
      1 + (fun i => ((fun i => (z)
          (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) + (fun i => (z) (Sum.inr
              ((finProdFinEquiv (m := 2) (n := 13)) (1,
          i))))) i + ((fun i => (z)
          (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) + (fun i => (z) (Sum.inr
              ((finProdFinEquiv (m := 2) (n := 13)) (1,
          i))))) (i - 1) + ((fun i => (z)
          (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) + (fun i => (z) (Sum.inr
              ((finProdFinEquiv (m := 2) (n := 13)) (1,
          i))))) (i - 2)) i ≠ 0 ↔ (fun i => ((fun i => (z) (Sum.inr ((finProdFinEquiv (m :=
              2) (n := 13)) (0, i)))) + (fun i => (z) (Sum.inr ((finProdFinEquiv (m :=
          2) (n := 13)) (1, i))))) i + ((fun i => (z) (Sum.inr ((finProdFinEquiv (m := 2)
              (n := 13)) (0, i)))) + (fun i => (z) (Sum.inr ((finProdFinEquiv (m :=
          2) (n := 13)) (1, i))))) (i - 1) + ((fun i => (z) (Sum.inr ((finProdFinEquiv (m
              := 2) (n := 13)) (0, i)))) + (fun i => (z) (Sum.inr ((finProdFinEquiv (m :=
          2) (n := 13)) (1, i))))) (i -
          2)) i = 0 := by
    by_cases h : (fun i => ((fun i => (z)
        (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) + (fun i => (z) (Sum.inr
            ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) i + ((fun i => (z)
        (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) + (fun i => (z) (Sum.inr
            ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) (i - 1) + ((fun i => (z)
        (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) + (fun i => (z) (Sum.inr
            ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) (i - 2)) i = 0
    · rw [h]; decide
    · rw [show (fun i => ((fun i => (z)
        (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) + (fun i => (z) (Sum.inr
            ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) i + ((fun i => (z)
        (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) + (fun i => (z) (Sum.inr
            ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) (i - 1) + ((fun i => (z)
        (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) + (fun i => (z) (Sum.inr
            ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) (i - 2)) i = 1 from
            Fin.eq_one_of_ne_zero _ h]
      decide
  rw [Finset.card_univ, Fintype.card_fin] at hc
  rw [he, hammingNorm] at hb
  have hf : Finset.univ.filter (fun i => 1 + (fun i => ((fun i => (z) (Sum.inr
      ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) +
      (fun i => (z) (Sum.inr ((finProdFinEquiv (m
      := 2) (n := 13)) (1, i))))) i + ((fun i => (z) (Sum.inr ((finProdFinEquiv (m := 2)
          (n := 13)) (0, i)))) +
      (fun i => (z) (Sum.inr ((finProdFinEquiv (m
      := 2) (n := 13)) (1, i))))) (i -
      1) + ((fun i => (z) (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) +
      (fun i => (z) (Sum.inr ((finProdFinEquiv (m
      := 2) (n := 13)) (1, i))))) (i - 2)) i ≠ 0) =
      Finset.univ.filter (fun i => (fun i => ((fun i => (z) (Sum.inr ((finProdFinEquiv (m :=
          2) (n := 13)) (0, i)))) + (fun i => (z) (Sum.inr ((finProdFinEquiv (m :=
          2) (n := 13)) (1, i))))) i + ((fun i => (z) (Sum.inr ((finProdFinEquiv (m := 2)
              (n := 13)) (0, i)))) + (fun i => (z) (Sum.inr ((finProdFinEquiv (m :=
          2) (n := 13)) (1, i))))) (i - 1) + ((fun i => (z) (Sum.inr ((finProdFinEquiv (m
              := 2) (n := 13)) (0, i)))) + (fun i => (z) (Sum.inr ((finProdFinEquiv (m :=
          2) (n := 13)) (1, i))))) (i -
          2)) i = 0) :=
    Finset.filter_congr (fun i _ => hflip i)
  rw [hf] at hb
  have ht := transpose_weight ((fun i => (z) (Sum.inr ((finProdFinEquiv (m := 2) (n := 13))
      (0, i)))) + (fun i => (z) (Sum.inr ((finProdFinEquiv
      (m := 2) (n := 13)) (1, i)))))
  change (Finset.univ.filter (fun i => (fun i => ((fun i => (z) (Sum.inr ((finProdFinEquiv (m
      := 2) (n := 13)) (0, i)))) + (fun i => (z) (Sum.inr ((finProdFinEquiv (m := 2) (n
      := 13)) (1, i))))) i + ((fun i => (z) (Sum.inr ((finProdFinEquiv (m := 2) (n := 13))
          (0, i)))) + (fun i => (z) (Sum.inr ((finProdFinEquiv (m := 2) (n
      := 13)) (1, i))))) (i - 1) + ((fun i => (z) (Sum.inr ((finProdFinEquiv (m := 2) (n
          := 13)) (0, i)))) + (fun i => (z) (Sum.inr ((finProdFinEquiv (m := 2) (n
      := 13)) (1, i)))))
      (i - 2)) i = 0)).card +
    hammingNorm (fun i => ((fun i => (z)
        (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) + (fun i => (z) (Sum.inr
            ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) i + ((fun i => (z)
        (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) + (fun i => (z) (Sum.inr
            ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) (i - 1) + ((fun i => (z)
        (Sum.inr ((finProdFinEquiv (m := 2) (n := 13)) (0, i)))) + (fun i => (z) (Sum.inr
            ((finProdFinEquiv (m := 2) (n := 13)) (1, i))))) (i - 2)) = 13 at hc
  omega

private lemma graph_nontrivial (f : (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2)) :
    (Sum.elim
        ((LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) (Pi.single 0 1))
        ((LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) (f (Pi.single 0 1)))) ∈
        extension (le_refl (LinearMap.range (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)))) (((LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)).comp f).comp
    (LinearEquiv.ofInjective (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))
        (LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
      (Prod.snd_surjective.comp (finProdFinEquiv (m := 2) (n :=
          13)).symm.surjective))).symm.toLinearMap) ∧
      (Sum.elim
          ((LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) (Pi.single 0 1))
        ((LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) (f (Pi.single 0 1)))) ∉
        extension (LinearMap.range_comp_le_range (LinearMap.ker (LinearMap.lsum (ZMod 2) (fun _ :
        Fin 13 => ZMod 2) (ZMod 2) (fun _ => LinearMap.id))).subtype (LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))) (((LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)).comp f).comp
    (LinearEquiv.ofInjective (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))
        (LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
      (Prod.snd_surjective.comp (finProdFinEquiv (m := 2) (n :=
          13)).symm.surjective))).symm.toLinearMap) := by
  constructor
  · unfold extension
    rw [LinearMap.graph_eq_range_prod, ← LinearMap.range_comp]
    refine ⟨⟨(LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) (Pi.single 0 1), ⟨(Pi.single 0 1),
        rfl⟩⟩, ?_⟩
    change (LinearEquiv.sumArrowLequivProdArrow _ _ (ZMod 2) (ZMod 2)).symm
      ((LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) (Pi.single 0 1),
        (((LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)).comp f).comp
    (LinearEquiv.ofInjective (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))
        (LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
      (Prod.snd_surjective.comp (finProdFinEquiv (m := 2) (n :=
          13)).symm.surjective))).symm.toLinearMap) ⟨(LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) (Pi.single 0 1), ⟨(Pi.single 0 1),
        rfl⟩⟩) = (Sum.elim
        ((LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) (Pi.single 0 1))
        ((LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) (f (Pi.single 0 1))))
    funext i
    cases i with
    | inl j => rw [LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl]; rfl
    | inr j =>
      rw [LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr]
      exact congrFun (congrArg (fun y => (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) (f y))
        ((LinearEquiv.ofInjective (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))
        (LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
      (Prod.snd_surjective.comp (finProdFinEquiv (m := 2) (n :=
          13)).symm.surjective))).symm_apply_apply (Pi.single 0 1))) j
  · intro h
    unfold extension at h
    rw [LinearMap.graph_eq_range_prod, ← LinearMap.range_comp] at h
    obtain ⟨⟨_, ⟨x, hx⟩, rfl⟩, he⟩ := h
    have hu := (LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
        (Prod.snd_surjective.comp (finProdFinEquiv (m := 2) (n := 13)).symm.surjective))
            (Sum.elim_eq_iff.mp he).1
    subst x
    rw [LinearMap.mem_ker, LinearMap.lsum_piSingle] at hx
    exact one_ne_zero hx
private lemma improved_distance :
    5 ≤ cssDistance (extension (LinearMap.range_comp_le_range (LinearMap.ker (LinearMap.lsum (ZMod
        2) (fun _ : Fin 13 => ZMod 2) (ZMod 2) (fun _ => LinearMap.id))).subtype
        (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))) (((LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)).comp (LinearMap.id +
        LinearMap.funLeft (ZMod 2)
          (ZMod 2) (fun i : Fin 13 => i + 1) +
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 2) :
      (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2))).comp
    (LinearEquiv.ofInjective (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))
        (LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
      (Prod.snd_surjective.comp (finProdFinEquiv (m := 2) (n :=
          13)).symm.surjective))).symm.toLinearMap))
      (extension (le_refl (LinearMap.range (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)))) (((LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)).comp (LinearMap.id +
        LinearMap.funLeft (ZMod 2)
          (ZMod 2) (fun i : Fin 13 => i + 1) +
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 2) :
      (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2))).comp
    (LinearEquiv.ofInjective (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))
        (LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
      (Prod.snd_surjective.comp (finProdFinEquiv (m := 2) (n :=
          13)).symm.surjective))).symm.toLinearMap)) := by
  have hn := graph_nontrivial (LinearMap.id + LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13
      => i + 1) +
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 2) :
      (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2))
  apply le_csInf
    (show ({d | ∃ x, x ∈ extension (le_refl (LinearMap.range (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)))) (((LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)).comp (LinearMap.id +
        LinearMap.funLeft (ZMod 2)
          (ZMod 2) (fun i : Fin 13 => i + 1) +
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 2) :
      (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2))).comp
    (LinearEquiv.ofInjective (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))
        (LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
      (Prod.snd_surjective.comp (finProdFinEquiv (m := 2) (n :=
          13)).symm.surjective))).symm.toLinearMap) ∧
      x ∉ extension (LinearMap.range_comp_le_range (LinearMap.ker (LinearMap.lsum (ZMod 2) (fun _
          : Fin 13 => ZMod 2) (ZMod 2) (fun _ => LinearMap.id))).subtype (LinearMap.funLeft (ZMod
          2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))) (((LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)).comp (LinearMap.id +
        LinearMap.funLeft (ZMod 2)
          (ZMod 2) (fun i : Fin 13 => i + 1) +
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 2) :
      (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2))).comp
    (LinearEquiv.ofInjective (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))
        (LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
      (Prod.snd_surjective.comp (finProdFinEquiv (m := 2) (n :=
          13)).symm.surjective))).symm.toLinearMap) ∧ hammingNorm x = d} ∪
      {d | ∃ z, z ∈ (extension (LinearMap.range_comp_le_range (LinearMap.ker (LinearMap.lsum (ZMod
          2) (fun _ : Fin 13 => ZMod 2) (ZMod 2) (fun _ => LinearMap.id))).subtype
          (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))) (((LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)).comp (LinearMap.id +
        LinearMap.funLeft (ZMod 2)
          (ZMod 2) (fun i : Fin 13 => i + 1) +
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 2) :
      (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2))).comp
    (LinearEquiv.ofInjective (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))
        (LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
      (Prod.snd_surjective.comp (finProdFinEquiv (m := 2) (n :=
          13)).symm.surjective))).symm.toLinearMap)).orthogonalBilin
        (dotProductBilin (ZMod 2) (ZMod 2)) ∧
        z ∉ (extension (le_refl (LinearMap.range (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)))) (((LinearMap.funLeft (ZMod 2)
        (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)).comp (LinearMap.id +
        LinearMap.funLeft (ZMod 2)
          (ZMod 2) (fun i : Fin 13 => i + 1) +
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 2) :
      (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2))).comp
    (LinearEquiv.ofInjective (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))
        (LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
      (Prod.snd_surjective.comp (finProdFinEquiv (m := 2) (n :=
          13)).symm.surjective))).symm.toLinearMap)).orthogonalBilin
          (dotProductBilin (ZMod 2) (ZMod 2)) ∧ hammingNorm z = d}).Nonempty
      from ⟨_, Or.inl ⟨_, hn.1, hn.2, rfl⟩⟩)
  rintro d (⟨v, hv, hn, rfl⟩ | ⟨z, hz, hn, rfl⟩)
  · unfold extension at hv
    rw [LinearMap.graph_eq_range_prod, ← LinearMap.range_comp] at hv
    obtain ⟨⟨_, x, rfl⟩, rfl⟩ := hv
    simp only [LinearMap.comp_apply, LinearMap.prod_apply, LinearMap.prodMap_apply,
      Function.prod_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap,
      Submodule.subtype_apply, Submodule.inclusion_apply]
    erw [(LinearEquiv.ofInjective
      (LinearMap.funLeft (ZMod 2) (ZMod 2)
        (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))
      (LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
        (Prod.snd_surjective.comp
          (finProdFinEquiv (m := 2) (n := 13)).symm.surjective))).symm_apply_apply x]
    have hp : (LinearMap.lsum (ZMod 2) (fun _ : Fin 13 => ZMod 2) (ZMod 2) (fun _ =>
        LinearMap.id)) x ≠ 0 := by
      intro hx
      apply hn
      unfold extension
      rw [LinearMap.graph_eq_range_prod, ← LinearMap.range_comp]
      refine ⟨⟨(LinearMap.funLeft (ZMod 2) (ZMod 2)
      (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) x, ⟨⟨x, hx⟩, rfl⟩⟩, ?_⟩
      rfl
    exact le_trans (by decide : 5 ≤ 8) (x_weight_bound x hp)
  · exact z_weight_bound z hz hn

/-- The cyclic length-thirteen map gives a strict improvement over identity doubling. -/
theorem result : claim := by
  refine ⟨26, (LinearMap.range ((LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)).comp (LinearMap.ker
        (LinearMap.lsum (ZMod 2) (fun _ : Fin 13 => ZMod 2) (ZMod 2) (fun _ =>
        LinearMap.id))).subtype)), (LinearMap.range (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))), (LinearMap.range_comp_le_range
        (LinearMap.ker (LinearMap.lsum (ZMod 2) (fun _ : Fin 13 => ZMod 2) (ZMod 2) (fun _ =>
        LinearMap.id))).subtype (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))), rank_strict,
        (((LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)).comp (LinearMap.id +
        LinearMap.funLeft (ZMod 2)
          (ZMod 2) (fun i : Fin 13 => i + 1) +
    LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin 13 => i + 2) :
      (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2))).comp
    (LinearEquiv.ofInjective (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))
        (LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
      (Prod.snd_surjective.comp (finProdFinEquiv (m := 2) (n :=
          13)).symm.surjective))).symm.toLinearMap), admissible_witness, ?_⟩
  have hφ := improved_distance
  have hI : cssDistance (extension (LinearMap.range_comp_le_range (LinearMap.ker (LinearMap.lsum
      (ZMod 2)
        (fun _ : Fin 13 => ZMod 2) (ZMod 2) (fun _ => LinearMap.id))).subtype (LinearMap.funLeft
        (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))) (LinearMap.range
        (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))).subtype) (extension (le_refl
        (LinearMap.range (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)))) (LinearMap.range
        (LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))).subtype) ≤ 4 := by
    rw [← (show (((LinearMap.funLeft
        (ZMod 2) (ZMod 2)
      (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)).comp (LinearMap.id : (Fin 13 →
          ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2))).comp
      (LinearEquiv.ofInjective (LinearMap.funLeft (ZMod 2) (ZMod 2)
      (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))
          (LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
        (Prod.snd_surjective.comp (finProdFinEquiv (m := 2) (n :=
            13)).symm.surjective))).symm.toLinearMap) = (LinearMap.range
            (LinearMap.funLeft (ZMod 2) (ZMod 2)
      (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2))).subtype from
      LinearMap.ext (LinearEquiv.ofInjective_symm_apply (LinearMap.funLeft (ZMod 2) (ZMod 2)
      (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) (h :=
          (LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
        (Prod.snd_surjective.comp (finProdFinEquiv (m := 2) (n := 13)).symm.surjective)))))]
    have hn := graph_nontrivial (LinearMap.id : (Fin 13 → ZMod 2) →ₗ[ZMod 2] (Fin 13 → ZMod 2))
    have hw : hammingNorm (Sum.elim ((LinearMap.funLeft (ZMod 2) (ZMod 2)
      (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) (Pi.single 0 1))
          ((LinearMap.funLeft (ZMod 2)
          (ZMod 2)
      (fun i => ((finProdFinEquiv (m := 2) (n := 13)).symm i).2)) ((LinearMap.id : (Fin 13 → ZMod
          2) →ₗ[ZMod 2] (Fin 13 → ZMod 2)) (Pi.single 0 1)))) = 4 := by
      decide
    exact Nat.sInf_le (Or.inl ⟨_, hn.1, hn.2, hw⟩)
  exact lt_of_le_of_lt hI (lt_of_lt_of_le (by decide : 4 < 5) hφ)

end
end D5.S3.Quantum.Codes.CssTDoublingMapImprovement
