/- GID: D5/S3/Entropy/Hypergraphs/FiniteFiber
   generality: G
   mirror-B: D5/B/S3/Entropy/Hypergraphs/FiniteFiber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite uniform coordinate fibres and disjoint coordinate-block averages. -/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic


/-! These are consumed proof-organizing auxiliaries, not independent escape witnesses.
Their general finite identities and estimates have proof_shape: bind-only.
The circular-law theorem is their actual consumer; its concrete geometric and
joint-law construction supplies the delivery's admission_basis: escape-witness. -/

public section

namespace D5.S3.Entropy.Hypergraphs.FiniteFiber

open scoped BigOperators

section Fiber
variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]

omit [Fintype ι] [DecidableEq ι] [DecidableEq V] in
private lemma selected_injective (E : ι → Finset V)
    (hE : ∀ i j, i ≠ j → Disjoint (E i) (E j))
    (g : ι → V) (hg : ∀ i, g i ∈ E i) : Function.Injective g := by
  intro i j hij
  by_contra hne
  exact Finset.disjoint_left.mp (hE i j hne) (hg i) (hij.symm ▸ hg j)

omit [DecidableEq ι] in
private lemma exposed_card_identity (E : ι → Finset V)
    (hE : ∀ i j, i ≠ j → Disjoint (E i) (E j))
    (O : Finset V) (g : ι → V) (hg : ∀ i, g i ∈ E i) :
    (O ∪ Finset.univ.image g).card =
      O.card + ∑ i : ι, if g i ∈ O then 0 else 1 := by
  classical
  have hinj := selected_injective E hE g hg
  have hd : (Finset.univ.image g) \ O =
      (Finset.univ.filter (fun i => g i ∉ O)).image g := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_univ,
      true_and, Finset.mem_filter]
    constructor
    · rintro ⟨⟨i, rfl⟩, hi⟩
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, rfl⟩, hi⟩
  have hc := Finset.card_sdiff_add_card (Finset.univ.image g) O
  rw [hd, Finset.card_image_of_injective _ hinj] at hc
  rw [Finset.union_comm] at hc
  rw [← hc, Nat.add_comm]
  congr 1
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all

omit [DecidableEq ι] in
private lemma exposed_phase_identity (E : ι → Finset V)
    (hE : ∀ i j, i ≠ j → Disjoint (E i) (E j))
    (O : Finset V) (g : ι → V) (hg : ∀ i, g i ∈ E i) (z : ℂ) :
    Complex.exp (z * (O ∪ Finset.univ.image g).card) =
      Complex.exp (z * O.card) * ∏ i : ι,
        if g i ∈ O then 1 else Complex.exp z := by
  classical
  rw [exposed_card_identity E hE O g hg, Nat.cast_add, mul_add,
    Complex.exp_add, Nat.cast_sum, Finset.mul_sum, Complex.exp_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp_all

private lemma one_edge_phase_sum (S O : Finset V) (z : ℂ) :
    (∑ v ∈ S, if v ∈ O then (1 : ℂ) else Complex.exp z) =
      (S.card : ℂ) - ((S \ O).card : ℂ) +
        ((S \ O).card : ℂ) * Complex.exp z := by
  classical
  have hleft : S.filter (fun v => v ∈ O) = S ∩ O := by
    ext v; simp
  have hright : S.filter (fun v => v ∉ O) = S \ O := by
    ext v; simp
  rw [Finset.sum_ite, hleft, hright]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hc : ((S \ O).card : ℂ) + ((S ∩ O).card : ℂ) = S.card := by
    exact_mod_cast Finset.card_sdiff_add_card_inter S O
  linear_combination hc

private lemma exposed_fiber_sum (E : ι → Finset V)
    (hE : ∀ i j, i ≠ j → Disjoint (E i) (E j))
    (O : Finset V) (z : ℂ) :
    (∑ g ∈ Fintype.piFinset E,
      Complex.exp (z * (O ∪ Finset.univ.image g).card)) =
      Complex.exp (z * O.card) * ∏ i : ι,
        (((E i).card : ℂ) - (((E i) \ O).card : ℂ) +
          (((E i) \ O).card : ℂ) * Complex.exp z) := by
  classical
  calc
    _ = ∑ g ∈ Fintype.piFinset E,
        Complex.exp (z * O.card) * ∏ i : ι,
          if g i ∈ O then 1 else Complex.exp z := by
      apply Finset.sum_congr rfl
      intro g hg
      exact exposed_phase_identity E hE O g (Fintype.mem_piFinset.mp hg) z
    _ = Complex.exp (z * O.card) *
        ∑ g ∈ Fintype.piFinset E, ∏ i : ι,
          if g i ∈ O then 1 else Complex.exp z := by rw [Finset.mul_sum]
    _ = _ := by
      rw [← Finset.prod_univ_sum E (fun (_ : ι) v => if v ∈ O then (1 : ℂ) else Complex.exp z)]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      exact one_edge_phase_sum (E i) O z

private lemma exposed_fiber_average (E : ι → Finset V)
    (hE : ∀ i j, i ≠ j → Disjoint (E i) (E j))
    (r : ℕ) (hr : 0 < r) (hcard : ∀ i, (E i).card = r)
    (O : Finset V) (z : ℂ) :
    (∑ g ∈ Fintype.piFinset E,
      Complex.exp (z * (O ∪ Finset.univ.image g).card)) /
      (r : ℂ) ^ Fintype.card ι =
      Complex.exp (z * O.card) * ∏ i : ι,
        (1 - (((E i) \ O).card : ℂ) / r +
          (((E i) \ O).card : ℂ) / r * Complex.exp z) := by
  classical
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  rw [exposed_fiber_sum E hE O z]
  simp_rw [hcard]
  have hfactor (i : ι) :
      (1 - (((E i) \ O).card : ℂ) / r +
          (((E i) \ O).card : ℂ) / r * Complex.exp z) =
        ((r : ℂ) - (((E i) \ O).card : ℂ) +
          (((E i) \ O).card : ℂ) * Complex.exp z) / r := by
    field_simp [hr0]
  simp_rw [hfactor]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ]
  ring

end Fiber


section BlockMean
variable {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq ι]
variable (β : ι → Type*) [∀ i, Fintype (β i)]
variable (D : J → Finset ι)

private def blockRestriction (o : ∀ i, β i) :
    (∀ j, ∀ i : D j, β i.val) ×
      (∀ i : {i // ∀ j, i ∉ D j}, β i.val) :=
  (fun _ i => o i.val, fun i => o i.val)

omit [Fintype ι] [Fintype J] [DecidableEq ι] [∀ i, Fintype (β i)] in
private theorem blockRestriction_bijective
    (hD : ∀ j k, j ≠ k → Disjoint (D j) (D k)) :
    Function.Bijective (blockRestriction β D) := by
  classical
  constructor
  · intro o p hop
    funext i
    by_cases hi : ∃ j, i ∈ D j
    · obtain ⟨j, hj⟩ := hi
      exact congrArg (fun b => b.1 j ⟨i, hj⟩) hop
    · have hi' : ∀ j, i ∉ D j := by simpa only [not_exists] using hi
      exact congrArg (fun b => b.2 ⟨i, hi'⟩) hop
  · intro b
    let o : ∀ i, β i := fun i =>
      if h : ∃ j, i ∈ D j then
        b.1 (Classical.choose h) ⟨i, Classical.choose_spec h⟩
      else b.2 ⟨i, by simpa only [not_exists] using h⟩
    have hin (j : J) (i : ι) (hi : i ∈ D j) : o i = b.1 j ⟨i, hi⟩ := by
      dsimp only [o]
      rw [dite_eq_left (show ∃ k, i ∈ D k from ⟨j, hi⟩)]
      have heq : Classical.choose (show ∃ k, i ∈ D k from ⟨j, hi⟩) = j := by
        by_contra hne
        exact Finset.disjoint_left.mp (hD _ _ hne)
          (Classical.choose_spec (show ∃ k, i ∈ D k from ⟨j, hi⟩)) hi
      have hval (k : J) (hk : i ∈ D k) (hkj : k = j) :
          b.1 k ⟨i, hk⟩ = b.1 j ⟨i, hi⟩ := by
        subst k
        rfl
      exact hval _ _ heq
    have hout (i : ι) (hi : ∀ j, i ∉ D j) : o i = b.2 ⟨i, hi⟩ := by
      dsimp only [o]
      rw [dite_eq_right (show ¬∃ j, i ∈ D j by simpa only [not_exists] using hi)]
    refine ⟨o, ?_⟩
    apply Prod.ext
    · funext j i
      exact hin j i.val i.property
    · funext i
      exact hout i.val i.property

private noncomputable def blockEquiv
    (hD : ∀ j k, j ≠ k → Disjoint (D j) (D k)) :
    (∀ i, β i) ≃
      ((∀ j, ∀ i : D j, β i.val) ×
        (∀ i : {i // ∀ j, i ∉ D j}, β i.val)) :=
  Equiv.ofBijective (blockRestriction β D) (blockRestriction_bijective β D hD)

theorem block_average_product [∀ i, Nonempty (β i)]
    (hD : ∀ j k, j ≠ k → Disjoint (D j) (D k))
    (F : ∀ j, (∀ i : D j, β i.val) → ℝ) :
    (∑ o : ∀ i, β i, ∏ j, F j (fun i => o i.val)) /
        (Fintype.card (∀ i, β i) : ℝ) =
      ∏ j, ((∑ b : ∀ i : D j, β i.val, F j b) /
        (Fintype.card (∀ i : D j, β i.val) : ℝ)) := by
  classical
  let A := ∀ j, ∀ i : D j, β i.val
  let C := ∀ i : {i // ∀ j, i ∉ D j}, β i.val
  let e : (∀ i, β i) ≃ A × C := blockEquiv β D hD
  have heval (o : ∀ i, β i) : e o = blockRestriction β D o := rfl
  have hs :
      (∑ o : ∀ i, β i, ∏ j, F j (fun i => o i.val)) =
        (∏ j, ∑ b : ∀ i : D j, β i.val, F j b) * (Fintype.card C : ℝ) := by
    calc
      _ = ∑ b : A × C, ∏ j, F j (b.1 j) := by
        simpa only [heval, blockRestriction] using
          e.sum_comp (fun b : A × C => ∏ j, F j (b.1 j))
      _ = (∑ b : A, ∏ j, F j (b j)) * (Fintype.card C : ℝ) := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [← Finset.mul_sum]
        ring
      _ = _ := by rw [← Fintype.prod_sum]
  have hc : (Fintype.card (∀ i, β i) : ℝ) =
      (Fintype.card A : ℝ) * (Fintype.card C : ℝ) := by
    exact_mod_cast (Fintype.card_congr e).trans (Fintype.card_prod A C)
  have hC : (Fintype.card C : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := C)).ne'
  have hA : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := A)).ne'
  rw [hs, hc]
  calc
    _ = (∏ j, ∑ b : ∀ i : D j, β i.val, F j b) /
        (Fintype.card A : ℝ) := by field_simp [hA, hC]
    _ = _ := by
      rw [Finset.prod_div_distrib]
      congr 1
      simp only [A, Fintype.card_pi, Nat.cast_prod]

end BlockMean

private theorem pair_event_sum {A B : Type*} [Fintype A] [Fintype B]
    (P : A → Prop) (Q : B → Prop) [DecidablePred P] [DecidablePred Q] (z : ℝ) :
    (∑ x : A × B, if P x.1 ∧ ¬ Q x.2 then z else 1) =
      (Fintype.card A : ℝ) * Fintype.card B +
      (z - 1) * (∑ a : A, if P a then (1 : ℝ) else 0) *
        ((Fintype.card B : ℝ) - ∑ b : B, if Q b then (1 : ℝ) else 0) := by
  have hp (a : A) (b : B) : (if P a ∧ ¬ Q b then z else 1) =
      1 + (z - 1) * (if P a then (1 : ℝ) else 0) -
        (z - 1) * (if P a then (1 : ℝ) else 0) * (if Q b then (1 : ℝ) else 0) := by
    by_cases hP : P a <;> by_cases hQ : Q b <;> simp [hP, hQ]
  rw [Fintype.sum_prod_type]
  simp_rw [hp, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum,
    ← Finset.sum_mul]
  ring

private theorem pair_event_average {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B]
    (P : A → Prop) (Q : B → Prop) [DecidablePred P] [DecidablePred Q] (z : ℝ) :
    (∑ x : A × B, if P x.1 ∧ ¬ Q x.2 then z else 1) /
        (Fintype.card (A × B) : ℝ) =
      let q := ((∑ a : A, if P a then (1 : ℝ) else 0) / Fintype.card A) *
        (1 - (∑ b : B, if Q b then (1 : ℝ) else 0) / Fintype.card B);
      1 - q + q * z := by
  rw [pair_event_sum, Fintype.card_prod, Nat.cast_mul]
  dsimp only
  have hA : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hB : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  ring


theorem two_block_event_average {ι : Type*} [DecidableEq ι]
    (β : ι → Type*) [∀ i, Fintype (β i)] [∀ i, Nonempty (β i)]
    [∀ i, DecidableEq (β i)]
    (L R : Finset ι) (hLR : Disjoint L R)
    (u : ∀ i : L, β i.val) (v : ∀ i : R, β i.val)
    (A B z : ℝ)
    (ha : (∑ a : ∀ i : L, β i.val,
        if (∀ i : L, a i ≠ u i) then (1 : ℝ) else 0) /
        Fintype.card (∀ i : L, β i.val) = A)
    (hb : (∑ b : ∀ i : R, β i.val,
        if (∀ i : R, b i ≠ v i) then (1 : ℝ) else 0) /
        Fintype.card (∀ i : R, β i.val) = B) :
    (∑ o : ∀ i : (L ∪ R : Finset ι), β i.val,
      if ((∀ i : L,
            o ⟨i.val, Finset.mem_union_left R i.property⟩ ≠ u i) ∧
          ¬ (∀ i : R,
            o ⟨i.val, Finset.mem_union_right L i.property⟩ ≠ v i))
        then z else 1) /
      Fintype.card (∀ i : (L ∪ R : Finset ι), β i.val) =
        1 - A * (1 - B) + A * (1 - B) * z := by
  classical
  let P : (∀ i : L, β i.val) → Prop := fun a => ∀ i, a i ≠ u i
  let Q : (∀ i : R, β i.val) → Prop := fun b => ∀ i, b i ≠ v i
  let G : (∀ i : (L ∪ R : Finset ι), β i.val) → Prop := fun o =>
    (∀ i : L, o ⟨i.val, Finset.mem_union_left R i.property⟩ ≠ u i) ∧
    ¬ (∀ i : R, o ⟨i.val, Finset.mem_union_right L i.property⟩ ≠ v i)
  let e := Equiv.piFinsetUnion β hLR
  have hG (b : (∀ i : L, β i.val) × (∀ i : R, β i.val)) :
      G (e b) ↔ P b.1 ∧ ¬ Q b.2 := by
    have hl (i : L) :
        e b ⟨i.val, Finset.mem_union_left R i.property⟩ = b.1 i :=
      Equiv.piFinsetUnion_left β hLR i.property _
    have hr (i : R) :
        e b ⟨i.val, Finset.mem_union_right L i.property⟩ = b.2 i :=
      Equiv.piFinsetUnion_right β hLR i.property _
    simp only [G, P, Q, hl, hr]
  have hs :
      (∑ b : (∀ i : L, β i.val) × (∀ i : R, β i.val),
        if P b.1 ∧ ¬ Q b.2 then z else 1) =
      ∑ o : ∀ i : (L ∪ R : Finset ι), β i.val,
        if G o then z else 1 := by
    calc
      _ = ∑ b : (∀ i : L, β i.val) × (∀ i : R, β i.val),
          if G (e b) then z else 1 := by
        apply Finset.sum_congr rfl
        intro b _
        simp only [hG b]
      _ = _ := e.sum_comp (fun o => if G o then z else 1)
  have hc : Fintype.card ((∀ i : L, β i.val) × (∀ i : R, β i.val)) =
      Fintype.card (∀ i : (L ∪ R : Finset ι), β i.val) :=
    Fintype.card_congr e
  have h := pair_event_average P Q z
  dsimp only at h
  rw [hs, hc] at h
  change (∑ o : ∀ i : (L ∪ R : Finset ι), β i.val, if G o then z else 1) /
      Fintype.card (∀ i : (L ∪ R : Finset ι), β i.val) =
    1 - A * (1 - B) + A * (1 - B) * z
  change (∑ a : ∀ i : L, β i.val, if P a then (1 : ℝ) else 0) /
      Fintype.card (∀ i : L, β i.val) = A at ha
  change (∑ b : ∀ i : R, β i.val, if Q b then (1 : ℝ) else 0) /
      Fintype.card (∀ i : R, β i.val) = B at hb
  rw [ha, hb] at h
  exact h


-- No independence or constancy of W in its second coordinate is assumed.
lemma double_uniform_mean_norm_le
    {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (f : A → B → ℂ) (W : A → B → ℝ)
    (h : ∀ a b, ‖(∑ b' : B, f a b') / (Fintype.card B : ℂ)‖ ≤ W a b) :
    ‖(∑ x : A × B, f x.1 x.2) / (Fintype.card (A × B) : ℂ)‖ ≤
      (∑ x : A × B, W x.1 x.2) / (Fintype.card (A × B) : ℝ) := by
  classical
  let g : A → ℂ := fun a => (∑ b : B, f a b) / (Fintype.card B : ℂ)
  have hA : 0 < (Fintype.card A : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A)
  have hB : 0 < (Fintype.card B : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card B)
  have hg (a : A) : ‖g a‖ ≤ (∑ b : B, W a b) / (Fintype.card B : ℝ) := by
    apply (le_div_iff₀ hB).2
    have hs := Finset.sum_le_sum (s := (Finset.univ : Finset B))
      (fun b _ => h a b)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using hs
  have hcomplex :
      (∑ x : A × B, f x.1 x.2) / (Fintype.card (A × B) : ℂ) =
        (∑ a : A, g a) / (Fintype.card A : ℂ) := by
    dsimp only [g]
    simp only [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
      ← Finset.sum_div]
    ring
  have hreal :
      (∑ a : A, (∑ b : B, W a b) / (Fintype.card B : ℝ)) /
          (Fintype.card A : ℝ) =
        (∑ x : A × B, W x.1 x.2) / (Fintype.card (A × B) : ℝ) := by
    simp only [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
      ← Finset.sum_div]
    ring
  rw [hcomplex, norm_div, Complex.norm_natCast]
  calc
    ‖∑ a : A, g a‖ / (Fintype.card A : ℝ) ≤
        (∑ a : A, ‖g a‖) / (Fintype.card A : ℝ) :=
      div_le_div_of_nonneg_right (norm_sum_le _ _) hA.le
    _ ≤ (∑ a : A, (∑ b : B, W a b) / (Fintype.card B : ℝ)) /
        (Fintype.card A : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => hg a)) hA.le
    _ = _ := hreal

section SplitFiber
variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]

def selectedChoiceEquiv (E : ι → Finset V) :
    (∀ i, ↥(E i)) ≃ ↥(Fintype.piFinset E) where
  toFun b := ⟨fun i => (b i).val, Fintype.mem_piFinset.mpr (fun i => (b i).property)⟩
  invFun o i := ⟨o.val i, Fintype.mem_piFinset.mp o.property i⟩
  left_inv b := by funext i; apply Subtype.ext; rfl
  right_inv o := by apply Subtype.ext; rfl

def splitCompletion (E : ι → Finset V) (S : Finset ι)
    (a : ∀ i : {i // i ∉ S}, ↥(E i.val))
    (b : ∀ i : S, ↥(E i.val)) : ∀ i, ↥(E i) :=
  fun i => if h : i ∈ S then b ⟨i, h⟩ else a ⟨i, h⟩

def splitChoiceEquiv (E : ι → Finset V) (S : Finset ι) :
    (∀ i, ↥(E i)) ≃
      ((∀ i : {i // i ∉ S}, ↥(E i.val)) × (∀ i : S, ↥(E i.val))) :=
  (Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun i => ↥(E i))).trans
    (Equiv.prodComm _ _)

def splitRevealedImage (E : ι → Finset V) (S : Finset ι)
    (a : ∀ i : {i // i ∉ S}, ↥(E i.val)) : Finset V :=
  Finset.univ.image (fun i => (a i).val)

private lemma splitCompletion_image (E : ι → Finset V) (S : Finset ι)
    (a : ∀ i : {i // i ∉ S}, ↥(E i.val))
    (b : ∀ i : S, ↥(E i.val)) :
    Finset.univ.image (fun i => (splitCompletion E S a b i).val) =
      splitRevealedImage E S a ∪ Finset.univ.image (fun i : S => (b i).val) := by
  classical
  ext v
  simp only [splitRevealedImage, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    by_cases his : i ∈ S
    · right
      refine ⟨⟨i, his⟩, ?_⟩
      simpa only [splitCompletion, dite_eq_left his] using hi
    · left
      refine ⟨⟨i, his⟩, ?_⟩
      simpa only [splitCompletion, dite_eq_right his] using hi
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · refine ⟨i.val, ?_⟩
      simpa only [splitCompletion, dite_eq_right i.property] using hi
    · refine ⟨i.val, ?_⟩
      simpa only [splitCompletion, dite_eq_left i.property] using hi

lemma split_fiber_average (E : ι → Finset V) (S : Finset ι)
    (hS : ∀ i j : S, i ≠ j → Disjoint (E i.val) (E j.val))
    (r : ℕ) (hr : 0 < r) (hcard : ∀ i, (E i).card = r)
    (a : ∀ i : {i // i ∉ S}, ↥(E i.val)) (z : ℂ) :
    (∑ b : ∀ i : S, ↥(E i.val),
      Complex.exp (z * (Finset.univ.image
        (fun i => (splitCompletion E S a b i).val)).card)) /
      (Fintype.card (∀ i : S, ↥(E i.val)) : ℂ) =
    Complex.exp (z * (splitRevealedImage E S a).card) * ∏ i : S,
      (1 - (((E i.val) \ splitRevealedImage E S a).card : ℂ) / r +
        (((E i.val) \ splitRevealedImage E S a).card : ℂ) / r * Complex.exp z) := by
  classical
  let O := splitRevealedImage E S a
  let ES : S → Finset V := fun i => E i.val
  let e := selectedChoiceEquiv ES
  have hs :
      (∑ b : ∀ i : S, ↥(E i.val),
        Complex.exp (z * (Finset.univ.image
          (fun i => (splitCompletion E S a b i).val)).card)) =
      ∑ g ∈ Fintype.piFinset ES,
        Complex.exp (z * (O ∪ Finset.univ.image g).card) := by
    calc
      _ = ∑ b : ∀ i : S, ↥(E i.val),
          Complex.exp (z * (O ∪ Finset.univ.image (fun i => (b i).val)).card) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [splitCompletion_image]
      _ = ∑ g : ↥(Fintype.piFinset ES),
          Complex.exp (z * (O ∪ Finset.univ.image g.val).card) := by
        exact e.sum_comp (fun g => Complex.exp (z * (O ∪ Finset.univ.image g.val).card))
      _ = _ := Finset.sum_coe_sort (Fintype.piFinset ES)
        (fun g => Complex.exp (z * (O ∪ Finset.univ.image g).card))
  have hc : (Fintype.card (∀ i : S, ↥(E i.val)) : ℂ) =
      (r : ℂ) ^ Fintype.card S := by
    simp only [Fintype.card_pi, Fintype.card_coe, hcard,
      Finset.prod_const, Finset.card_univ, Nat.cast_pow]
  rw [hs, hc]
  exact exposed_fiber_average ES hS r hr (fun i => hcard i.val) O z

end SplitFiber


end D5.S3.Entropy.Hypergraphs.FiniteFiber
