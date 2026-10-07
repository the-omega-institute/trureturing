/- GID: D5/S3/FiniteGroups/GaschutzFixed
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GaschutzFixed
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaschutz generator lifting with a fixed set in every finite group. -/

import Mathlib.GroupTheory.Rank
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.SetLike.Fintype
import Mathlib.Tactic.Choose

set_option autoImplicit false

/-!
Gaschütz lifting with an arbitrary fixed set, as in Nikolov–Segal (2011),
"Powers in finite groups", p. 504, Lemma 1.
The proof counts corrections using Mathlib's finite inclusion-exclusion identity.
-/

namespace D5.S3.FiniteGroups.GaschutzFixed

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable {G : Type*} [Group G]

/-- A coset fiber inside a subgroup is a translate of the kernel intersection. -/
def correctionFiberEquiv (N H : Subgroup G) (y : G) (c : N)
    (hc : (c : G) * y ∈ H) :
    {a : N // (a : G) * y ∈ H} ≃ ↥(N ⊓ H) where
  toFun a := ⟨(a.1 : G) * (c : G)⁻¹,
    N.mul_mem a.1.property (N.inv_mem c.property), by
      have h := H.mul_mem a.property (H.inv_mem hc)
      simpa [mul_inv_rev, mul_assoc] using h⟩
  invFun b := ⟨⟨(b : G) * (c : G), N.mul_mem b.property.1 c.property⟩, by
    simpa [mul_assoc] using H.mul_mem b.property.2 hc⟩
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    simp [mul_assoc]
  right_inv b := by
    apply Subtype.ext
    simp [mul_assoc]

/-- Normality makes every quotient coset meet a supplement. -/
theorem correction_exists (N H : Subgroup G) [N.Normal]
    (h : N ⊔ H = ⊤) (y : G) : ∃ c : N, (c : G) * y ∈ H := by
  have hy : y ∈ N ⊔ H := by rw [h]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp hy
  refine ⟨⟨a⁻¹, N.inv_mem ha⟩, ?_⟩
  rw [← hab]
  simpa [mul_assoc] using hb

/-- If a corrected tuple lies in `H`, its quotient generation forces `NH = G`. -/
theorem constraint_sup_eq_top {n : ℕ} (N H : Subgroup G) (X : Set G)
    (y : Fin n → G)
    (hquot : N ⊔ Subgroup.closure (X ∪ Set.range y) = ⊤)
    (hX : X ⊆ H) (a : Fin n → N) (ha : ∀ i, (a i : G) * y i ∈ H) :
    N ⊔ H = ⊤ := by
  apply top_unique
  rw [← hquot]
  refine sup_le le_sup_left ((Subgroup.closure_le (N ⊔ H)).2 ?_)
  rintro g (hx | ⟨i, rfl⟩)
  · exact (show H ≤ N ⊔ H from le_sup_right) (hX hx)
  · have h1 : (a i : G)⁻¹ ∈ N ⊔ H :=
      (show N ≤ N ⊔ H from le_sup_left) (N.inv_mem (a i).property)
    have h2 : (a i : G) * y i ∈ N ⊔ H :=
      (show H ≤ N ⊔ H from le_sup_right) (ha i)
    simpa [mul_assoc] using (N ⊔ H).mul_mem h1 h2

variable [Fintype G]

/-- The number of tuples constrained to a supplement is the kernel-intersection size to `n`. -/
theorem constraint_card_of_sup_eq_top {n : ℕ} (N H : Subgroup G) [N.Normal]
    (y : Fin n → G) (hsup : N ⊔ H = ⊤) :
    Fintype.card {a : Fin n → N // ∀ i, (a i : G) * y i ∈ H} =
      Fintype.card ↥(N ⊓ H) ^ n := by
  classical
  choose c hc using fun i => correction_exists N H hsup (y i)
  let e : {a : Fin n → N // ∀ i, (a i : G) * y i ∈ H} ≃ (Fin n → ↥(N ⊓ H)) :=
    Equiv.subtypePiEquivPi.trans
      (Equiv.piCongrRight fun i => correctionFiberEquiv N H (y i) (c i) (hc i))
  rw [Fintype.card_congr e, Fintype.card_pi_const]

/-- For quotient-generating tuples the constrained count depends only on `N`, `H`, and `n`. -/
theorem constraint_card {n : ℕ} (N H : Subgroup G) [N.Normal] (X : Set G)
    (y : Fin n → G)
    (hquot : N ⊔ Subgroup.closure (X ∪ Set.range y) = ⊤) (hX : X ⊆ H) :
    Fintype.card {a : Fin n → N // ∀ i, (a i : G) * y i ∈ H} =
      if N ⊔ H = ⊤ then Fintype.card ↥(N ⊓ H) ^ n else 0 := by
  classical
  by_cases h : N ⊔ H = ⊤
  · simpa [h] using constraint_card_of_sup_eq_top N H y h
  · simp only [h, ↓reduceIte]
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun a => h (constraint_sup_eq_top N H X y hquot hX a.val a.property)⟩

/-- Proper overgroups of the fixed set are precisely the possible obstructions. -/
def properOvergroups (X : Set G) : Finset (Subgroup G) := by
  letI := Fintype.ofFinite (Subgroup G)
  exact Finset.univ.filter fun H => X ⊆ H ∧ H ≠ ⊤

@[simp] theorem mem_properOvergroups (X : Set G) (H : Subgroup G) :
    H ∈ properOvergroups X ↔ X ⊆ H ∧ H ≠ ⊤ := by
  simp [properOvergroups]

/-- Tuples all of whose corrected coordinates lie in a given subgroup. -/
def constrainedCorrections {n : ℕ} (N H : Subgroup G) (y : Fin n → G) :
    Finset (Fin n → N) :=
  Finset.univ.filter fun a => ∀ i, (a i : G) * y i ∈ H

@[simp] theorem mem_constrainedCorrections {n : ℕ} (N H : Subgroup G)
    (y : Fin n → G) (a : Fin n → N) :
    a ∈ constrainedCorrections N H y ↔ ∀ i, (a i : G) * y i ∈ H := by
  simp [constrainedCorrections]

omit [Fintype G] in
/-- Membership in a finite subgroup intersection, including the empty intersection. -/
theorem mem_subgroup_finset_inf (t : Finset (Subgroup G)) (g : G) :
    g ∈ t.inf id ↔ ∀ H ∈ t, g ∈ H := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert H t h ih => simp [Finset.inf_insert, ih]

private theorem mem_finset_inf {α ι : Type*} [Fintype α] [DecidableEq α]
    (t : Finset ι) (f : ι → Finset α) (a : α) :
    a ∈ t.inf f ↔ ∀ i ∈ t, a ∈ f i := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih => simp [Finset.inf_insert, ih]

/-- Intersecting bad tuple sets constrains the tuple to the subgroup intersection. -/
theorem inf_constrainedCorrections {n : ℕ} (N : Subgroup G)
    (y : Fin n → G) (t : Finset (Subgroup G)) :
    t.inf (fun H => constrainedCorrections N H y) =
      constrainedCorrections N (t.inf id) y := by
  ext a
  simp only [mem_finset_inf, mem_constrainedCorrections, mem_subgroup_finset_inf]
  exact ⟨fun h i H hH => h H hH i, fun h H hH i => h i H hH⟩

/-- Good corrections avoid every proper subgroup containing `X`. -/
theorem mem_goodCorrections {n : ℕ} (N : Subgroup G) (X : Set G)
    (y : Fin n → G) (a : Fin n → N) :
    a ∈ (properOvergroups X).inf (fun H => (constrainedCorrections N H y)ᶜ) ↔
      Subgroup.closure (X ∪ Set.range (fun i => (a i : G) * y i)) = ⊤ := by
  simp only [mem_finset_inf, Finset.mem_compl, mem_constrainedCorrections]
  constructor
  · intro ha
    by_contra h
    let H := Subgroup.closure (X ∪ Set.range (fun i => (a i : G) * y i))
    have hX : X ⊆ H := fun g hg => Subgroup.subset_closure (Or.inl hg)
    have hH : H ∈ properOvergroups X := mem_properOvergroups X H |>.mpr ⟨hX, h⟩
    exact ha H hH (fun i => Subgroup.subset_closure (Or.inr ⟨i, rfl⟩))
  · intro h H hH ha
    have hle : Subgroup.closure (X ∪ Set.range (fun i => (a i : G) * y i)) ≤ H :=
      (Subgroup.closure_le H).2 (by
        rintro g (hg | ⟨i, rfl⟩)
        · exact (mem_properOvergroups X H |>.mp hH).1 hg
        · exact ha i)
    exact (mem_properOvergroups X H |>.mp hH).2 (top_unique (h ▸ hle))

/-- The number of generating corrections is independent of the quotient-generating tuple. -/
theorem good_correction_card_eq {n : ℕ} (N : Subgroup G) [N.Normal] (X : Set G)
    (y z : Fin n → G)
    (hy : N ⊔ Subgroup.closure (X ∪ Set.range y) = ⊤)
    (hz : N ⊔ Subgroup.closure (X ∪ Set.range z) = ⊤) :
    ((properOvergroups X).inf (fun H => (constrainedCorrections N H y)ᶜ)).card =
      ((properOvergroups X).inf (fun H => (constrainedCorrections N H z)ᶜ)).card := by
  classical
  have hinter : ∀ t ∈ (properOvergroups X).powerset,
      (t.inf (fun H => constrainedCorrections N H y)).card =
        (t.inf (fun H => constrainedCorrections N H z)).card := by
    intro t ht
    rw [inf_constrainedCorrections, inf_constrainedCorrections]
    have hX : X ⊆ (t.inf id : Subgroup G) := by
      intro g hg
      apply (mem_subgroup_finset_inf t g).2
      intro H hH
      exact (mem_properOvergroups X H |>.mp ((Finset.mem_powerset.mp ht) hH)).1 hg
    have hcy := constraint_card N (t.inf id) X y hy hX
    have hcz := constraint_card N (t.inf id) X z hz hX
    simpa [Fintype.card_subtype, constrainedCorrections] using hcy.trans hcz.symm
  apply Int.ofNat_inj.mp
  rw [Finset.inclusion_exclusion_card_inf_compl, Finset.inclusion_exclusion_card_inf_compl]
  apply Finset.sum_congr rfl
  intro t ht
  rw [hinter t ht]

end

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
variable {G : Type*} [Group G] [Finite G]

/-- Gaschütz generator lifting with an arbitrary fixed set, for all finite groups and all `n`. -/
theorem gaschutz_fixed {n : ℕ} (N : Subgroup G) [N.Normal] (X : Set G)
    (y : Fin n → G)
    (hgen : ∃ z : Fin n → G, Subgroup.closure (Set.range z) = ⊤)
    (hquot : N ⊔ Subgroup.closure (X ∪ Set.range y) = ⊤) :
    ∃ a : Fin n → N,
      Subgroup.closure (X ∪ Set.range (fun i => (a i : G) * y i)) = ⊤ := by
  classical
  let := Fintype.ofFinite G
  obtain ⟨z, hz⟩ := hgen
  have hzX : Subgroup.closure (X ∪ Set.range z) = ⊤ := by
    apply top_unique
    rw [← hz]
    exact Subgroup.closure_mono Set.subset_union_right
  have hzquot : N ⊔ Subgroup.closure (X ∪ Set.range z) = ⊤ := by rw [hzX, sup_top_eq]
  have hzero : (fun _ : Fin n => (1 : N)) ∈
      (properOvergroups X).inf (fun H => (constrainedCorrections N H z)ᶜ) := by
    apply (mem_goodCorrections N X z _).2
    simpa using hzX
  have hpos : 0 < ((properOvergroups X).inf
      (fun H => (constrainedCorrections N H y)ᶜ)).card := by
    rw [good_correction_card_eq N X y z hquot hzquot]
    exact Finset.card_pos.mpr ⟨_, hzero⟩
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  exact ⟨a, (mem_goodCorrections N X y a).1 ha⟩

/-- An ordered `n`-tuple of generators is exactly the at-most-`n` rank condition. -/
theorem tuple_generation_iff_rank_le {n : ℕ} :
    (∃ z : Fin n → G, Subgroup.closure (Set.range z) = ⊤) ↔ Group.rank G ≤ n := by
  classical
  constructor
  · rintro ⟨z, hz⟩
    let S : Finset G := Finset.univ.image z
    have hS : Subgroup.closure (S : Set G) = ⊤ := by simpa [S] using hz
    apply (Group.rank_le hS).trans
    simpa [S] using (Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := z))
  · intro hr
    obtain ⟨S, hcard, hS⟩ := Group.rank_spec G
    have hSn : S.card ≤ n := hcard ▸ hr
    let e : S ≃ Fin S.card := S.equivFin
    let z : Fin n → G := fun i =>
      if hi : i.val < S.card then (e.symm ⟨i.val, hi⟩ : G) else 1
    have hsub : (S : Set G) ⊆ Set.range z := by
      intro g hg
      let j : Fin S.card := e ⟨g, hg⟩
      let i : Fin n := ⟨j.val, lt_of_lt_of_le j.isLt hSn⟩
      refine ⟨i, ?_⟩
      have hi : i.val < S.card := j.isLt
      dsimp [z]
      rw [dif_pos hi]
      change (e.symm (e ⟨g, hg⟩) : G) = g
      simp
    refine ⟨z, top_unique ?_⟩
    rw [← hS]
    exact Subgroup.closure_mono hsub

end
end D5.S3.FiniteGroups.GaschutzFixed
