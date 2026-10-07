/- GID: D5/S3/Combinatorics/GroupActions/FiniteColorVirtualNilpotence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/GroupActions/FiniteColorVirtualNilpotence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite displacement colors yield virtually nilpotent small-displacement groups. -/

import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace D5.S3.Combinatorics.GroupActions.FiniteColorVirtualNilpotence

noncomputable section
set_option autoImplicit false
open MulAction
universe u v

/-- The nilpotent subgroup need not be normal, and the small generators need not be finite. -/
theorem result {G : Type u} {X : Type v} [Group G] [PseudoMetricSpace X] [MulAction G X]
    (hisom : ∀ g : G, Isometry (fun x : X => g • x)) (p : X)
    (H : Subgroup G) (hH : Group.IsNilpotent H) (m : ℕ)
    (color : {g : G | dist p (g • p) ≤ 1} → Fin m)
    (hcolor : ∀ v w, color v = color w → (v : G)⁻¹ * w ∈ H) :
    Group.IsVirtuallyNilpotent (Subgroup.closure
      {g : G | dist p (g • p) < 1 / ((m : ℝ) + 1)}) := by
  classical
  have hfinite {G : Type u} {X : Type u} [Group G] [MulAction G X]
    [MulAction.IsPretransitive G X] (x0 : X) (S : Set G)
    (hsym : ∀ g ∈ S, g⁻¹ ∈ S) (hgen : Subgroup.closure S = ⊤)
    (m : ℕ)
    (hcollision : ∀ f : Fin (m + 1) → List G,
      (∀ i, (f i).length ≤ m) → (∀ i, ∀ g ∈ f i, g ∈ S) →
      ∃ i j, i ≠ j ∧ (f i).prod • x0 = (f j).prod • x0) : Finite X := by
    classical
    by_contra hnot
    let : Infinite X := not_finite_iff_infinite.mp hnot
    have hout (U : Finset X) : ∃ x, x ∉ U := by
      by_contra hh
      push Not at hh
      have hf : Finite X := Finite.of_injective (fun x : X => (⟨x, hh x⟩ : U))
        (fun _ _ he => congrArg Subtype.val he)
      exact hnot hf
    have hescape (U : Finset X) (hx0 : x0 ∈ U) :
        ∃ s ∈ S, ∃ y ∈ U, s • y ∉ U := by
      by_contra hh
      push Not at hh
      have hinvariant (g : G) (hg : g ∈ Subgroup.closure S) :
          ∀ y ∈ U, g • y ∈ U := by
        induction hg using Subgroup.closure_induction_left with
        | one => intro y hy; simpa using hy
        | mul_left s hs y hy ih =>
          intro z hz
          rw [mul_smul]
          exact hh s hs _ (ih z hz)
        | inv_mul_cancel s hs y hy ih =>
          intro z hz
          rw [mul_smul]
          exact hh s⁻¹ (hsym s hs) _ (ih z hz)
      obtain ⟨z, hz⟩ := hout U
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x0 z
      have hgmem : g ∈ Subgroup.closure S := by rw [hgen]; exact Subgroup.mem_top g
      exact hz (hg ▸ hinvariant g hgmem x0 hx0)
    have hsets : ∀ n : ℕ, ∃ U : Finset X,
        U.card = n + 1 ∧ x0 ∈ U ∧
          ∀ x ∈ U, ∃ l : List G, l.length ≤ n ∧ (∀ g ∈ l, g ∈ S) ∧ l.prod • x0 = x := by
      intro n
      induction n with
      | zero =>
        refine ⟨{x0}, by simp, by simp, ?_⟩
        intro x hx
        have he : x = x0 := Finset.mem_singleton.mp hx
        subst x
        exact ⟨[], by simp, by simp, by simp⟩
      | succ n ih =>
        obtain ⟨U, hcard, hx0, hwords⟩ := ih
        obtain ⟨s, hs, y, hy, hnew⟩ := hescape U hx0
        obtain ⟨l, hlen, hmem, hprod⟩ := hwords y hy
        refine ⟨insert (s • y) U, ?_, Finset.mem_insert_of_mem hx0, ?_⟩
        · rw [Finset.card_insert_of_notMem hnew, hcard]
        · intro z hz
          rcases Finset.mem_insert.mp hz with hz | hz
          · subst z
            refine ⟨s :: l, by simpa using Nat.succ_le_succ hlen, ?_, ?_⟩
            · intro g hg
              rcases List.mem_cons.mp hg with hg | hg
              · simpa only [hg] using hs
              · exact hmem g hg
            · simp only [List.prod_cons, mul_smul, hprod]
          · obtain ⟨lz, hlz, hmz, hpz⟩ := hwords z hz
            exact ⟨lz, hlz.trans (Nat.le_succ n), hmz, hpz⟩
    obtain ⟨U, hcard, _, hwords⟩ := hsets m
    let enum : Fin (m + 1) → U := (Finset.equivFinOfCardEq hcard).symm
    have hexists (i : Fin (m + 1)) : ∃ l : List G,
        l.length ≤ m ∧ (∀ g ∈ l, g ∈ S) ∧ l.prod • x0 = (enum i : X) :=
      hwords (enum i) (enum i).property
    choose f hf using hexists
    obtain ⟨i, j, hij, heq⟩ := hcollision f (fun i => (hf i).1) (fun i => (hf i).2.1)
    have he : (enum i : X) = (enum j : X) := (hf i).2.2.symm.trans (heq.trans (hf j).2.2)
    exact hij ((Finset.equivFinOfCardEq hcard).symm.injective (Subtype.ext he))
  let ε : ℝ := 1 / ((m : ℝ) + 1)
  have hden : 0 < (m : ℝ) + 1 := by positivity
  have hε : 0 < ε := one_div_pos.mpr hden
  let S : Set G := {g | dist p (g • p) < ε}
  let Γ : Subgroup G := Subgroup.closure S
  let K : Subgroup Γ := H.subgroupOf Γ
  let T : Set Γ := ((↑) : Γ → G) ⁻¹' S
  have hisodist (g : G) (x y : X) : dist (g • x) (g • y) = dist x y :=
    (hisom g).dist_eq x y
  have hdinv (g : G) : dist p (g⁻¹ • p) = dist p (g • p) := by
    calc
      _ = dist (g • p) (g • (g⁻¹ • p)) := (hisodist g p (g⁻¹ • p)).symm
      _ = dist p (g • p) := by rw [smul_inv_smul, dist_comm]
  have hdmul (g k : G) :
      dist p ((g * k) • p) ≤ dist p (g • p) + dist p (k • p) := by
    rw [mul_smul]
    exact (dist_triangle p (g • p) (g • (k • p))).trans_eq
      (congrArg (dist p (g • p) + ·) (hisodist g p (k • p)))
  have hsym : ∀ g ∈ T, g⁻¹ ∈ T := by
    intro g hg
    change dist p ((g : G)⁻¹ • p) < ε
    rw [hdinv]
    exact hg
  have hgen : Subgroup.closure T = ⊤ := Subgroup.closure_closure_coe_preimage
  have hword (l : List Γ) (hl : ∀ g ∈ l, g ∈ T) :
      dist p ((l.prod : G) • p) ≤ (l.length : ℝ) * ε := by
    induction l with
    | nil => simp
    | cons g l ih =>
      have hg : dist p ((g : G) • p) ≤ ε := (hl g List.mem_cons_self).le
      have htail : ∀ k ∈ l, k ∈ T := fun k hk => hl k (List.mem_cons_of_mem g hk)
      have hh := hdmul (g : G) (l.prod : G)
      have hih := ih htail
      simp only [List.prod_cons, Subgroup.coe_mul, List.length_cons, Nat.cast_add,
        Nat.cast_one]
      linarith
  have hunit : (m : ℝ) * ε ≤ 1 := by
    dsimp [ε]
    rw [mul_one_div]
    exact (div_le_one hden).mpr (by linarith)
  have hcollision : ∀ f : Fin (m + 1) → List Γ,
      (∀ i, (f i).length ≤ m) → (∀ i, ∀ g ∈ f i, g ∈ T) →
      ∃ i j, i ≠ j ∧ (f i).prod • (QuotientGroup.mk (1 : Γ) : Γ ⧸ K) =
        (f j).prod • (QuotientGroup.mk (1 : Γ) : Γ ⧸ K) := by
    intro f hlen hmem
    have hb (i : Fin (m + 1)) : dist p (((f i).prod : G) • p) ≤ 1 := by
      exact (hword (f i) (hmem i)).trans
        ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hlen i)) hε.le).trans hunit)
    let b (i : Fin (m + 1)) : {g : G | dist p (g • p) ≤ 1} :=
      ⟨((f i).prod : G), hb i⟩
    have hn := Fintype.not_injective_of_card_lt (fun i => color (b i))
      (by simp only [Fintype.card_fin]; exact Nat.lt_succ_self m)
    obtain ⟨i, j, he, hij⟩ := Function.not_injective_iff.mp hn
    have hK : ((f i).prod)⁻¹ * (f j).prod ∈ K := hcolor (b i) (b j) he
    refine ⟨i, j, hij, ?_⟩
    simp only [Quotient.smul_mk, smul_eq_mul, mul_one]
    exact QuotientGroup.eq.mpr hK
  have hquot : Finite (Γ ⧸ K) := hfinite
    (QuotientGroup.mk (1 : Γ) : Γ ⧸ K) T hsym hgen m hcollision
  have hindex : K.FiniteIndex := Subgroup.finiteIndex_iff_finite_quotient.mpr hquot
  let : Group.IsNilpotent H := hH
  let e : K ≃* (Γ.subgroupOf H) :=
    { toFun := fun k => ⟨⟨((k : Γ) : G), k.property⟩, (k : Γ).property⟩
      invFun := fun k => ⟨⟨((k : H) : G), k.property⟩, (k : H).property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hKnil : Group.IsNilpotent K :=
    (Group.isNilpotent_congr e).mpr (inferInstance : Group.IsNilpotent (Γ.subgroupOf H))
  exact ⟨K, hKnil, hindex⟩

#print axioms result

end

end D5.S3.Combinatorics.GroupActions.FiniteColorVirtualNilpotence
