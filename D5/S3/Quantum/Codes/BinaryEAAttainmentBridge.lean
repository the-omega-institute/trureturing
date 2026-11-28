/- GID: D5/S3/Quantum/Codes/BinaryEAAttainmentBridge
   generality: I
   mirror-B: D5/B/S3/Quantum/Codes/BinaryEAAttainmentBridge
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Quantum/Codes/BinaryEAAttainmentBridge.claim; result=D5/S3/Quantum/Codes/BinaryEAAttainmentBridge.result; claim=D5/S3/Quantum/Codes/BinaryEAAttainmentBridge.claim
   digest: Binary Singleton attainment is excluded from length eight onward. -/

import D5.S3.Quantum.Codes.BinaryEAAttainment
import D5.S3.Quantum.Codes.BinaryEARankOneBridge
import D5.S3.Quantum.Codes.BinaryEAShortening

/-! Compression to the radical support and exclusion of all lengths at least eight. [Helper escape audits](https://github.com/the-omega-institute/trureturing/issues/34915). -/

set_option autoImplicit false

namespace D5.S3.Quantum.Codes.BinaryEAAttainmentBridge

open BinaryEAAttainment
open D5.S3.Quantum.Information.BinaryLagrangianGraphForm (sp)
open D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm (spForm sp_alt)
open scoped BigOperators

local notation "F" => ZMod 2
local notation "E" n:arg => ((Fin n → F) × (Fin n → F))
local notation "dim" => Module.finrank F

private theorem site_rank_le_singleton_rank {n : ℕ} (H : Submodule F (E n)) (i : Fin n) :
    dim (H.map (site i)) ≤ dim (((restrictSites {i}).domRestrict H).range) := by
  let p := LinearMap.proj (R := F) (φ := fun _ : ({i} : Finset (Fin n)) => F × F)
    ⟨i, Finset.mem_singleton_self i⟩
  have hp : (((restrictSites {i}).domRestrict H).range).map p = H.map (site i) := by
    rw [LinearMap.range_domRestrict, ← Submodule.map_comp]
    rfl
  rw [← hp]
  exact Submodule.finrank_map_le _ _

private theorem site_rank_le_one_of_not_surjective {n : ℕ} (H : Submodule F (E n))
    (i : Fin n) (hi : ¬ Function.Surjective ((site i).domRestrict H)) :
    dim (H.map (site i)) ≤ 1 := by
  by_contra! h
  have hd : dim (F × F) = 2 := by simp [Module.finrank_prod]
  have hle := Submodule.finrank_le (H.map (site i))
  apply hi
  apply LinearMap.range_eq_top.mp
  rw [LinearMap.range_domRestrict]
  exact Submodule.eq_top_of_finrank_eq (by omega)

private theorem no_rank_two_at_eight (U : Submodule F (E 8)) (hU : ZeroBound U)
    (hdU : dim U = 8) (hdH : dim (radical U) = 4)
    (i : Fin 8) (hi : Function.Surjective ((site i).domRestrict (radical U))) : False := by
  refine BinaryEAShortening.length_eight_no_rank_two_site (radical U) U inf_le_left
    hdH hdU (fun h hh u hu => (sp_alt 8).isRefl u h (hh.2 u hu)) hU i hi ?_
  intro j hj
  have hdim := dim_kernel_add_rank (radical U) {i, j}
  have hker := pair_kernel_dim_pos_at_eight U hU hdU {i, j} (Finset.card_pair hj.symm)
  change dim (((restrictSites {i, j}).domRestrict (radical U)).range) ≤ 3
  omega

private def restrictWord {n s : ℕ} (f : Fin s → Fin n) : E n →ₗ[F] E s where
  toFun v := (v.1 ∘ f, v.2 ∘ f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem no_rank_one_on_small_support {n : ℕ} (U : Submodule F (E n)) (hU : ZeroBound U)
    (hdU : dim U = 8) (hdH : dim (radical U) = 4)
    (hS : (support (radical U)).card ≤ 10)
    (hr : ∀ i, dim ((radical U).map (site i)) ≤ 1) : False := by
  classical
  let H := radical U
  let S := support H
  let e : Fin S.card ≃ S := (Fintype.equivFinOfCardEq (Fintype.card_coe S)).symm
  let f : Fin S.card ↪ Fin n := e.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩
  let p := restrictWord f
  let C := U.map p
  let G := H.map p
  have hHU : H ≤ U := inf_le_left
  have hf (j : Fin S.card) : f j ∈ S := (e j).property
  have h7 := seven_le_support U hU hdU hdH
  have hinj : Function.Injective (p.domRestrict U) := by
    intro a b hab
    apply core_injective U hU (by omega)
    change mask S a = mask S b
    apply Prod.ext <;> funext i <;> by_cases hi : i ∈ S
    · obtain ⟨j, hj⟩ := e.surjective ⟨i, hi⟩
      have h := congrFun (congrArg Prod.fst hab) j
      change a.val.1 (f j) = b.val.1 (f j) at h
      have hji : f j = i := congrArg Subtype.val hj
      simpa [mask, hi, hji] using h
    · simp [mask, hi]
    · obtain ⟨j, hj⟩ := e.surjective ⟨i, hi⟩
      have h := congrFun (congrArg Prod.snd hab) j
      change a.val.2 (f j) = b.val.2 (f j) at h
      have hji : f j = i := congrArg Subtype.val hj
      simpa [mask, hi, hji] using h
    · simp [mask, hi]
  have hinjH : Function.Injective (p.domRestrict H) :=
    hinj.comp (Submodule.inclusion_injective hHU)
  have hC : dim C = 8 := by
    change dim (U.map p) = 8
    rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj, hdU]
  have hG : dim G = 4 := by
    change dim (H.map p) = 4
    rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinjH, hdH]
  refine BinaryEARankOneBridge.no_rank_one_of_card_le_ten C G hS
    (Submodule.map_mono hHU) hC hG ?_ ?_ ?_
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨h, hh, rfl⟩
    have hort := (core_le_orthogonal U (Submodule.mem_map.mpr ⟨u, hu, rfl⟩)).1 h hh
    change sp (p h) (p u) = 0
    change sp h (mask S u) = 0 at hort
    let g (i : Fin n) := h.1 i * u.2 i + h.2 i * u.1 i
    have hs : sp (p h) (p u) = ∑ i ∈ S, g i := by
      change (∑ j : Fin S.card, g (e j).val) = _
      exact (Equiv.sum_comp e (fun i : S => g i.val)).trans
        (S.sum_subtype (fun _ => Iff.rfl) g).symm
    rw [hs]
    have hm : sp h (mask S u) = ∑ i ∈ S, g i := by
      unfold sp
      rw [← Finset.sum_add_sum_compl S]
      have hOut : (∑ i ∈ Sᶜ, (h.1 i * (mask S u).2 i + h.2 i * (mask S u).1 i)) = 0 :=
        Finset.sum_eq_zero (fun i hi => by simp [mask, Finset.mem_compl.mp hi])
      rw [hOut, add_zero]
      exact Finset.sum_congr rfl (fun i hi => by simp [mask, hi, g])
    exact hm.symm.trans hort
  · intro j
    have hp : G.map (BinaryEARankOneBridge.site j) = H.map (site (f j)) := by
      change (H.map p).map (BinaryEARankOneBridge.site j) = H.map (site (f j))
      rw [← Submodule.map_comp]
      rfl
    rw [hp]
    have hpos : 0 < dim (H.map (site (f j))) := by
      obtain ⟨h, hh, hn⟩ := mem_support.mp (hf j)
      by_contra! hz
      have hb := Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hz)
      exact hn ((Submodule.mem_bot F).mp (hb ▸ Submodule.mem_map.mpr ⟨h, hh, rfl⟩))
    exact Nat.le_antisymm (hr (f j)) hpos
  · rintro _ ⟨u, hu, rfl⟩ hnu
    have huH : u ∉ H := fun h => hnu (Submodule.mem_map.mpr ⟨u, h, rfl⟩)
    let Z := (Finset.univ : Finset (Fin S.card)).filter
      (fun i => (p u).1 i = 0 ∧ (p u).2 i = 0)
    change Z.card ≤ 3
    have hsub : Z.map f ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => site i u = 0) := by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
      obtain ⟨h₁, h₂⟩ := (Finset.mem_filter.mp hj).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Prod.ext h₁ h₂⟩
    exact (Finset.card_map f).symm.trans_le ((Finset.card_le_card hsub).trans (hU u hu huH))

/-- A length of at least eight with dimensions eight and four and at most three zeros
on each nonradical word. -/
def claim : Prop :=
  ∃ (n : ℕ) (U : Submodule F (E n)),
    8 ≤ n ∧ dim U = 8 ∧ dim (radical U) = 4 ∧ ZeroBound U

/-- The zero bound is impossible at any length of at least eight. -/
theorem result : ¬ claim := by
  rintro ⟨n, U, hn, hdU, hdH, hU⟩
  by_cases h9 : 9 ≤ n
  · apply no_rank_one_on_small_support U hU hdU hdH (radical_support_upper_bound U hU hdU hdH h9).2
    exact fun i => (site_rank_le_singleton_rank (radical U) i).trans
      (radical_site_rank_le_one U hU hdU hdH h9 i)
  · obtain rfl : n = 8 := by omega
    have hs : (support (radical U)).card ≤ 10 := by
      have : (support (radical U)).card ≤ 8 := by
        simpa only [Fintype.card_fin] using (support (radical U)).card_le_univ
      omega
    exact no_rank_one_on_small_support U hU hdU hdH hs (fun i =>
      site_rank_le_one_of_not_surjective (radical U) i (no_rank_two_at_eight U hU hdU hdH i))

/-- Excluding a rank-two radical site at length seven suffices to refute exact attainment. -/
theorem refute_attainment_of_length_seven_rank_two
    (hseven : ∀ U : Submodule F (E 7), dim U = 8 → dim (radical U) = 4 → ZeroBound U →
      (∃ i, Function.Surjective ((site i).domRestrict (radical U))) → False) :
    ¬ Attainment := by
  rintro ⟨n, hn, U, hdU, hdH, hweight, _⟩
  have hU := zeroBound_of_weight_bound U hn hweight
  have hs := seven_le_support U hU hdU hdH
  have hs' : (support (radical U)).card ≤ n := by
    simpa only [Fintype.card_fin] using (support (radical U)).card_le_univ
  by_cases hn8 : 8 ≤ n
  · exact result ⟨n, U, hn8, hdU, hdH, hU⟩
  obtain rfl : n = 7 := by omega
  by_cases htwo : ∃ i, Function.Surjective ((site i).domRestrict (radical U))
  · exact hseven U hdU hdH hU htwo
  · exact no_rank_one_on_small_support U hU hdU hdH (by omega) (fun i =>
      site_rank_le_one_of_not_surjective (radical U) i (fun hi => htwo ⟨i, hi⟩))

end D5.S3.Quantum.Codes.BinaryEAAttainmentBridge
