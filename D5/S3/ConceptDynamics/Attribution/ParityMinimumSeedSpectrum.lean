/- GID: D5/S3/ConceptDynamics/Attribution/ParityMinimumSeedSpectrum
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/ParityMinimumSeedSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact coordinate-fixed counts at the least positive coloured parity budget. -/

import D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum
import D5.S3.Combinatorics.Graph.Hypercube.ParityMismatchCounts

/-! The coloured joint readout reflects fixed sets at the least positive seed budget. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Attribution.ParityMinimumSeedSpectrum

open Finset CoordinateFlagCoupling ParitySeedBudget ParitySeedOptimization ParitySeedCountSpectrum
open D5.S3.Combinatorics.Graph.Hypercube.ParityProfileMatching
open D5.S3.Combinatorics.Graph.Hypercube.ParityMismatchCounts
open scoped Classical

section
attribute [local instance 10000] Classical.propDecidable

private theorem equal_or_equal_of_two {S X : Type*} [Fintype S] (f : S → X) (x : X)
    (count : (∑ s, if f s = x then (1 : ℕ) else 0) = 2)
    {s t : S} (different : s ≠ t) (hs : f s = x) (ht : f t = x)
    {a : S} (ha : f a = x) : a = s ∨ a = t := by
  classical
  let F := univ.filter (fun a => f a = x)
  have subset : {s,t} ⊆ F := by
    intro b hb
    rcases mem_insert.mp hb with rfl | hb
    · exact mem_filter.mpr ⟨mem_univ _, hs⟩
    · have eq := mem_singleton.mp hb
      subst b
      exact mem_filter.mpr ⟨mem_univ _, ht⟩
  have cardF : F.card = 2 := by
    simpa [F, ← Finset.sum_filter] using count
  have eq : {s,t} = F := eq_of_subset_of_card_le subset (by rw [cardF]; simp [different])
  have h : a ∈ F := mem_filter.mpr ⟨mem_univ _, ha⟩
  rw [← eq] at h
  simpa using h

private theorem two_seeds_per_colour_joint_injective {n : ℕ} {S : Type*} [Fintype S]
    [MulAction (Acting (Fin (n + 2))) S] (f : S → Pair n)
    (equivariant : ∀ (g : Acting (Fin (n + 2))) s, f (g • s) = g • f s)
    (rows : ∀ x : slice (n + 2) 0, (∑ s, if (f s).1 = x then (1 : ℕ) else 0) = 2)
    (cols : ∀ y : slice (n + 2) 1, (∑ s, if (f s).2 = y then (1 : ℕ) else 0) = 2) :
    Function.Injective f := by
  classical
  intro s t same
  by_contra distinct
  have sameLeft : (f s).1 = (f t).1 := congrArg Prod.fst same
  have sameRight : (f s).2 = (f t).2 := congrArg Prod.snd same
  have equalFix (g : Acting (Fin (n + 2))) :
      g • (f s).1 = (f s).1 ↔ g • (f s).2 = (f s).2 := by
    constructor
    · intro fix
      have moved : (f (g • s)).1 = (f s).1 :=
        (congrArg Prod.fst (equivariant g s)).trans fix
      rcases equal_or_equal_of_two (fun a => (f a).1) (f s).1
        (rows (f s).1) distinct rfl sameLeft.symm moved with h | h
      · exact (congrArg Prod.snd (equivariant g s)).symm.trans
          (congrArg (fun a => (f a).2) h)
      · exact (congrArg Prod.snd (equivariant g s)).symm.trans
          ((congrArg (fun a => (f a).2) h).trans sameRight.symm)
    · intro fix
      have moved : (f (g • s)).2 = (f s).2 :=
        (congrArg Prod.snd (equivariant g s)).trans fix
      rcases equal_or_equal_of_two (fun a => (f a).2) (f s).2
        (cols (f s).2) distinct rfl sameRight.symm moved with h | h
      · exact (congrArg Prod.fst (equivariant g s)).symm.trans
          (congrArg (fun a => (f a).1) h)
      · exact (congrArg Prod.fst (equivariant g s)).symm.trans
          ((congrArg (fun a => (f a).1) h).trans sameLeft.symm)
  have sameProfile : (f s).1.val.profile = (f s).2.val.profile := by
    funext i
    have rightOfLeft : (f s).1.val.profile i = true → (f s).2.val.profile i = true := by
      intro hx
      have all := (fixed_pair_iff (f s).1.val (f s).1.val i).mpr (by simp [hx])
      suffices h : ((f s).2.val.profile i && (f s).2.val.profile i) = true by simpa using h
      apply (fixed_pair_iff (f s).2.val (f s).2.val i).mp
      intro g hg
      have left : g • (f s).1 = (f s).1 := Subtype.ext (all g hg).1
      have right := congrArg Subtype.val ((equalFix g).mp left)
      exact ⟨right, right⟩
    have leftOfRight : (f s).2.val.profile i = true → (f s).1.val.profile i = true := by
      intro hy
      have all := (fixed_pair_iff (f s).2.val (f s).2.val i).mpr (by simp [hy])
      suffices h : ((f s).1.val.profile i && (f s).1.val.profile i) = true by simpa using h
      apply (fixed_pair_iff (f s).1.val (f s).1.val i).mp
      intro g hg
      have right : g • (f s).2 = (f s).2 := Subtype.ext (all g hg).1
      have left := congrArg Subtype.val ((equalFix g).mpr right)
      exact ⟨left, left⟩
    cases hl : (f s).1.val.profile i <;> cases hr : (f s).2.val.profile i <;>
      simp_all
  have contradiction := congrArg (fun p => D5.S3.ConceptDynamics.Attribution.ParitySeedBudget.parity
    (bitProfile p)) sameProfile
  rw [(f s).1.property, (f s).2.property] at contradiction
  exact zero_ne_one contradiction


end

set_option maxHeartbeats 600000 in
private theorem observed_counts_of_injective_readout {n : ℕ} {S : Type} [Fintype S]
    [MulAction (Acting (Fin (n + 2))) S] (f : S → Pair n)
    (equivariant : ∀ (g : Acting (Fin (n + 2))) s, f (g • s) = g • f s)
    (inj : Function.Injective f) (i : Fin (n + 2)) :
    fixedSeedCount (n := n) S i =
      ∑ a : Pair n, if (∀ h : coordinate i, (h : Acting (Fin (n + 2))) • a = a)
        then seedWeight (seedPushforward f) a else 0 := by
  classical
  let P (x : Pair n) := ∀ h : coordinate i, (h : Acting (Fin (n + 2))) • x = x
  have bridge : (∑ s : S, if (∀ h : coordinate i,
      (h : Acting (Fin (n + 2))) • f s = f s) then (1 : ℕ) else 0) =
      ∑ a : Pair n, if (∀ h : coordinate i, (h : Acting (Fin (n + 2))) • a = a)
        then seedWeight (seedPushforward f) a else 0 := by
    convert seed_indicator_sum f P using 1 <;>
      apply sum_congr rfl <;> intro x _ <;>
        (first | by_cases h : P (f x) | by_cases h : P x) <;> simp [P] at h ⊢
  rw [← bridge]
  unfold fixedSeedCount
  apply sum_congr rfl
  intro s _
  have states : (∀ h : coordinate i, (h : Acting (Fin (n + 2))) • s = s) ↔
      (∀ h : coordinate i, (h : Acting (Fin (n + 2))) • f s = f s) := by
    constructor <;> intro all h
    · rw [← equivariant, all h]
    · apply inj
      rw [equivariant, all h]
  simp only [states]

set_option maxHeartbeats 450000 in
/-- At the least positive seed budget, the even-word cuts classify the actual fixed counts. -/
theorem exact_minimal_budget_fixed_counts (n : ℕ) (z : Fin (n + 2) → ℕ) :
    RealizableSeedCounts n 1 z ↔
    ∃ a : Fin (n + 2) → ℕ, (∀ i, a i ≤ 2 ^ n ∧ z i = 4 * (2 ^ n - a i)) ∧
      ∀ e : Profile (n + 2), parity e = 0 →
        2 ^ n ≤ ∑ i, if e i = 0 then a i else 2 ^ n - a i := by
  constructor
  · rintro ⟨S, _, _, f, card, equivariant, ⟨c, rows, cols⟩, counts⟩
    have c_eq : c = 2 := by simpa using left_colour_marginal f card c rows
    have inj := two_seeds_per_colour_joint_injective f equivariant
      (fun x => (rows x).trans c_eq) (fun y => (cols y).trans c_eq)
    obtain ⟨W, rowW, colW, scale⟩ := normalize_coloured_counts
      (seeds_to_pushforward f card equivariant c rows cols)
    let a (i : Fin (n + 2)) := 2 ^ n - commonOneCount W i
    have diffs (i : Fin (n + 2)) :
        (∑ p, ∑ q, if p.val i ≠ q.val i then W p q else 0) = 2 * a i := by
      have h := mismatch_add_twice_common n 1 W rowW colW i
      simp only [one_mul] at h
      have arithmetic : 2 * (2 ^ n - commonOneCount W i) =
           2 * 2 ^ n - 2 * commonOneCount W i := by omega
      change (∑ p, ∑ q, if p.val i ≠ q.val i then W p q else 0) =
        2 * (2 ^ n - commonOneCount W i)
      rw [arithmetic, h, Nat.add_sub_cancel_left]
      apply sum_congr rfl
      intro p _
      apply sum_congr rfl
      intro q _
      by_cases same : p.val i = q.val i <;> simp [same]
    have evenCuts := (exact_integer_parity_mismatch_counts n 1 a).mp ⟨W, rowW, colW, diffs⟩
    refine ⟨a, fun i => ⟨by simpa using evenCuts.1 i, ?_⟩, ?_⟩
    · rw [← counts i, observed_counts_of_injective_readout f equivariant inj,
        scaled_fixed_total scale]
      have h := mismatch_add_twice_common n 1 W rowW colW i
      simp only [one_mul] at h
      dsimp only [a]
      omega
    · intro e he
      have h := evenCuts.2 e he
      simpa only [one_mul] using h
  · rintro ⟨a, cap, cuts⟩
    obtain ⟨W, rows, cols, diffs⟩ := (exact_integer_parity_mismatch_counts n 1 a).mpr
      ⟨fun i => by simpa using (cap i).1, by intro e he; simpa only [one_mul] using cuts e he⟩
    have same (i : Fin (n + 2)) : 4 * commonOneCount W i = z i := by
      have h := mismatch_add_twice_common n 1 W rows cols i
      rw [one_mul, diffs i] at h
      rw [(cap i).2]
      omega
    simpa only [same] using realize_scaled_profile_counts W rows cols


end D5.S3.ConceptDynamics.Attribution.ParityMinimumSeedSpectrum
