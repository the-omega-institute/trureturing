/- GID: D5/S3/Combinatorics/Graph/Chordal/ChordalFanLower
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-exact-strata-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Chordal fans of clique number three give normed gain obstructions below unit error. -/

import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.Chordal.SimplicialAndIntervalPotential
import D5.S3.Combinatorics.Graph.Chordal.ScalarCycleReconstruction
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Real

compile_only_with_mathlib

/-!
Omega original.

Arbitrarily long scalar cycle obstructions already occur at clique number three.
-/

namespace SimpleGraph

private def fanLeft {n : ℕ} (v : Fin (n + 1)) : ℝ := v.val
private def fanRight {n : ℕ} (v : Fin (n + 1)) : ℝ :=
  if v.val = 0 then n + 1 else v.val + 1

/-- A fan with its universal vertex at index zero and consecutive remaining edges. -/
def gainFan (n : ℕ) : SimpleGraph (Fin (n + 1)) where
  Adj a b := a ≠ b ∧ max (fanLeft a) (fanLeft b) ≤ min (fanRight a) (fanRight b)
  symm := ⟨fun _ _ h => ⟨h.1.symm, by simpa [max_comm, min_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private theorem gainFan_chordal (n : ℕ) : (gainFan n).IsChordal := by
  have hI (v : Fin (n + 1)) : fanLeft v ≤ fanRight v := by
    by_cases h : v.val = 0
    · have hn : (0 : ℝ) ≤ n := by positivity
      simp [fanLeft, fanRight, h, show (0 : ℝ) ≤ n + 1 by linarith]
    · simp [fanLeft, fanRight, h]
  exact (intervalGraph_isChordal_and_two_approximate_gain_potential fanLeft fanRight hI
    (fun _ _ => Iff.rfl) (fun _ _ => (1 : Multiplicative ℝ)) 0 le_rfl
    (fun _ _ _ => by simp) (fun _ _ _ _ _ _ => by simp)).1

private theorem fan_pos_close {n : ℕ} {a b : Fin (n + 1)} (ha : a.val ≠ 0)
    (_hb : b.val ≠ 0) (h : (gainFan n).Adj a b) : b.val ≤ a.val + 1 := by
  have he := (le_max_right (fanLeft a) (fanLeft b)).trans (h.2.trans (min_le_left _ _))
  simp [fanLeft, fanRight, ha] at he
  exact_mod_cast he

private theorem gainFan_clique {n : ℕ} {s : Finset (Fin (n+1))}
    (h : (gainFan n).IsClique (s : Set (Fin (n+1)))) : s.card ≤ 3 := by
  classical
  let t := s.erase 0
  have ht : t.card ≤ 2 := by
    by_cases ht : t.Nonempty
    · obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image t Fin.val ht
      have ha0 : a.val ≠ 0 := fun hh => (Finset.mem_erase.mp ha).1 (Fin.ext hh)
      have hs : t.image Fin.val ⊆ Finset.Icc a.val (a.val + 1) := by
        intro i hi
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hi
        refine Finset.mem_Icc.mpr ⟨hmin b hb, ?_⟩
        by_cases hab : a = b
        · simp [hab]
        · have hb0 : b.val ≠ 0 := fun hh => (Finset.mem_erase.mp hb).1 (Fin.ext hh)
          exact fan_pos_close ha0 hb0 (h (Finset.mem_erase.mp ha).2 (Finset.mem_erase.mp hb).2 hab)
      rw [← t.card_image_of_injective Fin.val_injective]
      exact (Finset.card_le_card hs).trans (by rw [Nat.card_Icc]; omega)
    · simp [Finset.not_nonempty_iff_eq_empty.mp ht]
  by_cases h0 : (0 : Fin (n + 1)) ∈ s
  · have := Finset.card_erase_add_one h0
    change (s.erase 0).card ≤ 2 at ht
    omega
  · simpa [t, Finset.erase_eq_of_notMem h0] using ht.trans (by decide : 2 ≤ 3)

private theorem fan_consecutive {n i : ℕ} (hi : i + 1 ≤ n) :
    (gainFan n).Adj ⟨i, by omega⟩ ⟨i + 1, by omega⟩ := by
  refine ⟨fun he => by have := congrArg Fin.val he; simp at this, ?_⟩
  change max (i : ℝ) ((i + 1 : ℕ) : ℝ) ≤ min (fanRight ⟨i, by omega⟩)
    (fanRight ⟨i + 1, by omega⟩)
  have hnr : ((i + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hi
  simp only [fanRight, Nat.succ_ne_zero, ite_false, Nat.cast_add, Nat.cast_one] at *
  rw [max_eq_right (by linarith)]
  by_cases h : i = 0 <;> simp [h]

private theorem fan_last {n : ℕ} (hn : 0 < n) :
    (gainFan n).Adj ⟨n, by omega⟩ 0 := by
  refine ⟨fun he => by have := congrArg Fin.val he; simp at this; omega, ?_⟩
  simp [fanLeft, fanRight, hn.ne']

private theorem fan_cycle {n : ℕ} (hn : 2 ≤ n) :
    ∃ c : (gainFan n).Walk 0 0, c.IsCycle ∧ c.length = n + 1 := by
  let v (i : ℕ) (h : i ≤ n) : Fin (n + 1) := ⟨i, by omega⟩
  have paths (i : ℕ) (hi : i ≤ n) :
      ∃ p : (gainFan n).Walk (v i hi) (v n le_rfl),
        p.IsPath ∧ p.length = n - i ∧ ∀ w ∈ p.support, i ≤ w.val := by
    suffices h : ∀ m i (hi : i ≤ n), n - i = m →
        ∃ p : (gainFan n).Walk (v i hi) (v n le_rfl),
          p.IsPath ∧ p.length = n - i ∧ ∀ w ∈ p.support, i ≤ w.val by
      exact h _ i hi rfl
    intro m
    induction m with
    | zero =>
      intro i hi hm
      have he : i = n := by omega
      subst i
      exact ⟨.nil, by simp, by simp, by simp [v]⟩
    | succ m ih =>
      intro i hi hm
      have hi' : i + 1 ≤ n := by omega
      obtain ⟨p, hp, hl, hmem⟩ := ih (i + 1) hi' (by omega)
      have h := fan_consecutive hi'
      refine ⟨p.cons h, (Walk.cons_isPath_iff h p).2 ⟨hp, ?_⟩, ?_, ?_⟩
      · intro hh
        have hge := hmem _ hh
        change i + 1 ≤ i at hge
        omega
      · simp only [Walk.length_cons, hl]; omega
      · intro w hw
        rw [Walk.support_cons, List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact le_rfl
        · exact (Nat.le_succ _).trans (hmem _ hw)
  obtain ⟨p, hp, hl, _⟩ := paths 0 (Nat.zero_le _)
  let p' : (gainFan n).Walk 0 (v n le_rfl) := p
  let h := fan_last (show 0 < n by omega)
  have he : (p'.concat h).length = n + 1 := by
    rw [Walk.length_concat]
    change p.length + 1 = n + 1
    simpa using hl
  have hc : (p'.concat h).IsCycle := by
    rw [Walk.isCycle_iff_isPath_dropLast_and_le_length]
    refine ⟨?_, by omega⟩
    rw [Walk.dropLast_concat, Walk.isPath_copy]
    exact hp
  exact ⟨p'.concat h, hc, he⟩

/-- Every nonzero real normed space has worst-case coefficient at least one
already on chordal graphs with clique number at most three. -/
theorem exists_chordal_clique_three_normed_gain_obstruction
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    (C : ℝ) (hC : C < 1) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin (n+1))) (g : Fin (n+1) → Fin (n+1) → E),
      G.IsChordal ∧ (∀ s : Finset (Fin (n+1)), G.IsClique (s : Set (Fin (n+1))) → s.card ≤ 3) ∧
      (∀ a b, g b a = -g a b) ∧ (∀ a b c, ‖g a b + g b c - g a c‖ ≤ 1) ∧
      ∀ φ : Fin (n+1) → E, ∃ a b, G.Adj a b ∧ C < ‖g a b - (φ b - φ a)‖ := by
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / (1 - C))
  let n := m + 2
  have hn : 2 ≤ n := by dsimp [n]; omega
  have hcoef : C < 1 - 2 / ((n + 1 : ℕ) : ℝ) := by
    have hpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have hm' : (m : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast (show m ≤ n + 1 by dsimp [n]; omega)
    have h := (div_lt_iff₀ (sub_pos.mpr hC)).mp (hm.trans_le hm')
    have h' := (div_lt_iff₀ hpos).mpr (by linarith : (2 : ℝ) < (1-C) * (n + 1 : ℕ))
    linarith
  obtain ⟨p, hp, hl⟩ := fan_cycle hn
  obtain ⟨f, hrev, htri, hobs⟩ := hp.exists_scalar_gain_obstruction
  obtain ⟨x, hx⟩ := exists_norm_eq E (show (0 : ℝ) ≤ 1 by norm_num)
  obtain ⟨F, hF, hFx⟩ := exists_dual_vector ℝ x (by simp [hx])
  let g (a b : Fin (n+1)) := f a b • x
  refine ⟨n, gainFan n, g, gainFan_chordal n, fun _ hs => gainFan_clique hs,
    fun a b => by simp [g, hrev a b, neg_smul], fun a b c => ?_, fun φ => ?_⟩
  · dsimp [g]
    rw [← add_smul, ← sub_smul, norm_smul, Real.norm_eq_abs, hx, mul_one]
    exact htri a b c
  · obtain ⟨a, b, hab, he⟩ := hobs (fun v => F (φ v))
    refine ⟨a, b, hab, (hcoef.trans_le (hl ▸ he)).trans_le ?_⟩
    have h := F.le_opNorm (g a b - (φ b - φ a))
    simpa [g, hx, hF, hFx, Real.norm_eq_abs] using h

end SimpleGraph
