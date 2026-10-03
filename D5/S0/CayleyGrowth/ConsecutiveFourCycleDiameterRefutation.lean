/- GID: D5/S0/CayleyGrowth/ConsecutiveFourCycleDiameterRefutation
   generality: G
   mirror-B: D5/B/S0/CayleyGrowth/ConsecutiveFourCycleDiameterRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S0/CayleyGrowth/ConsecutiveFourCycleDiameterRefutation.claim; result=D5/S0/CayleyGrowth/ConsecutiveFourCycleDiameterRefutation.result; claim=D5/S0/CayleyGrowth/ConsecutiveFourCycleDiameterRefutation.claim
   digest: Reversal in S6 contradicts the consecutive-four-cycle diameter formula. -/

import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.GroupTheory.Perm.List
import Mathlib.Tactic

set_option autoImplicit false

namespace CayleyGrowth.ConsecutiveFourCycleDiameterRefutation

/-- The nonwrapped cycle `(i, i+1, i+2, i+3)` on `Fin n`. -/
def cycle (n i : ℕ) (h : i + 4 ≤ n) : Equiv.Perm (Fin n) :=
  ([⟨i, by omega⟩, ⟨i + 1, by omega⟩, ⟨i + 2, by omega⟩,
    ⟨i + 3, by omega⟩] : List (Fin n)).formPerm

/-- All consecutive four-cycles and their inverses, with no wrapping. -/
def generators (n : ℕ) : Set (Equiv.Perm (Fin n)) :=
  {g | ∃ (i : ℕ) (h : i + 4 ≤ n), g = cycle n i h ∨ g = (cycle n i h)⁻¹}

/-- The inverse-closed, undirected Cayley graph on the full symmetric group. -/
def graph (n : ℕ) : SimpleGraph (Equiv.Perm (Fin n)) :=
  SimpleGraph.mulCayley (generators n)

/-- The exact rational formula in the `k = 4` clause of Conjecture 11. -/
def formula (n : ℕ) : ℚ :=
  if n % 3 = 2 then (n : ℚ) * ((n : ℚ) - 1) / 6 + 2 / 3
  else (n : ℚ) * ((n : ℚ) - 1) / 6 - 1

/-- The complete universal clause, including finiteness of the diameter. -/
def claim : Prop :=
  ∀ n : ℕ, 6 ≤ n → ∃ d : ℕ, (graph n).ediam = (d : ℕ∞) ∧ (d : ℚ) = formula n

/-- Conjecture 11's complete `k = 4` diameter clause is false. -/
theorem result : ¬ claim := by
  let a : Equiv.Perm (Fin 6) := ([0, 1, 2, 3] : List (Fin 6)).formPerm
  let b : Equiv.Perm (Fin 6) := ([1, 2, 3, 4] : List (Fin 6)).formPerm
  let c : Equiv.Perm (Fin 6) := ([2, 3, 4, 5] : List (Fin 6)).formPerm
  let gs := [a, a⁻¹, b, b⁻¹, c, c⁻¹]
  let reversal : Equiv.Perm (Fin 6) :=
    Equiv.swap 0 5 * Equiv.swap 1 4 * Equiv.swap 2 3
  let ball : ℕ → List (Equiv.Perm (Fin 6)) :=
    fun m => Nat.rec [1] (fun _ previous =>
      previous ++ previous.flatMap (fun p => gs.map (p * ·))) m
  have excluded : reversal ∉ ball 4 := by decide +kernel
  have exact_generators : ∀ g, g ∈ generators 6 ↔ g ∈ gs := by
    intro g
    constructor
    · rintro ⟨i, h, hg⟩
      have hi : i ≤ 2 := by omega
      interval_cases i <;> rcases hg with rfl | rfl <;>
        simp [cycle, gs, a, b, c]
    · intro hg
      simp only [gs, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, by decide, Or.inl rfl⟩
      · exact ⟨0, by decide, Or.inr rfl⟩
      · exact ⟨1, by decide, Or.inl rfl⟩
      · exact ⟨1, by decide, Or.inr rfl⟩
      · exact ⟨2, by decide, Or.inl rfl⟩
      · exact ⟨2, by decide, Or.inr rfl⟩
  have inverse_closed : ∀ g ∈ gs, g⁻¹ ∈ gs := by
    intro g hg
    simp only [gs, List.mem_cons, List.not_mem_nil, or_false] at hg ⊢
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have extend : ∀ k p g, p ∈ ball k → g ∈ gs → p * g ∈ ball (k + 1) := by
    intro k p g hp hg
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    exact ⟨p, hp, List.mem_map.mpr ⟨g, hg, rfl⟩⟩
  have monotone : ∀ k l, k ≤ l → ∀ p, p ∈ ball k → p ∈ ball l := by
    intro k l hkl p hp
    induction hkl with
    | refl => exact hp
    | @step l hkl ih => exact List.mem_append_left _ ih
  have walk_sound : ∀ {u v : Equiv.Perm (Fin 6)} (w : (graph 6).Walk u v),
      ∀ k, u ∈ ball k → v ∈ ball (k + w.length) := by
    intro u v w
    induction w with
    | nil => intro k hk; simpa using hk
    | @cons u m v h w ih =>
      intro k hk
      obtain ⟨_, g, hg, hmove⟩ :=
        (SimpleGraph.mulCayley_adj' (generators 6) u m).mp h
      have hg' := (exact_generators g).mp hg
      have hm : m ∈ ball (k + 1) := by
        rcases hmove with hforward | hreverse
        · rw [← hforward]
          exact extend k u g hk hg'
        · have hm : m = u * g⁻¹ := by rw [hreverse]; simp [mul_assoc]
          rw [hm]
          exact extend k u g⁻¹ hk (inverse_closed g hg')
      simpa [SimpleGraph.Walk.length_cons, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using ih (k + 1) hm
  intro universal
  obtain ⟨d, hdiam, hd⟩ := universal 6 (by decide)
  have hd4 : d = 4 := by
    norm_num [formula] at hd
    exact_mod_cast hd
  subst d
  have hdist : (graph 6).edist 1 reversal ≤ (4 : ℕ∞) := by
    simpa [hdiam] using
      (SimpleGraph.edist_le_ediam (G := graph 6) (u := 1) (v := reversal))
  have hfinite : (graph 6).edist 1 reversal ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hdist
  obtain ⟨w, hw⟩ := SimpleGraph.exists_walk_of_edist_ne_top hfinite
  have hlength : w.length ≤ 4 := by
    have : (w.length : ℕ∞) ≤ 4 := hw ▸ hdist
    exact_mod_cast this
  have hmember : reversal ∈ ball w.length := by
    simpa using walk_sound w 0 (by simp [ball])
  exact excluded (monotone w.length 4 hlength reversal hmember)

end CayleyGrowth.ConsecutiveFourCycleDiameterRefutation
