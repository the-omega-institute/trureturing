/- GID: D5/S3/Combinatorics/Graph/Chordal/CliqueTreeBanachPotential
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/CliqueTreeBanachPotential
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Center extension and separator midpoint bounds on clique trees. -/

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-! # Gain reconstruction on clique trees -/

open scoped BigOperators

namespace SimpleGraph

universe u v w

/-- A tree of clique bags covering the vertices and edges, with running intersection
expressed along simple paths. -/
structure IsCliqueTree {I : Type w} {V : Type u} (T : SimpleGraph I) (G : SimpleGraph V)
    (K : I → Set V) : Prop where
  isTree : T.IsTree
  clique : ∀ a, G.IsClique (K a)
  cover : ∀ x, ∃ a, x ∈ K a
  edge : ∀ u v, G.Adj u v → ∃ a, u ∈ K a ∧ v ∈ K a
  running : ∀ {a b} (p : T.Walk a b), p.IsPath →
    ∀ x ∈ K a, x ∈ K b → ∀ c ∈ p.support, x ∈ K c

/-- Residual coefficients after successive waves of separator averaging. -/
def cliqueTreeRadius (m : ℕ) (R₀ : ℝ) : ℕ → ℝ
  | 0 => R₀
  | n + 1 =>
    let R := cliqueTreeRadius m R₀ n
    max (max R 1) ((1 - 1 / (m : ℝ)) * (1 + R))

/-- The bound on the change at a separator vertex when taking its midpoint. -/
noncomputable def sepShift {I : Type w} {V : Type u} (K : I → Set V) (a b : I) : ℝ :=
  (1 - 1 / ((K a ∩ K b).ncard : ℝ)) *
    (1 - ((K a ∩ K b).ncard : ℝ) / (max (K a).ncard (K b).ncard : ℝ))

namespace CliqueTreeBanach

variable {V : Type u} {I : Type w} {G : SimpleGraph V} {T : SimpleGraph I} {K : I → Set V}
variable {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

private noncomputable def mean (S : Finset V) (f : V → E) : E :=
  (S.card : ℝ)⁻¹ • ∑ t ∈ S, f t

private theorem mean_sub (S : Finset V) (f h : V → E) :
    mean S f - mean S h = mean S (fun t => f t - h t) := by
  simp [mean, Finset.sum_sub_distrib, smul_sub]

private theorem const_sub_mean {S : Finset V} (hS : S.Nonempty) (e : E) (f : V → E) :
    e - mean S f = mean S (fun t => e - f t) := by
  have hpos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  simp [mean, Finset.sum_sub_distrib, smul_sub, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, hpos.ne']

private theorem mean_bound {S A : Finset V} (hS : S.Nonempty) (hAS : A ⊆ S)
    (f : V → E) (B : ℝ) (hz : ∀ t ∈ S, t ∉ A → f t = 0)
    (hb : ∀ t ∈ A, ‖f t‖ ≤ B) :
    ‖mean S f‖ ≤ ((A.card : ℝ) / S.card) * B := by
  classical
  have hp : 0 ≤ (S.card : ℝ)⁻¹ := by positivity
  have hs : ∑ t ∈ A, f t = ∑ t ∈ S, f t := Finset.sum_subset hAS hz
  rw [mean, ← hs, norm_smul, Real.norm_eq_abs, abs_of_nonneg hp]
  calc
    _ ≤ (S.card : ℝ)⁻¹ * (∑ t ∈ A, ‖f t‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hp
    _ ≤ (S.card : ℝ)⁻¹ * (∑ _t ∈ A, B) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hb) hp
    _ = _ := by simp [div_eq_mul_inv]; ring

private theorem diag_zero (g : V → V → E) (hrev : ∀ i j, g j i = -g i j)
    (x : V) : g x x = 0 := by
  have hz : (2 : ℝ) • g x x = 0 := by rw [two_smul, eq_neg_iff_add_eq_zero.mp (hrev x x)]
  calc
    g x x = (1 / 2 : ℝ) • ((2 : ℝ) • g x x) := by rw [smul_smul]; norm_num
    _ = 0 := by rw [hz, smul_zero]

private theorem defect_bound (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, g j i = -g i j)
    (htri : ∀ i j l, G.Adj i j → G.Adj j l → G.Adj i l →
      ‖g i j + g j l - g i l‖ ≤ ε)
    {u v t : V} (huv : G.Adj u v) (htu : t ≠ u → G.Adj t u)
    (htv : t ≠ v → G.Adj t v) : ‖g u v - (g t v - g t u)‖ ≤ ε := by
  by_cases hu : t = u
  · subst t
    simpa [diag_zero g hrev] using hε
  by_cases hv : t = v
  · subst t
    simpa [diag_zero g hrev, hrev u v] using hε
  convert htri t u v (htu hu) huv (htv hv) using 1 <;> abel

private theorem star_residual {S : Finset V} (hS : S.Nonempty) (g : V → V → E) (u v : V) :
    g u v - (mean S (fun t => g t v) - mean S (fun t => g t u)) =
      mean S (fun t => g u v - (g t v - g t u)) := by
  rw [mean_sub, const_sub_mean hS]

private theorem star_bound {S : Finset V} (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, g j i = -g i j)
    (htri : ∀ i j l, G.Adj i j → G.Adj j l → G.Adj i l →
      ‖g i j + g j l - g i l‖ ≤ ε)
    (hcl : G.IsClique (S : Set V)) {u v : V} (hu : u ∈ S) (hv : v ∈ S) (huv : G.Adj u v) :
    ‖g u v - (mean S (fun t => g t v) - mean S (fun t => g t u))‖ ≤
      (1 - 2 / (S.card : ℝ)) * ε := by
  classical
  let A := (S.erase u).erase v
  have hs : S.Nonempty := ⟨u, hu⟩
  have hc : A.card + 2 = S.card := by
    have h₁ := Finset.card_erase_add_one hu
    have h₂ := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨huv.ne.symm, hv⟩)
    dsimp [A]
    omega
  have hr : (A.card : ℝ) + 2 = S.card := by exact_mod_cast hc
  have hp : (0 : ℝ) < S.card := by exact_mod_cast hs.card_pos
  rw [star_residual hs]
  calc
    _ ≤ ((A.card : ℝ) / S.card) * ε := by
      apply mean_bound hs ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
      · intro t ht hta
        by_cases htu : t = u
        · subst t
          simp [diag_zero g hrev]
        have htv : t = v := by by_contra h; exact hta (by simp [A, htu, h, ht])
        subst t
        simp [diag_zero g hrev, hrev u v]
      · intro t ht
        have hts : t ∈ S := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _) ht
        exact defect_bound g ε hε hrev htri huv (fun hn => hcl hts hu hn)
          (fun hn => hcl hts hv hn)
    _ = _ := by rw [show (A.card : ℝ) = S.card - 2 by linarith]; field_simp

private noncomputable def bag [Finite V] (S : Set V) : Finset V :=
  S.toFinite.toFinset

@[simp] private theorem mem_bag [Finite V] {x : V} {S : Set V} : x ∈ bag S ↔ x ∈ S := by
  simp [bag]

@[simp] private theorem card_bag [Finite V] (S : Set V) : (bag S).card = S.ncard := by
  simp [bag, Set.ncard_eq_toFinset_card]

end CliqueTreeBanach

end SimpleGraph
