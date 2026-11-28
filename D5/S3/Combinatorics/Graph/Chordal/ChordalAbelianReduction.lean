/- GID: D5/S3/Combinatorics/Graph/Chordal/ChordalAbelianReduction
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-exact-strata-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integral and modular cochain reconstruction on chordal graphs. -/

import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.Chordal.GainPotential
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import D5.S3.Combinatorics.Graph.Chordal.ChordalGainReduction

compile_only_with_mathlib

/-! Omega original.

Canonical skew cochains on cotree edges and the integral lifting of short residuals.
-/

namespace SimpleGraph.GainReduction

universe u

variable {V : Type u} {A : Type*} {G T : SimpleGraph V}

/-- The triangle-defect set of a cochain, with zero included for padding. -/
def defects [AddCommGroup A] (G : SimpleGraph V) (g : V → V → A) : Set A :=
  {d | d = 0 ∨ ∃ v w x, G.Adj v w ∧ G.Adj w x ∧ G.Adj v x ∧
    d = g v w + g w x - g v x}

/-- Reconstruction with a uniform budget on the number of triangle defects. -/
def Reconstructs [AddCommGroup A] (G : SimpleGraph V) (g : V → V → A)
    (U : Set A) (k : ℕ) : Prop :=
  ∃ p : V → A, ∀ v w, G.Adj v w → Short U k (g v w - (p w - p v))

/-- A chosen orientation of the edges outside a spanning tree. -/
abbrev CotreeEdge (G T : SimpleGraph V) [LT V] :=
  {e : V × V // e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ ¬ T.Adj e.1 e.2}

/-- The canonical integer cochain in tree gauge, using one coordinate per cotree edge. -/
def canonical [LinearOrder V] (G T : SimpleGraph V) (v w : V) (i : CotreeEdge G T) : ℤ :=
  if (v, w) = i.val then 1 else if (w, v) = i.val then -1 else 0

theorem canonical_rev [LinearOrder V] (v w : V) :
    canonical G T w v = -canonical G T v w := by
  funext i
  have hne : i.val.1 ≠ i.val.2 := ne_of_lt i.property.1
  have hpair : ¬ ((v, w) = i.val ∧ (w, v) = i.val) := by
    rw [Prod.ext_iff, Prod.ext_iff]
    grind
  by_cases h1 : (v, w) = i.val <;> by_cases h2 : (w, v) = i.val
  · exact (hpair ⟨h1, h2⟩).elim
  all_goals simp [canonical, h1, h2]

private theorem canonical_triangle [LinearOrder V] {v w x : V}
    (hvw : v ≠ w) (hwx : w ≠ x) (hvx : v ≠ x) (i : CotreeEdge G T) :
    |canonical G T v w i + canonical G T w x i - canonical G T v x i| ≤ 1 := by
  have hne : i.val.1 ≠ i.val.2 := ne_of_lt i.property.1
  simp only [canonical, Prod.ext_iff]
  split_ifs <;> norm_num <;> grind

private theorem defects_neg [AddCommGroup A] {g : V → V → A}
    (hrev : ∀ v w, G.Adj v w → g w v = -g v w) : ∀ u ∈ defects G g, -u ∈ defects G g := by
  rintro u (rfl | ⟨v, w, x, hvw, hwx, hvx, rfl⟩)
  · exact Or.inl (neg_zero)
  refine Or.inr ⟨x, w, v, hwx.symm, hvw.symm, hvx.symm, ?_⟩
  rw [hrev w x hwx, hrev v w hvw, hrev v x hvx]
  abel

theorem integrate [Finite V] [AddCommGroup A] (hG : G.IsChordal) (g : V → V → A)
    (hrev : ∀ v w, G.Adj v w → g w v = -g v w)
    (htri : ∀ v w x, G.Adj v w → G.Adj w x → G.Adj v x →
      g v w + g w x = g v x) :
    ∃ p : V → A, ∀ v w, G.Adj v w → g v w = p w - p v := by
  obtain ⟨p, hp⟩ := hG.exists_gain_potential (fun v w => Multiplicative.ofAdd (g v w))
    (fun v w h => hrev v w h) (fun v w x hvw hwx hvx => htri v w x hvw hwx hvx)
  exact ⟨fun v => Multiplicative.toAdd (p v), fun v w h => by
    have he := congrArg Multiplicative.toAdd (hp v w h)
    change g v w = -Multiplicative.toAdd (p v) + Multiplicative.toAdd (p w) at he
    rw [sub_eq_add_neg, add_comm]
    exact he⟩

theorem reconstructs_modular_iff_integral [Finite V] [LinearOrder V] (hG : G.IsChordal)
    {k q : ℕ} (hq : 3 * k + 1 < q) :
    Reconstructs G (fun v w => reduce q (canonical G T v w))
      (reduce q '' defects G (canonical G T)) k ↔
    Reconstructs G (canonical G T) (defects G (canonical G T)) k := by
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨r, hrev, hr, htri⟩ := exists_integral_residuals_of_modular_potential
      (canonical G T) (fun v w _ => canonical_rev v w) (defects G (canonical G T))
      (defects_neg fun v w _ => canonical_rev v w)
      (by
        rintro u (rfl | ⟨v, w, x, hvw, hwx, hvx, rfl⟩) i
        · simp
        · exact canonical_triangle hvw.ne hwx.ne hvx.ne i)
      (fun _ _ _ hvw hwx hvx => canonical_triangle hvw.ne hwx.ne hvx.ne) hq p hp
    obtain ⟨p', hp'⟩ := integrate hG (fun v w => canonical G T v w - r v w)
      (fun v w h => by rw [canonical_rev, hrev v w h]; abel)
      (fun v w x hvw hwx hvx => by
        rw [← sub_eq_zero]
        calc
          _ = (canonical G T v w + canonical G T w x - canonical G T v x) -
                (r v w + r w x - r v x) := by abel
          _ = 0 := by rw [htri v w x hvw hwx hvx, sub_self])
    refine ⟨p', fun v w h => ?_⟩
    rw [← hp' v w h, sub_sub_cancel]
    exact hr v w h
  · rintro ⟨p, hp⟩
    refine ⟨fun v => reduce q (p v), fun v w h => ?_⟩
    simpa only [map_sub] using (hp v w h).map (reduce q)

noncomputable def evalCochain [Finite V] [LinearOrder V] [AddCommGroup A]
    (g : V → V → A) : (CotreeEdge G T → ℤ) →+ A := by
  classical
  letI := Fintype.ofFinite (CotreeEdge G T)
  exact
    { toFun := fun z => ∑ i, z i • g i.val.1 i.val.2
      map_zero' := by simp
      map_add' := fun z z' => by simp [add_zsmul, Finset.sum_add_distrib] }

open Classical in
theorem eval_canonical [Finite V] [LinearOrder V] [AddCommGroup A]
    (g : V → V → A) (hrev : ∀ v w, G.Adj v w → g w v = -g v w)
    (hzero : ∀ v w, T.Adj v w → g v w = 0) (v w : V) (h : G.Adj v w) :
    evalCochain (G := G) (T := T) g (canonical G T v w) = g v w := by
  let := Fintype.ofFinite (CotreeEdge G T)
  change (∑ i : CotreeEdge G T, canonical G T v w i • g i.val.1 i.val.2) = _
  by_cases ht : T.Adj v w
  · rw [hzero v w ht]
    apply Finset.sum_eq_zero
    intro i _
    have h1 : (v, w) ≠ i.val := fun he => i.property.2.2 (he ▸ ht)
    have h2 : (w, v) ≠ i.val := fun he => i.property.2.2 (he ▸ ht.symm)
    simp [canonical, h1, h2]
  · rcases lt_or_gt_of_ne h.ne with hlt | hlt
    · let e : CotreeEdge G T := ⟨(v, w), hlt, h, ht⟩
      rw [Finset.sum_eq_single e]
      · simp [e, canonical]
      · intro i _ hi
        have h1 : (v, w) ≠ i.val := fun he => hi (Subtype.ext he.symm)
        have h2 : (w, v) ≠ i.val := fun he => by
          have hi := i.property.1
          rw [← he] at hi
          exact hlt.not_gt hi
        simp [canonical, h1, h2]
      · simp
    · let e : CotreeEdge G T := ⟨(w, v), hlt, h.symm, fun he => ht he.symm⟩
      rw [Finset.sum_eq_single e]
      · have hrv := hrev v w h
        simp [e, canonical, h.ne, hrv]
      · intro i _ hi
        have h1 : (v, w) ≠ i.val := fun he => by
          have hi := i.property.1
          rw [← he] at hi
          exact hlt.not_gt hi
        have h2 : (w, v) ≠ i.val := fun he => hi (Subtype.ext he.symm)
        simp [canonical, h1, h2]
      · simp

end SimpleGraph.GainReduction
