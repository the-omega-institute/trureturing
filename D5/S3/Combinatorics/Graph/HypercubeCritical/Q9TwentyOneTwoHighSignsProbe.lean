import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9TwentyOneTwoHighProbe

/-! The actual signed eight-cycle through an end on each side of the two-root pair. -/

set_option autoImplicit false
noncomputable section

open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced flip)
open private armTypes arm_coordinates flip_direction_unique from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointSquareExclusion
open private diff diff_flip from D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private diff_self from D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointGeometry
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth

/-- An eight-cycle through the two roots labels its core point. Distinct
outward directions force a unique core point, and equal directions fix
the support of the intervening low vertex as well. -/
private lemma two_high_arm_label
    {n : ℕ} {S : Finset (Q n)} (hb : IsBalanced S)
    (v : Fin 8 → (S : Set (Q n))) (hv : Function.Injective v)
    (hAdj : ∀ i, (hypercube n).Adj (v i).val (v (i + 1)).val)
    {a b c u : Fin n}
    (ha : (v 1).val = flip (v 0).val a)
    (hb' : (v 2).val = flip (v 1).val b)
    (hc : (v 3).val = flip (v 2).val c)
    (hu : (v 7).val = flip (v 0).val u) :
    let D := fun i : Fin 8 => diff (v i).val (v 0).val
    (u ≠ c ∧ D 5 = {b, c, u}) ∨
      (u = c ∧ ∃ t : Fin n, t ≠ a ∧ t ≠ b ∧ t ≠ c ∧ D 5 = {a, c, t} ∧ D 6 = {c, t}) := by
  classical
  choose w hw using fun i => adjacent_exists_flip (hAdj i)
  obtain ⟨g, hgi, hg0, hg1, hg2, hwords⟩ := arm_coordinates hb v hv w hw
  have h0 : g 0 = a := by
    rw [← hg0]
    exact flip_direction_unique ((hw 0).symm.trans ha)
  have h1 : g 1 = b := by
    rw [← hg1]
    exact flip_direction_unique ((hw 1).symm.trans hb')
  have h2 : g 2 = c := by
    rw [← hg2]
    exact flip_direction_unique ((hw 2).symm.trans hc)
  let D := fun i : Fin 8 => diff (v i).val (v 0).val
  have huD : D 7 = {u} := by change diff (v 7).val (v 0).val = _; rw [hu, diff_flip, diff_self]; simp
  change armTypes (v 0).val (v 7).val (v 6).val (v 5).val (v 4).val
    (g 0) (g 1) (g 2) (g 3) at hwords
  have h' : armTypes (v 0).val (v 7).val (v 6).val (v 5).val (v 4).val a b c (g 3) := by
    simpa only [h0, h1, h2] using hwords
  unfold armTypes at h'
  have d_ne_a : g 3 ≠ a := h0 ▸ hgi.ne (by decide : (3 : Fin 4) ≠ 0)
  have d_ne_b : g 3 ≠ b := h1 ▸ hgi.ne (by decide : (3 : Fin 4) ≠ 1)
  have d_ne_c : g 3 ≠ c := h2 ▸ hgi.ne (by decide : (3 : Fin 4) ≠ 2)
  rcases h' with ⟨hd, _, hcore, _⟩ | ⟨hd, _, hcore, _⟩ | ⟨hd, hlow, hcore, _⟩
  · have he : u = g 3 := singleton_inj.mp (huD.symm.trans hd)
    exact Or.inl ⟨he ▸ d_ne_c, he ▸ hcore⟩
  · have he : u = g 3 := singleton_inj.mp (huD.symm.trans hd)
    exact Or.inl ⟨he ▸ d_ne_c, he ▸ hcore⟩
  · have he : u = c := singleton_inj.mp (huD.symm.trans hd)
    exact Or.inr ⟨he, g 3, d_ne_a, d_ne_b, d_ne_c, hcore, hlow⟩

#print axioms two_high_arm_label
