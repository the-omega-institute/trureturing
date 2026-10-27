/- GID: D5/S3/Observer/CubicGain/MixedTripleExclusion
   generality: G
   mirror-B: D5/B/S3/Observer/CubicGain/MixedTripleExclusion
   mirror-E: none(waiver:entire-cubic-world-mixed-prefix-exclusion)
   anchors: []
   utility: none
   digest: Full response intersections retain the original complete worlds and chronological mixed prefix. -/

import D5.S3.Observer.Linear.GainRayWordGeometry

set_option autoImplicit false
noncomputable section
open scoped Matrix Classical
namespace D5.S3.Observer.CubicGain.MixedTripleExclusion
open D5.S3.Observer.Linear.GainRay

abbrev World3 := D5.S3.Observer.Linear.GainRay.World 3

/-- The whole response intersection of the current support, at the next original clock. -/
def responseSlice (T : Finset World3) (v : List Bool) (E : Bool) (z : ℝ) : Finset World3 :=
  T.filter (fun W => readAt W (v ++ [E]) (v.length + 1) = z)

/-- Every node has its own stopping guard. Descendants filter the current support. -/
def Losing : ℕ → Finset World3 → List Bool → Prop
  | 0, T, _ => 2 ≤ T.card
  | n + 1, T, v => 2 ≤ T.card ∧ ∀ E : Bool, ∃ z : ℝ,
      Losing n (responseSlice T v E z) (v ++ [E])

private theorem losing_guard (n : ℕ) (T : Finset World3) (v : List Bool)
    (h : Losing n T v) : 2 ≤ T.card := by
  cases n with
  | zero => exact h
  | succ n => exact h.1

private theorem responseSlice_subset (T : Finset World3) (v : List Bool) (E : Bool) (z : ℝ) :
    responseSlice T v E z ⊆ T := Finset.filter_subset _ _

private theorem losing_pair_step (n : ℕ) (T : Finset World3) (v : List Bool)
    (hT : T.card = 2) (h : Losing (n + 1) T v) (E : Bool) :
    ∃ z : ℝ, (∀ W ∈ T, readAt W (v ++ [E]) (v.length + 1) = z) ∧
      Losing n T (v ++ [E]) := by
  obtain ⟨z,hz⟩ := h.2 E
  have he : responseSlice T v E z = T :=
    Finset.eq_of_subset_of_card_le (responseSlice_subset T v E z)
      (by rw [hT]; exact losing_guard n _ _ hz)
  refine ⟨z, ?_, he ▸ hz⟩
  intro W hW
  have hm : W ∈ responseSlice T v E z := he.symm ▸ hW
  exact (Finset.mem_filter.mp hm).2

private theorem losing_pair_suffix (n : ℕ) (T : Finset World3) (v : List Bool)
    (hT : T.card = 2) (h : Losing n T v) (u : List Bool) (hu : u.length ≤ n) :
    Losing (n - u.length) T (v ++ u) ∧
      u ≠ [] → ∀ W ∈ T, ∀ Z ∈ T,
        readAt W (v ++ u) (v.length + u.length) =
          readAt Z (v ++ u) (v.length + u.length) := by
  induction u using List.reverseRecOn generalizing n with
  | nil =>
    constructor
    · simpa using h
    · intro hu0
      exact (hu0 rfl).elim
  | append_singleton u E ih =>
    have hlen : u.length < n := by simpa using hu
    obtain ⟨hprev,_⟩ := ih n h (by omega)
    obtain ⟨k,hk⟩ : ∃ k, n - u.length = k + 1 := ⟨n - u.length - 1, by omega⟩
    rw [hk] at hprev
    obtain ⟨z,hz,hnext⟩ := losing_pair_step k T (v ++ u) hT hprev E
    constructor
    · convert hnext using 1 <;> simp only [List.length_append, List.length_singleton, List.append_assoc] <;> omega
    · intro _ W hW Z hZ
      have hw := hz W hW
      have hz' := hz Z hZ
      simpa [List.append_assoc, List.length_append] using hw.trans hz'.symm

private theorem two_product_equal_trace (S : Mat) (c : ℝ)
    (h : ∀ E F : Bool, Matrix.trace (action F * action E * S) = c) :
    S = !![c,0;0,0] := by
  have hJJ := h true true
  have hJM := h true false
  have hMJ := h false true
  have hMM := h false false
  simp only [action_j_shape, action_m_shape, Matrix.mul_apply, Matrix.trace,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_fin_const] at hJJ hJM hMJ hMM
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> linarith

private theorem three_product_equal_trace (S : Mat) (c : ℝ)
    (h : ∀ E F G : Bool, Matrix.trace (action G * action F * action E * S) = c) :
    S = 0 ∧ c = 0 := by
  have hJJJ := h true true true
  have hJJM := h true true false
  have hJMJ := h true false true
  have hJMM := h true false false
  have hMMJ := h false false true
  simp only [action_j_shape, action_m_shape, Matrix.mul_apply, Matrix.trace,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_fin_const] at hJJJ hJJM hJMJ hJMM hMMJ
  have hzero : S = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> linarith
  exact ⟨hzero, by simpa [hzero] using hJJJ.symm⟩

end D5.S3.Observer.CubicGain.MixedTripleExclusion
