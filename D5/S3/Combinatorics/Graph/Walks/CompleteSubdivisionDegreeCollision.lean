/- GID: D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionDegreeCollision
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/CompleteSubdivisionDegreeCollision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Order.BigOperators.Group.Finset]
   utility: none
   digest: Equal augmented selected degrees force actual edge-profile collisions. -/
import D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionSelection
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionDegreeCollision

open D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionMetric
open D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionProfiles
open D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionCounting
open D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionSelection

variable {n : ℕ}

private theorem different_bits_collision (S : Finset (Vertex n)) (u x : Fin n)
    (hux : u ≠ x) (hu : originalBit S u = 0) (hx : originalBit S x = 1)
    (hd : selectedDegree S u = selectedDegree S x + 1) : ¬ Resolves S := by
  classical
  have ex : ∃ v, u ≠ v ∧ x ≠ v ∧ pairBit S x v < pairBit S u v := by
    by_contra! h
    have pointwise (v : Fin n) :
        pairBit S u v ≤ pairBit S x (Equiv.swap u x v) := by
      by_cases hvu : v = u
      · subst v; simp [pairBit]
      by_cases hvx : v = x
      · subst v
        rw [Equiv.swap_apply_right, pairBit_symm S u x]
      · rw [Equiv.swap_apply_of_ne_of_ne hvu hvx]
        exact h v (Ne.symm hvu) (Ne.symm hvx)
    have hle := Finset.sum_le_sum (s := Finset.univ) (fun v _ => pointwise v)
    rw [Equiv.sum_comp (Equiv.swap u x) (pairBit S x)] at hle
    rw [← selectedDegree_eq_sum_pairBit, ← selectedDegree_eq_sum_pairBit] at hle
    omega
  obtain ⟨v, huv, hxv, hv⟩ := ex
  have hbu : pairBit S u v = 1 := by
    have := pairBit_binary S u v
    have := pairBit_binary S x v
    omega
  have hbx : pairBit S x v = 0 := by
    have := pairBit_binary S u v
    have := pairBit_binary S x v
    omega
  have bu : midpointBit S (subdivisionVertex u v huv) = 1 := by
    simpa [pairBit, huv] using hbu
  have bx : midpointBit S (subdivisionVertex x v hxv) = 0 := by
    simpa [pairBit, hxv] using hbx
  have H := histogram S u v huv
  have K := histogram S x v hxv
  dsimp only at H K
  have eqprof : profile S (incidence u v huv) = profile S (incidence x v hxv) := by
    apply profile_eq_of_histogram
    intro i
    fin_cases i <;> dsimp <;> omega
  intro hresolve
  have eqedge := hresolve (incidence_mem u v huv) (incidence_mem x v hxv) eqprof
  exact hux ((incidence_eq_iff u v x v huv hxv).mp eqedge).1

theorem resolving_augmented_injective (S : Finset (Vertex n)) (hresolve : Resolves S) :
    Function.Injective (fun u => selectedDegree S u + originalBit S u) := by
  classical
  intro u x hr
  change selectedDegree S u + originalBit S u = selectedDegree S x + originalBit S x at hr
  by_contra hux
  by_cases ha : originalBit S u = originalBit S x
  · have hd : selectedDegree S u = selectedDegree S x := by omega
    have H := histogram S u x hux
    have K := histogram S x u (Ne.symm hux)
    dsimp only at H K
    have hb := midpointBit_swap S u x hux
    have eqprof : profile S (incidence u x hux) = profile S (incidence x u (Ne.symm hux)) := by
      apply profile_eq_of_histogram
      intro i
      fin_cases i <;> dsimp <;> omega
    have eqedge := hresolve (incidence_mem u x hux) (incidence_mem x u (Ne.symm hux)) eqprof
    exact hux ((incidence_eq_iff u x x u hux (Ne.symm hux)).mp eqedge).1
  · have au : originalBit S u = 0 ∨ originalBit S u = 1 := by
      unfold originalBit; split_ifs <;> simp
    have ax : originalBit S x = 0 ∨ originalBit S x = 1 := by
      unfold originalBit; split_ifs <;> simp
    rcases au with hu | hu <;> rcases ax with hx | hx
    · exact ha (hu.trans hx.symm)
    · exact different_bits_collision S u x hux hu hx (by omega) hresolve
    · exact different_bits_collision S x u (Ne.symm hux) hx hu (by omega) hresolve
    · exact ha (hu.trans hx.symm)

theorem resolving_rows_injective (S : Finset (Vertex n)) (hresolve : Resolves S) :
    Function.Injective (fun u => ∑ v, selection S u v) := by
  intro u x hr
  apply resolving_augmented_injective S hresolve
  change selectedDegree S u + originalBit S u = selectedDegree S x + originalBit S x
  rw [← selection_row, ← selection_row]
  exact_mod_cast hr

end D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionDegreeCollision
