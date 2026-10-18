/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/PathRigidity
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/PathRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed biased zero-prefix masses recover distinct consecutive edges and target separation. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SpinWindowProducts
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
namespace SpinWindow

/-- An integer path's vertices are precisely incident to its edges when it is nonempty. -/
theorem path_vertices_supported (V : Finset ℤ) (L : ℤ) {n : ℕ} (hn : 1 ≤ n)
    (h : ∀ e ∈ pathEdges L n, e ∈ V ∧ e + 1 ∈ V) : pathVertices L n ⊆ V := by
  intro v hv
  have hv' : L ≤ v ∧ v ≤ L + n := by simpa [pathVertices] using hv
  by_cases he : v ≤ L + n - 1
  · exact (h v (by simp [pathEdges]; omega)).1
  · have hm : v - 1 ∈ pathEdges L n := by simp [pathEdges]; omega
    have hp := (h (v - 1) hm).2
    simpa using hp

/-- The required new mass rules out repetition and a vertex-disjoint edge. -/
theorem mass_forces_extension (β : Bias) (V : Finset ℤ) (L e : ℤ) {n : ℕ}
    (hn : 1 ≤ n) (hV : pathVertices L n ⊆ V) (heV : {e, e + 1} ⊆ V)
    (hm : prob β V (zeroEdges (insert e (pathEdges L n))) = β.T (n + 2)) :
    e = L - 1 ∨ e = L + n := by
  rcases integer_edge_trichotomy L e hn with hrep | hext | hsep
  · have hsame := repeated_edge_prob β V L e n hV hrep
    have hlt := β.T_succ_lt (n + 1)
    rw [hm] at hsame
    linarith
  · exact hext
  · have hdis := separated_edge_prob β V L e n hV heV hsep
    obtain ⟨m, hm'⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
    subst n
    have hlt := β.detached_gap_pos m
    rw [hm] at hdis
    have heq : β.T (m + 3) = β.T 2 * β.T (m + 2) := by
      simpa only [Nat.add_assoc] using hdis
    linarith

/-- A finite list is supported together with both endpoints of each queried edge. -/
def SupportsEdges (V : Finset ℤ) (es : List ℤ) : Prop :=
  ∀ e ∈ es, e ∈ V ∧ e + 1 ∈ V

def PrefixMasses (β : Bias) (V : Finset ℤ) (es : List ℤ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → r ≤ es.length →
    prob β V (zeroEdges (es.take r).toFinset) = β.T (r + 1)

/-- Query order is arbitrary: each prefix may extend either endpoint. -/
theorem prefixes_force_consecutive (β : Bias) (V : Finset ℤ) (es : List ℤ)
    (hV : SupportsEdges V es) (hm : PrefixMasses β V es) (hk : 1 ≤ es.length) :
    es.Nodup ∧ ∃ L : ℤ, es.toFinset = pathEdges L es.length := by
  revert hV hm hk
  induction es using List.reverseRecOn with
  | nil => intro _ _ h; simp at h
  | append_singleton es e ih =>
    intro hV hm hk
    by_cases hempty : es = []
    · subst es
      refine ⟨by simp, e, ?_⟩
      simp [pathEdges]
    have hlen : 1 ≤ es.length := List.length_pos_iff.mpr hempty
    have holdV : SupportsEdges V es := fun a ha => hV a (by simp [ha])
    have holdm : PrefixMasses β V es := by
      intro r hr hrk
      have hp := hm r hr (by simp; omega)
      simpa only [List.take_append_of_le_length hrk] using hp
    obtain ⟨hnod, L, hL⟩ := ih holdV holdm hlen
    have hvpath : pathVertices L es.length ⊆ V :=
      path_vertices_supported V L hlen (fun a ha => holdV a (by simpa [← hL] using ha))
    have hev : {e, e + 1} ⊆ V := by
      have hv := hV e (by simp)
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact hv.1
      · exact hv.2
    have hnew : prob β V (zeroEdges (insert e (pathEdges L es.length))) =
        β.T (es.length + 2) := by
      have hp := hm (es ++ [e]).length (by simp) le_rfl
      rw [List.take_length] at hp
      simpa [hL, Nat.add_assoc] using hp
    have hext := mass_forces_extension β V L e hlen hvpath hev hnew
    have hnot : e ∉ es := by
      intro he
      have hmemb : e ∈ pathEdges L es.length := by
        rw [← hL]
        exact List.mem_toFinset.mpr he
      simp only [pathEdges, Finset.mem_Icc] at hmemb
      rcases hext with h | h <;> omega
    refine ⟨by simpa using List.Nodup.concat hnot hnod, ?_⟩
    rcases hext with rfl | rfl
    · refine ⟨L - 1, ?_⟩
      simpa [hL] using extend_left L es.length
    · refine ⟨L, ?_⟩
      simpa [hL] using extend_right L es.length

/-- Both actual target-spin sections exclude a target vertex on the recovered path. -/
theorem joint_masses_force_target_separation (β : Bias) (V : Finset ℤ)
    (es : List ℤ) (q L : ℤ) (hk : 1 ≤ es.length)
    (hV : SupportsEdges V es) (hL : es.toFinset = pathEdges L es.length)
    (htarget : ∀ s : Bool,
      prob β V (zeroEdges es.toFinset ∩ {S | S q = s}) = β.π s * β.T (es.length + 1)) :
    q ∉ pathVertices L es.length := by
  intro hq
  have hvpath : pathVertices L es.length ⊆ V :=
    path_vertices_supported V L hk (fun a ha => hV a (by simpa [← hL] using ha))
  have hp (s : Bool) : (β.π s)^es.length = β.T (es.length + 1) := by
    have ht := htarget s
    rw [hL, target_collision_prob β V L q es.length hvpath hq s, pow_succ] at ht
    have he : (β.π s)^es.length * β.π s = β.T (es.length + 1) * β.π s := by
      simpa [mul_comm] using ht
    exact (mul_right_cancel₀ (ne_of_gt (β.π_pos s))) he
  have hne := β.unequal_powers hk
  apply hne
  exact (hp false).trans (hp true).symm

/-- Prefix and target masses together recover injective consecutive edges detached from q. -/
theorem finite_path_geometry (β : Bias) (V : Finset ℤ) (es : List ℤ) (q : ℤ)
    (hk : 1 ≤ es.length) (hV : SupportsEdges V es) (hm : PrefixMasses β V es)
    (htarget : ∀ s : Bool,
      prob β V (zeroEdges es.toFinset ∩ {S | S q = s}) = β.π s * β.T (es.length + 1)) :
    es.Nodup ∧ ∃ L : ℤ, es.toFinset = pathEdges L es.length ∧
      q ∉ pathVertices L es.length := by
  obtain ⟨hnod, L, hL⟩ := prefixes_force_consecutive β V es hV hm hk
  exact ⟨hnod, L, hL,
    joint_masses_force_target_separation β V es q L hk hV hL htarget⟩

end SpinWindow
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
