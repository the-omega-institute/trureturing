/- GID: D5/S3/Quantum/Dynamics/ResponseOrderGraphDistance
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/ResponseOrderGraphDistance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The first positive power of a symmetric nonnegative-off-diagonal coupling occurs at graph distance. -/

import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance

open Matrix

def couplingGraph {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ) : SimpleGraph (Fin d) :=
  SimpleGraph.fromRel (fun i j => 0 < H i j)

theorem first_nonzero_power_eq_graph_distance {d : ℕ}
    (H : Matrix (Fin d) (Fin d) ℝ)
    (hsym : ∀ i j, H i j = H j i)
    (hoff : ∀ i j, i ≠ j → 0 ≤ H i j)
    {i j : Fin d} (hne : i ≠ j)
    (hreach : (couplingGraph H).Reachable i j) :
    (∀ n < (couplingGraph H).dist i j, (H ^ n) j i = 0) ∧
      0 < (H ^ (couplingGraph H).dist i j) j i := by
  let G := couplingGraph H
  have hadj_iff : ∀ a b, G.Adj a b ↔ a ≠ b ∧ 0 < H a b := by
    intro a b
    change (SimpleGraph.fromRel (fun x y => 0 < H x y)).Adj a b ↔ _
    rw [SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨hab, h | h⟩
      · exact ⟨hab, h⟩
      · exact ⟨hab, by simpa [hsym b a] using h⟩
    · rintro ⟨hab, h⟩
      exact ⟨hab, Or.inl h⟩
  have hbound : ∀ n (a b : Fin d), (H ^ n) a b ≠ 0 → G.dist a b ≤ n := by
    intro n
    induction n with
    | zero =>
        intro a b hpow
        by_cases hab : a = b
        · subst b
          simp
        · exfalso
          apply hpow
          simp [Matrix.one_apply, hab]
    | succ n ih =>
        intro a b hpow
        rw [pow_succ, Matrix.mul_apply] at hpow
        obtain ⟨c, hc⟩ : ∃ c, (H ^ n) a c * H c b ≠ 0 := by
          by_contra h
          push_neg at h
          exact hpow (Finset.sum_eq_zero fun c _ => h c)
        have hleft : (H ^ n) a c ≠ 0 := by
          intro hz
          apply hc
          simp [hz]
        have hright : H c b ≠ 0 := by
          intro hz
          apply hc
          simp [hz]
        have hdistac := ih a c hleft
        by_cases hcb : c = b
        · subst b
          exact hdistac.trans (Nat.le_succ n)
        · have hpos : 0 < H c b := lt_of_le_of_ne (hoff c b hcb) (Ne.symm hright)
          have hadj : G.Adj c b := (hadj_iff c b).2 ⟨hcb, hpos⟩
          have htri := hadj.reachable.dist_triangle_right a
          have hdistcb : G.dist c b = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
          omega
  have hzero : ∀ n < G.dist i j, (H ^ n) j i = 0 := by
    intro n hn
    by_contra hne'
    have hle := hbound n j i hne'
    have hle' : G.dist i j ≤ n := by simpa [SimpleGraph.dist_comm] using hle
    omega
  have hexact : ∀ n (a b : Fin d), G.Reachable a b → G.dist a b = n → 0 < (H ^ n) a b := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro a b hab hdist
        cases n with
        | zero =>
            have : a = b := hab.dist_eq_zero_iff.mp hdist
            subst b
            simp
        | succ n =>
            rw [pow_succ, Matrix.mul_apply]
            apply Finset.sum_pos'
            · intro c hc
              by_cases hcb : c = b
              · subst c
                have hz : (H ^ n) a b = 0 := by
                  by_contra hne'
                  have hle := hbound n a b hne'
                  omega
                simp [hz]
              · rcases eq_or_ne ((H ^ n) a c) 0 with hzero | hzero
                · simp [hzero]
                · rcases eq_or_ne (H c b) 0 with hHzero | hHzero
                  · simp [hHzero]
                  · have hposH : 0 < H c b :=
                      lt_of_le_of_ne (hoff c b hcb) (Ne.symm hHzero)
                    have hadj : G.Adj c b := (hadj_iff c b).2 ⟨hcb, hposH⟩
                    have hreachac : G.Reachable a c := hab.trans hadj.symm.reachable
                    have hle := hbound n a c hzero
                    have htri := hadj.reachable.dist_triangle_right a
                    have hdistcb : G.dist c b = 1 :=
                      SimpleGraph.dist_eq_one_iff_adj.mpr hadj
                    have hdistac : G.dist a c = n := by omega
                    exact (mul_pos (ih n (Nat.lt_succ_self n) a c hreachac hdistac) hposH).le
            · obtain ⟨p, hp⟩ := hab.exists_walk_length_eq_dist
              have hpne : ¬p.Nil := by
                intro hpnil
                have : G.dist a b = 0 := by simpa [hpnil.eq] using hp
                omega
              have hadj : G.Adj p.penultimate b := p.adj_penultimate hpne
              have hreachac : G.Reachable a p.penultimate := hab.trans hadj.symm.reachable
              have hle : G.dist a p.penultimate ≤ n := by
                have htmp := G.dist_le p.dropLast
                have hplen : p.length = n + 1 := hp.trans hdist
                rw [p.length_dropLast, hplen] at htmp
                simpa using htmp
              have htri := hadj.reachable.dist_triangle_right a
              have hdistcb : G.dist p.penultimate b = 1 :=
                SimpleGraph.dist_eq_one_iff_adj.mpr hadj
              have hdistac : G.dist a p.penultimate = n := by omega
              exact ⟨p.penultimate, Finset.mem_univ _,
                mul_pos (ih n (Nat.lt_succ_self n) a p.penultimate hreachac hdistac) (by
                  exact (hadj_iff p.penultimate b).mp hadj |>.2)⟩
  have hsymm : H.IsSymm := Matrix.IsSymm.ext (fun a b => hsym b a)
  have hpos : 0 < (H ^ G.dist i j) i j := hexact _ i j hreach rfl
  have hpowsym := hsymm.pow (G.dist i j)
  have hpos' : 0 < (H ^ G.dist i j) j i := by
    rw [hpowsym.apply i j]
    exact hpos
  exact ⟨by simpa [G] using hzero, by simpa [G] using hpos'⟩

#print axioms first_nonzero_power_eq_graph_distance

end D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance
