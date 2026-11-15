/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeGirth
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeGirth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Short-cycle exclusion for balanced restrictions of Huang's fixed cube signing. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Batteries.Tactic.OpenPrivate

/-! Balanced restrictions use the original FALSE-prefix Huang signing throughout. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube

open D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
  (Q flip gamma IsSwitching IsBalanced)
open private gammaV coeff switching_sq from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open private huangMatrix cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum

private theorem gammaV_anticommute (n : Nat) (i j : Fin n) (hij : i ≠ j)
    (v : Sensitivity.V n) :
    gammaV n i (gammaV n j v) = -gammaV n j (gammaV n i v) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      induction i using Fin.cases with
      | zero =>
          induction j using Fin.cases with
          | zero => exact (hij rfl).elim
          | succ j =>
              apply Prod.ext
              · change -gammaV n j v.2 = -gammaV n j v.2
                rfl
              · change gammaV n j v.1 = -(-gammaV n j v.1)
                simp
      | succ i =>
          induction j using Fin.cases with
          | zero =>
              apply Prod.ext
              · change gammaV n i v.2 = -(-gammaV n i v.2)
                simp
              · change -gammaV n i v.1 = -gammaV n i v.1
                rfl
          | succ j =>
              have h : i ≠ j := fun he => hij (congrArg Fin.succ he)
              apply Prod.ext
              · change gammaV n i (gammaV n j v.1) = -gammaV n j (gammaV n i v.1)
                exact ih i j h v.1
              · change -gammaV n i (-gammaV n j v.2) = -(-gammaV n j (-gammaV n i v.2))
                simpa only [map_neg, neg_neg] using ih i j h v.2

/-- Distinct actual coordinate operators anticommute for the fixed Huang matrix. -/
theorem gamma_anticommute {n : Nat} {i j : Fin n} (hij : i ≠ j)
    (z : Q n → Real) : gamma i (gamma j z) = -gamma j (gamma i z) := by
  change coeff n (gammaV n i ((coeff n).symm
      (coeff n (gammaV n j ((coeff n).symm z))))) =
    -coeff n (gammaV n j ((coeff n).symm
      (coeff n (gammaV n i ((coeff n).symm z)))))
  rw [(coeff n).symm_apply_apply, (coeff n).symm_apply_apply,
    gammaV_anticommute n i j hij, map_neg]

private theorem flip_comm {n : Nat} (x : Q n) (i j : Fin n) :
    flip (flip x i) j = flip (flip x j) i := by
  funext r
  by_cases hri : r = i
  · subst r
    by_cases hij : i = j
    · subst j
      rfl
    · simp [BalancedCriticalSpectrum.flip, hij, Ne.symm hij]
  · by_cases hrj : r = j
    · subst r
      simp [BalancedCriticalSpectrum.flip, hri, Ne.symm hri]
    · simp [BalancedCriticalSpectrum.flip, hri, hrj]

private theorem switching_ne_zero {n : Nat} {C : Finset (Q n)}
    {sigma : Q n → Real} (hs : IsSwitching C sigma) {x : Q n} (hx : x ∈ C) :
    sigma x ≠ 0 := by
  rcases hs.1 x hx with h | h <;> rw [h] <;> norm_num

private theorem gamma_two_switching {n : Nat} {C : Finset (Q n)}
    {sigma : Q n → Real} (hs : IsSwitching C sigma)
    (x : Q n) (i j : Fin n) (hx : x ∈ C) (hxi : flip x i ∈ C)
    (hxij : flip (flip x i) j ∈ C) :
    gamma i (gamma j (fun _ => 1)) x = sigma x * sigma (flip (flip x i) j) := by
  rw [BalancedCriticalSpectrum.gamma_apply, BalancedCriticalSpectrum.gamma_apply, mul_one,
    hs.2 x hx (flip x i) hxi (BalancedCriticalSpectrum.flip_adj x i),
    hs.2 (flip x i) hxi (flip (flip x i) j) hxij (BalancedCriticalSpectrum.flip_adj _ j)]
  calc
    (sigma x * sigma (flip x i)) *
        (sigma (flip x i) * sigma (flip (flip x i) j)) =
      (sigma x * sigma (flip (flip x i) j)) * sigma (flip x i) ^ 2 := by ring
    _ = _ := by rw [switching_sq hs hxi, mul_one]

/-- A balanced selected set contains no coordinate square of the actual cube. -/
theorem no_selected_square {n : Nat} {C : Finset (Q n)} (hC : IsBalanced C)
    {x : Q n} {i j : Fin n} (hij : i ≠ j) (hx : x ∈ C)
    (hxi : flip x i ∈ C) (hxj : flip x j ∈ C) :
    flip (flip x i) j ∉ C := by
  intro hxij
  obtain ⟨sigma, hs⟩ := hC
  have hxji : flip (flip x j) i ∈ C := by
    simpa only [flip_comm x j i] using hxij
  have h := congrFun (gamma_anticommute hij (fun _ => (1 : Real))) x
  simp only [Pi.neg_apply] at h
  rw [gamma_two_switching hs x i j hx hxi hxij,
    gamma_two_switching hs x j i hx hxj hxji, flip_comm x j i] at h
  have hn := mul_ne_zero (switching_ne_zero hs hx) (switching_ne_zero hs hxij)
  apply hn
  linarith

private theorem gamma_three_switching {n : Nat} {C : Finset (Q n)}
    {sigma : Q n → Real} (hs : IsSwitching C sigma)
    (x : Q n) (i j k : Fin n) (hx : x ∈ C) (hxi : flip x i ∈ C)
    (hxij : flip (flip x i) j ∈ C) (hxijk : flip (flip (flip x i) j) k ∈ C) :
    gamma i (gamma j (gamma k (fun _ => 1))) x =
      sigma x * sigma (flip (flip (flip x i) j) k) := by
  rw [BalancedCriticalSpectrum.gamma_apply, BalancedCriticalSpectrum.gamma_apply, BalancedCriticalSpectrum.gamma_apply, mul_one,
    hs.2 x hx (flip x i) hxi (BalancedCriticalSpectrum.flip_adj x i),
    hs.2 (flip x i) hxi (flip (flip x i) j) hxij (BalancedCriticalSpectrum.flip_adj _ j),
    hs.2 (flip (flip x i) j) hxij (flip (flip (flip x i) j) k) hxijk
      (BalancedCriticalSpectrum.flip_adj _ k)]
  calc
    (sigma x * sigma (flip x i)) *
        ((sigma (flip x i) * sigma (flip (flip x i) j)) *
          (sigma (flip (flip x i) j) * sigma (flip (flip (flip x i) j) k))) =
      (sigma x * sigma (flip (flip (flip x i) j) k)) *
        sigma (flip x i) ^ 2 * sigma (flip (flip x i) j) ^ 2 := by ring
    _ = _ := by
      rw [switching_sq hs hxi, switching_sq hs hxij, mul_one, mul_one]

private theorem gamma_reverse_three {n : Nat} {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (z : Q n → Real) :
    gamma i (gamma j (gamma k z)) = -gamma k (gamma j (gamma i z)) := by
  calc
    gamma i (gamma j (gamma k z)) = -gamma j (gamma i (gamma k z)) :=
      gamma_anticommute hij _
    _ = gamma j (gamma k (gamma i z)) := by
      rw [gamma_anticommute hik z, map_neg, neg_neg]
    _ = -gamma k (gamma j (gamma i z)) := gamma_anticommute hjk _

/-- A selected nonbacktracking three-step word has three distinct directions. -/
theorem three_directions_distinct {n : Nat} {C : Finset (Q n)} (hC : IsBalanced C)
    {x : Q n} {i j k : Fin n} (hij : i ≠ j) (_hjk : j ≠ k)
    (hx : x ∈ C) (hxi : flip x i ∈ C) (hxij : flip (flip x i) j ∈ C)
    (hxijk : flip (flip (flip x i) j) k ∈ C) : i ≠ k := by
  intro hik
  subst k
  have he : flip (flip (flip x i) j) i = flip x j := by
    rw [flip_comm (flip x i) j i, BalancedCriticalSpectrum.flip_flip]
  have hxj : flip x j ∈ C := by simpa only [he] using hxijk
  exact no_selected_square hC hij hx hxi hxj hxij

private theorem triple_coord_mem {n : Nat} (x : Q n) {i j k a b c : Fin n}
    (hab : a ≠ b) (hac : a ≠ c)
    (he : flip (flip (flip x i) j) k = flip (flip (flip x a) b) c) :
    a = i ∨ a = j ∨ a = k := by
  by_contra h
  push Not at h
  have hv := congrFun he a
  cases hxa : x a <;>
    simp [BalancedCriticalSpectrum.flip, h.1, h.2.1, h.2.2, hab, hac, hxa] at hv

private theorem no_selected_reverse_three {n : Nat} {C : Finset (Q n)}
    (hC : IsBalanced C) {x : Q n} {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hx : x ∈ C) (hxi : flip x i ∈ C) (hxij : flip (flip x i) j ∈ C)
    (hxijk : flip (flip (flip x i) j) k ∈ C)
    (hxk : flip x k ∈ C) (hxkj : flip (flip x k) j ∈ C)
    (hxkji : flip (flip (flip x k) j) i ∈ C)
    (he : flip (flip (flip x i) j) k = flip (flip (flip x k) j) i) : False := by
  obtain ⟨sigma, hs⟩ := hC
  have h := congrFun (gamma_reverse_three hij hik hjk (fun _ => (1 : Real))) x
  simp only [Pi.neg_apply] at h
  rw [gamma_three_switching hs x i j k hx hxi hxij hxijk,
    gamma_three_switching hs x k j i hx hxk hxkj hxkji, ← he] at h
  have hn := mul_ne_zero (switching_ne_zero hs hx) (switching_ne_zero hs hxijk)
  apply hn
  linarith

/-- Selected nonbacktracking three-step words with the same endpoints have the same
first actual cube direction. All intermediate vertices are required to belong to `C`. -/
theorem three_step_first_direction_eq {n : Nat} {C : Finset (Q n)}
    (hC : IsBalanced C) {x : Q n} {i j k a b c : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hab : a ≠ b) (hbc : b ≠ c)
    (hx : x ∈ C) (hxi : flip x i ∈ C) (hxij : flip (flip x i) j ∈ C)
    (hxijk : flip (flip (flip x i) j) k ∈ C)
    (hxa : flip x a ∈ C) (hxab : flip (flip x a) b ∈ C)
    (hxabc : flip (flip (flip x a) b) c ∈ C)
    (he : flip (flip (flip x i) j) k = flip (flip (flip x a) b) c) : i = a := by
  have hik := three_directions_distinct hC hij hjk hx hxi hxij hxijk
  have hac := three_directions_distinct hC hab hbc hx hxa hxab hxabc
  rcases triple_coord_mem x hab hac he with hai | haj | hak
  · exact hai.symm
  · subst a
    exact (no_selected_square hC hij hx hxi hxa hxij).elim
  · subst a
    rcases triple_coord_mem x hij hik he.symm with hik' | hib | hic
    · exact (hik hik').elim
    · subst b
      have hxik : flip (flip x i) k ∈ C := by
        simpa only [flip_comm x k i] using hxab
      exact (no_selected_square hC hik hx hxi hxa hxik).elim
    · subst c
      have hbj : b = j := by
        by_contra hbj
        have hv := congrFun he j
        cases hxj : x j <;>
          simp [BalancedCriticalSpectrum.flip, Ne.symm hij, hjk, Ne.symm hbj, hxj] at hv
      subst b
      exact (no_selected_reverse_three hC hij hik hjk hx hxi hxij hxijk
        hxa hxab hxabc he).elim

private theorem two_step_first_direction_eq {n : Nat} {C : Finset (Q n)}
    (hC : IsBalanced C) {x : Q n} {i j a b : Fin n}
    (_hij : i ≠ j) (hab : a ≠ b) (hx : x ∈ C)
    (hxi : flip x i ∈ C) (hxij : flip (flip x i) j ∈ C)
    (hxa : flip x a ∈ C)
    (he : flip (flip x i) j = flip (flip x a) b) : i = a := by
  have ha : a = i ∨ a = j := by
    by_contra h
    push Not at h
    have hv := congrFun he a
    cases hxa' : x a <;> simp [BalancedCriticalSpectrum.flip, h.1, h.2, hab, hxa'] at hv
  rcases ha with hai | haj
  · exact hai.symm
  · subst a
    exact (no_selected_square hC _hij hx hxi hxa hxij).elim

private theorem adjacent_exists_flip {n : Nat} {x y : Q n}
    (hxy : (hypercube n).Adj x y) : ∃ i : Fin n, y = flip x i := by
  change (Finset.univ.filter (fun i => x i ≠ y i)).card = 1 at hxy
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hxy
  have hdiff (j : Fin n) : x j ≠ y j ↔ j = i := by
    have hj := Finset.ext_iff.mp hi j
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton] using hj
  refine ⟨i, ?_⟩
  funext j
  by_cases hji : j = i
  · subst j
    have hne := (hdiff i).mpr rfl
    cases hx : x i <;> cases hy : y i <;> simp_all [BalancedCriticalSpectrum.flip]
  · have heq : x j = y j := by
      by_contra hne
      exact hji ((hdiff j).mp hne)
    simpa [BalancedCriticalSpectrum.flip, hji] using heq.symm

/-- The actual induced graph of a balanced cube restriction has no four-cycle. -/
theorem no_four_cycle {n : Nat} {C : Finset (Q n)} (hC : IsBalanced C)
    {u : (C : Set (Q n))}
    (p : ((hypercube n).induce (C : Set (Q n))).Walk u u) (hp : p.IsCycle) :
    p.length ≠ 4 := by
  intro hlen
  let v : Nat → Q n := fun t => (p.getVert t).1
  have hv (t : Nat) : v t ∈ C := (p.getVert t).2
  have hadj (t : Nat) (ht : t < 4) : (hypercube n).Adj (v t) (v (t + 1)) :=
    p.adj_getVert_succ (by omega)
  have hend : v 4 = v 0 := by
    change (p.getVert 4).1 = (p.getVert 0).1
    rw [← hlen, p.getVert_length, p.getVert_zero]
  have hinj {s t : Nat} (hs : s < 4) (ht : t < 4) (he : v s = v t) : s = t := by
    apply hp.getVert_injOn' (by change s ≤ p.length - 1; omega)
      (by change t ≤ p.length - 1; omega)
    exact Subtype.ext he
  obtain ⟨i, hi⟩ := adjacent_exists_flip (hadj 0 (by omega))
  obtain ⟨j, hj⟩ := adjacent_exists_flip (hadj 1 (by omega))
  have h03 : (hypercube n).Adj (v 0) (v 3) := by
    simpa only [hend] using (hadj 3 (by omega)).symm
  obtain ⟨a, ha⟩ := adjacent_exists_flip h03
  obtain ⟨b, hb⟩ := adjacent_exists_flip (hadj 2 (by omega)).symm
  have hij : i ≠ j := by
    intro he
    subst j
    have he20 : v 2 = v 0 := by rw [hj, hi, BalancedCriticalSpectrum.flip_flip]
    have := hinj (by omega : 2 < 4) (by omega : 0 < 4) he20
    omega
  have hab : a ≠ b := by
    intro he
    subst b
    have he20 : v 2 = v 0 := by rw [hb, ha, BalancedCriticalSpectrum.flip_flip]
    have := hinj (by omega : 2 < 4) (by omega : 0 < 4) he20
    omega
  have hword : flip (flip (v 0) i) j = flip (flip (v 0) a) b := by
    rw [← hi, ← hj, ← ha, ← hb]
  have hfirst : i = a := two_step_first_direction_eq hC hij hab (hv 0)
    (by simpa only [hi] using hv 1) (by simpa only [hi, hj] using hv 2)
    (by simpa only [ha] using hv 3) hword
  have he13 : v 1 = v 3 := by rw [hi, ha, hfirst]
  have := hinj (by omega : 1 < 4) (by omega : 3 < 4) he13
  omega

/-- The actual induced graph of a balanced cube restriction has no six-cycle. -/
theorem no_six_cycle {n : Nat} {C : Finset (Q n)} (hC : IsBalanced C)
    {u : (C : Set (Q n))}
    (p : ((hypercube n).induce (C : Set (Q n))).Walk u u) (hp : p.IsCycle) :
    p.length ≠ 6 := by
  intro hlen
  let v : Nat → Q n := fun t => (p.getVert t).1
  have hv (t : Nat) : v t ∈ C := (p.getVert t).2
  have hadj (t : Nat) (ht : t < 6) : (hypercube n).Adj (v t) (v (t + 1)) :=
    p.adj_getVert_succ (by omega)
  have hend : v 6 = v 0 := by
    change (p.getVert 6).1 = (p.getVert 0).1
    rw [← hlen, p.getVert_length, p.getVert_zero]
  have hinj {s t : Nat} (hs : s < 6) (ht : t < 6) (he : v s = v t) : s = t := by
    apply hp.getVert_injOn' (by change s ≤ p.length - 1; omega)
      (by change t ≤ p.length - 1; omega)
    exact Subtype.ext he
  obtain ⟨i, hi⟩ := adjacent_exists_flip (hadj 0 (by omega))
  obtain ⟨j, hj⟩ := adjacent_exists_flip (hadj 1 (by omega))
  obtain ⟨k, hk⟩ := adjacent_exists_flip (hadj 2 (by omega))
  have h05 : (hypercube n).Adj (v 0) (v 5) := by
    simpa only [hend] using (hadj 5 (by omega)).symm
  obtain ⟨a, ha⟩ := adjacent_exists_flip h05
  obtain ⟨b, hb⟩ := adjacent_exists_flip (hadj 4 (by omega)).symm
  obtain ⟨c, hc⟩ := adjacent_exists_flip (hadj 3 (by omega)).symm
  have hij : i ≠ j := by
    intro he
    subst j
    have he20 : v 2 = v 0 := by rw [hj, hi, BalancedCriticalSpectrum.flip_flip]
    have := hinj (by omega : 2 < 6) (by omega : 0 < 6) he20
    omega
  have hjk : j ≠ k := by
    intro he
    subst k
    have he31 : v 3 = v 1 := by rw [hk, hj, BalancedCriticalSpectrum.flip_flip]
    have := hinj (by omega : 3 < 6) (by omega : 1 < 6) he31
    omega
  have hab : a ≠ b := by
    intro he
    subst b
    have he40 : v 4 = v 0 := by rw [hb, ha, BalancedCriticalSpectrum.flip_flip]
    have := hinj (by omega : 4 < 6) (by omega : 0 < 6) he40
    omega
  have hbc : b ≠ c := by
    intro he
    subst c
    have he35 : v 3 = v 5 := by rw [hc, hb, BalancedCriticalSpectrum.flip_flip]
    have := hinj (by omega : 3 < 6) (by omega : 5 < 6) he35
    omega
  have hword : flip (flip (flip (v 0) i) j) k =
      flip (flip (flip (v 0) a) b) c := by
    rw [← hi, ← hj, ← hk, ← ha, ← hb, ← hc]
  have hfirst : i = a := three_step_first_direction_eq hC hij hjk hab hbc (hv 0)
    (by simpa only [hi] using hv 1)
    (by simpa only [hi, hj] using hv 2)
    (by simpa only [hi, hj, hk] using hv 3)
    (by simpa only [ha] using hv 5)
    (by simpa only [ha, hb] using hv 4)
    (by simpa only [ha, hb, hc] using hv 3) hword
  have he15 : v 1 = v 5 := by rw [hi, ha, hfirst]
  have := hinj (by omega : 1 < 6) (by omega : 5 < 6) he15
  omega

private def selectedColoring {n : Nat} (C : Finset (Q n)) :
    ((hypercube n).induce (C : Set (Q n))).Coloring Bool :=
  SimpleGraph.Coloring.mk (fun x => cubeParity x.1) (fun hxy => cubeParity_ne_of_adj hxy)

/-- Every balanced restriction of the original Huang signing has extended girth at
least eight, including the empty and acyclic restrictions. -/
theorem eight_le_egirth {n : Nat} (C : Finset (Q n)) (hC : IsBalanced C) :
    8 ≤ ((hypercube n).induce (C : Set (Q n))).egirth := by
  apply SimpleGraph.le_egirth.mpr
  intro u p hp
  have heven : Even p.length :=
    ((selectedColoring C).even_length_iff_congr p).mpr Iff.rfl
  have hthree := hp.three_le_length
  have hfour := no_four_cycle hC p hp
  have hsix := no_six_cycle hC p hp
  have hlen : 8 ≤ p.length := by
    obtain ⟨k, hk⟩ := heven
    omega
  exact_mod_cast hlen

end D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
