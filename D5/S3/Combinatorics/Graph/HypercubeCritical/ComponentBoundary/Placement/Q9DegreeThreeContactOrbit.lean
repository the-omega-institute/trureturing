/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DegreeThreeContactOrbit
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DegreeThreeContactOrbit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: A cubic contact axis forces a simultaneous translation of both endpoints. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCenter

/-! The forced coordinate translations for the edges of a cubic mask graph. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DegreeThreeContactOrbit

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced flip flip_adj)
open BalancedCubeComponentBoundary (directions mem_directions exterior_even)
open BalancedCubeGirth (adjacent_exists_flip flip_comm)
open Q9IsotropicHuang (parity weightedLinear)
open Q9MinimumDistanceOperator
  (RidgeActiveAxis RidgeContact minimum_distance_contact_has_companion minimumDisplacements wordParity)
open private differingAxes parity_flip mem_minimumDisplacements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private differingAxes_right_inj from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactComplement
open private diff_pair from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactStar

open private row_contact minimumDisplacements_swap_two from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCenter

private theorem contact_mask {C D : Finset (Q 9)} {b : Bool} {i j : Fin 9} {x : Q 9}
    (h : RidgeContact C D b [i] j x) : ({i, j} : Finset (Fin 9)) ∈
      minimumDisplacements C D b 2 := by
  have hij : i ≠ j := fun he => h.1 (by simp [he])
  have hdiff := diff_pair x hij
  have hd : hammingDist x (flip (flip x i) j) = 2 := by
    change (differingAxes x (flip (flip x i) j)).card = 2
    rw [hdiff, card_pair hij]
  exact mem_minimumDisplacements.mpr ⟨x, h.2.1, _, h.2.2.2, h.2.2.1, hd, hdiff⟩

/-- At an edge of a degree-three mask vertex, the other two partners generate
a translation preserving the whole fiber of realized contacts of that edge. -/
theorem translated_contact_of_three_partners
    {C D : Finset (Q 9)} {b : Bool} {i j p q : Fin 9} {x : Q 9}
    (hpq : p ≠ q)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hpartners : ∀ k, ({i, k} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2 →
      k = j ∨ k = p ∨ k = q)
    (f g : Q 9 → ℝ)
    (hf : ∀ z, f z ≠ 0 ↔ z ∈ C ∧ parity z = b)
    (hg : ∀ z, g z ≠ 0 ↔ z ∈ D ∧ parity z = b)
    (hAf : ∀ z ∉ C, weightedLinear (fun k => if k = j then 2 else 1) f z = 0)
    (hAg : ∀ z ∉ D, weightedLinear (fun _ => 1) g z = 0)
    (hx : RidgeContact C D b [i] j x) :
    RidgeContact C D b [i] j (flip (flip x p) q) := by
  have hg' : ∀ z, g z ≠ 0 ↔ z ∈ D ∧ parity z = !(wordParity [i] b) := by
    simpa [wordParity] using hg
  obtain ⟨y, hyx, hy, hagree⟩ :=
    minimum_distance_contact_has_companion (ridge := [i]) (by simp) hsep f g hf hg'
      hAf hAg hx
  have hsub : differingAxes x y ⊆ ({p, q} : Finset (Fin 9)) := by
    intro k hk
    have hbits : x k ≠ y k := (mem_filter.mp hk).2
    have hactive : RidgeActiveAxis C D b [i] k ∧ k ≠ j := by
      by_contra hn
      exact hbits (hagree k hn).symm
    obtain ⟨v, hv⟩ := hactive.1
    rcases hpartners k (contact_mask hv) with he | he | he
    · exact False.elim (hactive.2 he)
    · simp [he]
    · simp [he]
  have hcap := card_le_card hsub
  rw [card_pair hpq] at hcap
  have hzero : (differingAxes x y).card ≠ 0 := fun he =>
    hyx (hammingDist_eq_zero.mp he).symm
  have hone : (differingAxes x y).card ≠ 1 := by
    intro he
    obtain ⟨k, hk⟩ := adjacent_exists_flip (show (hypercube 9).Adj x y from he)
    have hpar : b = !b := by
      calc
        b = parity y := hy.2.2.1.symm
        _ = parity (flip x k) := congrArg parity hk
        _ = !b := by rw [parity_flip, hx.2.2.1]
    cases b <;> cases hpar
  have hfull : differingAxes x y = ({p, q} : Finset (Fin 9)) := by
    apply eq_of_subset_of_card_le hsub
    rw [card_pair hpq]
    omega
  have he : y = flip (flip x p) q :=
    differingAxes_right_inj (hfull.trans (diff_pair x hpq).symm)
  exact he ▸ hy

open Classical in
/-- The midpoint of a contact has exactly two neighbors on one support if
the opposite mask axis has at most three partners. -/
theorem exterior_midpoint_directions
    {C D : Finset (Q 9)} {b : Bool} {x : Q 9} {i j : Fin 9} {A : Finset (Fin 9)}
    (hA : A.card ≤ 3)
    (hpartners : ∀ k, ({j, k} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2 → k ∈ A)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hp : parity x = b)
    (hx : x ∈ C) (hy : flip (flip x i) j ∈ D) :
    directions C (flip x i) ⊆ A ∧ (directions C (flip x i)).card = 2 := by
  let z := flip x i
  change flip z j ∈ D at hy
  have hz : z ∉ C := by
    intro hzC
    have h := hsep z hzC (flip z j) hy
    have hd : hammingDist z (flip z j) = 1 := flip_adj z j
    omega
  have hsub : directions C z ⊆ A := by
    intro k hk
    have hC := (mem_directions C z k).mp hk
    have hkj : k ≠ j := by
      intro h
      subst k
      have hbad := hsep (flip z j) hC (flip z j) hy
      simpa using hbad
    have hpar : parity (flip z k) = b := by
      dsimp only [z]
      rw [parity_flip, parity_flip, Bool.not_not, hp]
    have hm := row_contact hC hy hkj hpar
    rw [Finset.pair_comm] at hm
    exact hpartners k hm
  have hpos : 0 < (directions C z).card := card_pos.mpr ⟨i,
    (mem_directions C z i).mpr (by simpa only [z, BalancedCriticalSpectrum.flip_flip] using hx)⟩
  have hbound := (card_le_card hsub).trans hA
  obtain ⟨n, hn⟩ := exterior_even C hr hb z hz
  change directions C z ⊆ A ∧ (directions C z).card = 2
  exact ⟨hsub, by omega⟩

open Classical in
/-- A two-edge walk through a mask edge whose endpoints have degree three
can be closed into a four-cycle, using another partner of the second axis. -/
theorem three_partner_contact_completes_square
    {C D : Finset (Q 9)} {b : Bool} {x : Q 9} {i j p q : Fin 9}
    {B : Finset (Fin 9)}
    (hiP : i ≠ p) (hjP : j ≠ p) (hpq : p ≠ q)
    (hB : B.card ≤ 3)
    (hiPart : ∀ k, ({i, k} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2 →
      k = j ∨ k = p ∨ k = q)
    (hjPart : ∀ k, ({j, k} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2 → k ∈ B)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (f g : Q 9 → ℝ)
    (hf : ∀ z, f z ≠ 0 ↔ z ∈ C ∧ parity z = b)
    (hg : ∀ z, g z ≠ 0 ↔ z ∈ D ∧ parity z = b)
    (hAf : ∀ z ∉ C, weightedLinear (fun k => if k = j then 2 else 1) f z = 0)
    (hAg : ∀ z ∉ D, weightedLinear (fun _ => 1) g z = 0)
    (hx : RidgeContact C D b [i] j x) :
    ∃ r ∈ B, r ≠ i ∧ r ≠ j ∧ r ≠ p ∧
      ({j, r} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2 ∧
      ({p, r} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2 := by
  have get_other (u : Q 9) (hu : RidgeContact C D b [i] j u) :
      ∃ t, t ≠ j ∧ (t = p ∨ t = q) ∧ flip (flip u i) t ∈ D := by
    let y := flip (flip u i) j
    have hy : y ∈ D := hu.2.2.2
    have hp : parity y = b := by
      simp only [y, parity_flip, Bool.not_not, hu.2.2.1]
    have hr : flip (flip y j) i ∈ C := by
      simpa only [y, BalancedCriticalSpectrum.flip_flip] using hu.2.1
    have hpartners (k : Fin 9)
        (hk : ({i, k} : Finset (Fin 9)) ∈ minimumDisplacements D C b 2) :
        k ∈ ({j, p, q} : Finset (Fin 9)) := by
      rw [minimumDisplacements_swap_two D C b] at hk
      rcases hiPart k hk with he | he | he <;> simp [he]
    have hcard : ({j, p, q} : Finset (Fin 9)).card ≤ 3 := by
      calc
        _ ≤ 1 + ({p, q} : Finset (Fin 9)).card := by
          simpa [Nat.add_comm] using
            (Finset.card_insert_le (s := ({p, q} : Finset (Fin 9))) (a := j))
        _ = 3 := by rw [card_pair hpq]
    have ⟨hsub, hc⟩ := exterior_midpoint_directions hcard hpartners
      (fun v hv u hu => by rw [hammingDist_comm]; exact hsep u hu v hv) hrD hbD hp hy hr
    obtain ⟨t, ht, htj⟩ := exists_mem_ne (by rw [hc]; decide) j
    refine ⟨t, htj, ?_, ?_⟩
    · simpa [htj] using hsub ht
    · simpa only [y, BalancedCriticalSpectrum.flip_flip] using (mem_directions D (flip y j) t).mp ht
  obtain ⟨t, _, ht, hD⟩ := get_other x hx
  have chosen : ∃ u, RidgeContact C D b [i] j u ∧ flip (flip u i) p ∈ D := by
    rcases ht with ht | ht
    · exact ⟨x, hx, ht ▸ hD⟩
    · rw [ht] at hD
      refine ⟨flip (flip x p) q,
        translated_contact_of_three_partners hpq hsep hiPart f g hf hg hAf hAg hx, ?_⟩
      rw [flip_comm (flip (flip x p) q) i p, flip_comm (flip x p) q p,
        BalancedCriticalSpectrum.flip_flip]
      exact flip_comm x q i ▸ hD
  obtain ⟨u, hu, hup⟩ := chosen
  let z := flip u i
  have hD' : flip z j ∈ D := hu.2.2.2
  obtain ⟨hsub, hc⟩ :=
    exterior_midpoint_directions hB hjPart hsep hrC hbC hu.2.2.1 hu.2.1 hD'
  obtain ⟨r, hr, hri⟩ := exists_mem_ne (by rw [hc]; decide) i
  have hCr := (mem_directions C z r).mp hr
  have different {k : Fin 9} (hk : flip z k ∈ D) : r ≠ k := by
    intro h
    subst k
    simpa using hsep (flip z r) hCr (flip z r) hk
  have hp : parity (flip z r) = b := by
    simp only [z, parity_flip, Bool.not_not, hu.2.2.1]
  refine ⟨r, hsub hr, hri, different hD', different hup, ?_, ?_⟩
  · rw [Finset.pair_comm]
    exact row_contact hCr hD' (different hD') hp
  · rw [Finset.pair_comm]
    exact row_contact hCr hup (different hup) hp

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DegreeThreeContactOrbit
