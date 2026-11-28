/- GID: D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2CaratheodoryBounds
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2CaratheodoryBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Caratheodory caps bound round unit-quaternion gains globally at clique cutoffs five and six. -/

import D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalSU2SharpBounds
import D5.S3.Geometry.SU2CaratheodoryRadius
import D5.S3.Geometry.SU2FivePointCover

compile_only_with_mathlib

/-! # Caratheodory bounds for round unit-quaternion gains

The arbitrary finite-family cap estimate controls all chordal graphs up to
`arccos (1/6)/2`. Matching it with the existing hemisphere fit or the
five-point cap gives global coefficients at clique cutoffs five and six.
-/

open scoped Quaternion InnerProductSpace

noncomputable section

namespace SimpleGraph

open Omega.Geometry.UnitQuaternion
open Omega.Geometry.HolonomySpectrum
open Omega.Geometry.SU2Caratheodory
open Real

local notation "U" => unitary ℍ[ℝ]

variable {V : Type*} {G : SimpleGraph V}

set_option maxHeartbeats 2000000 in
private theorem fits_of_bfs_centers [Finite V] (hG : G.IsChordal) (hconn : G.Connected)
    (o : V) {g : V → V → U} (hskew : G.SU2Skew g) {δ r R : ℝ} (hδ : 0 ≤ δ)
    (htri : G.SU2TriangleBound g δ) (hR : 0 ≤ R) (hr : 2 * R ≤ r)
    (center : ∀ (I : Finset V) (_ : I.Nonempty) (q : I → U),
      (∀ i j, i ≠ j → roundDist (q i) (q j) ≤ 2 * δ) → Nonempty (SU2Cap q R))
    (same : ∀ (I J : Finset V) (q : I → U) (v : J → U)
      (e : I → J) (u : U) (C : SU2Cap q R) (D : SU2Cap v R),
      (∀ i, roundDist (q i * u) (v (e i)) ≤ δ) →
      roundDist (C.center * u) D.center ≤ r) :
    ∃ p : V → U, G.SU2Fits g p r := by
  classical
  let := Fintype.ofFinite V
  let γ := gain g
  have hg {x y : V} (h : G.Adj x y) : γ x y = g x y := gain_adj g h
  have hg₀ (x : V) : γ x x = 1 := by simp [γ, gain]
  have hrev {x y : V} (h : x = y ∨ G.Adj x y) : γ y x = (γ x y)⁻¹ := by
    rcases h with rfl | h
    · simp [hg₀]
    · rw [hg h, hg h.symm]
      exact hskew _ _ h
  have tri {x y z : V} (hxy : x = y ∨ G.Adj x y) (hyz : y = z ∨ G.Adj y z)
      (hxz : x = z ∨ G.Adj x z) : roundDist (γ x y * γ y z) (γ x z) ≤ δ := by
    rcases hxy with rfl | hxy
    · simp [hg₀, hδ]
    rcases hyz with rfl | hyz
    · simp [hg₀, hδ]
    rcases hxz with rfl | hxz
    · simp [hg₀, hrev (Or.inr hxy), hδ]
    · simpa only [hg hxy, hg hyz, hg hxz] using htri _ _ _ hxy hyz hxz
  have near {k : ℕ} {C : Component G o (k + 1)} {x y : V}
      (hx : x ∈ Shadow G o C) (hy : y ∈ Shadow G o C) : x = y ∨ G.Adj x y :=
    (eq_or_ne x y).imp_right (shadow_clique hG hconn C hx hy)
  choose anchor anchor_parent anchor_adj using
    (fun (k : ℕ) (C : Component G o (k + 2)) => exists_shadow_anchor hG hconn C)
  let a : (k : ℕ) → Component G o (k + 1) → V
    | 0, _ => o
    | k + 1, C => anchor k C
  have a_adj {k : ℕ} {C : Component G o (k + 1)} {x : V} (hx : x ∈ Shadow G o C) :
      a k C = x ∨ G.Adj (a k C) x := by
    cases k with
    | zero => exact Or.inl (hconn.dist_eq_zero_iff.mp hx.1)
    | succ k => exact Or.inr (anchor_adj k C x hx)
  let parents (k : ℕ) (x : V) := Finset.univ.filter (fun y => G.dist o y = k ∧ G.Adj y x)
  have memP {k : ℕ} {x y : V} : y ∈ parents k x ↔ G.dist o y = k ∧ G.Adj y x := by
    simp [parents]
  have Pnon {k : ℕ} {x : V} (hx : G.dist o x = k + 1) : (parents k x).Nonempty := by
    obtain ⟨y, hy, hk⟩ := exists_predecessor hx
    exact ⟨y, memP.mpr ⟨hk, hy⟩⟩
  have Pshadow {k : ℕ} {x : V} (hx : G.dist o x = k + 1) (i : parents k x) :
      (i : V) ∈ Shadow G o (componentOf G o (k + 1) x hx.ge) :=
    mem_shadow_of_adj (memP.mp i.property).1 hx.ge (memP.mp i.property).2
  let P (k : ℕ) (x : V) (hx : G.dist o x = k + 1) (i : parents k x) : U :=
    γ (a k (componentOf G o (k + 1) x hx.ge)) i * γ i x
  have Pdiam (k : ℕ) (x : V) (hx : G.dist o x = k + 1)
      (i j : parents k x) (_ : i ≠ j) : roundDist (P k x hx i) (P k x hx j) ≤ 2 * δ := by
    let A := a k (componentOf G o (k + 1) x hx.ge)
    have h₁ : roundDist (γ A i * γ i x) ((γ A i * γ i j) * γ j x) ≤ δ := by
      rw [mul_assoc, round_mul_left, round_comm]
      exact tri (near (Pshadow hx i) (Pshadow hx j))
        (Or.inr (memP.mp j.property).2) (Or.inr (memP.mp i.property).2)
    have h₂ : roundDist ((γ A i * γ i j) * γ j x) (γ A j * γ j x) ≤ δ := by
      rw [round_mul_right]
      exact tri (a_adj (Pshadow hx i)) (near (Pshadow hx i) (Pshadow hx j)) (a_adj (Pshadow hx j))
    exact (round_triangle _ _ _).trans (by linarith)
  let D (k : ℕ) (x : V) (hx : G.dist o x = k + 1) : SU2Cap (P k x hx) R :=
    (center (parents k x) (Pnon hx) (P k x hx) (Pdiam k x hx)).some
  let Q := anchorGain γ a
  let atLevel (x : V) : (k : ℕ) → G.dist o x = k → U
    | 0, _ => 1
    | k + 1, hx => Q k (componentOf G o (k + 1) x hx.ge) * (D k x hx).center
  let p (x : V) := atLevel x (G.dist o x) rfl
  have pat (x : V) (k : ℕ) (hx : G.dist o x = k) : p x = atLevel x k hx := by
    subst k
    rfl
  have peval {k : ℕ} {x : V} (hx : G.dist o x = k + 1) :
      p x = Q k (componentOf G o (k + 1) x hx.ge) * (D k x hx).center := pat x _ hx
  have across {x y : V} {k : ℕ} (hx : G.dist o x = k) (hy : G.dist o y = k + 1)
      (hxy : G.Adj x y) : roundDist (p x * γ x y) (p y) ≤ r := by
    cases k with
    | zero =>
      have hroot : o = x := hconn.dist_eq_zero_iff.mp hx
      subst x
      have hp0 : p o = 1 := pat o 0 (by simp)
      rw [hp0, peval hy]
      simpa only [one_mul, Q, anchorGain, P, a, hg₀] using
        ((D 0 y hy).radius ⟨o, memP.mpr ⟨hx, hxy⟩⟩).trans (by linarith)
    | succ k =>
      let C := componentOf G o (k + 2) y hy.ge
      let i : parents (k + 1) y := ⟨x, memP.mpr ⟨hx, hxy⟩⟩
      have hs := Pshadow hy i
      have hc := shadow_parent hs
      have ha := anchor_parent k C
      have hadj := anchor_adj k C x hs
      let j : parents k x := ⟨anchor k C, memP.mpr ⟨ha.1, hadj⟩⟩
      have hm := (D k x hx).radius j
      have hn := (D (k + 1) y hy).radius i
      have hm' : roundDist (Q (k + 1) C * γ (a (k + 1) C) x) (p x) ≤ R := by
        rw [peval hx, ← hc]
        change roundDist
          ((Q k (parent G o C) * γ (a k (parent G o C)) (anchor k C)) * γ (anchor k C) x)
          (Q k (parent G o C) * (D k x hx).center) ≤ R
        rw [mul_assoc, round_mul_left, hc]
        exact hm
      have hn' : roundDist ((Q (k + 1) C * γ (a (k + 1) C) x) * γ x y) (p y) ≤ R := by
        rw [peval hy, mul_assoc, round_mul_left]
        exact hn
      have hm'' : roundDist (p x * γ x y) ((Q (k + 1) C * γ (a (k + 1) C) x) * γ x y) ≤ R := by
        rw [round_mul_right, round_comm]
        exact hm'
      exact (round_triangle _ _ _).trans ((add_le_add hm'' hn').trans (by linarith only [hr]))
  have within {x y : V} {k : ℕ} (hx : G.dist o x = k + 1) (hy : G.dist o y = k + 1)
      (hxy : G.Adj x y) : roundDist (p x * γ x y) (p y) ≤ r := by
    have hc := componentOf_adj hx.ge hy.ge hxy
    have hnest : parents k x ⊆ parents k y ∨ parents k y ⊆ parents k x := by
      by_contra h
      obtain ⟨i, hi, hiy⟩ := Finset.not_subset.mp (fun hn => h (Or.inl hn))
      obtain ⟨j, hj, hjx⟩ := Finset.not_subset.mp (fun hn => h (Or.inr hn))
      have hij : i ≠ j := fun he => hiy (he.symm ▸ hj)
      have hi' := Pshadow hx (⟨i, hi⟩ : parents k x)
      have hj' := Pshadow hy (⟨j, hj⟩ : parents k y)
      rw [← hc] at hj'
      have hij' := shadow_clique hG hconn _ hi' hj' hij
      have hxi := (memP.mp hi).2
      have hyj := (memP.mp hj).2
      rcases four_cycle_diagonal hG hxi hxy hyj.symm hij'.symm
        (by intro he; have := (memP.mp hi).1; rw [he] at this; omega)
        (by intro he; have := (memP.mp hj).1; rw [← he] at this; omega) with h | h
      · exact hiy (memP.mpr ⟨(memP.mp hi).1, h⟩)
      · exact hjx (memP.mpr ⟨(memP.mp hj).1, h.symm⟩)
    have hforward {x y : V} (hx : G.dist o x = k + 1) (hy : G.dist o y = k + 1)
        (hxy : G.Adj x y) (hs : parents k x ⊆ parents k y) :
        roundDist (p x * γ x y) (p y) ≤ r := by
      let e (i : parents k x) : parents k y := ⟨i, hs i.property⟩
      have hc := componentOf_adj hx.ge hy.ge hxy
      have hpairs (i : parents k x) :
          roundDist ((P k x hx) i * γ x y) ((P k y hy) (e i)) ≤ δ := by
        change roundDist ((γ (a k _) i * γ i x) * γ x y) (γ (a k _) i * γ i y) ≤ δ
        rw [← hc, mul_assoc, round_mul_left]
        exact tri (Or.inr (memP.mp i.property).2) (Or.inr hxy) (Or.inr (memP.mp (e i).property).2)
      rw [peval hx, peval hy, hc, mul_assoc, round_mul_left]
      exact same _ _ _ _ e _ _ _ hpairs
    rcases hnest with hs | hs
    · exact hforward hx hy hxy hs
    · have h := hforward hy hx hxy.symm hs
      rw [hrev (Or.inr hxy), ← round_mul_right (γ x y), mul_assoc, inv_mul_cancel, mul_one] at h
      simpa only [round_comm] using h
  have hfit {x y : V} (hxy : G.Adj x y) (hord : G.dist o x ≤ G.dist o y) :
      roundDist (p x * γ x y) (p y) ≤ r := by
    by_cases heq : G.dist o x = G.dist o y
    · by_cases hz : G.dist o x = 0
      · have hx : o = x := hconn.dist_eq_zero_iff.mp hz
        have hy : o = y := hconn.dist_eq_zero_iff.mp (heq.symm.trans hz)
        exact (hxy.ne (hx.symm.trans hy)).elim
      · exact within (k := G.dist o x - 1) (by omega) (by omega) hxy
    · exact across rfl (by have := hxy.diff_dist_adj (u := o); omega) hxy
  refine ⟨p, fun x y hxy => ?_⟩
  rw [round_edge, ← hg hxy]
  rcases le_total (G.dist o x) (G.dist o y) with h | h
  · exact hfit hxy h
  · have hs := hfit hxy.symm h
    rw [hrev (Or.inr hxy), ← round_mul_right (γ x y), mul_assoc, inv_mul_cancel, mul_one] at hs
    simpa only [round_comm] using hs

private theorem connected_caratheodory_fit [Finite V] (hG : G.IsChordal)
    (hconn : G.Connected) {g : V → V → U} (hskew : G.SU2Skew g)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδπ : δ ≤ π / 2)
    (ht : sin δ ^ 2 ≤ 5 / 12) (htri : G.SU2TriangleBound g δ) :
    ∃ p : V → U, G.SU2Fits g p (2 * Omega.Geometry.SU2Caratheodory.radius δ) := by
  classical
  obtain ⟨o⟩ := hconn.nonempty
  apply fits_of_bfs_centers hG hconn o hskew hδ htri
    (Omega.Geometry.SU2Caratheodory.radius_facts hδ hδπ ht).1 le_rfl
  · intro I hI q hpair
    let : Nonempty I := ⟨⟨hI.choose, hI.choose_spec⟩⟩
    exact Omega.Geometry.SU2Caratheodory.exists_radius_cap q hδ hδπ ht hpair
  · intro I J q v e u C D hp
    exact Omega.Geometry.SU2Caratheodory.same_layer hδ hδπ ht C D e u hp

/-- The Caratheodory small-defect estimate applies to every finite chordal
graph, without a clique bound or a connectedness hypothesis. -/
theorem IsChordal.exists_su2_gain_potential_caratheodory [Finite V] (hG : G.IsChordal)
    {g : V → V → U} (hskew : G.SU2Skew g) {δ : ℝ} (hδ : 0 ≤ δ)
    (hδmax : δ ≤ arcsin (√(5 / 12 : ℝ))) (htri : G.SU2TriangleBound g δ) :
    ∃ p : V → U, G.SU2Fits g p
      (2 * arcsin (√(3 / 2 : ℝ) * sin δ)) := by
  classical
  rw [← cutoffSix_eq_arcsin] at hδmax
  have hδπ : δ ≤ π / 2 := hδmax.trans cutoffSix_facts.2.1
  have ht : sin δ ^ 2 ≤ 5 / 12 :=
    (sin_sq_mono hδ hδmax cutoffSix_facts.2.1).trans_eq cutoffSix_facts.2.2.1
  have hcomp (c : G.ConnectedComponent) :
      ∃ p : c → U, c.toSimpleGraph.SU2Fits (fun a b => g a b) p
        (2 * Omega.Geometry.SU2Caratheodory.radius δ) := by
    exact connected_caratheodory_fit (hG.induce c.supp) c.connected_toSimpleGraph
      (fun a b h => hskew a b h) hδ hδπ ht (fun a b c hab hbc hac => htri a b c hab hbc hac)
  choose p hp using hcomp
  let φ (i : V) := p (G.connectedComponentMk i) ⟨i, ConnectedComponent.connectedComponentMk_mem⟩
  have φ_eq (i : V) (c : G.ConnectedComponent) (hi : G.connectedComponentMk i = c) :
      φ i = p c ⟨i, hi ▸ ConnectedComponent.connectedComponentMk_mem⟩ := by subst c; rfl
  refine ⟨φ, fun x y hxy => ?_⟩
  have hy := ConnectedComponent.connectedComponentMk_eq_of_adj hxy.symm
  rw [φ_eq y _ hy]
  exact hp (G.connectedComponentMk x) ⟨x, ConnectedComponent.connectedComponentMk_mem⟩
    ⟨y, hy ▸ ConnectedComponent.connectedComponentMk_mem⟩ hxy

/-- Five arbitrary insertion candidates have cap radius `arccos (-1/4)`;
reverse simplicial elimination extends this to the clique-six stratum. -/
theorem IsChordal.exists_cliqueSix_su2_gain_potential_cap [Finite V] (hG : G.IsChordal)
    {g : V → V → U} (hskew : G.SU2Skew g)
    (hclique : ∀ S : Finset V, G.IsClique (↑S : Set V) → S.card ≤ 6) :
    ∃ p : V → U, G.SU2Fits g p (arccos (-(1 / 4 : ℝ))) := by
  classical
  let := Fintype.ofFinite V
  let r := arccos (-(1 / 4 : ℝ))
  have hmain (S : Finset V) : ∃ p : V → U, ∀ x ∈ S, ∀ y ∈ S,
      G.Adj x y → roundDist (p x * g x y) (p y) ≤ r := by
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      by_cases hs : S.Nonempty
      · let : Nonempty (↑S : Set V) := ⟨⟨hs.choose, hs.choose_spec⟩⟩
        obtain ⟨z, hz⟩ := (hG.induce (S : Set V)).exists_isSimplicial
        let a : V := z.val
        have ha : a ∈ S := z.property
        obtain ⟨p, hp⟩ := ih (S.erase a) (Finset.erase_ssubset ha)
        let N := S.filter fun x => G.Adj x a
        have memN {x : V} : x ∈ N ↔ x ∈ S ∧ G.Adj x a := Finset.mem_filter
        have hN (x) (hx : x ∈ N) : G.Adj x a := (memN.mp hx).2
        have haN : a ∉ N := fun h => (hN a h).ne rfl
        have hcl : G.IsClique (↑N : Set V) := by
          intro x hx y hy hne
          exact hz (show (⟨x, (memN.mp hx).1⟩ : (S : Set V)) ∈ _ from (hN x hx).symm)
            (show (⟨y, (memN.mp hy).1⟩ : (S : Set V)) ∈ _ from (hN y hy).symm)
            (by simpa [Subtype.ext_iff] using hne)
        have hcard : N.card ≤ 5 := by
          have h := hclique (insert a N) (by
            intro x hx y hy hxy
            simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
            rcases hx with rfl | hx
            · exact (hN y (hy.resolve_left hxy.symm)).symm
            · rcases hy with rfl | hy
              · exact hN x hx
              · exact hcl hx hy hxy)
          rw [Finset.card_insert_of_notMem haN] at h
          omega
        have hc : ∃ c : U, ∀ x ∈ N, roundDist (p x * g x a) c ≤ r := by
          by_cases hnon : N.Nonempty
          · let : Nonempty N := ⟨⟨hnon.choose, hnon.choose_spec⟩⟩
            obtain ⟨c, hc⟩ := exists_center_card_le_five (fun i : N => p i * g i a)
              (by simpa only [Fintype.card_coe] using hcard)
            exact ⟨c, fun x hx => hc ⟨x, hx⟩⟩
          · exact ⟨1, fun x hx => (hnon ⟨x, hx⟩).elim⟩
        obtain ⟨c, hc⟩ := hc
        let p' (x : V) := if x = a then c else p x
        have hnew (x) (hx : x ∈ N) : roundDist (p' x * g x a) (p' a) ≤ r := by
          simpa [p', (hN x hx).ne] using hc x hx
        refine ⟨p', fun x hx y hy hxy => ?_⟩
        by_cases hxa : x = a
        · subst x
          rw [hskew y a hxy.symm, ← round_mul_right (g y a)]
          simp only [mul_assoc, inv_mul_cancel, mul_one]
          rw [round_comm]
          exact hnew y (memN.mpr ⟨hy, hxy.symm⟩)
        · by_cases hya : y = a
          · subst y
            exact hnew x (memN.mpr ⟨hx, hxy⟩)
          · simpa [p', hxa, hya] using
              hp x (Finset.mem_erase.mpr ⟨hxa, hx⟩) y (Finset.mem_erase.mpr ⟨hya, hy⟩) hxy
      · exact ⟨fun _ => 1, fun x hx => (hs ⟨x, hx⟩).elim⟩
  obtain ⟨p, hp⟩ := hmain Finset.univ
  exact ⟨p, fun x y hxy => (round_edge _ _ _).trans_le
    (hp x (Finset.mem_univ _) y (Finset.mem_univ _) hxy)⟩

/-- Matching the Caratheodory estimate with the public hemisphere fit gives
the global clique-five coefficient `π / arccos (1/3)`. -/
theorem IsChordal.exists_cliqueFive_su2_gain_potential_caratheodory [Finite V]
    (hG : G.IsChordal) {g : V → V → U} (hskew : G.SU2Skew g) {δ : ℝ} (hδ : 0 ≤ δ)
    (htri : G.SU2TriangleBound g δ)
    (hclique : ∀ S : Finset V, G.IsClique (↑S : Set V) → S.card ≤ 5) :
    ∃ p : V → U, G.SU2Fits g p ((π / arccos (1 / 3 : ℝ)) * δ) := by
  obtain ⟨hb, hbπ, ht, hR⟩ := cutoffFive_facts
  have hcoeff : 2 * (radius cutoffFive / cutoffFive) = π / arccos (1 / 3 : ℝ) := by
    rw [show radius cutoffFive = π / 4 by linarith]
    unfold cutoffFive
    ring
  by_cases hsmall : δ ≤ cutoffFive
  · have hmax : δ ≤ arccos (1 / 6 : ℝ) / 2 := by
      have h := arccos_le_arccos (by norm_num : (1 / 6 : ℝ) ≤ 1 / 3)
      unfold cutoffFive at hsmall
      linarith
    obtain ⟨p, hp⟩ := hG.exists_su2_gain_potential_caratheodory hskew hδ
      (by rw [← cutoffSix_eq_arcsin]; exact hmax) htri
    have hs := radius_le_secant hb hbπ (by rw [ht]; norm_num) hδ hsmall
    refine ⟨p, fun x y hxy => (hp x y hxy).trans ?_⟩
    change 2 * radius δ ≤ _
    rw [← hcoeff]
    nlinarith only [hs]
  · obtain ⟨p, hp⟩ := hG.exists_cliqueFive_su2_gain_potential_half_pi hskew hclique
    have hlarge : cutoffFive ≤ δ := le_of_not_ge hsmall
    have hc : 0 ≤ π / arccos (1 / 3 : ℝ) := div_nonneg pi_pos.le (arccos_nonneg _)
    have he : (π / arccos (1 / 3 : ℝ)) * cutoffFive = π / 2 := by
      unfold cutoffFive
      field_simp [(arccos_pos.2 (by norm_num : (1 / 3 : ℝ) < 1)).ne']
      exact div_self (arccos_pos.2 (by norm_num : (1 / 3 : ℝ) < 1)).ne'
    exact ⟨p, fun x y hxy => (hp x y hxy).trans
      (he.symm.trans_le (mul_le_mul_of_nonneg_left hlarge hc))⟩

/-- Matching at `δ = arccos (1/6)/2` gives the global clique-six coefficient
`2 * arccos (-1/4) / arccos (1/6)`. -/
theorem IsChordal.exists_cliqueSix_su2_gain_potential_caratheodory [Finite V]
    (hG : G.IsChordal) {g : V → V → U} (hskew : G.SU2Skew g) {δ : ℝ} (hδ : 0 ≤ δ)
    (htri : G.SU2TriangleBound g δ)
    (hclique : ∀ S : Finset V, G.IsClique (↑S : Set V) → S.card ≤ 6) :
    ∃ p : V → U, G.SU2Fits g p
      ((2 * arccos (-(1 / 4 : ℝ)) / arccos (1 / 6 : ℝ)) * δ) := by
  obtain ⟨hb, hbπ, ht, hR⟩ := cutoffSix_facts
  have hcoeff : 2 * (radius cutoffSix / cutoffSix) =
      2 * arccos (-(1 / 4 : ℝ)) / arccos (1 / 6 : ℝ) := by
    rw [show radius cutoffSix = arccos (-(1 / 4 : ℝ)) / 2 by linarith]
    unfold cutoffSix
    ring
  by_cases hsmall : δ ≤ cutoffSix
  · obtain ⟨p, hp⟩ := hG.exists_su2_gain_potential_caratheodory hskew hδ
      (by rw [← cutoffSix_eq_arcsin]; exact hsmall) htri
    have hs := radius_le_secant hb hbπ ht.le hδ hsmall
    refine ⟨p, fun x y hxy => (hp x y hxy).trans ?_⟩
    change 2 * radius δ ≤ _
    rw [← hcoeff]
    nlinarith only [hs]
  · obtain ⟨p, hp⟩ := hG.exists_cliqueSix_su2_gain_potential_cap hskew hclique
    have hlarge : cutoffSix ≤ δ := le_of_not_ge hsmall
    have hc : 0 ≤ 2 * arccos (-(1 / 4 : ℝ)) / arccos (1 / 6 : ℝ) :=
      div_nonneg (mul_nonneg (by norm_num) (arccos_nonneg _)) (arccos_nonneg _)
    have he : (2 * arccos (-(1 / 4 : ℝ)) / arccos (1 / 6 : ℝ)) * cutoffSix =
        arccos (-(1 / 4 : ℝ)) := by
      unfold cutoffSix
      field_simp [(arccos_pos.2 (by norm_num : (1 / 6 : ℝ) < 1)).ne']
      exact mul_div_cancel_right₀ _ (arccos_pos.2 (by norm_num : (1 / 6 : ℝ) < 1)).ne'
    exact ⟨p, fun x y hxy => (hp x y hxy).trans
      (he.symm.trans_le (mul_le_mul_of_nonneg_left hlarge hc))⟩

end SimpleGraph
