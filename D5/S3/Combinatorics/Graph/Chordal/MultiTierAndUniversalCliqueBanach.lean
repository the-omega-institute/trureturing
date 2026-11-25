/- GID: D5/S3/Combinatorics/Graph/Chordal/MultiTierAndUniversalCliqueBanach
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/MultiTierAndUniversalCliqueBanach
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Predecessor profiles and universal cores give sharper chordal gain bounds. -/

import D5.S3.Combinatorics.Graph.Chordal.TwoStepBFSAndBarycenterObstructions
import D5.S3.Combinatorics.Graph.Chordal.WeightedCliqueBanachPotential
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Set.Card

/-! # Multi-tier and universal-core gain potentials -/

open scoped BigOperators

namespace SimpleGraph

universe u v

namespace MultiTierBanach
open CliqueBoundedBanach (diagonal_zero predecessors)
open WeightedCliqueBanach (average average_add average_bound average_bound_at)

variable {V : Type u} {G : SimpleGraph V}
variable {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

private noncomputable def denominator (k : ℕ) : ℝ := (k : ℝ)^2 - 3 * k + 3
private noncomputable def bottomWeight (k : ℕ) : ℝ := ((k : ℝ) - 3) / denominator k
private noncomputable def middleWeight (k : ℕ) : ℝ := ((k : ℝ) - 2) / denominator k
private noncomputable def profile (k n : ℕ) : ℝ :=
  if n = k then bottomWeight k else if n = k - 1 then middleWeight k
  else if n = 0 then 1 else (n : ℝ)⁻¹
private theorem profile_distributions {k : ℕ} (hk : 4 ≤ k) (P : V → Finset V)
    (hcard : ∀ a, (P a).card ≤ k)
    (hstairs : ∀ a s, ((P a).filter (fun b => s ≤ (P b).card)).Nonempty →
      ((P a).filter (fun b => s ≤ (P b).card)).card + s ≤ k + 1) :
    0 < bottomWeight k ∧ 2 * middleWeight k - bottomWeight k ≤ 1 / 2 ∧
    ∃ w : V → V → ℝ, ∀ a, (P a).Nonempty →
      (∑ b ∈ P a, w a b = 1) ∧
      ∀ b, 0 ≤ w a b ∧ bottomWeight k ≤ w a b ∧
        profile k (P a).card ≤ w a b ∧ 2 * middleWeight k - profile k (P b).card ≤ w a b := by
  classical
  let x := bottomWeight k
  let y := middleWeight k
  let θ := 2 * y
  let D := denominator k
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hD : 0 < D := by dsimp [D, denominator]; nlinarith [sq_nonneg ((k : ℝ) - 4)]
  have hx : 0 < x := div_pos (by linarith) hD
  have hxy : x < y := (div_lt_div_iff_of_pos_right hD).2 (by linarith)
  have hz : θ - x = ((k : ℝ) - 1) / D := by
    dsimp [θ, x, y, bottomWeight, middleWeight, D]
    ring
  have hhalf : θ - x ≤ 1 / 2 := by
    rw [hz, div_le_iff₀ hD]
    dsimp [D, denominator]
    nlinarith [sq_nonneg ((k : ℝ) - 4)]
  let low := ((k : ℝ) - 2)⁻¹
  have hzlow : θ - x < low := by
    have hc : 0 < (k : ℝ) - 2 := by linarith
    rw [hz, show low = 1 / ((k : ℝ) - 2) by simp [low, one_div],
      div_lt_div_iff₀ hD hc]
    dsimp [D, denominator]
    ring_nf
    linarith
  have hsmall {n : ℕ} (hn : n ≤ k - 2) : low ≤ profile k n := by
    rw [profile, ite_eq_right (by omega : n ≠ k), ite_eq_right (by omega : n ≠ k - 1)]
    have hc : (1 : ℝ) ≤ (k : ℝ) - 2 := by linarith
    by_cases h : n = 0
    · rw [ite_eq_left h]
      exact inv_le_one_of_one_le₀ hc
    · rw [ite_eq_right h]
      exact (inv_le_inv₀ (by linarith) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h))).2
        (by
          have h := (Nat.cast_le (α := ℝ)).2 hn
          rwa [Nat.cast_sub (by omega : 2 ≤ k), Nat.cast_ofNat] at h)
  have hfloor {n : ℕ} (hn : n ≤ k) : x ≤ profile k n := by
    by_cases h : n = k
    · simp [profile, h, x]
    by_cases h' : n = k - 1
    · simpa [profile, h', y, show k - 1 ≠ k by omega] using hxy.le
    exact (show x ≤ low by dsimp [θ] at hzlow; linarith).trans (hsmall (by omega))
  have hmiddle : profile k (k - 1) = y := by simp [profile, y, show k - 1 ≠ k by omega]
  have hbottom : profile k k = x := by simp [profile, x]
  let w₀ (a b : V) := max (profile k (P a).card) (θ - profile k (P b).card)
  have hsum (a : V) (ha : (P a).Nonempty) : ∑ b ∈ P a, w₀ a b ≤ 1 := by
    let m := (P a).card
    have hm : 0 < m := ha.card_pos
    have hm' : m ≤ k := hcard a
    let top := (P a).filter (fun b => k ≤ (P b).card)
    let high := (P a).filter (fun b => k - 1 ≤ (P b).card)
    have ht : top.card ≤ 1 := by
      by_cases h : top.Nonempty
      · have hs : top.card + k ≤ k + 1 := hstairs a k h
        omega
      · simp [Finset.not_nonempty_iff_eq_empty.mp h]
    have hh : high.card ≤ 2 := by
      by_cases h : high.Nonempty
      · have hs : high.card + (k - 1) ≤ k + 1 := hstairs a (k - 1) h
        omega
      · simp [Finset.not_nonempty_iff_eq_empty.mp h]
    have bump (s : ℕ) {t : ℝ} (ht : 0 ≤ t) (hc : ((P a).filter (fun b => s ≤ (P b).card)).card ≤ 1) :
        ∑ b ∈ P a, (if s ≤ (P b).card then t else 0) ≤ t := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      simpa using mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc : (_ : ℝ) ≤ ↑(1 : ℕ)) ht
    by_cases hsmallrow : m ≤ k - 2
    · have hw (b : V) : w₀ a b = (m : ℝ)⁻¹ := by
        change max (profile k m) (θ - profile k (P b).card) = _
        rw [max_eq_left ((show θ - profile k (P b).card ≤ θ - x by
          linarith [hfloor (hcard b)]).trans (hzlow.le.trans (hsmall hsmallrow)))]
        rw [profile, ite_eq_right (by omega : m ≠ k), ite_eq_right (by omega : m ≠ k - 1),
          ite_eq_right (by omega : m ≠ 0)]
      simp only [hw, Finset.sum_const, nsmul_eq_mul]
      exact (mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hm.ne')).le
    · have hk1 : (k : ℝ) - 1 = (↑(k - 1) : ℝ) := by rw [Nat.cast_sub (by omega), Nat.cast_one]
      have hrow₁ : ((k : ℝ) - 1) * y + (y - x) = 1 := by
        change ((k : ℝ) - 1) * (((k : ℝ) - 2) / D) +
          (((k : ℝ) - 2) / D - ((k : ℝ) - 3) / D) = 1
        rw [← sub_div, ← mul_div_assoc, ← add_div, div_eq_iff hD.ne']
        dsimp [D, denominator]
        ring
      have hrow₂ : (k : ℝ) * x + 3 * (y - x) = 1 := by
        change (k : ℝ) * (((k : ℝ) - 3) / D) +
          3 * (((k : ℝ) - 2) / D - ((k : ℝ) - 3) / D) = 1
        rw [← sub_div, ← mul_div_assoc, ← mul_div_assoc, ← add_div, div_eq_iff hD.ne']
        dsimp [D, denominator]
        ring
      have hbump : 0 ≤ y - x := sub_nonneg.mpr hxy.le
      have htSum := bump k hbump ht
      by_cases hmiddleRow : m = k - 1
      · have hw (b : V) :
            w₀ a b = y + (if k ≤ (P b).card then y - x else 0) := by
          change max (profile k m) (θ - profile k (P b).card) = _
          rw [hmiddleRow, hmiddle]
          by_cases h : k ≤ (P b).card
          · rw [ite_eq_left h, show (P b).card = k by have := hcard b; omega, hbottom,
              max_eq_right (by dsimp [θ]; linarith)]
            dsimp [θ]
            ring
          · rw [ite_eq_right h, add_zero, max_eq_left]
            have hf : y ≤ profile k (P b).card := by
              by_cases hb : (P b).card = k - 1
              · rw [hb, hmiddle]
              · exact (show y ≤ low by dsimp [θ] at hzlow; linarith).trans
                  (hsmall (by omega))
            dsimp [θ]
            linarith
        simp only [hw, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        change (m : ℝ) * y + _ ≤ 1
        rw [hmiddleRow, ← hk1]
        linarith
      · have hlargeRow : m = k := by omega
        have hhSum : ∑ b ∈ P a, (if k - 1 ≤ (P b).card then y - x else 0) ≤ 2 * (y - x) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hh) hbump
        have hw (b : V) :
            w₀ a b = x + (if k - 1 ≤ (P b).card then y - x else 0) +
              (if k ≤ (P b).card then y - x else 0) := by
          change max (profile k m) (θ - profile k (P b).card) = _
          rw [hlargeRow, hbottom]
          by_cases h : k ≤ (P b).card
          · rw [ite_eq_left h, ite_eq_left (by omega : k - 1 ≤ (P b).card),
              show (P b).card = k by have := hcard b; omega, hbottom,
              max_eq_right (by dsimp [θ]; linarith)]
            dsimp [θ]
            ring
          · rw [ite_eq_right h, add_zero]
            by_cases h' : k - 1 ≤ (P b).card
            · rw [ite_eq_left h', show (P b).card = k - 1 by omega, hmiddle,
                max_eq_right (by dsimp [θ]; linarith)]
              dsimp [θ]
              ring
            · rw [ite_eq_right h', add_zero, max_eq_left]
              linarith [hsmall (n := (P b).card) (by omega)]
        simp only [hw, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        change (m : ℝ) * x + _ + _ ≤ 1
        rw [hlargeRow, ← hrow₂]
        linarith
  let w (a b : V) := w₀ a b + (1 - ∑ c ∈ P a, w₀ a c) / (P a).card
  refine ⟨hx, hhalf, w, fun a ha => ⟨?_, ?_⟩⟩
  · have hm : ((P a).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ha.card_pos.ne'
    simp only [w, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    field_simp [hm]
    <;> ring
  · intro b
    have hb : w₀ a b ≤ w a b :=
      le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr (hsum a ha)) (Nat.cast_nonneg _))
    have hf : profile k (P a).card ≤ w a b := (le_max_left _ _).trans hb
    have hm := (hfloor (hcard a)).trans hf
    exact ⟨hx.le.trans hm, hm, hf, (le_max_right _ _).trans hb⟩

private theorem connected_bound [Finite V] (hG : G.IsChordal) (hconn : G.Connected) (o : V)
    (k : ℕ) (hk : 4 ≤ k)
    (hclique : ∀ s : Finset V, G.IsClique (s : Set V) → s.card ≤ k + 1)
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, g j i = -g i j)
    (htri : ∀ i j l, G.Adj i j → G.Adj j l → G.Adj i l →
      ‖g i j + g j l - g i l‖ ≤ ε) :
    ∃ φ : V → E, ∀ x y, G.Adj x y →
      ‖g x y - (φ y - φ x)‖ ≤ (4 - 4 * ((k : ℝ) - 2) / denominator k) * ε := by
  classical
  let := Fintype.ofFinite V
  let P (x : V) := predecessors G o x
  have memP {b x : V} : b ∈ P x ↔ G.Adj b x ∧ G.dist o b + 1 = G.dist o x := by
    simp [P, predecessors]
  have inhabitedP {x : V} {i : ℕ} (hx : G.dist o x = i + 1) : (P x).Nonempty := by
    obtain ⟨b, hbx, hb⟩ := exists_predecessor hx
    exact ⟨b, memP.mpr ⟨hbx, by omega⟩⟩
  have inShadow {b x : V} {i : ℕ} (hx : G.dist o x = i + 1) (hb : b ∈ P x) :
      b ∈ Shadow G o (componentOf G o (i + 1) x hx.ge) :=
    mem_shadow_of_adj (by have := (memP.mp hb).2; omega) hx.ge (memP.mp hb).1
  choose anchor hAnchor using
    (fun (i : ℕ) (C : Component G o (i + 2)) => exists_shadow_anchor hG hconn C)
  have anchor_parent (i : ℕ) (C : Component G o (i + 2)) := (hAnchor i C).1
  have anchor_adj (i : ℕ) (C : Component G o (i + 2)) := (hAnchor i C).2
  let a : (i : ℕ) → Component G o (i + 1) → V
    | 0, _ => o
    | i + 1, C => anchor i C
  have firstPred {x : V} (hx : G.dist o x = 1) : P x = {o} := by
    obtain ⟨b, hb⟩ := inhabitedP hx
    have root {b : V} (hb : b ∈ P x) : b = o :=
      (hconn.dist_eq_zero_iff.mp (by have := (memP.mp hb).2; omega)).symm
    ext b'
    simp only [Finset.mem_singleton]
    exact ⟨root, fun h => (h.trans (root hb).symm).symm ▸ hb⟩
  have predNear {x : V} {i : ℕ} (hx : G.dist o x = i + 1) {b d : V}
      (hb : b ∈ P x) (hd : d ∈ P x) (hne : b ≠ d) : G.Adj b d :=
    shadow_clique hG hconn _ (inShadow hx hb) (inShadow hx hd) hne
  have cardP {x : V} : (P x).card ≤ k := by
    cases hx : G.dist o x with
    | zero =>
      have he : P x = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun b hb => by
        have := (memP.mp hb).2
        omega
      simp [he]
    | succ i =>
      have hn : x ∉ P x := fun h => (memP.mp h).1.ne rfl
      have hc : G.IsClique (↑(insert x (P x)) : Set V) := by
        intro b hb d hd hbd
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hb hd
        rcases hb with rfl | hb
        · exact (memP.mp (hd.resolve_left hbd.symm)).1.symm
        · rcases hd with rfl | hd
          · exact (memP.mp hb).1
          · exact predNear hx hb hd hbd
      have h := hclique _ hc
      rw [Finset.card_insert_of_notMem hn] at h
      omega
  have nested {x y : V} {i : ℕ} (hx : G.dist o x = i + 1) (hy : G.dist o y = i + 1)
      (hxy : G.Adj x y) : P x ⊆ P y ∨ P y ⊆ P x := by
    by_contra h
    obtain ⟨b, hb, hby⟩ := Finset.not_subset.mp (fun hs => h (Or.inl hs))
    obtain ⟨d, hd, hdx⟩ := Finset.not_subset.mp (fun hs => h (Or.inr hs))
    have hC := componentOf_adj hx.ge hy.ge hxy
    have bs := inShadow hx hb
    have ds := hC.symm ▸ inShadow hy hd
    have hbd := shadow_clique hG hconn _ bs ds (fun e => hby (e.symm ▸ hd))
    have bl := bs.1
    have dl := ds.1
    have hby' : b ≠ y := fun e => by rw [e] at bl; omega
    have hdx' : d ≠ x := fun e => by rw [e] at dl; omega
    rcases four_cycle_diagonal hG (memP.mp hb).1 hxy (memP.mp hd).1.symm
        hbd.symm hby' hdx'.symm with h | h
    · exact hby (memP.mpr ⟨h, by omega⟩)
    · exact hdx (memP.mpr ⟨h.symm, by omega⟩)
  have stairs (v : V) (s : ℕ) (hs : ((P v).filter (fun b => s ≤ (P b).card)).Nonempty) :
      ((P v).filter (fun b => s ≤ (P b).card)).card + s ≤ k + 1 := by
    let S := (P v).filter (fun b => s ≤ (P b).card)
    change S.Nonempty at hs
    obtain ⟨u, hu, hmin⟩ := Finset.exists_min_image S (fun b => (P b).card) hs
    have hu' := Finset.mem_filter.mp hu
    have hv := (memP.mp hu'.1).2
    have hl {b : V} (hb : b ∈ S) : G.dist o b = G.dist o u := by
      have := (memP.mp (Finset.mem_filter.mp hb).1).2
      omega
    have hS {b d : V} (hb : b ∈ S) (hd : d ∈ S) (hne : b ≠ d) : G.Adj b d :=
      predNear hv.symm (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp hd).1 hne
    by_cases hroot : G.dist o u = 0
    · have hzero : (P u).card = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro b hb
        have := (memP.mp hb).2
        omega
      have hcard := cardP (x := v)
      have hsub : S.card ≤ (P v).card := Finset.card_le_card (Finset.filter_subset _ _)
      change S.card + s ≤ k + 1
      omega
    obtain ⟨i, hi⟩ : ∃ i, G.dist o u = i + 1 := ⟨G.dist o u - 1, by omega⟩
    have hsub {b : V} (hb : b ∈ S) : P u ⊆ P b := by
      by_cases h : u = b
      · subst b
        rfl
      rcases nested hi ((hl hb).trans hi) (hS hu hb h) with hin | hin
      · exact hin
      · exact (Finset.eq_of_subset_of_card_le hin (hmin b hb)).ge
    have hdisj : Disjoint (P u) S := Finset.disjoint_left.mpr fun b hp hb => by
      have := (memP.mp hp).2
      have := hl hb
      omega
    have hcl : G.IsClique (↑(P u ∪ S) : Set V) := by
      intro b hb d hd hne
      simp only [Finset.mem_coe, Finset.mem_union] at hb hd
      rcases hb with hb | hb <;> rcases hd with hd | hd
      · exact predNear hi hb hd hne
      · exact (memP.mp (hsub hd hb)).1
      · exact (memP.mp (hsub hb hd)).1.symm
      · exact hS hb hd hne
    have h := hclique _ hcl
    rw [Finset.card_union_of_disjoint hdisj] at h
    change S.card + s ≤ k + 1
    omega
  obtain ⟨_, hhalf, w, hw⟩ := profile_distributions hk P (fun _ => cardP) stairs
  let x₀ := bottomWeight k
  let θ := 2 * middleWeight k
  have wsum {x : V} {i : ℕ} (hx : G.dist o x = i + 1) := (hw x (inhabitedP hx)).1
  have wnonneg {x : V} {i : ℕ} (hx : G.dist o x = i + 1) (b : V) (_ : b ∈ P x) :=
    ((hw x (inhabitedP hx)).2 b).1
  have wmin {x : V} {i : ℕ} (hx : G.dist o x = i + 1) (b : V) :=
    ((hw x (inhabitedP hx)).2 b).2.1
  have near {i : ℕ} {C : Component G o (i + 1)} {b d : V}
      (hb : b ∈ Shadow G o C) (hd : d ∈ Shadow G o C) : b = d ∨ G.Adj b d :=
    (eq_or_ne b d).imp_right (shadow_clique hG hconn C hb hd)
  have anchorNear {i : ℕ} {C : Component G o (i + 1)} {b : V} (hb : b ∈ Shadow G o C) :
      a i C = b ∨ G.Adj (a i C) b := by
    cases i with
    | zero => exact Or.inl (hconn.dist_eq_zero_iff.mp hb.1)
    | succ i => exact Or.inr (anchor_adj i C b hb)
  let tagged (b c : V) := Multiplicative.ofAdd (g b c)
  have gain_eq (b c : V) : gain tagged b c = tagged b c := by
    by_cases h : b = c
    · subst c
      change (if b = b then 1 else tagged b b) = tagged b b
      rw [ite_eq_left rfl]
      change (0 : E) = g b b
      exact (diagonal_zero hrev b).symm
    · exact ite_eq_right h
  have tri {b c d : V} (hbc : b = c ∨ G.Adj b c) (hcd : c = d ∨ G.Adj c d)
      (hbd : b = d ∨ G.Adj b d) : Dist.dist (g b c + g c d) (g b d) ≤ ε := by
    have h := gain_triangle (G := G) (g := tagged) hε (fun i j _ => hrev i j)
      (fun i j l hij hjl hil => by
        change Dist.dist (g i j + g j l) (g i l) ≤ ε
        rw [dist_eq_norm]
        exact htri i j l hij hjl hil) hbc hcd hbd
    simp only [gain_eq] at h
    change Dist.dist (g b c + g c d) (g b d) ≤ ε at h
    exact h
  have two_triangles {b c d e : V} (hbcd : Dist.dist (g b c + g c d) (g b d) ≤ ε)
      (hcde : Dist.dist (g c d + g d e) (g c e) ≤ ε) :
      Dist.dist (g b c + g c e) (g b d + g d e) ≤ 2 * ε :=
    two_triangle_comparisons tagged (a := b) (b := c) (c := d) (d := e) hbcd hcde
  let Q (i : ℕ) (C : Component G o (i + 1)) := (anchorGain tagged a i C).toAdd
  let path (c x b : V) := g c b + g b x
  let atLevel (x : V) : (i : ℕ) → G.dist o x = i → E
    | 0, _ => 0
    | i + 1, hx =>
      let C := componentOf G o (i + 1) x hx.ge
      Q i C + average (P x) (w x) (path (a i C) x)
  let φ (x : V) := atLevel x (G.dist o x) rfl
  have eval (x : V) (i : ℕ) (hx : G.dist o x = i) : φ x = atLevel x i hx := by
    subst i
    rfl
  have atSucc {x : V} {i : ℕ} (hx : G.dist o x = i + 1) :
      let C := componentOf G o (i + 1) x hx.ge
      φ x = Q i C + average (P x) (w x) (path (a i C) x) := eval x (i + 1) hx
  let layerError := (3 - 2 * x₀) * ε
  let bound := (4 - 4 * ((k : ℝ) - 2) / denominator k) * ε
  have crossTotal : (4 - 2 * θ) * ε = bound := by
    dsimp [θ, middleWeight, bound]
    ring
  have layerTotal : layerError ≤ bound := by
    rw [← crossTotal]
    exact mul_le_mul_of_nonneg_right (by dsimp [θ, x₀]; linarith) hε
  have nonnegBound : 0 ≤ bound := by
    rw [← crossTotal]
    have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
    have hden : 0 < denominator k := by
      dsimp [denominator]
      nlinarith [sq_nonneg ((k : ℝ) - 4)]
    have htwo : θ ≤ 2 := by
      dsimp [θ, middleWeight]
      have h : ((k : ℝ) - 2) / denominator k ≤ 1 :=
        (div_le_iff₀ hden).2 (by dsimp [denominator]; nlinarith [sq_nonneg ((k : ℝ) - 4)])
      linarith
    exact mul_nonneg (by linarith) hε
  have across {x y : V} {i : ℕ} (hx : G.dist o x = i) (hy : G.dist o y = i + 1)
      (hxy : G.Adj x y) : Dist.dist (φ x + g x y) (φ y) ≤ bound := by
    cases i with
    | zero =>
      have he := hconn.dist_eq_zero_iff.mp hx
      subst x
      have hs := wsum hy
      rw [firstPred hy, Finset.sum_singleton] at hs
      rw [eval o 0 (by simp), atSucc hy, firstPred hy]
      simpa [atLevel, Q, anchorGain, a, average, hs, path, diagonal_zero hrev] using nonnegBound
    | succ i =>
      let C := componentOf G o (i + 2) y hy.ge
      let D := parent G o C
      let c := a (i + 1) C
      let d := a i D
      have xs : x ∈ Shadow G o C := mem_shadow_of_adj hx hy.ge hxy
      have hD : D = componentOf G o (i + 1) x hx.ge := shadow_parent xs
      have cs : c ∈ Shadow G o D := anchor_parent i C
      have hcx : G.Adj c x := anchor_adj i C x xs
      have cp : c ∈ P x := memP.mpr ⟨hcx, by
        have hc : G.dist o c = i := cs.1
        omega⟩
      have xp : x ∈ P y := memP.mpr ⟨hxy, by omega⟩
      have Qstep : Q (i + 1) C = Q i D + g d c := rfl
      let m := Q (i + 1) C + g c x
      have earlier : Dist.dist (average (P x) (w x) (path d x)) (path d x c) ≤ (2 - 2 * w x c) * ε := by
        have h := average_bound_at (f := path d x) (z := path d x c) cp
          (wnonneg hx) (wsum hx) (A := 0) (B := 2 * ε) (by simp)
        apply (h ?_).trans_eq (by ring)
        intro b hb
        have hb' := (Finset.mem_erase.mp hb).2
        have bs : b ∈ Shadow G o D := hD ▸ inShadow hx hb'
        exact two_triangles (tri (anchorNear bs) (near bs cs) (anchorNear cs))
          (tri (near bs cs) (Or.inr hcx) (Or.inr (memP.mp hb').1))
      have later : Dist.dist (average (P y) (w y) (path c y)) (path c y x) ≤ (2 - 2 * w y x) * ε := by
        have h := average_bound_at (f := path c y) (z := path c y x) xp
          (wnonneg hy) (wsum hy) (A := 0) (B := 2 * ε) (by simp)
        apply (h ?_).trans_eq (by ring)
        intro b hb
        have hb' := (Finset.mem_erase.mp hb).2
        have bs := inShadow hy hb'
        exact two_triangles (tri (anchorNear bs) (near bs xs) (Or.inr hcx))
          (tri (near bs xs) (Or.inr hxy) (Or.inr (memP.mp hb').1))
      have h₁ : Dist.dist (φ x) m ≤ (2 - 2 * w x c) * ε := by
        rw [atSucc hx, ← hD]
        change Dist.dist (Q i D + average (P x) (w x) (path d x)) (Q (i + 1) C + g c x) ≤ _
        rw [Qstep, add_assoc, dist_add_left]
        exact earlier
      have h₂ : Dist.dist (m + g x y) (φ y) ≤ (2 - 2 * w y x) * ε := by
        rw [atSucc hy]
        change Dist.dist ((Q (i + 1) C + g c x) + g x y)
          (Q (i + 1) C + average (P y) (w y) (path c y)) ≤ _
        rwa [add_assoc, dist_add_left, _root_.dist_comm]
      have mass : θ ≤ w x c + w y x := by
        have h₁ := ((hw x (inhabitedP hx)).2 c).2.2.1
        have h₂ := ((hw y (inhabitedP hy)).2 x).2.2.2
        dsimp only [θ]
        linarith
      rw [← crossTotal]
      refine (dist_triangle _ (m + g x y) _).trans
        ((add_le_add (by rwa [dist_add_right] : Dist.dist (φ x + g x y) (m + g x y) ≤
          (2 - 2 * w x c) * ε) h₂).trans ?_)
      nlinarith [mul_le_mul_of_nonneg_right mass hε]
  have symmError (x y : V) :
      Dist.dist (φ y + g y x) (φ x) = Dist.dist (φ x + g x y) (φ y) := by
    rw [hrev x y, ← dist_add_right _ _ (g x y), add_assoc, neg_add_cancel, add_zero]
    exact _root_.dist_comm _ _
  have within {x y : V} {i : ℕ} (hx : G.dist o x = i + 1) (hy : G.dist o y = i + 1)
      (hxy : G.Adj x y) : Dist.dist (φ x + g x y) (φ y) ≤ bound := by
    have oriented {x y : V} (hx : G.dist o x = i + 1) (hy : G.dist o y = i + 1)
        (hxy : G.Adj x y) (hsub : P x ⊆ P y) : Dist.dist (φ x + g x y) (φ y) ≤ layerError := by
      let C := componentOf G o (i + 1) x hx.ge
      let c := a i C
      have hC : C = componentOf G o (i + 1) y hy.ge := componentOf_adj hx.ge hy.ge hxy
      have perPred (b : V) (hb : b ∈ P x) :
          Dist.dist (path c x b + g x y) (average (P y) (w y) (path c y)) ≤ layerError := by
        have hb' := hsub hb
        have bs : b ∈ Shadow G o C := inShadow hx hb
        have diag : Dist.dist (path c x b + g x y) (path c y b) ≤ ε := by
          dsimp only [path]
          rw [add_assoc, dist_add_left]
          exact tri (Or.inr (memP.mp hb).1) (Or.inr hxy) (Or.inr (memP.mp hb').1)
        rw [_root_.dist_comm]
        have h := average_bound_at (f := path c y) (z := path c x b + g x y) hb'
          (wnonneg hy) (wsum hy) (A := ε) (B := 3 * ε) (by rwa [_root_.dist_comm])
        refine (h ?_).trans ?_
        · intro d hd
          have hd' := (Finset.mem_erase.mp hd).2
          have ds : d ∈ Shadow G o C := hC.symm ▸ inShadow hy hd'
          have two : Dist.dist (path c y d) (path c y b) ≤ 2 * ε :=
            two_triangles (tri (anchorNear ds) (near ds bs) (anchorNear bs))
              (tri (near ds bs) (Or.inr (memP.mp hb').1) (Or.inr (memP.mp hd').1))
          exact (dist_triangle _ (path c y b) _).trans
            (by linarith [add_le_add two (by rwa [_root_.dist_comm] : Dist.dist (path c y b) _ ≤ ε)])
        · dsimp [layerError]
          nlinarith [mul_le_mul_of_nonneg_right (wmin hy b) hε]
      rw [atSucc hx, atSucc hy, ← hC]
      change Dist.dist ((Q i C + average (P x) (w x) (path c x)) + g x y)
        (Q i C + average (P y) (w y) (path c y)) ≤ _
      rw [add_assoc, dist_add_left, ← average_add _ _ _ _ (wsum hx)]
      exact average_bound (wnonneg hx) (wsum hx) perPred
    rcases nested hx hy hxy with h | h
    · exact (oriented hx hy hxy h).trans layerTotal
    · rw [← symmError]
      exact (oriented hy hx hxy.symm h).trans layerTotal
  have forward {x y : V} (hxy : G.Adj x y) (h : G.dist o x ≤ G.dist o y) :
      Dist.dist (φ x + g x y) (φ y) ≤ bound := by
    by_cases he : G.dist o x = G.dist o y
    · cases hi : G.dist o x with
      | zero =>
        exact (hxy.ne ((hconn.dist_eq_zero_iff.mp hi).symm.trans
          (hconn.dist_eq_zero_iff.mp (he.symm.trans hi)))).elim
      | succ i => exact within hi (he.symm.trans hi) hxy
    · have hd := hxy.diff_dist_adj (u := o)
      exact across rfl (by omega) hxy
  refine ⟨φ, fun x y hxy => ?_⟩
  calc
    _ = Dist.dist (φ x + g x y) (φ y) := by
      rw [dist_eq_norm]
      congr 1
      abel
    _ ≤ bound := by
      rcases le_total (G.dist o x) (G.dist o y) with h | h
      · exact forward hxy h
      · rw [← symmError]
        exact forward hxy.symm h

end MultiTierBanach

/-- On a finite chordal graph with clique size at most `k + 1`, triangle defects of at most
`ε` give a potential with the multi-tier predecessor error bound on every edge. -/
theorem IsChordal.exists_multitier_clique_banach_gain_potential
    {V : Type u} [Finite V] {G : SimpleGraph V} (hG : G.IsChordal)
    (k : ℕ) (hk : 4 ≤ k)
    (hclique : ∀ s : Finset V, G.IsClique (s : Set V) → s.card ≤ k + 1)
    {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε) (hrev : ∀ i j, g j i = -g i j)
    (htri : ∀ i j l, G.Adj i j → G.Adj j l → G.Adj i l →
      ‖g i j + g j l - g i l‖ ≤ ε) :
    ∃ φ : V → E, ∀ u v, G.Adj u v →
      ‖g u v - (φ v - φ u)‖ ≤
        (4 - 4 * ((k : ℝ) - 2) / ((k : ℝ)^2 - 3 * (k : ℝ) + 3)) * ε := by
  classical
  have hcomp (c : G.ConnectedComponent) :
      ∃ ψ : c → E, ∀ i j, c.toSimpleGraph.Adj i j →
        ‖g i.val j.val - (ψ j - ψ i)‖ ≤
          (4 - 4 * ((k : ℝ) - 2) / ((k : ℝ)^2 - 3 * (k : ℝ) + 3)) * ε := by
    obtain ⟨o, ho⟩ := c.nonempty_supp
    have hc (s : Finset c) (hs : c.toSimpleGraph.IsClique (s : Set c)) : s.card ≤ k + 1 := by
      let e : c ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
      simpa only [Finset.card_map] using hclique (s.map e) (by
        rw [Finset.coe_map]
        exact isClique_induce_iff.mp hs)
    exact MultiTierBanach.connected_bound (hG.induce c.supp) c.connected_toSimpleGraph ⟨o, ho⟩
      k hk hc (fun i j => g i.val j.val) ε hε (fun i j => hrev i.val j.val)
      (fun i j l => htri i.val j.val l.val)
  choose ψ hψ using hcomp
  let φ (i : V) := ψ (G.connectedComponentMk i) ⟨i, ConnectedComponent.connectedComponentMk_mem⟩
  have φ_eq (i : V) (c : G.ConnectedComponent) (hi : G.connectedComponentMk i = c) :
      φ i = ψ c ⟨i, hi⟩ := by
    subst c
    rfl
  refine ⟨φ, fun i j hij => ?_⟩
  have hj := ConnectedComponent.connectedComponentMk_eq_of_adj hij.symm
  rw [φ_eq j _ hj]
  exact hψ (G.connectedComponentMk i) ⟨i, rfl⟩ ⟨j, hj⟩ hij
/-- Averaging over the universal vertices of the core and then over each attachment
clique gives a gain potential on the whole graph. -/
theorem exists_universal_core_simplicial_banach_potential
    {V : Type u} [Finite V] (G : SimpleGraph V) (H U : Set V)
    (_hUH : U ⊆ H) (hU : U.Nonempty)
    (huniv : ∀ u ∈ U, ∀ h ∈ H, u ≠ h → G.Adj u h)
    (hind : G.IsIndepSet Hᶜ) (m : ℕ) (hm : 1 ≤ m)
    (hattach : ∀ o ∉ H, {a : V | G.Adj o a} ⊆ H ∧ G.IsClique {a : V | G.Adj o a} ∧
      {a : V | G.Adj o a}.ncard ≤ m)
    {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε) (hrev : ∀ i j, g j i = -g i j)
    (htri : ∀ i j l, G.Adj i j → G.Adj j l → G.Adj i l →
      ‖g i j + g j l - g i l‖ ≤ ε) :
    ∃ φ : V → E, ∀ u v, G.Adj u v →
      ‖g u v - (φ v - φ u)‖ ≤ max 1 (2 - 2 / (m : ℝ)) * ε := by
  classical
  let anchors := U.toFinite.toFinset
  have anchor_mem {z : V} : z ∈ anchors ↔ z ∈ U := Set.Finite.mem_toFinset _
  have anchors_posR : (0 : ℝ) < anchors.card := by
    obtain ⟨z, hz⟩ := hU
    exact_mod_cast (Finset.card_pos.mpr ⟨z, anchor_mem.mpr hz⟩ : 0 < anchors.card)
  let w : V → ℝ := fun _ => (anchors.card : ℝ)⁻¹
  have wsum : ∑ z ∈ anchors, w z = 1 := by
    simp [w, nsmul_eq_mul, mul_inv_cancel₀ anchors_posR.ne']
  let core (x : V) : E := WeightedCliqueBanach.average anchors w (fun z => g z x)
  have core_bound {a b : V} (ha : a ∈ H) (hb : b ∈ H) (hab : G.Adj a b) :
      ‖core a + g a b - core b‖ ≤ ε := by
    have regroup : core a + g a b - core b =
        WeightedCliqueBanach.average anchors w (fun z => g z a + g a b - g z b) := by
      change WeightedCliqueBanach.average anchors w (fun z => g z a) + g a b -
        WeightedCliqueBanach.average anchors w (fun z => g z b) = _
      rw [← WeightedCliqueBanach.average_add _ _ _ _ wsum]
      simp only [WeightedCliqueBanach.average, smul_sub, Finset.sum_sub_distrib]
    rw [regroup, ← dist_zero_right]
    apply WeightedCliqueBanach.average_bound (fun _ _ => inv_nonneg.mpr anchors_posR.le) wsum
    intro z hz
    rw [dist_zero_right]
    have hzU := anchor_mem.mp hz
    by_cases hza : z = a
    · simpa [hza, CliqueBoundedBanach.diagonal_zero hrev a] using hε
    by_cases hzb : z = b
    · simpa [hzb, hrev a b, CliqueBoundedBanach.diagonal_zero hrev b] using hε
    exact htri z a b (huniv z hzU a ha hza) hab (huniv z hzU b hb hzb)
  let neighbors (o : V) := ({a : V | G.Adj o a} : Set V).toFinite.toFinset
  have mem_neighbors {o a : V} : a ∈ neighbors o ↔ G.Adj o a := Set.Finite.mem_toFinset _
  let candidate (o a : V) := core a + g a o
  let w' (o : V) (_ : V) : ℝ := ((neighbors o).card : ℝ)⁻¹
  let φ (x : V) := if x ∈ H then core x
    else WeightedCliqueBanach.average (neighbors x) (w' x) (candidate x)
  have attach_bound {a o : V} (ho : o ∉ H) (hao : G.Adj a o) :
      ‖φ a + g a o - φ o‖ ≤ max 1 (2 - 2 / (m : ℝ)) * ε := by
    let S := neighbors o
    have haS : a ∈ S := mem_neighbors.mpr hao.symm
    have haH : a ∈ H := (hattach o ho).1 hao.symm
    have hs : (0 : ℝ) < S.card := by exact_mod_cast (Finset.card_pos.mpr ⟨a, haS⟩)
    have hs_le : (S.card : ℝ) ≤ m := by
      have hc : ({b : V | G.Adj o b} : Set V).ncard = S.card := Set.ncard_eq_toFinset_card _
      exact_mod_cast (hc ▸ (hattach o ho).2.2 : S.card ≤ m)
    have sw : ∑ b ∈ S, w' o b = 1 := by
      change (∑ _b ∈ S, (S.card : ℝ)⁻¹) = 1
      simp [nsmul_eq_mul, mul_inv_cancel₀ hs.ne']
    have comparison (b : V) (hb : b ∈ S.erase a) :
        Dist.dist (candidate o b) (candidate o a) ≤ 2 * ε := by
      have hbo : G.Adj b o := (mem_neighbors.mp (Finset.mem_erase.mp hb).2).symm
      have hba := (hattach o ho).2.1 hbo.symm hao.symm (Finset.mem_erase.mp hb).1
      have hbH : b ∈ H := (hattach o ho).1 hbo.symm
      rw [dist_eq_norm, show candidate o b - candidate o a =
          (core b + g b a - core a) - (g b a + g a o - g b o) by dsimp [candidate]; abel]
      exact (norm_sub_le _ _).trans (by linarith [core_bound hbH haH hba, htri b a o hba hao hbo])
    have bound := WeightedCliqueBanach.average_bound_at (f := candidate o) (z := candidate o a)
      (A := 0) (B := 2 * ε) haS (fun _ _ => inv_nonneg.mpr hs.le) sw (by simp) comparison
    have hratio : 2 / (m : ℝ) ≤ 2 / (S.card : ℝ) := by
      have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      rw [div_le_div_iff₀ hmR hs]
      linarith
    simp only [φ, ite_eq_left haH, ite_eq_right ho]
    change ‖candidate o a - WeightedCliqueBanach.average S (w' o) (candidate o)‖ ≤ _
    rw [← dist_eq_norm, _root_.dist_comm]
    refine bound.trans ?_
    change (2 * ε - (2 * ε - 0) * (S.card : ℝ)⁻¹) ≤ _
    rw [show 2 * ε - (2 * ε - 0) * (S.card : ℝ)⁻¹ = (2 - 2 / (S.card : ℝ)) * ε by
      simp only [div_eq_mul_inv]; ring]
    exact mul_le_mul_of_nonneg_right
      ((sub_le_sub_left hratio 2).trans (le_max_right _ _)) hε
  refine ⟨φ, fun a b hab => ?_⟩
  rw [show g a b - (φ b - φ a) = φ a + g a b - φ b by abel]
  by_cases ha : a ∈ H <;> by_cases hb : b ∈ H
  · simp only [φ, ite_eq_left ha, ite_eq_left hb]
    exact (core_bound ha hb hab).trans (le_mul_of_one_le_left hε (le_max_left _ _))
  · exact attach_bound hb hab
  · rw [hrev b a, show φ a + -g b a - φ b = -(φ b + g b a - φ a) by abel, norm_neg]
    exact attach_bound ha hab.symm
  · exact (hind ha hb hab.ne hab).elim

/-- The local potentials on the gadget copies can be translated so that every
bridge is fitted exactly. -/
theorem bridgedGadget_banach_upper_bound
    (m N : ℕ) (hm : 2 ≤ m) (hN : 1 ≤ N)
    {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (g : (Fin N × GadgetVertex m) → (Fin N × GadgetVertex m) → E)
    (ε : ℝ) (hε : 0 ≤ ε) (hrev : ∀ i j, g j i = -g i j)
    (htri : ∀ i j l, (bridgedGadget m N).Adj i j → (bridgedGadget m N).Adj j l →
      (bridgedGadget m N).Adj i l → ‖g i j + g j l - g i l‖ ≤ ε) :
    ∃ φ : (Fin N × GadgetVertex m) → E, ∀ u v, (bridgedGadget m N).Adj u v →
      ‖g u v - (φ v - φ u)‖ ≤ (2 - 2 / (m : ℝ)) * ε := by
  classical
  let C (k : Fin N) := (bridgedGadget m N).comap (fun x => (k, x))
  let H : Set (GadgetVertex m) := {x | x ≠ .root}
  let U : Set (GadgetVertex m) := Set.range GadgetVertex.u
  let A : Set (GadgetVertex m) := Set.range GadgetVertex.a
  have hUH : U ⊆ H := by
    rintro x ⟨i, rfl⟩ h
    cases h
  have hU : U.Nonempty := ⟨.u ⟨0, by omega⟩, _, rfl⟩
  have huniv (k : Fin N) : ∀ u ∈ U, ∀ x ∈ H, u ≠ x → (C k).Adj u x := by
    rintro u ⟨i, rfl⟩ x hx hne
    cases x with
    | root => exact (hx rfl).elim
    | a j => exact Or.inl ⟨rfl, trivial⟩
    | u j => exact Or.inl ⟨rfl, fun hij => hne (congrArg GadgetVertex.u hij)⟩
    | v j => exact Or.inl ⟨rfl, trivial⟩
    | y j => exact Or.inl ⟨rfl, trivial⟩
  have hind (k : Fin N) : (C k).IsIndepSet Hᶜ := by
    intro x hx y hy hne
    have hroot {x : GadgetVertex m} (hx : x ∈ Hᶜ) : x = .root := by simpa [H] using hx
    exact (hne ((hroot hx).trans (hroot hy).symm)).elim
  have root_neighbors (k : Fin N) : {x | (C k).Adj .root x} = A := by
    ext x
    change (C k).Adj .root x ↔ x ∈ A
    constructor
    · rintro (⟨_, hx⟩ | ⟨_, _, hb⟩)
      · cases x with
        | a j => exact ⟨j, rfl⟩
        | root | u _ | v _ | y _ => exact (show False from hx).elim
      · change k.val + 1 = k.val ∨ k.val + 1 = k.val at hb
        omega
    · rintro ⟨j, rfl⟩
      exact Or.inl ⟨rfl, trivial⟩
  have hat (k : Fin N) : ∀ o ∉ H,
      {a | (C k).Adj o a} ⊆ H ∧ (C k).IsClique {a | (C k).Adj o a} ∧
      {a | (C k).Adj o a}.ncard ≤ m := by
    intro o ho
    have hroot : o = .root := by simpa [H] using ho
    subst o
    rw [root_neighbors k]
    refine ⟨?_, ?_, ?_⟩
    · rintro x ⟨j, rfl⟩ h
      cases h
    · rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩ hne
      exact Or.inl ⟨rfl, fun hij => hne (congrArg GadgetVertex.a hij)⟩
    · have hinj : Function.Injective (GadgetVertex.a : Fin m → GadgetVertex m) :=
        fun i j hij => GadgetVertex.a.inj hij
      simp [A, Set.ncard_range_of_injective hinj]
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hcoeff : 1 ≤ 2 - 2 / (m : ℝ) := by
    have hm_pos : (0 : ℝ) < m := by linarith
    have h : 2 / (m : ℝ) ≤ 1 := (div_le_iff₀ hm_pos).2 (by linarith)
    linarith
  have local_bound (k : Fin N) : ∃ p : GadgetVertex m → E, ∀ a b, (C k).Adj a b →
      ‖g (k, a) (k, b) - (p b - p a)‖ ≤ (2 - 2 / (m : ℝ)) * ε := by
    simpa only [max_eq_right hcoeff] using
      exists_universal_core_simplicial_banach_potential (C k) H U hUH hU (huniv k)
        (hind k) m (by omega) (hat k) (fun a b => g (k, a) (k, b)) ε hε
        (fun a b => hrev (k, a) (k, b)) (fun a b c => htri (k, a) (k, b) (k, c))
  choose p hp using local_bound
  let first : Fin N := ⟨0, by omega⟩
  let shift : (j : ℕ) → j < N → E := Nat.rec (motive := fun j => j < N → E)
    (fun _ => p first .root)
    (fun j prev hj => prev (by omega) + g (⟨j, by omega⟩, .root) (⟨j + 1, hj⟩, .root))
  let φ (z : Fin N × GadgetVertex m) :=
    p z.1 z.2 - p z.1 .root + shift z.1.val z.1.isLt
  have root_value (k : Fin N) : φ (k, .root) = shift k.val k.isLt := by simp [φ]
  have bridge_step (k l : Fin N) (hkl : k.val + 1 = l.val) :
      φ (l, .root) - φ (k, .root) = g (k, .root) (l, .root) := by
    rw [root_value, root_value]
    rcases l with ⟨l, hl⟩
    change k.val + 1 = l at hkl
    subst l
    change shift k.val k.isLt + g (k, .root) (⟨k.val + 1, _⟩, .root) -
      shift k.val k.isLt = _
    abel
  refine ⟨φ, ?_⟩
  rintro ⟨k, a⟩ ⟨l, b⟩ (⟨hkl, h⟩ | ⟨rfl, rfl, hb⟩)
  · change k = l at hkl
    subst l
    have same_shift : φ (k, b) - φ (k, a) = p k b - p k a := by
      dsimp [φ]
      abel
    rw [same_shift]
    exact hp k a b (Or.inl ⟨rfl, h⟩)
  · have fitted : φ (l, .root) - φ (k, .root) = g (k, .root) (l, .root) := by
      rcases hb with hkl | hlk
      · exact bridge_step k l hkl
      · rw [hrev (l, .root) (k, .root), ← bridge_step l k hlk, neg_sub]
    rw [fitted, sub_self, norm_zero]
    exact mul_nonneg (by linarith) hε
end SimpleGraph
