/- GID: D5/S3/Combinatorics/Graph/Chordal/WeightedCliqueBanachPotential
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/WeightedCliqueBanachPotential
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Biased predecessor averaging improves the clique-bounded chordal gain estimate. -/

import D5.S3.Combinatorics.Graph.Chordal.CliqueBoundedBanachPotential
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Module.BigOperators

/-! # Biased predecessor averaging on chordal graphs

A predecessor clique has at most one saturated vertex. Increasing that vertex's
weight balances the two cross-layer error estimates.
-/

open scoped BigOperators

namespace SimpleGraph
namespace WeightedCliqueBanach

universe u v

variable {V : Type u} {G : SimpleGraph V} {o : V}
variable {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

open CliqueBoundedBanach (diagonal_zero predecessors)

private noncomputable def average (s : Finset V) (w : V → ℝ) (f : V → E) : E :=
  ∑ b ∈ s, w b • f b

private theorem average_add (s : Finset V) (w : V → ℝ) (f : V → E) (z : E)
    (hw : ∑ b ∈ s, w b = 1) :
    average s w (fun b => f b + z) = average s w f + z := by
  simp only [average, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hw, one_smul]

private theorem dist_average_le (s : Finset V) (w : V → ℝ) (f : V → E) (z : E)
    (hn : ∀ b ∈ s, 0 ≤ w b) (hw : ∑ b ∈ s, w b = 1) :
    Dist.dist (average s w f) z ≤ ∑ b ∈ s, w b * Dist.dist (f b) z := by
  rw [dist_eq_norm, sub_eq_add_neg, ← average_add s w f (-z) hw]
  apply (norm_sum_le s _).trans_eq
  apply Finset.sum_congr rfl
  intro b hb
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hn b hb), dist_eq_norm, sub_eq_add_neg]

private theorem average_bound {s : Finset V} {w : V → ℝ} {f : V → E} {z : E} {B : ℝ}
    (hn : ∀ b ∈ s, 0 ≤ w b) (hw : ∑ b ∈ s, w b = 1)
    (h : ∀ b ∈ s, Dist.dist (f b) z ≤ B) : Dist.dist (average s w f) z ≤ B := by
  calc
    _ ≤ ∑ b ∈ s, w b * Dist.dist (f b) z := dist_average_le s w f z hn hw
    _ ≤ ∑ b ∈ s, w b * B := Finset.sum_le_sum fun b hb =>
      mul_le_mul_of_nonneg_left (h b hb) (hn b hb)
    _ = B := by rw [← Finset.sum_mul, hw, one_mul]

private theorem average_bound_at [DecidableEq V] {s : Finset V} {w : V → ℝ} {f : V → E}
    {z : E} {a : V} {A B : ℝ} (ha : a ∈ s)
    (hn : ∀ b ∈ s, 0 ≤ w b) (hw : ∑ b ∈ s, w b = 1)
    (hsmall : Dist.dist (f a) z ≤ A)
    (hlarge : ∀ b ∈ s.erase a, Dist.dist (f b) z ≤ B) :
    Dist.dist (average s w f) z ≤ B - (B - A) * w a := by
  have hsum : ∑ b ∈ s.erase a, w b = 1 - w a := by
    have h := s.sum_erase_add w ha
    linarith
  calc
    _ ≤ ∑ b ∈ s, w b * Dist.dist (f b) z := dist_average_le s w f z hn hw
    _ = (∑ b ∈ s.erase a, w b * Dist.dist (f b) z) + w a * Dist.dist (f a) z :=
      (s.sum_erase_add _ ha).symm
    _ ≤ (∑ b ∈ s.erase a, w b * B) + w a * A := add_le_add
      (Finset.sum_le_sum fun b hb =>
        mul_le_mul_of_nonneg_left (hlarge b hb) (hn b (Finset.mem_erase.mp hb).2))
      (mul_le_mul_of_nonneg_left hsmall (hn a ha))
    _ = B - (B - A) * w a := by rw [← Finset.sum_mul, hsum]; ring

private noncomputable def bias (k : ℕ) : ℝ :=
  ((k : ℝ) - 2) / ((k : ℝ) * ((k : ℝ) - 1)^2)

private noncomputable def floorWeight (δ : ℝ) (m : ℕ) : ℝ :=
  if m ≤ 1 then 1 else 1 / (m : ℝ) - δ / ((m : ℝ) - 1)

private theorem bias_bounds {k : ℕ} (hk : 3 ≤ k) : 0 < bias k ∧ bias k ≤ 1 / 4 := by
  have h : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : (0 : ℝ) < k := by linarith
  have hs : 4 ≤ ((k : ℝ) - 1)^2 := by nlinarith
  have hq : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hden := mul_pos hp (pow_pos hq 2)
  constructor
  · exact div_pos (by linarith [h]) hden
  · unfold bias
    apply (div_le_iff₀ hden).2
    nlinarith [mul_le_mul_of_nonneg_left hs hp.le]

private theorem floorWeight_pos {δ : ℝ} (hδ : δ ≤ 1 / 4) {m : ℕ} :
    0 < floorWeight δ m := by
  unfold floorWeight
  split
  · norm_num
  · rename_i hn
    have h : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
    have hp : (0 : ℝ) < m := by linarith
    have hq : (0 : ℝ) < (m : ℝ) - 1 := by linarith
    apply sub_pos.mpr
    apply (div_lt_div_iff₀ hq hp).2
    nlinarith [mul_le_mul_of_nonneg_right hδ hp.le]

private theorem floorWeight_le {δ : ℝ} (hd : 0 ≤ δ) (hδ : δ ≤ 1 / 4)
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    floorWeight δ n ≤ floorWeight δ m := by
  by_cases h₁ : m ≤ 1
  · simp only [floorWeight, ite_eq_left h₁]
    split
    · exact le_rfl
    · rename_i hn
      have H : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
      have hp : (0 : ℝ) < n := by linarith
      have hq : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
      have h : 1 / (n : ℝ) ≤ 1 := (div_le_iff₀ hp).2 (by linarith)
      linarith [div_nonneg hd hq]
  · have h₂ : ¬ n ≤ 1 := by omega
    rw [floorWeight, ite_eq_right h₂, floorWeight, ite_eq_right h₁]
    have M : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
    have N : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
    have mn : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have mp : (0 : ℝ) < m := by linarith
    have np : (0 : ℝ) < n := by linarith
    have mq : (0 : ℝ) < (m : ℝ) - 1 := by linarith
    have nq : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have hprod : δ * ((m : ℝ) * n) ≤ ((m : ℝ) - 1) * ((n : ℝ) - 1) := by
      calc
        _ ≤ (1 / 4 : ℝ) * ((m : ℝ) * n) :=
          mul_le_mul_of_nonneg_right hδ (by positivity)
        _ ≤ _ := by
          nlinarith [mul_le_mul (show (m : ℝ) / 2 ≤ (m : ℝ) - 1 by linarith)
            (show (n : ℝ) / 2 ≤ (n : ℝ) - 1 by linarith) (by positivity) mq.le]
    have h := mul_nonneg (sub_nonneg.mpr mn) (sub_nonneg.mpr hprod)
    field_simp (disch := positivity)
    nlinarith

private noncomputable def weight (s : Finset V) (sat : V → Prop) [DecidablePred sat]
    (δ : ℝ) (b : V) : ℝ :=
  if 2 ≤ s.card ∧ ∃ a ∈ s, sat a then
    if sat b then 1 / (s.card : ℝ) + δ
    else 1 / (s.card : ℝ) - δ / ((s.card : ℝ) - 1)
  else 1 / (s.card : ℝ)

private theorem weight_lower {s : Finset V} {sat : V → Prop} [DecidablePred sat]
    {δ : ℝ} (hd : 0 ≤ δ) (hs : s.Nonempty) (b : V) :
    floorWeight δ s.card ≤ weight s sat δ b := by
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  by_cases hm : 2 ≤ s.card
  · have h : (2 : ℝ) ≤ s.card := by exact_mod_cast hm
    have hq : 0 ≤ δ / ((s.card : ℝ) - 1) := div_nonneg hd (by linarith)
    rw [floorWeight, ite_eq_right (by omega)]
    by_cases hsat : 2 ≤ s.card ∧ ∃ a ∈ s, sat a
    · by_cases hb : sat b <;> simp [weight, hsat, hb] <;> linarith
    · simp [weight, hsat, sub_le_self _ hq]
  · have hpos := hs.card_pos
    have hc : s.card = 1 := by omega
    simp [floorWeight, weight, hc]

private theorem weight_sum {s : Finset V} {sat : V → Prop} [DecidablePred sat]
    {δ : ℝ} (hs : s.Nonempty) (hu : ∀ a ∈ s, ∀ b ∈ s, sat a → sat b → a = b) :
    ∑ b ∈ s, weight s sat δ b = 1 := by
  classical
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  by_cases h : 2 ≤ s.card ∧ ∃ a ∈ s, sat a
  · simp only [weight, ite_eq_left h]
    obtain ⟨hm, a, ha, hsa⟩ := h
    have h' : (2 : ℝ) ≤ s.card := by exact_mod_cast hm
    have hc : ((s.erase a).card : ℝ) + 1 = s.card := by
      exact_mod_cast Finset.card_erase_add_one ha
    rw [← s.sum_erase_add _ ha]
    have he : ∑ b ∈ s.erase a, (if sat b then 1 / (s.card : ℝ) + δ
        else 1 / (s.card : ℝ) - δ / ((s.card : ℝ) - 1)) =
        ∑ _b ∈ s.erase a, (1 / (s.card : ℝ) - δ / ((s.card : ℝ) - 1)) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [ite_eq_right (fun hsb => (Finset.mem_erase.mp hb).1
        (hu b (Finset.mem_erase.mp hb).2 a ha hsb hsa))]
    rw [he, ite_eq_left hsa, Finset.sum_const, nsmul_eq_mul]
    rw [show ((s.erase a).card : ℝ) = s.card - 1 by linarith]
    field_simp [ne_of_gt hn, show (s.card : ℝ) - 1 ≠ 0 by linarith]
    ring
  · simp only [weight, ite_eq_right h, Finset.sum_const, nsmul_eq_mul]
    field_simp [ne_of_gt hn]

set_option maxHeartbeats 1600000 in
-- Dependent component indices are transported in both edge comparisons.
private theorem connected_bound [Finite V] (hG : G.IsChordal) (hconn : G.Connected) (o : V)
    (k : ℕ) (hk : 3 ≤ k)
    (hclique : ∀ s : Finset V, G.IsClique (s : Set V) → s.card ≤ k + 1)
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, g j i = -g i j)
    (htri : ∀ i j l, G.Adj i j → G.Adj j l → G.Adj i l →
      ‖g i j + g j l - g i l‖ ≤ ε) :
    ∃ φ : V → E, ∀ x y, G.Adj x y →
      ‖g x y - (φ y - φ x)‖ ≤ (4 - 4 / (k : ℝ) - 2 * ((k : ℝ) - 2)^2 / ((k : ℝ) * ((k : ℝ) - 1)^3)) * ε := by
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
    have root {b : V} (hb : b ∈ P x) : b = o := by
      symm
      apply hconn.dist_eq_zero_iff.mp
      have := (memP.mp hb).2
      omega
    ext b'
    simp only [Finset.mem_singleton]
    exact ⟨root, fun h => (h.trans (root hb).symm).symm ▸ hb⟩
  have predNear {x : V} {i : ℕ} (hx : G.dist o x = i + 1) {b d : V}
      (hb : b ∈ P x) (hd : d ∈ P x) (hne : b ≠ d) : G.Adj b d :=
    shadow_clique hG hconn _ (inShadow hx hb) (inShadow hx hd) hne
  have cardP {x : V} : (P x).card ≤ k := by
    cases hx : G.dist o x with
    | zero =>
      have he : P x = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro b hb
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
  have uniqueSaturated {v x y : V} (hx : x ∈ P v) (hy : y ∈ P v)
      (hsx : (P x).card = k) (hsy : (P y).card = k) : x = y := by
    by_contra hne
    obtain ⟨i, hi⟩ : ∃ i, G.dist o x = i + 1 := by
      cases h : G.dist o x with
      | zero =>
        have hnon : (P x).Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨q, hq⟩ := hnon
        have := (memP.mp hq).2
        omega
      | succ i => exact ⟨i, rfl⟩
    have hlx := (memP.mp hx).2
    have hly := (memP.mp hy).2
    have hj : G.dist o y = i + 1 := by omega
    have hv : G.dist o v = (i + 1) + 1 := by omega
    have hxy := predNear hv hx hy hne
    have heq : P x = P y := by
      rcases nested hi hj hxy with h | h
      · exact Finset.eq_of_subset_of_card_le h (by omega)
      · exact (Finset.eq_of_subset_of_card_le h (by omega)).symm
    have hxp : x ∉ P x := fun h => (memP.mp h).1.ne rfl
    have hyp : y ∉ P x := by
      rw [heq]
      exact fun h => (memP.mp h).1.ne rfl
    have hcl : G.IsClique (↑(insert x (insert y (P x))) : Set V) := by
      intro b hb d hd hbd
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hb hd
      rcases hb with rfl | rfl | hb
      · rcases hd with rfl | rfl | hd
        · exact (hbd rfl).elim
        · exact hxy
        · exact (memP.mp hd).1.symm
      · rcases hd with rfl | rfl | hd
        · exact hxy.symm
        · exact (hbd rfl).elim
        · exact (memP.mp (heq ▸ hd)).1.symm
      · rcases hd with rfl | rfl | hd
        · exact (memP.mp hb).1
        · exact (memP.mp (heq ▸ hb)).1
        · exact predNear hi hb hd hbd
    have h := hclique _ hcl
    rw [Finset.card_insert_of_notMem (by simp [hne, hxp]), Finset.card_insert_of_notMem hyp,
      hsx] at h
    omega
  let δ := bias k
  have hd : 0 ≤ δ := (bias_bounds hk).1.le
  have hd' : δ ≤ 1 / 4 := (bias_bounds hk).2
  let w (x : V) := weight (P x) (fun b => (P b).card = k) δ
  have wsum {x : V} {i : ℕ} (hx : G.dist o x = i + 1) : ∑ b ∈ P x, w x b = 1 :=
    weight_sum (inhabitedP hx) (fun _ hb _ hc hs ht => uniqueSaturated hb hc hs ht)
  have wfloor {x : V} {i : ℕ} (hx : G.dist o x = i + 1) (b : V) :
      floorWeight δ (P x).card ≤ w x b := weight_lower hd (inhabitedP hx) b
  have wnonneg {x : V} {i : ℕ} (hx : G.dist o x = i + 1) (b : V) (_ : b ∈ P x) :
      0 ≤ w x b :=
    (floorWeight_pos hd' (m := (P x).card)).le.trans (wfloor hx b)
  have wmin {x : V} {i : ℕ} (hx : G.dist o x = i + 1) (b : V) :
      floorWeight δ k ≤ w x b :=
    (floorWeight_le hd hd' (inhabitedP hx).card_pos cardP).trans (wfloor hx b)
  have wminSmall {x : V} {i : ℕ} (hx : G.dist o x = i + 1)
      (hc : (P x).card < k) (b : V) : floorWeight δ (k - 1) ≤ w x b :=
    (floorWeight_le hd hd' (inhabitedP hx).card_pos (by omega)).trans (wfloor hx b)
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
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hkone : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hktwo : (0 : ℝ) < (k : ℝ) - 2 := by linarith
  let targetMass := 2 / (k : ℝ) + δ * ((k : ℝ) - 2) / ((k : ℝ) - 1)
  let layerError := (3 - 2 * floorWeight δ k) * ε
  let bound := (4 - 4 / (k : ℝ) - 2 * ((k : ℝ) - 2)^2 /
    ((k : ℝ) * ((k : ℝ) - 1)^3)) * ε
  have floorK : floorWeight δ k = 1 / (k : ℝ) - δ / ((k : ℝ) - 1) := by
    simp [floorWeight, show ¬ k ≤ 1 by omega]
  have massEq : floorWeight δ k + floorWeight δ (k - 1) = targetMass := by
    rw [floorK, floorWeight, ite_eq_right (by omega : ¬ k - 1 ≤ 1), Nat.cast_sub (by omega : 1 ≤ k)]
    dsimp [targetMass, δ, bias]
    rw [Nat.cast_one, show (k : ℝ) - 1 - 1 = (k : ℝ) - 2 by ring]
    field_simp [ne_of_gt hkpos, ne_of_gt hkone, ne_of_gt hktwo]
    <;> ring
  have massSat : floorWeight δ k + (1 / (k : ℝ) + δ) = targetMass := by
    rw [floorK]
    dsimp [targetMass]
    field_simp [ne_of_gt hkone]
    <;> ring
  have crossTotal : (4 - 2 * targetMass) * ε = bound := by
    dsimp [targetMass, bound, δ, bias]
    field_simp [ne_of_gt hkpos, ne_of_gt hkone]
    <;> ring
  have layerCoeff : 3 - 2 * floorWeight δ k ≤ 4 - 2 * targetMass := by
    rw [floorK]
    dsimp [targetMass]
    have hδ : 2 * δ ≤ 1 - 2 / (k : ℝ) := by
      have h : 2 * δ ≤ ((k : ℝ) - 2) / (k : ℝ) := by
        dsimp [δ, bias]
        have hs : 2 ≤ ((k : ℝ) - 1)^2 := by nlinarith
        rw [div_mul_eq_div_div, ← mul_div_assoc]
        apply (div_le_iff₀ (pow_pos hkone 2)).2
        have hq : 0 ≤ ((k : ℝ) - 2) / (k : ℝ) := div_nonneg hktwo.le hkpos.le
        nlinarith [mul_le_mul_of_nonneg_left hs hq]
      rw [sub_div, div_self (ne_of_gt hkpos)] at h
      exact h
    have he : δ / ((k : ℝ) - 1) + δ * ((k : ℝ) - 2) / ((k : ℝ) - 1) = δ := by
      field_simp [ne_of_gt hkone]
      <;> ring
    linarith
  have layerTotal : layerError ≤ bound := by
    rw [← crossTotal]
    exact mul_le_mul_of_nonneg_right layerCoeff hε
  have nonnegBound : 0 ≤ bound := by
    have hfl : floorWeight δ k ≤ 1 := by
      simpa [floorWeight] using (floorWeight_le hd hd' (m := 1) (n := k) (by decide) (by omega))
    exact (mul_nonneg (by linarith : 0 ≤ 3 - 2 * floorWeight δ k) hε).trans layerTotal
  have across {x y : V} {i : ℕ} (hx : G.dist o x = i) (hy : G.dist o y = i + 1)
      (hxy : G.Adj x y) : Dist.dist (φ x + g x y) (φ y) ≤ bound := by
    cases i with
    | zero =>
      have he := hconn.dist_eq_zero_iff.mp hx
      subst x
      rw [eval o 0 (by simp), atSucc hy, firstPred hy]
      simpa [atLevel, Q, anchorGain, a, average, w, weight, firstPred hy, path, diagonal_zero hrev] using nonnegBound
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
      have mass : targetMass ≤ w x c + w y x := by
        by_cases hxk : (P x).card = k
        · by_cases hyk : (P y).card = k
          · have hboost : w y x = 1 / (k : ℝ) + δ := by
              dsimp [w, weight]
              rw [ite_eq_left ⟨by omega, x, xp, hxk⟩, ite_eq_left hxk, hyk]
            rw [← massSat, hboost]
            exact add_le_add (wmin hx c) le_rfl
          · rw [← massEq]
            exact add_le_add (wmin hx c) (wminSmall hy (by have := cardP (x := y); omega) x)
        · rw [← massEq, add_comm]
          exact add_le_add (wminSmall hx (by have := cardP (x := x); omega) c) (wmin hy x)
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
        ·
          intro d hd
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

end WeightedCliqueBanach

/-- On a finite chordal graph with clique size at most `k + 1`, triangle defects of at most
`ε` give one real-vector-space potential with the biased predecessor error bound on every edge. -/
theorem IsChordal.exists_biased_clique_banach_gain_potential
    {V : Type u} [Finite V] {G : SimpleGraph V} (hG : G.IsChordal)
    (k : ℕ) (hk : 3 ≤ k)
    (hclique : ∀ s : Finset V, G.IsClique (s : Set V) → s.card ≤ k + 1)
    {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε) (hrev : ∀ i j, g j i = -g i j)
    (htri : ∀ i j l, G.Adj i j → G.Adj j l → G.Adj i l →
      ‖g i j + g j l - g i l‖ ≤ ε) :
    ∃ φ : V → E, ∀ u v, G.Adj u v →
      ‖g u v - (φ v - φ u)‖ ≤
        (4 - 4 / (k : ℝ) - 2 * ((k : ℝ) - 2)^2 / ((k : ℝ) * ((k : ℝ) - 1)^3)) * ε := by
  classical
  have hcomp (c : G.ConnectedComponent) :
      ∃ ψ : c → E, ∀ i j, c.toSimpleGraph.Adj i j →
        ‖g i.val j.val - (ψ j - ψ i)‖ ≤
          (4 - 4 / (k : ℝ) - 2 * ((k : ℝ) - 2)^2 / ((k : ℝ) * ((k : ℝ) - 1)^3)) * ε := by
    obtain ⟨o, ho⟩ := c.nonempty_supp
    have hc (s : Finset c) (hs : c.toSimpleGraph.IsClique (s : Set c)) : s.card ≤ k + 1 := by
      let e : c ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
      simpa only [Finset.card_map] using hclique (s.map e) (by
        rw [Finset.coe_map]
        exact isClique_induce_iff.mp hs)
    exact WeightedCliqueBanach.connected_bound (hG.induce c.supp) c.connected_toSimpleGraph ⟨o, ho⟩
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

end SimpleGraph
