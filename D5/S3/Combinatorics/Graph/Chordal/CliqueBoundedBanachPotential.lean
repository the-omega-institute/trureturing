/- GID: D5/S3/Combinatorics/Graph/Chordal/CliqueBoundedBanachPotential
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/CliqueBoundedBanachPotential
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Averaging over predecessors improves the chordal gain bound at bounded clique number. -/

import D5.S3.Combinatorics.Graph.Chordal.UniformGainPotential
import Mathlib.Analysis.Normed.Module.Basic

/-! # Averaged reconstruction on clique-bounded chordal graphs

A finite mean over predecessors keeps the zero-error comparison on each side of a
cross-layer edge. Within a layer, the smaller predecessor set lies in the larger one,
so every inner mean includes one comparison using a single triangle.
-/

open scoped BigOperators

namespace SimpleGraph
namespace CliqueBoundedBanach

universe u v

variable {V : Type u} {G : SimpleGraph V} {o : V}
variable {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

open private Component componentOf parent Shadow exists_predecessor componentOf_adj
  mem_shadow_of_adj shadow_parent shadow_clique exists_shadow_anchor four_cycle_diagonal from
  D5.S3.Combinatorics.Graph.Chordal.UniformGainPotential

private noncomputable def mean (s : Finset V) (f : V → E) : E :=
  (s.card : ℝ)⁻¹ • ∑ b ∈ s, f b

private theorem mean_add (s : Finset V) (hs : s.Nonempty) (f : V → E) (z : E) :
    mean s (fun b => f b + z) = mean s f + z := by
  have hn : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  simp [mean, Finset.sum_add_distrib, smul_add, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, inv_mul_cancel₀ hn]

private theorem dist_mean_le (s : Finset V) (hs : s.Nonempty) (f : V → E) (z : E) :
    dist (mean s f) z ≤ (s.card : ℝ)⁻¹ * ∑ b ∈ s, dist (f b) z := by
  rw [dist_eq_norm, ← mean_add s hs f (-z)]
  simp only [mean, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [dist_eq_norm, sub_eq_add_neg] using
      (norm_sum_le s fun b => f b + -z))
    (inv_nonneg.mpr (Nat.cast_nonneg _))

private theorem mean_bound {s : Finset V} (hs : s.Nonempty) {f : V → E} {z : E} {B : ℝ}
    (h : ∀ b ∈ s, dist (f b) z ≤ B) : dist (mean s f) z ≤ B := by
  have hn : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  calc
    _ ≤ (s.card : ℝ)⁻¹ * ∑ b ∈ s, dist (f b) z := dist_mean_le s hs f z
    _ ≤ (s.card : ℝ)⁻¹ * ∑ _b ∈ s, B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum h) (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = B := by simp [← mul_assoc, inv_mul_cancel₀ hn]

/-- One distinguished term saves at least a `1/k` share of its improvement. -/
private theorem mean_bound_at {s : Finset V} {f : V → E} {z : E} {a : V}
    {k : ℕ} {A B : ℝ} (ha : a ∈ s) (hk : s.card ≤ k) (hAB : A ≤ B)
    (hsmall : dist (f a) z ≤ A) (hlarge : ∀ b ∈ s.erase a, dist (f b) z ≤ B) :
    dist (mean s f) z ≤ B - (B - A) / (k : ℝ) := by
  classical
  have hs : s.Nonempty := ⟨a, ha⟩
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hnk : (s.card : ℝ) ≤ k := by exact_mod_cast hk
  have hc : ((s.erase a).card : ℝ) + 1 = s.card := by
    exact_mod_cast Finset.card_erase_add_one ha
  have hsum : ∑ b ∈ s, dist (f b) z ≤ (s.erase a).card * B + A := by
    rw [← s.sum_erase_add (fun b => dist (f b) z) ha]
    exact add_le_add ((Finset.sum_le_sum hlarge).trans_eq (by simp)) hsmall
  calc
    _ ≤ (s.card : ℝ)⁻¹ * ∑ b ∈ s, dist (f b) z := dist_mean_le s hs f z
    _ ≤ (s.card : ℝ)⁻¹ * (((s.erase a).card : ℝ) * B + A) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hn.le)
    _ = B - (B - A) / (s.card : ℝ) := by
      rw [show ((s.erase a).card : ℝ) = s.card - 1 by linarith]
      field_simp
      ring
    _ ≤ B - (B - A) / (k : ℝ) :=
      sub_le_sub_left (div_le_div_of_nonneg_left (sub_nonneg.mpr hAB) hn hnk) B

private theorem diagonal_zero {g : V → V → E} (hrev : ∀ i j, g j i = -g i j) (x : V) :
    g x x = 0 := by
  apply (smul_eq_zero_iff_right (by norm_num : (2 : ℝ) ≠ 0)).mp
  rw [two_smul]
  exact (add_eq_zero_iff_neg_eq.mpr (hrev x x).symm)

private theorem triangle_le {g : V → V → E} {ε : ℝ} (hε : 0 ≤ ε)
    (hrev : ∀ i j, g j i = -g i j)
    (htri : ∀ i j l, G.Adj i j → G.Adj j l → G.Adj i l →
      ‖g i j + g j l - g i l‖ ≤ ε)
    {a b c : V} (hab : a = b ∨ G.Adj a b) (hbc : b = c ∨ G.Adj b c)
    (hac : a = c ∨ G.Adj a c) : dist (g a b + g b c) (g a c) ≤ ε := by
  rcases hab with rfl | hab
  · simpa [diagonal_zero hrev] using hε
  rcases hbc with rfl | hbc
  · simpa [diagonal_zero hrev] using hε
  rcases hac with rfl | hac
  · simpa [diagonal_zero hrev, hrev a b] using hε
  simpa only [dist_eq_norm] using htri _ _ _ hab hbc hac

private theorem two_triangles (g : V → V → E) {a b c d : V} {ε : ℝ}
    (habc : dist (g a b + g b c) (g a c) ≤ ε)
    (hbcd : dist (g b c + g c d) (g b d) ≤ ε) :
    dist (g a b + g b d) (g a c + g c d) ≤ 2 * ε := by
  calc
    _ ≤ dist (g a b + g b d) (g a b + (g b c + g c d)) +
        dist (g a b + (g b c + g c d)) (g a c + g c d) := dist_triangle _ _ _
    _ ≤ ε + ε := by
      apply add_le_add
      · rw [dist_add_left, _root_.dist_comm]
        exact hbcd
      · rwa [← add_assoc, dist_add_right]
    _ = 2 * ε := by ring

private def predecessors (G : SimpleGraph V) (o : V) (x : V) [Fintype V]
    [DecidablePred fun b : V => G.Adj b x ∧ G.dist o b + 1 = G.dist o x] : Finset V :=
  Finset.univ.filter fun b => G.Adj b x ∧ G.dist o b + 1 = G.dist o x

private noncomputable def anchorSum (g : V → V → E)
    (a : (i : ℕ) → Component G o (i + 1) → V) :
    (i : ℕ) → Component G o (i + 1) → E
  | 0, _ => 0
  | i + 1, C => anchorSum g a i (parent G o C) + g (a i (parent G o C)) (a (i + 1) C)

private theorem connected_bound [Finite V] (hG : G.IsChordal) (hconn : G.Connected) (o : V)
    (k : ℕ) (hk : 2 ≤ k)
    (hclique : ∀ s : Finset V, G.IsClique (s : Set V) → s.card ≤ k + 1)
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, g j i = -g i j)
    (htri : ∀ i j l, G.Adj i j → G.Adj j l → G.Adj i l →
      ‖g i j + g j l - g i l‖ ≤ ε) :
    ∃ φ : V → E, ∀ x y, G.Adj x y →
      ‖g x y - (φ y - φ x)‖ ≤ (4 - 4 / (k : ℝ)) * ε := by
  classical
  letI := Fintype.ofFinite V
  let P := predecessors G o
  have memP {b x : V} : b ∈ P x ↔ G.Adj b x ∧ G.dist o b + 1 = G.dist o x := by
    simp [P, predecessors]
  have inhabitedP {x : V} {i : ℕ} (hx : G.dist o x = i + 1) : (P x).Nonempty := by
    obtain ⟨b, hbx, hb⟩ := exists_predecessor hx
    exact ⟨b, memP.mpr ⟨hbx, by omega⟩⟩
  have inShadow {b x : V} {i : ℕ} (hx : G.dist o x = i + 1) (hb : b ∈ P x) :
      b ∈ Shadow G o (componentOf G o (i + 1) x hx.ge) :=
    mem_shadow_of_adj (by have := (memP.mp hb).2; omega) hx.ge (memP.mp hb).1
  choose anchor anchor_parent anchor_adj using
    (fun (i : ℕ) (C : Component G o (i + 2)) => exists_shadow_anchor hG hconn C)
  let a : (i : ℕ) → Component G o (i + 1) → V
    | 0, _ => o
    | i + 1, C => anchor i C
  have firstPred {x : V} (hx : G.dist o x = 1) : P x = {o} := by
    obtain ⟨b, hb⟩ := inhabitedP hx
    have root {b : V} (hb : b ∈ P x) : b = o := by
      apply hconn.dist_eq_zero_iff.mp
      have := (memP.mp hb).2
      omega
    ext b'
    simp only [Finset.mem_singleton]
    exact ⟨root, fun h => (h.trans (root hb).symm).symm ▸ hb⟩
  have cardP {x : V} {i : ℕ} (hx : G.dist o x = i + 1) : (P x).card ≤ k := by
    cases i with
    | zero => simpa [firstPred hx] using (show 1 ≤ k by omega)
    | succ i =>
      let C := componentOf G o (i + 2) x hx.ge
      let c := anchor i C
      have hc : c ∉ P x := by
        intro h
        have h₁ := (anchor_parent i C).1
        have h₂ := (inShadow hx h).1
        change G.dist o c = i at h₁
        omega
      have hcl : G.IsClique (↑(insert c (P x)) : Set V) := by
        intro b hb d hd hbd
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hb hd
        rcases hb with rfl | hb
        · exact anchor_adj i C d (inShadow hx (hd.resolve_left hbd.symm))
        · rcases hd with rfl | hd
          · exact (anchor_adj i C b (inShadow hx hb)).symm
          · exact shadow_clique hG hconn C (inShadow hx hb) (inShadow hx hd) hbd
      have h := hclique _ hcl
      rw [Finset.card_insert_of_notMem hc] at h
      omega
  have near {i : ℕ} {C : Component G o (i + 1)} {b d : V}
      (hb : b ∈ Shadow G o C) (hd : d ∈ Shadow G o C) : b = d ∨ G.Adj b d :=
    (eq_or_ne b d).imp_right (shadow_clique hG hconn C hb hd)
  have anchorNear {i : ℕ} {C : Component G o (i + 1)} {b : V} (hb : b ∈ Shadow G o C) :
      a i C = b ∨ G.Adj (a i C) b := by
    cases i with
    | zero => exact Or.inl (hconn.dist_eq_zero_iff.mp hb.1)
    | succ i => exact Or.inr (anchor_adj i C b hb)
  have tri {b c d : V} (hbc : b = c ∨ G.Adj b c) (hcd : c = d ∨ G.Adj c d)
      (hbd : b = d ∨ G.Adj b d) : dist (g b c + g c d) (g b d) ≤ ε :=
    triangle_le hε hrev htri hbc hcd hbd
  let Q := anchorSum g a
  let path (c x b : V) := g c b + g b x
  let atLevel (x : V) : (i : ℕ) → G.dist o x = i → E
    | 0, _ => 0
    | i + 1, hx =>
      let C := componentOf G o (i + 1) x hx.ge
      Q i C + mean (P x) (path (a i C) x)
  let φ (x : V) := atLevel x (G.dist o x) rfl
  have eval (x : V) (i : ℕ) (hx : G.dist o x = i) : φ x = atLevel x i hx := by
    subst i
    rfl
  have atSucc {x : V} {i : ℕ} (hx : G.dist o x = i + 1) :
      let C := componentOf G o (i + 1) x hx.ge
      φ x = Q i C + mean (P x) (path (a i C) x) := eval x (i + 1) hx
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hfrac : (2 : ℝ) / k ≤ 1 := (div_le_iff₀ hkpos).mpr (by simpa using hkR)
  let crossError := 2 * ε - (2 * ε) / (k : ℝ)
  let layerError := 3 * ε - (2 * ε) / (k : ℝ)
  let bound := (4 - 4 / (k : ℝ)) * ε
  have crossTotal : crossError + crossError = bound := by
    dsimp [crossError, bound]
    ring
  have layerTotal : layerError ≤ bound := by
    dsimp [layerError, bound]
    have h := mul_le_mul_of_nonneg_right hfrac hε
    rw [div_mul_eq_mul_div, one_mul] at h
    have he : (4 : ℝ) / k * ε = (2 * ε) / k + (2 * ε) / k := by ring
    rw [sub_mul, he]
    linarith
  have nonnegBound : 0 ≤ bound := by
    have h := mul_le_mul_of_nonneg_right hfrac hε
    rw [div_mul_eq_mul_div, one_mul] at h
    rw [← crossTotal]
    dsimp [crossError]
    linarith
  have across {x y : V} {i : ℕ} (hx : G.dist o x = i) (hy : G.dist o y = i + 1)
      (hxy : G.Adj x y) : dist (φ x + g x y) (φ y) ≤ bound := by
    cases i with
    | zero =>
      subst x via hconn.dist_eq_zero_iff.mp hx
      rw [eval o 0 (by simp), atSucc hy, firstPred hy]
      simpa [atLevel, Q, anchorSum, a, mean, path, diagonal_zero hrev] using nonnegBound
    | succ i =>
      let C := componentOf G o (i + 2) y hy.ge
      let D := parent G o C
      let c := a (i + 1) C
      let d := a i D
      have xs : x ∈ Shadow G o C := mem_shadow_of_adj hx hy.ge hxy
      have hD : D = componentOf G o (i + 1) x hx.ge := shadow_parent xs
      have cs : c ∈ Shadow G o D := anchor_parent i C
      have hcx : G.Adj c x := anchor_adj i C x xs
      have cp : c ∈ P x := memP.mpr ⟨hcx, by have := cs.1; omega⟩
      have xp : x ∈ P y := memP.mpr ⟨hxy, by omega⟩
      have Qstep : Q (i + 1) C = Q i D + g d c := rfl
      let m := Q (i + 1) C + g c x
      have earlier : dist (mean (P x) (path d x)) (path d x c) ≤ crossError := by
        have h := mean_bound_at (f := path d x) (z := path d x c) cp (cardP hx)
          (show (0 : ℝ) ≤ 2 * ε by linarith) (by simp)
        apply (h ?_).trans_eq (by simp [crossError])
        intro b hb
        have hb' := (Finset.mem_erase.mp hb).2
        have bs : b ∈ Shadow G o D := hD ▸ inShadow hx hb'
        exact two_triangles g (tri (anchorNear bs) (near bs cs) (anchorNear cs))
          (tri (near bs cs) (Or.inr hcx) (Or.inr (memP.mp hb').1))
      have later : dist (mean (P y) (path c y)) (path c y x) ≤ crossError := by
        have h := mean_bound_at (f := path c y) (z := path c y x) xp (cardP hy)
          (show (0 : ℝ) ≤ 2 * ε by linarith) (by simp)
        apply (h ?_).trans_eq (by simp [crossError])
        intro b hb
        have hb' := (Finset.mem_erase.mp hb).2
        have bs := inShadow hy hb'
        exact two_triangles g (tri (anchorNear bs) (near bs xs) (Or.inr hcx))
          (tri (near bs xs) (Or.inr hxy) (Or.inr (memP.mp hb').1))
      have h₁ : dist (φ x) m ≤ crossError := by
        rw [atSucc hx, ← hD]
        change dist (Q i D + mean (P x) (path d x)) (Q (i + 1) C + g c x) ≤ _
        rw [Qstep, add_assoc, dist_add_left]
        exact earlier
      have h₂ : dist (m + g x y) (φ y) ≤ crossError := by
        rw [atSucc hy]
        change dist ((Q (i + 1) C + g c x) + g x y)
          (Q (i + 1) C + mean (P y) (path c y)) ≤ _
        rwa [add_assoc, dist_add_left, _root_.dist_comm]
      rw [← crossTotal]
      exact (dist_triangle _ (m + g x y) _).trans
        (add_le_add (by rwa [dist_add_right]) h₂)
  have symmError (x y : V) :
      dist (φ y + g y x) (φ x) = dist (φ x + g x y) (φ y) := by
    rw [hrev x y, ← dist_add_right _ _ (g x y)]
    simp [add_assoc, _root_.dist_comm]
  have within {x y : V} {i : ℕ} (hx : G.dist o x = i + 1) (hy : G.dist o y = i + 1)
      (hxy : G.Adj x y) : dist (φ x + g x y) (φ y) ≤ bound := by
    have nested : P x ⊆ P y ∨ P y ⊆ P x := by
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
    have oriented {x y : V} (hx : G.dist o x = i + 1) (hy : G.dist o y = i + 1)
        (hxy : G.Adj x y) (hsub : P x ⊆ P y) : dist (φ x + g x y) (φ y) ≤ layerError := by
      let C := componentOf G o (i + 1) x hx.ge
      let c := a i C
      have hC : C = componentOf G o (i + 1) y hy.ge := componentOf_adj hx.ge hy.ge hxy
      have perPred (b : V) (hb : b ∈ P x) :
          dist (path c x b + g x y) (mean (P y) (path c y)) ≤ layerError := by
        have hb' := hsub hb
        have bs : b ∈ Shadow G o C := inShadow hx hb
        have diag : dist (path c x b + g x y) (path c y b) ≤ ε := by
          dsimp only [path]
          rw [add_assoc, dist_add_left]
          exact tri (Or.inr (memP.mp hb).1) (Or.inr hxy) (Or.inr (memP.mp hb').1)
        rw [_root_.dist_comm]
        have h := mean_bound_at (f := path c y) (z := path c x b + g x y) hb' (cardP hy)
          (show ε ≤ 3 * ε by linarith) (by rwa [_root_.dist_comm])
        apply (h ?_).trans_eq (by dsimp [layerError]; ring)
        intro d hd
        have hd' := (Finset.mem_erase.mp hd).2
        have ds : d ∈ Shadow G o C := hC.symm ▸ inShadow hy hd'
        have two : dist (path c y d) (path c y b) ≤ 2 * ε :=
          two_triangles g (tri (anchorNear ds) (near ds bs) (anchorNear bs))
            (tri (near ds bs) (Or.inr (memP.mp hb').1) (Or.inr (memP.mp hd').1))
        exact (dist_triangle _ (path c y b) _).trans
          (by linarith [add_le_add two (by rwa [_root_.dist_comm] : dist (path c y b) _ ≤ ε)])
      rw [atSucc hx, atSucc hy, ← hC]
      change dist ((Q i C + mean (P x) (path c x)) + g x y)
        (Q i C + mean (P y) (path c y)) ≤ _
      rw [add_assoc, dist_add_left, ← mean_add _ (inhabitedP hx)]
      exact mean_bound (inhabitedP hx) perPred
    rcases nested with h | h
    · exact (oriented hx hy hxy h).trans layerTotal
    · rw [← symmError]
      exact (oriented hy hx hxy.symm h).trans layerTotal
  have forward {x y : V} (hxy : G.Adj x y) (h : G.dist o x ≤ G.dist o y) :
      dist (φ x + g x y) (φ y) ≤ bound := by
    by_cases he : G.dist o x = G.dist o y
    · cases hi : G.dist o x with
      | zero =>
        exact (hxy.ne ((hconn.dist_eq_zero_iff.mp hi).trans
          (hconn.dist_eq_zero_iff.mp (he.symm.trans hi)).symm)).elim
      | succ i => exact within hi (he.symm.trans hi) hxy
    · have hd := hxy.diff_dist_adj (u := o)
      exact across rfl (by omega) hxy
  refine ⟨φ, fun x y hxy => ?_⟩
  calc
    _ = dist (φ x + g x y) (φ y) := by
      rw [dist_eq_norm]
      congr 1
      abel
    _ ≤ bound := by
      rcases le_total (G.dist o x) (G.dist o y) with h | h
      · exact forward hxy h
      · rw [← symmError]
        exact forward hxy.symm h

end CliqueBoundedBanach

/-- On a finite chordal graph with clique size at most `k + 1`, triangle defects of at most
`ε` give one real-vector-space potential with error at most `(4 - 4/k)ε` on every edge. -/
theorem IsChordal.exists_clique_bounded_banach_gain_potential
    {V : Type u} [Finite V] {G : SimpleGraph V} (hG : G.IsChordal)
    (k : ℕ) (hk : 2 ≤ k)
    (hclique : ∀ s : Finset V, G.IsClique (s : Set V) → s.card ≤ k + 1)
    {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε) (hrev : ∀ i j, g j i = -g i j)
    (htri : ∀ i j l, G.Adj i j → G.Adj j l → G.Adj i l →
      ‖g i j + g j l - g i l‖ ≤ ε) :
    ∃ φ : V → E, ∀ u v, G.Adj u v →
      ‖g u v - (φ v - φ u)‖ ≤ (4 - 4 / (k : ℝ)) * ε := by
  classical
  have hcomp (c : G.ConnectedComponent) :
      ∃ ψ : c → E, ∀ i j, c.toSimpleGraph.Adj i j →
        ‖g i.val j.val - (ψ j - ψ i)‖ ≤ (4 - 4 / (k : ℝ)) * ε := by
    obtain ⟨o, ho⟩ := c.nonempty_supp
    have hc (s : Finset c) (hs : c.toSimpleGraph.IsClique (s : Set c)) : s.card ≤ k + 1 := by
      let e : c ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
      simpa only [Finset.card_map] using hclique (s.map e) (by
        rw [Finset.coe_map]
        exact (isClique_map_iff (f := e)).mp hs)
    exact CliqueBoundedBanach.connected_bound (hG.induce c.supp) c.connected_toSimpleGraph ⟨o, ho⟩
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
