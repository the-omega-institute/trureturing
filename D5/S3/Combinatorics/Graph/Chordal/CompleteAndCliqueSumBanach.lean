/- GID: D5/S3/Combinatorics/Graph/Chordal/CompleteAndCliqueSumBanach
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/CompleteAndCliqueSumBanach
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact complete graph radii and midpoint averaging on separated cliques. -/

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

/-! # Complete graph constants and separated clique sums -/

open scoped BigOperators

namespace SimpleGraph

universe u v w

/-- Averaging all star potentials gives the optimal universal complete graph radius. -/
theorem completeGraph_banach_upper_bound {V : Type u} [Finite V]
    (hm : 2 ≤ Nat.card V) {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V → V → E) (ε : ℝ)
    (hrev : ∀ i j, g j i = -g i j)
    (htri : ∀ i j l, i ≠ j → j ≠ l → i ≠ l → ‖g i j + g j l - g i l‖ ≤ ε) :
    ∃ φ : V → E, ∀ u v, u ≠ v →
      ‖g u v - (φ v - φ u)‖ ≤ ((Nat.card V : ℝ) - 2) / Nat.card V * ε := by
  classical
  let := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card] at hm ⊢
  have hmR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hm
  have hpos : (0 : ℝ) < Fintype.card V := by linarith
  have hdiag (u : V) : g u u = 0 := by
    have h₂ : (2 : ℝ) • g u u = 0 := by
      rw [two_smul, eq_neg_iff_add_eq_zero.mp (hrev u u)]
    calc
      g u u = (1 / 2 : ℝ) • ((2 : ℝ) • g u u) := by rw [smul_smul]; norm_num
      _ = 0 := by rw [h₂, smul_zero]
  let φ (v : V) := (Fintype.card V : ℝ)⁻¹ • ∑ w : V, g w v
  refine ⟨φ, fun u v huv => ?_⟩
  let r (w : V) := g u v + g w u - g w v
  have he : g u v - (φ v - φ u) = (Fintype.card V : ℝ)⁻¹ • ∑ w, r w := by
    simp [r, φ, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_add, smul_sub, smul_smul, hpos.ne']
    abel
  have hu : r u = 0 := by simp [r, hdiag]
  have hv : r v = 0 := by simp [r, hdiag, hrev u v]
  let S := (Finset.univ.erase u).erase v
  have hc : (S.card : ℝ) = Fintype.card V - 2 := by
    have h₁ := Finset.card_erase_add_one (Finset.mem_univ u)
    have h₂ := Finset.card_erase_add_one (s := Finset.univ.erase u)
      (Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ v⟩)
    simp only [Finset.card_univ] at h₁
    have h : (S.card : ℝ) + 2 = Fintype.card V := by
      exact_mod_cast (show S.card + 2 = Fintype.card V by dsimp [S]; omega)
    linarith
  have hsum : (∑ w : V, ‖r w‖) ≤ (S.card : ℝ) * ε := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ u), hu, norm_zero, add_zero,
      ← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ v⟩),
      hv, norm_zero, add_zero]
    calc
      _ ≤ ∑ _w ∈ S, ε := by
        apply Finset.sum_le_sum
        intro w hw
        obtain ⟨hwv, hw'⟩ := Finset.mem_erase.mp hw
        obtain ⟨hwu, _⟩ := Finset.mem_erase.mp hw'
        simpa [r, add_comm] using htri w u v hwu huv hwv
      _ = _ := by simp
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
  calc
    _ ≤ (Fintype.card V : ℝ)⁻¹ * ∑ w : V, ‖r w‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hpos.le)
    _ ≤ (Fintype.card V : ℝ)⁻¹ * ((S.card : ℝ) * ε) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hpos.le)
    _ = _ := by rw [hc]; ring

/-- Real skew matrices with vanishing row sums, carrying the induced supremum norm. -/
def ZeroDivSkew (m : ℕ) : Submodule ℝ (Fin m → Fin m → ℝ) where
  carrier := {f | (∀ i j, f j i = -f i j) ∧ ∀ i, ∑ j, f i j = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f h hf hh
    constructor
    · intro i j
      change f j i + h j i = -(f i j + h i j)
      rw [hf.1 i j, hh.1 i j]
      ring
    · intro i
      change ∑ j, (f i j + h i j) = 0
      rw [Finset.sum_add_distrib, hf.2 i, hh.2 i, add_zero]
  smul_mem' := by
    intro c f hf
    constructor
    · intro i j
      change c * f j i = -(c * f i j)
      rw [hf.1 i j]
      ring
    · intro i
      change ∑ j, c * f i j = 0
      rw [← Finset.mul_sum, hf.2 i, mul_zero]

private noncomputable def edgeVal {m : ℕ} (a b u v : Fin m) : ℝ :=
  (if a = u ∧ b = v then 1 else 0) - (if b = u ∧ a = v then 1 else 0)

private theorem edgeVal_skew {m : ℕ} (a b u v : Fin m) :
    edgeVal a b v u = -edgeVal a b u v := by
  simp only [edgeVal, and_comm]
  ring

private theorem edgeVal_row {m : ℕ} (a b u : Fin m) :
    ∑ v, edgeVal a b u v = (if a = u then 1 else 0) - (if b = u then 1 else 0) := by
  by_cases ha : a = u <;> by_cases hb : b = u <;>
    simp [edgeVal, ha, hb]

private noncomputable def triangle {m : ℕ} (a b c : Fin m) : ZeroDivSkew m :=
  ⟨fun u v => edgeVal a b u v + edgeVal b c u v + edgeVal c a u v, by
    constructor
    · intro u v
      change edgeVal a b v u + edgeVal b c v u + edgeVal c a v u =
        -(edgeVal a b u v + edgeVal b c u v + edgeVal c a u v)
      rw [edgeVal_skew a b u v, edgeVal_skew b c u v, edgeVal_skew c a u v]
      ring
    · intro u
      simp only [Finset.sum_add_distrib, edgeVal_row]
      ring⟩

private theorem triangle_reverse {m : ℕ} (a b c : Fin m) :
    triangle a c b = -triangle a b c := by
  apply Subtype.ext
  funext u v
  change edgeVal a c u v + edgeVal c b u v + edgeVal b a u v =
    -(edgeVal a b u v + edgeVal b c u v + edgeVal c a u v)
  simp only [edgeVal]
  ring

private theorem triangle_defect {m : ℕ} (o a b c : Fin m) :
    triangle o a b + triangle o b c - triangle o a c = triangle a b c := by
  apply Subtype.ext
  funext u v
  change (edgeVal o a u v + edgeVal a b u v + edgeVal b o u v) +
      (edgeVal o b u v + edgeVal b c u v + edgeVal c o u v) -
      (edgeVal o a u v + edgeVal a c u v + edgeVal c o u v) =
      edgeVal a b u v + edgeVal b c u v + edgeVal c a u v
  simp only [edgeVal]
  ring

private theorem triangle_norm {m : ℕ} (a b c : Fin m) : ‖triangle a b c‖ ≤ 1 := by
  change ‖(triangle a b c).val‖ ≤ 1
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro u
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro v
  change ‖edgeVal a b u v + edgeVal b c u v + edgeVal c a u v‖ ≤ 1
  by_cases hab : a = b
  · subst b; simp [edgeVal]
  by_cases hbc : b = c
  · subst c; simp [edgeVal]
  by_cases hac : a = c
  · subst c; simp [edgeVal]
  simp only [edgeVal]
  split_ifs <;> norm_num <;> grind

private theorem triangle_coordinate {m : ℕ} {i j : Fin m} (hij : i ≠ j) (o : Fin m) :
    (triangle o i j).val i j = if o = i ∨ o = j then 0 else 1 := by
  by_cases hoi : o = i <;> by_cases hoj : o = j <;>
    simp_all [triangle, edgeVal, Ne.symm hij]

/-- The divergence-free space supplies sharp examples in every complete graph size. -/
theorem completeGraph_banach_lower_bound (m : ℕ) (hm : 2 ≤ m) :
    ∃ g : Fin m → Fin m → ZeroDivSkew m,
      (∀ i j, g j i = -g i j) ∧
      (∀ i j l, i ≠ j → j ≠ l → i ≠ l → ‖g i j + g j l - g i l‖ ≤ 1) ∧
      ∀ φ : Fin m → ZeroDivSkew m, ∃ u v, u ≠ v ∧
        ((m : ℝ) - 2) / m ≤ ‖g u v - (φ v - φ u)‖ := by
  classical
  let o : Fin m := ⟨0, by omega⟩
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : (0 : ℝ) < m := by linarith
  let g (i j : Fin m) := triangle o i j
  refine ⟨g, fun i j => triangle_reverse o i j, ?_, ?_⟩
  · intro i j l _ _ _
    rw [show g i j + g j l - g i l = triangle i j l from triangle_defect o i j l]
    exact triangle_norm i j l
  intro φ
  by_contra! h
  let c := ((m : ℝ) - 2) / m
  let δ (i j : Fin m) := (φ j).val i j - (φ i).val i j
  have hcancel : ∑ i, ∑ j, δ i j = 0 := by
    simp only [δ, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun i j => (φ j).val i j)]
    have hrow (i : Fin m) : ∑ j, (φ i).val i j = 0 := (φ i).property.2 i
    have hcol (i : Fin m) : ∑ j, (φ i).val j i = 0 := by
      rw [show (∑ j, (φ i).val j i) = ∑ j, -(φ i).val i j by
        exact Finset.sum_congr rfl (fun j _ => (φ i).property.1 i j)]
      rw [Finset.sum_neg_distrib, hrow, neg_zero]
    simp [hrow, hcol]
  let S : Fin m → Finset (Fin m) := fun i => Finset.univ.erase i
  have hgain (i : Fin m) : ∑ j ∈ S i, (g i j).val i j =
      if i = o then 0 else (m : ℝ) - 2 := by
    by_cases hio : i = o
    · subst i
      rw [ite_eq_left rfl]
      apply Finset.sum_eq_zero
      intro j hj
      rw [triangle_coordinate (Finset.mem_erase.mp hj).1.symm]
      simp
    · have he : (∑ j ∈ S i, (g i j).val i j) = ∑ j ∈ (S i).erase o, (1 : ℝ) := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨(Ne.symm hio), Finset.mem_univ _⟩)]
        rw [triangle_coordinate hio]
        simp only [or_true, ite_true, add_zero]
        apply Finset.sum_congr rfl
        intro j hj
        have hji := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
        have hjo := (Finset.mem_erase.mp hj).1
        rw [triangle_coordinate hji.symm]
        simp [(Ne.symm hio), hjo.symm]
      rw [ite_eq_right hio, he]
      have h₁ : (S i).card + 1 = m := by
        simpa [S] using Finset.card_erase_add_one (Finset.mem_univ i)
      have h₂ := Finset.card_erase_add_one (s := S i)
        (Finset.mem_erase.mpr ⟨Ne.symm hio, Finset.mem_univ o⟩)
      have h₃ : (((S i).erase o).card : ℝ) + 2 = m := by
        exact_mod_cast (show ((S i).erase o).card + 2 = m by omega)
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      linarith
  have ht : ∑ i, ∑ j ∈ S i, (g i j).val i j = (m - 1 : ℝ) * (m - 2) := by
    simp_rw [hgain]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ o)]
    simp only [ite_true, add_zero]
    rw [Finset.sum_congr rfl (fun i hi => ite_eq_right (Finset.mem_erase.mp hi).1)]
    simp [Finset.card_erase_of_mem (Finset.mem_univ o), Nat.cast_sub (by omega : 1 ≤ m)]
    ring
  have hδ : ∑ i, ∑ j ∈ S i, δ i j = 0 := by
    convert hcancel using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp [S, δ]
  have hlt (i : Fin m) (j : Fin m) (hj : j ∈ S i) :
      (g i j).val i j - δ i j < c := by
    have hnorm := h i j (Finset.mem_erase.mp hj).1.symm
    let e := g i j - (φ j - φ i)
    have hcoord : ‖e.val i j‖ ≤ ‖e‖ :=
      (norm_le_pi_norm (e.val i) j).trans (norm_le_pi_norm e.val i)
    exact (le_abs_self _).trans_lt (hcoord.trans_lt hnorm)
  have hs (i : Fin m) : (S i).Nonempty := by
    apply Finset.card_pos.mp
    simp [S, Finset.card_erase_of_mem (Finset.mem_univ i)]
    omega
  have hrow (i : Fin m) : ∑ j ∈ S i, ((g i j).val i j - δ i j) < (m - 1 : ℝ) * c := by
    calc
      _ < ∑ _j ∈ S i, c := Finset.sum_lt_sum_of_nonempty (hs i) (hlt i)
      _ = _ := by simp [S, Finset.card_erase_of_mem (Finset.mem_univ i),
        Nat.cast_sub (by omega : 1 ≤ m)]
  have htotal : ∑ i, ∑ j ∈ S i, ((g i j).val i j - δ i j) <
      (m : ℝ) * ((m - 1 : ℝ) * c) := by
    calc
      _ < ∑ _i : Fin m, (m - 1 : ℝ) * c :=
        Finset.sum_lt_sum_of_nonempty ⟨o, Finset.mem_univ _⟩ (fun i _ => hrow i)
      _ = _ := by simp
  simp_rw [Finset.sum_sub_distrib] at htotal
  rw [ht, hδ, sub_zero] at htotal
  dsimp [c] at htotal
  rw [show (m : ℝ) * ((m - 1 : ℝ) * (((m : ℝ) - 2) / m)) =
    (m - 1 : ℝ) * (m - 2) by field_simp] at htotal
  exact (lt_irrefl _ htotal)

example (m : ℕ) : FiniteDimensional ℝ (ZeroDivSkew m) := inferInstance

example (m : ℕ) : CompleteSpace (ZeroDivSkew m) := inferInstance


section CliqueSums

variable {I : Type w} {V : Type u} {E : Type v}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]

private def walkGain {T : SimpleGraph I} (d : I → I → E) {a b : I} :
    T.Walk a b → E
  | .nil => 0
  | .cons' x y _ _ p => d x y + walkGain d p

omit [NormedSpace ℝ E] in
private theorem walkGain_concat {T : SimpleGraph I} (d : I → I → E)
    {a b c : I} (p : T.Walk a b) (h : T.Adj b c) :
    walkGain d (p.concat h) = walkGain d p + d b c := by
  induction p with
  | nil => simp [Walk.concat, walkGain]
  | cons h' p ih =>
    change _ + walkGain d (p.concat h) = (_ + walkGain d p) + d _ _
    rw [ih, add_assoc]

omit [NormedSpace ℝ E] in
theorem tree_offsets {T : SimpleGraph I} (hT : T.IsTree)
    (d : I → I → E) (hrev : ∀ a b, T.Adj a b → d b a = -d a b) :
    ∃ c : I → E, ∀ a b, T.Adj a b → c b - c a = d a b := by
  classical
  let r := hT.connected.nonempty.some
  let p (a : I) := (hT.existsUnique_path r a).exists.choose
  have hp (a : I) : (p a).IsPath := (hT.existsUnique_path r a).exists.choose_spec
  refine ⟨fun a => walkGain d (p a), fun a b hab => ?_⟩
  change walkGain d (p b) - walkGain d (p a) = d a b
  by_cases ha : a ∈ (p b).support
  · rw [hT.isAcyclic.path_concat (hp a) (hp b) hab ha, walkGain_concat]
    abel
  · have hb := hT.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath
      (hp a) (hp b) hab ha
    rw [hT.isAcyclic.path_concat (hp b) (hp a) hab.symm hb, walkGain_concat, hrev a b hab]
    abel

/-- Midpoint averaging gives the stated bound for separated clique attachments. -/
theorem separatedCliqueSum_banach_gain_potential [Finite V]
    (T : SimpleGraph I) (hT : T.IsTree) (G : SimpleGraph V) (P : I → Set V)
    (hcover : ∀ v, ∃ a, v ∈ P a)
    (hedge : ∀ u v, G.Adj u v → ∃ a, u ∈ P a ∧ v ∈ P a)
    (m : ℕ) (hm : 1 ≤ m)
    (hattach : ∀ a b, T.Adj a b → (P a ∩ P b).Nonempty ∧
      G.IsClique (P a ∩ P b) ∧ Nat.card ↥(P a ∩ P b) ≤ m)
    (hdisjoint : ∀ a b, a ≠ b → ¬ T.Adj a b → Disjoint (P a) (P b))
    (hsep : ∀ a b c, T.Adj a b → T.Adj a c → b ≠ c →
      Disjoint (P a ∩ P b) (P a ∩ P c) ∧
      ∀ u ∈ P a ∩ P b, ∀ v ∈ P a ∩ P c, ¬ G.Adj u v)
    (g : V → V → E) (R : ℝ) (hR : 0 ≤ R)
    (φ : I → V → E)
    (hfit : ∀ a u, u ∈ P a → ∀ v, v ∈ P a → G.Adj u v →
      ‖g u v - (φ a v - φ a u)‖ ≤ R) :
    ∃ Φ : V → E, ∀ u v, G.Adj u v →
      ‖g u v - (Φ v - Φ u)‖ ≤ (2 - 1 / (m : ℝ)) * R := by
  classical
  let := Fintype.ofFinite V
  let S (a b : I) := Finset.univ.filter fun v => v ∈ P a ∩ P b
  have memS (a b : I) (v : V) : v ∈ S a b ↔ v ∈ P a ∩ P b := by simp [S]
  have Ssymm (a b : I) : S b a = S a b := by ext v; simp [S, and_comm]
  have Scard (a b : I) : (S a b).card = Nat.card ↥(P a ∩ P b) := by
    let e : ↥(S a b) ≃ ↥(P a ∩ P b) :=
      { toFun := fun x => ⟨x.val, (memS a b _).mp x.property⟩
        invFun := fun x => ⟨x.val, (memS a b _).mpr x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  have Spos (a b : I) (hab : T.Adj a b) : (0 : ℝ) < (S a b).card := by
    obtain ⟨x, hx⟩ := (hattach a b hab).1
    exact_mod_cast Finset.card_pos.mpr ⟨x, (memS a b x).mpr hx⟩
  let d (a b : I) := ((S a b).card : ℝ)⁻¹ • ∑ s ∈ S a b, (φ a s - φ b s)
  have drev (a b : I) (_ : T.Adj a b) : d b a = -d a b := by
    dsimp [d]
    rw [Ssymm a b]
    rw [show (∑ s ∈ S a b, (φ b s - φ a s)) =
        ∑ s ∈ S a b, -(φ a s - φ b s) by
      exact Finset.sum_congr rfl (fun s _ => (neg_sub _ _).symm)]
    rw [Finset.sum_neg_distrib, smul_neg]
  obtain ⟨c, hc⟩ := tree_offsets hT d drev
  let ψ (a : I) (v : V) := φ a v + c a
  have fit (a : I) (u : V) (hu : u ∈ P a) (v : V) (hv : v ∈ P a) (huv : G.Adj u v) :
      ‖g u v - (ψ a v - ψ a u)‖ ≤ R := by
    convert hfit a u hu v hv huv using 2 <;> dsimp [ψ] <;> abel
  let D (a b : I) (s : V) := ψ b s - ψ a s
  have center (a b : I) (hab : T.Adj a b) : ∑ s ∈ S a b, D a b s = 0 := by
    have he (s : V) : D a b s = (φ b s - φ a s) + (c b - c a) := by
      dsimp [D, ψ]; abel
    simp_rw [he, hc a b hab, Finset.sum_add_distrib, Finset.sum_const,
      ← Nat.cast_smul_eq_nsmul ℝ]
    dsimp [d]
    rw [smul_smul, mul_inv_cancel₀ (Spos a b hab).ne', one_smul]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero (fun s _ => by abel)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  let B := (1 - 1 / (m : ℝ)) * R
  have hB : 0 ≤ B := mul_nonneg (sub_nonneg.mpr ((div_le_one (by linarith)).mpr hmR)) hR
  have bound (a b : I) (hab : T.Adj a b) (s : V) (hs : s ∈ P a ∩ P b) :
      ‖(1 / 2 : ℝ) • D a b s‖ ≤ B := by
    let A := S a b
    have hsA : s ∈ A := (memS a b s).mpr hs
    have hA : 0 < (A.card : ℝ) := Spos a b hab
    have hpair (t : V) (ht : t ∈ A.erase s) : ‖D a b s - D a b t‖ ≤ 2 * R := by
      obtain ⟨hts, htA⟩ := Finset.mem_erase.mp ht
      have ht' := (memS a b t).mp htA
      have hst := (hattach a b hab).2.1 hs ht' hts.symm
      have he : D a b s - D a b t =
          (g s t - (ψ b t - ψ b s)) - (g s t - (ψ a t - ψ a s)) := by
        dsimp [D]; abel
      rw [he]
      exact (norm_sub_le _ _).trans (by linarith [fit a s hs.1 t ht'.1 hst, fit b s hs.2 t ht'.2 hst])
    have he : D a b s = (A.card : ℝ)⁻¹ • ∑ t ∈ A, (D a b s - D a b t) := by
      rw [Finset.sum_sub_distrib, center a b hab, sub_zero, Finset.sum_const,
        ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hA.ne', one_smul]
    have hsum : ∑ t ∈ A, ‖D a b s - D a b t‖ ≤ ((A.erase s).card : ℝ) * (2 * R) := by
      rw [← A.sum_erase_add _ hsA, sub_self, norm_zero, add_zero]
      exact (Finset.sum_le_sum hpair).trans_eq (by simp)
    have hcard : ((A.erase s).card : ℝ) = A.card - 1 := by
      have h := Finset.card_erase_add_one hsA
      have h' : ((A.erase s).card : ℝ) + 1 = A.card := by exact_mod_cast h
      linarith
    have hAm : (A.card : ℝ) ≤ m := by
      exact_mod_cast (show A.card ≤ m by dsimp [A]; rw [Scard]; exact (hattach a b hab).2.2)
    have hfrac : ((A.card : ℝ) - 1) / A.card ≤ 1 - 1 / (m : ℝ) := by
      have hinv := one_div_le_one_div_of_le hA hAm
      rw [show ((A.card : ℝ) - 1) / A.card = 1 - 1 / A.card by field_simp [hA.ne']]
      linarith
    rw [he, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_pos (inv_pos.mpr hA)]
    calc
      _ ≤ (1 / 2 : ℝ) * ((A.card : ℝ)⁻¹ * ∑ t ∈ A, ‖D a b s - D a b t‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hA.le)) (by norm_num)
      _ ≤ (1 / 2 : ℝ) * ((A.card : ℝ)⁻¹ * (((A.erase s).card : ℝ) * (2 * R))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hA.le)) (by norm_num)
      _ = ((A.card : ℝ) - 1) / A.card * R := by rw [hcard]; ring
      _ ≤ B := mul_le_mul_of_nonneg_right hfrac hR
  have adjacent (a b : I) {x : V} (ha : x ∈ P a) (hb : x ∈ P b) (hne : a ≠ b) :
      T.Adj a b := by
    by_contra hn
    exact Set.disjoint_left.mp (hdisjoint a b hne hn) ha hb
  have unique (a b c : I) {x : V} (ha : x ∈ P a) (hb : x ∈ P b) (hc' : x ∈ P c)
      (hab : a ≠ b) (hac : a ≠ c) : b = c := by
    by_contra hbc
    exact Set.disjoint_left.mp (hsep a b c (adjacent a b ha hb hab)
      (adjacent a c ha hc' hac) hbc).1 ⟨ha, hb⟩ ⟨ha, hc'⟩
  let attached (a : I) (x : V) := ∃ b, a ≠ b ∧ x ∈ P b
  let mid (a : I) (x : V) := if h : attached a x then
      (1 / 2 : ℝ) • (ψ a x + ψ h.choose x) else ψ a x
  have midShared (a b : I) (x : V) (ha : x ∈ P a) (hb : x ∈ P b) (hab : a ≠ b) :
      mid a x = (1 / 2 : ℝ) • (ψ a x + ψ b x) := by
    have h : attached a x := ⟨b, hab, hb⟩
    have he := unique a h.choose b ha h.choose_spec.2 hb h.choose_spec.1 hab
    simp [mid, h, he]
  let Φ (x : V) := mid (hcover x).choose x
  have localValue (a : I) (x : V) (hx : x ∈ P a) : Φ x = mid a x := by
    let b := (hcover x).choose
    have hb : x ∈ P b := (hcover x).choose_spec
    change mid b x = mid a x
    by_cases hab : a = b
    · rw [hab]
    · rw [midShared b a x hb hx (Ne.symm hab), midShared a b x hx hb hab, add_comm]
  have shift (a : I) (x : V) (hx : x ∈ P a) : ‖mid a x - ψ a x‖ ≤ B := by
    by_cases h : attached a x
    · obtain ⟨b, hab, hb⟩ := h
      rw [midShared a b x hx hb hab,
        show (1 / 2 : ℝ) • (ψ a x + ψ b x) - ψ a x = (1 / 2 : ℝ) • D a b x by
          dsimp [D]; rw [smul_add, smul_sub]; module]
      exact bound a b (adjacent a b hx hb hab) x ⟨hx, hb⟩
    · simp [mid, h, hB]
  have hradius : (2 - 1 / (m : ℝ)) * R = R + B := by dsimp [B]; ring
  refine ⟨Φ, fun u v huv => ?_⟩
  obtain ⟨a, hu, hv⟩ := hedge u v huv
  rw [localValue a u hu, localValue a v hv, hradius]
  by_cases huA : attached a u
  · by_cases hvA : attached a v
    · obtain ⟨b, hab, hub⟩ := huA
      obtain ⟨b', hab', hvb'⟩ := hvA
      have heq : b = b' := by
        by_contra hh
        exact (hsep a b b' (adjacent a b hu hub hab) (adjacent a b' hv hvb' hab') hh).2
          u ⟨hu, hub⟩ v ⟨hv, hvb'⟩ huv
      subst b'
      rw [midShared a b u hu hub hab, midShared a b v hv hvb' hab]
      have he : g u v - ((1 / 2 : ℝ) • (ψ a v + ψ b v) -
          (1 / 2 : ℝ) • (ψ a u + ψ b u)) =
          (1 / 2 : ℝ) • ((g u v - (ψ a v - ψ a u)) + (g u v - (ψ b v - ψ b u))) := by
        module
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      calc
        _ ≤ (1 / 2 : ℝ) * (‖g u v - (ψ a v - ψ a u)‖ + ‖g u v - (ψ b v - ψ b u)‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
        _ ≤ R + B := by linarith [fit a u hu v hv huv, fit b u hub v hvb' huv]
    · rw [show mid a v = ψ a v by simp [mid, hvA]]
      rw [show g u v - (ψ a v - mid a u) =
        (g u v - (ψ a v - ψ a u)) + (mid a u - ψ a u) by abel]
      exact (norm_add_le _ _).trans (add_le_add (fit a u hu v hv huv) (shift a u hu))
  · rw [show mid a u = ψ a u by simp [mid, huA]]
    rw [show g u v - (mid a v - ψ a u) =
      (g u v - (ψ a v - ψ a u)) - (mid a v - ψ a v) by abel]
    exact (norm_sub_le _ _).trans (add_le_add (fit a u hu v hv huv) (shift a v hv))

end CliqueSums

example : Nonempty (Fin 2) := ⟨0⟩

example : ∃ g : Fin 2 → Fin 2 → ℝ, (∀ i j, g j i = -g i j) ∧
    (∀ i j l, i ≠ j → j ≠ l → i ≠ l → ‖g i j + g j l - g i l‖ ≤ 0) :=
  ⟨fun _ _ => 0, by simp, by simp⟩

#print axioms completeGraph_banach_upper_bound
#print axioms completeGraph_banach_lower_bound
#print axioms separatedCliqueSum_banach_gain_potential

end SimpleGraph
