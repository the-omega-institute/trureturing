/- GID: D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Fixed-resistance Fiedler optimization on labelled complete bipartite graphs. -/

import D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceInvariantWeightsRefutation
import D5.S3.Combinatorics.SpectralGraph.AlbrightKemenyEdgeDerivativeRefutation
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.BigOperators.Sym
import Mathlib.Tactic

set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer

open FiedlerResistanceInvariantWeightsRefutation

def K2m (m : ℕ) : SimpleGraph (Fin (2 + m)) :=
  (completeBipartiteGraph (Fin 2) (Fin m)).comap finSumFinEquiv.symm

instance (m : ℕ) : DecidableRel (K2m m).Adj := by
  unfold K2m SimpleGraph.comap completeBipartiteGraph
  infer_instance

private def hub (m : ℕ) (j : Fin 2) : Fin (2 + m) := j.castAdd m
private def leaf (m : ℕ) (i : Fin m) : Fin (2 + m) := i.natAdd 2

private lemma adj_hub_hub (m : ℕ) (i j : Fin 2) :
    ¬ (K2m m).Adj (hub m i) (hub m j) := by
  simp [K2m, SimpleGraph.comap, completeBipartiteGraph, hub, finSumFinEquiv]

private lemma adj_leaf_leaf (m : ℕ) (i j : Fin m) :
    ¬ (K2m m).Adj (leaf m i) (leaf m j) := by
  simp [K2m, SimpleGraph.comap, completeBipartiteGraph, leaf, finSumFinEquiv]

private lemma adj_hub_leaf (m : ℕ) (i : Fin 2) (j : Fin m) :
    (K2m m).Adj (hub m i) (leaf m j) := by
  simp [K2m, SimpleGraph.comap, completeBipartiteGraph, hub, leaf, finSumFinEquiv]

private lemma sum_vertices {m : ℕ} (f : Fin (2 + m) → ℝ) :
    ∑ i, f i = f (hub m 0) + f (hub m 1) + ∑ i, f (leaf m i) := by
  rw [Fin.sum_univ_add]
  simp [hub, leaf, Fin.sum_univ_two]

private lemma lap_mul {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    (wLap G w *ᵥ x) i = ∑ j with G.Adj i j, w s(i,j) * (x i - x j) := by
  have he (j : Fin n) : wLap G w i j =
      (if i = j then ∑ k with G.Adj i k, w s(i,k) else 0) -
      (if G.Adj i j then w s(i,j) else 0) := by
    by_cases h : i = j
    · subst j; simp [wLap]
    · simp [wLap, h]; split_ifs <;> ring
  simp only [Matrix.mulVec, dotProduct, he, sub_mul, Finset.sum_sub_distrib]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, mem_univ, ite_true]
  simp only [Finset.sum_filter, mul_sub, Finset.sum_sub_distrib]
  rw [Finset.sum_mul]
  congr 1
  all_goals apply Finset.sum_congr rfl; intro j hj; split_ifs <;> ring

private lemma lap_mul_hub {m : ℕ} (w : Sym2 (Fin (2 + m)) → ℝ)
    (x : Fin (2 + m) → ℝ) (j : Fin 2) :
    (wLap (K2m m) w *ᵥ x) (hub m j) =
      ∑ i, w s(hub m j,leaf m i) * (x (hub m j) - x (leaf m i)) := by
  rw [lap_mul]
  simp only [Finset.sum_filter, sum_vertices, adj_hub_hub, adj_hub_leaf,
    ite_false, ite_true, zero_add]

private lemma lap_mul_leaf {m : ℕ} (w : Sym2 (Fin (2 + m)) → ℝ)
    (x : Fin (2 + m) → ℝ) (i : Fin m) :
    (wLap (K2m m) w *ᵥ x) (leaf m i) =
      w s(hub m 0,leaf m i) * (x (leaf m i) - x (hub m 0)) +
      w s(hub m 1,leaf m i) * (x (leaf m i) - x (hub m 1)) := by
  rw [lap_mul]
  simp only [Finset.sum_filter, sum_vertices, adj_leaf_leaf,
    (adj_hub_leaf m 0 i).symm, (adj_hub_leaf m 1 i).symm, ite_true, ite_false,
    Finset.sum_const_zero, add_zero]
  congr 2 <;> exact congrArg w Sym2.eq_swap

private lemma energy {m : ℕ} (w : Sym2 (Fin (2 + m)) → ℝ)
    (x : Fin (2 + m) → ℝ) :
    dotProduct x (wLap (K2m m) w *ᵥ x) =
      ∑ i, (w s(hub m 0,leaf m i) * (x (hub m 0) - x (leaf m i)) ^ 2 +
        w s(hub m 1,leaf m i) * (x (hub m 1) - x (leaf m i)) ^ 2) := by
  simp only [dotProduct, sum_vertices, lap_mul_hub, lap_mul_leaf,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private lemma lap_hermitian {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) : (wLap G w).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  ext i j
  change wLap G w j i = wLap G w i j
  by_cases h : i = j
  · subst j; rfl
  · simp only [wLap, if_neg h, if_neg (Ne.symm h), G.adj_comm]
    rw [Sym2.eq_swap]

private lemma lap_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) : wLap G w *ᵥ (1 : Fin n → ℝ) = 0 := by
  ext i
  simp [lap_mul]

private lemma energy_nonneg {m : ℕ} (w : Sym2 (Fin (2 + m)) → ℝ)
    (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) (x : Fin (2 + m) → ℝ) :
    0 ≤ dotProduct x (wLap (K2m m) w *ᵥ x) := by
  rw [energy]
  apply Finset.sum_nonneg
  intro i hi
  have ha := hw s(hub m 0,leaf m i) (by simpa using adj_hub_leaf m 0 i)
  have hb := hw s(hub m 1,leaf m i) (by simpa using adj_hub_leaf m 1 i)
  positivity

private lemma energy_zero_iff {m : ℕ} (hm : 0 < m)
    (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e)
    (x : Fin (2 + m) → ℝ) :
    dotProduct x (wLap (K2m m) w *ᵥ x) = 0 ↔ ∃ c : ℝ, x = fun _ => c := by
  constructor
  · intro hx
    rw [energy] at hx
    have hterms (i : Fin m) :
        w s(hub m 0,leaf m i) * (x (hub m 0) - x (leaf m i)) ^ 2 +
        w s(hub m 1,leaf m i) * (x (hub m 1) - x (leaf m i)) ^ 2 = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by
        have ha := hw s(hub m 0,leaf m j) (by simpa using adj_hub_leaf m 0 j)
        have hb := hw s(hub m 1,leaf m j) (by simpa using adj_hub_leaf m 1 j)
        positivity)).mp hx i (Finset.mem_univ i)
    have hcoords (i : Fin m) : x (hub m 0) = x (leaf m i) ∧
        x (hub m 1) = x (leaf m i) := by
      have ha := hw s(hub m 0,leaf m i) (by simpa using adj_hub_leaf m 0 i)
      have hb := hw s(hub m 1,leaf m i) (by simpa using adj_hub_leaf m 1 i)
      have hz := hterms i
      have hza : (x (hub m 0) - x (leaf m i)) ^ 2 = 0 := by
        nlinarith [mul_nonneg hb.le (sq_nonneg (x (hub m 1) - x (leaf m i)))]
      have hzb : (x (hub m 1) - x (leaf m i)) ^ 2 = 0 := by
        nlinarith [mul_nonneg ha.le (sq_nonneg (x (hub m 0) - x (leaf m i)))]
      constructor <;> nlinarith
    refine ⟨x (hub m 0), ?_⟩
    funext k
    refine Fin.addCases (fun j => ?_) (fun i => ?_) k
    · fin_cases j
      · rfl
      · exact (hcoords ⟨0,hm⟩).2.trans (hcoords ⟨0,hm⟩).1.symm
    · exact (hcoords i).1.symm
  · rintro ⟨c,rfl⟩
    rw [energy]
    simp

private def constProj (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun _ _ => (n : ℝ)⁻¹

private lemma proj_hermitian (n : ℕ) : (constProj n).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [constProj]

private lemma proj_mul {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    (constProj n *ᵥ x) i = (∑ j, x j) / n := by
  simp only [Matrix.mulVec, dotProduct, constProj, ← Finset.mul_sum]
  ring

private lemma proj_energy {n : ℕ} (x : Fin n → ℝ) :
    dotProduct x (constProj n *ᵥ x) = (∑ j, x j) ^ 2 / n := by
  simp only [dotProduct, proj_mul, ← Finset.sum_mul]
  ring

private lemma proj_sq {n : ℕ} (hn : 0 < n) : constProj n * constProj n = constProj n := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  ext i j
  simp [Matrix.mul_apply, constProj]
  field_simp

private lemma lap_proj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) : wLap G w * constProj n = 0 := by
  have hrow (i : Fin n) : ∑ j, wLap G w i j = 0 := by
    have h := congrFun (lap_one G w) i
    simpa [Matrix.mulVec, dotProduct] using h
  ext i j
  simp [Matrix.mul_apply, constProj, ← Finset.sum_mul, hrow]

private lemma proj_lap {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) : constProj n * wLap G w = 0 := by
  have h := congrArg Matrix.transpose (lap_proj G w)
  simpa only [Matrix.transpose_mul, (proj_hermitian n).isSymm.eq,
    (lap_hermitian G w).isSymm.eq, Matrix.transpose_zero] using h

private lemma lap_sum {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (x : Fin n → ℝ) : ∑ i, (wLap G w *ᵥ x) i = 0 := by
  have h := Matrix.dotProduct_mulVec (1 : Fin n → ℝ) (wLap G w) x
  rw [← (lap_hermitian G w).isSymm.eq, Matrix.vecMul_transpose, lap_one] at h
  simpa [dotProduct, (lap_hermitian G w).isSymm.eq] using h

private lemma shifted_posDef {m : ℕ} (hm : 0 < m)
    (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) :
    (wLap (K2m m) w + constProj (2 + m)).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact (lap_hermitian _ _).add (proj_hermitian _)
  · intro x hx
    simp only [star_trivial, Matrix.add_mulVec, dotProduct_add]
    rw [proj_energy]
    have hE := energy_nonneg w hw x
    have hP : 0 ≤ (∑ j, x j) ^ 2 / (2 + m : ℕ) := by positivity
    by_contra! h
    have hz : dotProduct x (wLap (K2m m) w *ᵥ x) = 0 := by linarith
    obtain ⟨c,rfl⟩ := (energy_zero_iff hm w hw x).mp hz
    have hc : c ≠ 0 := by
      intro hc
      apply hx
      ext i
      exact hc
    have hn : (0 : ℝ) < (2 + m : ℕ) := by positivity
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hP h
    have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
    have hp : 0 < ((2 + m : ℕ) * c) ^ 2 / (2 + m : ℕ) := by positivity
    linarith

private def shiftInv {m : ℕ} (w : Sym2 (Fin (2 + m)) → ℝ) :=
  (wLap (K2m m) w + constProj (2 + m))⁻¹

private lemma inverse_properties {m : ℕ} (hm : 0 < m)
    (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) :
    (shiftInv w).PosDef ∧
    wLap (K2m m) w * shiftInv w = 1 - constProj (2 + m) ∧
    shiftInv w * constProj (2 + m) = constProj (2 + m) ∧
    constProj (2 + m) * shiftInv w = constProj (2 + m) := by
  have hB := shifted_posDef hm w hw
  have hN : (shiftInv w).PosDef := hB.inv
  have hBN : (wLap (K2m m) w + constProj (2 + m)) * shiftInv w = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hB.isUnit)
  have hNB : shiftInv w * (wLap (K2m m) w + constProj (2 + m)) = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hB.isUnit)
  have hBP : (wLap (K2m m) w + constProj (2 + m)) * constProj (2 + m) =
      constProj (2 + m) := by
    rw [add_mul, lap_proj, proj_sq (by omega), zero_add]
  have hNP : shiftInv w * constProj (2 + m) = constProj (2 + m) := by
    calc
      _ = shiftInv w * ((wLap (K2m m) w + constProj (2 + m)) * constProj (2 + m)) := by rw [hBP]
      _ = _ := by rw [← mul_assoc, hNB, one_mul]
  have hPN : constProj (2 + m) * shiftInv w = constProj (2 + m) := by
    have h := congrArg Matrix.transpose hNP
    simpa only [Matrix.transpose_mul, hN.1.isSymm.eq, (proj_hermitian _).isSymm.eq] using h
  refine ⟨hN, ?_, hNP, hPN⟩
  rw [add_mul, hPN] at hBN
  exact eq_sub_iff_add_eq.mpr hBN

private def delta {n : ℕ} (p q : Fin n) : Fin n → ℝ := Pi.single p 1 - Pi.single q 1

private lemma delta_sum {n : ℕ} (p q : Fin n) : ∑ i, delta p q i = 0 := by
  simp [delta, Finset.sum_sub_distrib]

private lemma delta_dot {n : ℕ} (p q : Fin n) (x : Fin n → ℝ) :
    dotProduct (delta p q) x = x p - x q := by
  simp [delta, sub_dotProduct]

private lemma delta_ne {n : ℕ} {p q : Fin n} (hpq : p ≠ q) : delta p q ≠ 0 := by
  intro h
  have := congrFun h p
  simp [delta, hpq] at this

private lemma proj_delta {n : ℕ} (p q : Fin n) : constProj n *ᵥ delta p q = 0 := by
  ext i
  simp [proj_mul, delta_sum]

private lemma inv_delta_equation {m : ℕ} (hm : 0 < m)
    (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e)
    (p q : Fin (2 + m)) :
    wLap (K2m m) w *ᵥ (shiftInv w *ᵥ delta p q) = delta p q := by
  rw [Matrix.mulVec_mulVec, (inverse_properties hm w hw).2.1,
    Matrix.sub_mulVec, Matrix.one_mulVec, proj_delta, sub_zero]

private lemma harmonic_unique {m : ℕ} (hm : 0 < m)
    (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e)
    (p q : Fin (2 + m)) (x y : Fin (2 + m) → ℝ)
    (hx : Harmonic (K2m m) w p q x) (hy : Harmonic (K2m m) w p q y) : x = y := by
  have hp : (x-y) p = 0 := by simp [hx.1,hy.1]
  have hq : (x-y) q = 0 := by simp [hx.2.1,hy.2.1]
  have hE : dotProduct (x-y) (wLap (K2m m) w *ᵥ (x-y)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hip : i = p
    · subst i; simp [hp]
    by_cases hiq : i = q
    · subst i; simp [hq]
    simp [Matrix.mulVec_sub, hx.2.2 i hip hiq, hy.2.2 i hip hiq]
  obtain ⟨c,hc⟩ := (energy_zero_iff hm w hw (x-y)).mp hE
  have hcz : c = 0 := by simpa [hp] using (congrFun hc p).symm
  exact sub_eq_zero.mp (hc.trans (by ext i; exact hcz))

private lemma harmonic_resistance {m : ℕ} (hm : 0 < m)
    (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e)
    (p q : Fin (2 + m)) (hpq : p ≠ q) :
    (∃! x, Harmonic (K2m m) w p q x) ∧
    effRes (K2m m) w p q =
      (shiftInv w *ᵥ delta p q) p - (shiftInv w *ᵥ delta p q) q := by
  let v := shiftInv w *ᵥ delta p q
  let d := v p - v q
  have hd : 0 < d := by
    have h := (inverse_properties hm w hw).1.dotProduct_mulVec_pos (delta_ne hpq)
    simpa only [star_trivial, delta_dot] using h
  let h : Fin (2 + m) → ℝ := fun i => (v i - v q) / d
  have hLp : wLap (K2m m) w *ᵥ h = d⁻¹ • delta p q := by
    have he : h = d⁻¹ • (v - v q • (1 : Fin (2 + m) → ℝ)) := by
      ext i; simp [h,div_eq_mul_inv,mul_comm]
    rw [he, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul,
      lap_one, smul_zero, sub_zero, inv_delta_equation hm w hw]
  have hh : Harmonic (K2m m) w p q h := by
    refine ⟨?_, ?_, ?_⟩
    · exact div_self hd.ne'
    · simp [h]
    · intro k hkp hkq
      rw [hLp]
      simp [delta, hkp, hkq]
  have he : harmonicExt (K2m m) w p q = h := by
    unfold harmonicExt
    rw [dif_pos ⟨h,hh⟩]
    exact harmonic_unique hm w hw p q _ h (Classical.choose_spec _) hh
  refine ⟨⟨h,hh,fun y hy => harmonic_unique hm w hw p q y h hy hh⟩, ?_⟩
  rw [effRes, if_neg hpq, he, hLp]
  simp [delta, hpq, hd.ne', d, v]

private lemma effRes_inverse {m : ℕ} (hm : 0 < m)
    (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e)
    (p q : Fin (2 + m)) :
    effRes (K2m m) w p q =
      shiftInv w p p + shiftInv w q q - shiftInv w p q - shiftInv w q p := by
  by_cases hpq : p = q
  · subst q; simp [effRes]
  · rw [(harmonic_resistance hm w hw p q hpq).2]
    simp only [delta, Matrix.mulVec_sub, Matrix.mulVec_single_one, Matrix.col_apply, Pi.sub_apply]
    ring

private lemma pairRes_inverse {m : ℕ} (hm : 0 < m)
    (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e)
    (p q : Fin (2 + m)) :
    pairRes (K2m m) w s(p,q) =
      shiftInv w p p + shiftInv w q q - shiftInv w p q - shiftInv w q p := by
  simp only [pairRes, Sym2.lift_mk, effRes_inverse hm w hw]
  rcases le_total p q with hpq | hqp
  · rw [min_eq_left hpq, max_eq_right hpq]
  · rw [min_eq_right hqp, max_eq_left hqp]; ring

private lemma double_sum_lt {n : ℕ} (f : Fin n → Fin n → ℝ)
    (hsymm : ∀ i j, f i j = f j i) (hdiag : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = 2 * ∑ i, ∑ j with i < j, f i j := by
  have hsplit : (∑ i, ∑ j, f i j) =
      (∑ i, ∑ j with i < j, f i j) + (∑ i, ∑ j with j < i, f i j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt.mpr h.le]
    · subst j; simp [hdiag]
    · simp [h, not_lt.mpr h.le]
  have hswap : (∑ i, ∑ j with j < i, f i j) = ∑ i, ∑ j with i < j, f i j := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsymm j i]
  rw [hsplit, hswap]
  ring

private lemma totalRes_twice {m : ℕ} (hm : 0 < m)
    (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) :
    2 * totalRes (K2m m) w =
      ∑ p, ∑ q, (shiftInv w p p + shiftInv w q q - shiftInv w p q - shiftInv w q p) := by
  let f := fun p q => shiftInv w p p + shiftInv w q q - shiftInv w p q - shiftInv w q p
  have hs : (Finset.univ : Finset (Fin (2+m))).sym2 = Finset.univ := by ext p; simp
  have ht : ((Finset.univ : Finset (Fin (2+m))).offDiag.filter fun p => p.1 < p.2) =
      (Finset.univ ×ˢ Finset.univ).filter (fun p : Fin (2+m) × Fin (2+m) => p.1 < p.2) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ,
      Finset.mem_product, true_and]
    exact and_iff_right_of_imp (fun h => ne_of_lt h)
  rw [totalRes, ← hs, Finset.sum_sym2_filter_not_isDiag, ht]
  simp only [Finset.sum_filter, Finset.sum_product, pairRes_inverse hm w hw]
  simpa only [f, Finset.sum_filter] using
    (double_sum_lt f (by intro i j; dsimp [f]; ring) (by intro i; dsimp [f]; ring)).symm

private lemma inverse_row_sum {m : ℕ} (hm : 0 < m)
    (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e)
    (i : Fin (2+m)) : ∑ j, shiftInv w i j = 1 := by
  have h := congrArg (fun M : Matrix (Fin (2+m)) (Fin (2+m)) ℝ => M i 0)
    (inverse_properties hm w hw).2.2.1
  simp only [Matrix.mul_apply, constProj, ← Finset.sum_mul] at h
  have hn : (2+m : ℝ) ≠ 0 := by positivity
  apply mul_right_cancel₀ (inv_ne_zero hn)
  simpa only [one_mul, Nat.cast_add, Nat.cast_ofNat] using h

private lemma totalRes_trace {m : ℕ} (hm : 0 < m)
    (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) :
    totalRes (K2m m) w = (2+m : ℕ) * ((shiftInv w).trace - 1) := by
  have h := totalRes_twice hm w hw
  have hsum : (∑ p, ∑ q, shiftInv w p q) = (2+m : ℕ) := by
    simp_rw [inverse_row_sum hm w hw]
    simp
  have hsum' : (∑ p, ∑ q, shiftInv w q p) = (2+m : ℕ) := by
    rw [Finset.sum_comm]; exact hsum
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_mul,
    ← Finset.mul_sum, hsum, hsum'] at h
  simp only [Matrix.trace, Matrix.diag_apply]
  nlinarith

private lemma projection_spectral {m : ℕ} (hm : 0 < m)
    (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) :
    let hL := lap_hermitian (K2m m) w
    Unitary.conjStarAlgAut ℝ _ (star hL.eigenvectorUnitary) (constProj (2+m)) =
      diagonal (fun i => if hL.eigenvalues i = 0 then 1 else 0) := by
  dsimp only
  let hL := lap_hermitian (K2m m) w
  let f := Unitary.conjStarAlgAut ℝ (Matrix (Fin (2+m)) (Fin (2+m)) ℝ)
    (star hL.eigenvectorUnitary)
  have hfL : f (wLap (K2m m) w) = diagonal hL.eigenvalues := by
    simpa [f] using hL.conjStarAlgAut_star_eigenvectorUnitary
  have hDN := congrArg f (inverse_properties hm w hw).2.1
  have hDQ := congrArg f (lap_proj (K2m m) w)
  simp only [map_mul, map_sub, map_one, hfL] at hDN
  simp only [map_mul, map_zero, hfL] at hDQ
  change f (constProj (2+m)) = _
  ext i j
  by_cases hi : hL.eigenvalues i = 0
  · have h := congrArg (fun M : Matrix (Fin (2+m)) (Fin (2+m)) ℝ => M i j) hDN
    simp only [Matrix.diagonal_mul, hi, zero_mul, Matrix.sub_apply] at h
    simp only [Matrix.diagonal_apply, hi, ite_true, Matrix.one_apply] at ⊢
    simp only [Matrix.one_apply] at h
    linarith
  · have h := congrArg (fun M : Matrix (Fin (2+m)) (Fin (2+m)) ℝ => M i j) hDQ
    simp only [Matrix.diagonal_mul, Matrix.zero_apply] at h
    have hz := (mul_eq_zero.mp h).resolve_left hi
    simp [Matrix.diagonal_apply, hi, hz]

private lemma zero_eigenvalue_count {m : ℕ} (hm : 0 < m)
    (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) :
    (Finset.univ.filter (fun i => (lap_hermitian (K2m m) w).eigenvalues i = 0)).card = 1 := by
  let hL := lap_hermitian (K2m m) w
  let f := Unitary.conjStarAlgAut ℝ (Matrix (Fin (2+m)) (Fin (2+m)) ℝ)
    (star hL.eigenvectorUnitary)
  have htr : (f (constProj (2+m))).trace = (constProj (2+m)).trace := trace_map f _
  rw [projection_spectral hm w hw] at htr
  have hn : (2+m : ℝ) ≠ 0 := by positivity
  simp only [Matrix.trace_diagonal, Matrix.trace, Matrix.diag_apply, constProj,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_ofNat, mul_inv_cancel₀ hn] at htr
  simp only [Matrix.diagonal_apply_eq] at htr
  simp only [Finset.sum_boole] at htr
  exact_mod_cast htr

private lemma lap_psd {m : ℕ}
    (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) :
    (wLap (K2m m) w).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (lap_hermitian _ _)
  intro x
  simpa only [star_trivial] using energy_nonneg w hw x

private lemma centered_psd {m : ℕ} (hm : 0 < m)
    (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e)
    (t : ℝ) (ht : ∀ i, (lap_hermitian (K2m m) w).eigenvalues i ≠ 0 →
      t ≤ (lap_hermitian (K2m m) w).eigenvalues i) :
    (wLap (K2m m) w - t • (1 - constProj (2+m))).PosSemidef := by
  let hL := lap_hermitian (K2m m) w
  let f := Unitary.conjStarAlgAut ℝ (Matrix (Fin (2+m)) (Fin (2+m)) ℝ)
    (star hL.eigenvectorUnitary)
  have hfL : f (wLap (K2m m) w) = diagonal hL.eigenvalues := by
    simpa [f] using hL.conjStarAlgAut_star_eigenvectorUnitary
  have hM : f (wLap (K2m m) w - t • (1 - constProj (2+m))) =
      diagonal (fun i => hL.eigenvalues i - t * (1 - if hL.eigenvalues i = 0 then 1 else 0)) := by
    rw [map_sub, map_smul, map_sub, map_one, hfL, projection_spectral hm w hw]
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
  have hpos : (f (wLap (K2m m) w - t • (1 - constProj (2+m)))).PosSemidef := by
    rw [hM, Matrix.posSemidef_diagonal_iff]
    intro i
    by_cases hi : hL.eigenvalues i = 0
    · simp [hi]
    · simpa only [hi, ite_false, sub_zero, mul_one] using sub_nonneg.mpr (ht i hi)
  simpa only [f, Unitary.conjStarAlgAut_apply,
    Unitary.isUnit_coe.posSemidef_star_right_conjugate_iff] using hpos

private lemma psd_rayleigh {m : ℕ} (w : Sym2 (Fin (2+m)) → ℝ) (t : ℝ)
    (hP : (wLap (K2m m) w - t • (1 - constProj (2+m))).PosSemidef)
    (x : Fin (2+m) → ℝ) (hx : ∑ i, x i = 0) :
    t * dotProduct x x ≤ dotProduct x (wLap (K2m m) w *ᵥ x) := by
  have hp : constProj (2+m) *ᵥ x = 0 := by ext i; simp [proj_mul,hx]
  have h := hP.dotProduct_mulVec_nonneg x
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    hp, sub_zero, dotProduct_sub, dotProduct_smul, smul_eq_mul] at h
  linarith

private lemma lambda2_spectral {m : ℕ} (hm : 0 < m)
    (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) :
    0 < lambda2 (K2m m) w ∧
    (wLap (K2m m) w - lambda2 (K2m m) w • (1 - constProj (2+m))).PosSemidef ∧
    (∀ i, (lap_hermitian (K2m m) w).eigenvalues i ≠ 0 →
      lambda2 (K2m m) w ≤ (lap_hermitian (K2m m) w).eigenvalues i) := by
  let hL := lap_hermitian (K2m m) w
  let e := hL.eigenvalues
  let J := Finset.univ.filter (fun i => e i ≠ 0)
  have hcard : J.card = m+1 := by
    have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => e i = 0)
    rw [zero_eigenvalue_count hm w hw] at hc
    simp only [Finset.card_univ,Fintype.card_fin] at hc
    dsimp [J]
    omega
  have hJ : J.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i, hi, hmin⟩ := J.exists_min_image e hJ
  have hi0 : e i ≠ 0 := (Finset.mem_filter.mp hi).2
  have hepos : 0 < e i := lt_of_le_of_ne ((lap_psd w hw).eigenvalues_nonneg i) (Ne.symm hi0)
  have hmin' : ∀ j, e j ≠ 0 → e i ≤ e j := fun j hj => hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩)
  have hP := centered_psd hm w hw (e i) hmin'
  let v : Fin (2+m) → ℝ := ⇑(hL.eigenvectorBasis i)
  have hv : v ≠ 0 := (WithLp.ofLp_eq_zero 2).ne.2 (hL.eigenvectorBasis.orthonormal.ne_zero i)
  have heigen : wLap (K2m m) w *ᵥ v = e i • v := hL.mulVec_eigenvectorBasis i
  have hsum : ∑ j, v j = 0 := by
    have hs := lap_sum (K2m m) w v
    rw [heigen] at hs
    simp only [Pi.smul_apply,smul_eq_mul,← Finset.mul_sum] at hs
    exact (mul_eq_zero.mp hs).resolve_left hi0
  have hval : lambda2 (K2m m) w = e i := lambda2_eq_of_rayleigh _ _ _
    (fun x hx => psd_rayleigh w (e i) hP x hx) v hv hsum heigen
  rw [hval]
  exact ⟨hepos,hP,hmin'⟩

private lemma resistance_spectral {m : ℕ} (hm : 0 < m)
    (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) :
    totalRes (K2m m) w = (2+m : ℕ) *
      ∑ i, ((lap_hermitian (K2m m) w).eigenvalues i)⁻¹ := by
  let L := wLap (K2m m) w
  let P := constProj (2+m)
  let T := shiftInv w - P
  have hLT : L * T = 1-P := by
    dsimp [L,T,P]
    rw [mul_sub, (inverse_properties hm w hw).2.1, lap_proj, sub_zero]
  have hPT : P * T = 0 := by
    dsimp [P,T]
    rw [mul_sub, (inverse_properties hm w hw).2.2.2, proj_sq (by omega), sub_self]
  have h := AlbrightKemenyEdgeDerivativeRefutation.reciprocalRoots_eq_trace
    L P T (lap_hermitian _ _) hLT (lap_proj _ _) hPT
  rw [AlbrightKemenyEdgeDerivativeRefutation.reciprocalRoots_eq_sum L (lap_hermitian _ _)] at h
  have hn : (2+m : ℝ) ≠ 0 := by positivity
  have hPtr : P.trace = 1 := by
    simp [P,Matrix.trace,constProj,Nat.cast_add,Nat.cast_ofNat,hn]
  rw [totalRes_trace hm w hw]
  congr 1
  rw [h]
  dsimp [T]
  rw [Matrix.trace_sub, hPtr]

end D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer
