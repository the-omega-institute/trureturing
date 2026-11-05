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
/-! The ordinary weighted K₂,ₘ Laplacian and harmonic resistance determine exactly two fixed-resistance Fiedler maximizers. -/
set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer
open FiedlerResistanceInvariantWeightsRefutation
def K2m (m : ℕ) : SimpleGraph (Fin (2 + m)) :=
  (completeBipartiteGraph (Fin 2) (Fin m)).comap finSumFinEquiv.symm
instance K2m_dec (m : ℕ) : DecidableRel (K2m m).Adj := by
  unfold K2m SimpleGraph.comap completeBipartiteGraph
  infer_instance
def hub (m : ℕ) (j : Fin 2) : Fin (2 + m) := j.castAdd m
def leaf (m : ℕ) (i : Fin m) : Fin (2 + m) := i.natAdd 2
lemma adj_hub_hub (m : ℕ) (i j : Fin 2) : ¬ (K2m m).Adj (hub m i) (hub m j) := by
  simp [K2m, SimpleGraph.comap, completeBipartiteGraph, hub, finSumFinEquiv]
lemma adj_leaf_leaf (m : ℕ) (i j : Fin m) : ¬ (K2m m).Adj (leaf m i) (leaf m j) := by
  simp [K2m, SimpleGraph.comap, completeBipartiteGraph, leaf, finSumFinEquiv]
private lemma adj_hub_leaf (m : ℕ) (i : Fin 2) (j : Fin m) : (K2m m).Adj (hub m i) (leaf m j) := by
  simp [K2m, SimpleGraph.comap, completeBipartiteGraph, hub, leaf, finSumFinEquiv]
private lemma sum_vertices {m : ℕ} (f : Fin (2 + m) → ℝ) : ∑ i, f i = f (hub m 0) + f (hub m 1) + ∑ i, f (leaf m i) := by
  rw [Fin.sum_univ_add]
  simp [hub, leaf, Fin.sum_univ_two]
lemma lap_mul {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℝ) (x : Fin n → ℝ) (i : Fin n) : (wLap G w *ᵥ x) i = ∑ j with G.Adj i j, w s(i,j) * (x i - x j) := by
  have he (j : Fin n) : wLap G w i j = (if i = j then ∑ k with G.Adj i k, w s(i,k) else 0) - (if G.Adj i j then w s(i,j) else 0) := by
    by_cases h : i = j
    · subst j; simp [wLap]
    · simp [wLap, h]; split_ifs <;> ring
  simp only [Matrix.mulVec, dotProduct, he, sub_mul, Finset.sum_sub_distrib]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, mem_univ, ite_true]
  simp only [Finset.sum_filter, mul_sub, Finset.sum_sub_distrib]
  rw [Finset.sum_mul]
  congr 1
  all_goals apply Finset.sum_congr rfl; intro j hj; split_ifs <;> ring
private lemma lap_mul_hub {m : ℕ} (w : Sym2 (Fin (2 + m)) → ℝ) (x : Fin (2 + m) → ℝ) (j : Fin 2) : (wLap (K2m m) w *ᵥ x) (hub m j) = ∑ i, w s(hub m j,leaf m i) * (x (hub m j) - x (leaf m i)) := by
  rw [lap_mul]
  simp only [Finset.sum_filter, sum_vertices, adj_hub_hub, adj_hub_leaf, ite_false, ite_true, zero_add]
private lemma lap_mul_leaf {m : ℕ} (w : Sym2 (Fin (2 + m)) → ℝ) (x : Fin (2 + m) → ℝ) (i : Fin m) : (wLap (K2m m) w *ᵥ x) (leaf m i) = w s(hub m 0,leaf m i) * (x (leaf m i) - x (hub m 0)) +
      w s(hub m 1,leaf m i) * (x (leaf m i) - x (hub m 1)) := by
  rw [lap_mul]
  simp only [Finset.sum_filter, sum_vertices, adj_leaf_leaf, (adj_hub_leaf m 0 i).symm, (adj_hub_leaf m 1 i).symm, ite_true, ite_false, Finset.sum_const_zero, add_zero]
  congr 2 <;> exact congrArg w Sym2.eq_swap
private lemma energy {m : ℕ} (w : Sym2 (Fin (2 + m)) → ℝ) (x : Fin (2 + m) → ℝ) : dotProduct x (wLap (K2m m) w *ᵥ x) = ∑ i, (w s(hub m 0,leaf m i) * (x (hub m 0) - x (leaf m i)) ^ 2 +
        w s(hub m 1,leaf m i) * (x (hub m 1) - x (leaf m i)) ^ 2) := by
  simp only [dotProduct, sum_vertices, lap_mul_hub, lap_mul_leaf, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring
lemma lap_hermitian {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℝ) : (wLap G w).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  ext i j
  change wLap G w j i = wLap G w i j
  by_cases h : i = j
  · subst j; rfl
  · simp only [wLap, if_neg h, if_neg (Ne.symm h), G.adj_comm]
    rw [Sym2.eq_swap]
lemma lap_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℝ) : wLap G w *ᵥ (1 : Fin n → ℝ) = 0 := by
  ext i
  simp [lap_mul]
private lemma energy_nonneg {m : ℕ} (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) (x : Fin (2 + m) → ℝ) : 0 ≤ dotProduct x (wLap (K2m m) w *ᵥ x) := by
  rw [energy]
  apply Finset.sum_nonneg
  intro i hi
  have ha := hw s(hub m 0,leaf m i) (by simpa using adj_hub_leaf m 0 i)
  have hb := hw s(hub m 1,leaf m i) (by simpa using adj_hub_leaf m 1 i)
  positivity
private lemma energy_zero_iff {m : ℕ} (hm : 0 < m) (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) (x : Fin (2 + m) → ℝ) :
    dotProduct x (wLap (K2m m) w *ᵥ x) = 0 ↔ ∃ c : ℝ, x = fun _ => c := by
  constructor
  · intro hx
    rw [energy] at hx
    have hterms (i : Fin m) : w s(hub m 0,leaf m i) * (x (hub m 0) - x (leaf m i)) ^ 2 + w s(hub m 1,leaf m i) * (x (hub m 1) - x (leaf m i)) ^ 2 = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by
        have ha := hw s(hub m 0,leaf m j) (by simpa using adj_hub_leaf m 0 j)
        have hb := hw s(hub m 1,leaf m j) (by simpa using adj_hub_leaf m 1 j)
        positivity)).mp hx i (Finset.mem_univ i)
    have hcoords (i : Fin m) : x (hub m 0) = x (leaf m i) ∧ x (hub m 1) = x (leaf m i) := by
      have ha := hw s(hub m 0,leaf m i) (by simpa using adj_hub_leaf m 0 i)
      have hb := hw s(hub m 1,leaf m i) (by simpa using adj_hub_leaf m 1 i)
      have hz := hterms i
      have hza : (x (hub m 0) - x (leaf m i)) ^ 2 = 0 := by nlinarith [mul_nonneg hb.le (sq_nonneg (x (hub m 1) - x (leaf m i)))]
      have hzb : (x (hub m 1) - x (leaf m i)) ^ 2 = 0 := by nlinarith [mul_nonneg ha.le (sq_nonneg (x (hub m 0) - x (leaf m i)))]
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
def constProj (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun _ _ => (n : ℝ)⁻¹
lemma proj_hermitian (n : ℕ) : (constProj n).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [constProj]
lemma proj_mul {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : (constProj n *ᵥ x) i = (∑ j, x j) / n := by
  simp only [Matrix.mulVec, dotProduct, constProj, ← Finset.mul_sum]
  ring
lemma proj_energy {n : ℕ} (x : Fin n → ℝ) : dotProduct x (constProj n *ᵥ x) = (∑ j, x j) ^ 2 / n := by
  simp only [dotProduct, proj_mul, ← Finset.sum_mul]
  ring
lemma proj_sq {n : ℕ} (hn : 0 < n) : constProj n * constProj n = constProj n := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  ext i j
  simp [Matrix.mul_apply, constProj]
  field_simp
lemma lap_proj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℝ) : wLap G w * constProj n = 0 := by
  have hrow (i : Fin n) : ∑ j, wLap G w i j = 0 := by
    have h := congrFun (lap_one G w) i
    simpa [Matrix.mulVec, dotProduct] using h
  ext i j
  simp [Matrix.mul_apply, constProj, ← Finset.sum_mul, hrow]
lemma lap_sum {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℝ) (x : Fin n → ℝ) : ∑ i, (wLap G w *ᵥ x) i = 0 := by
  have h := Matrix.dotProduct_mulVec (1 : Fin n → ℝ) (wLap G w) x
  rw [← (lap_hermitian G w).isSymm.eq, Matrix.vecMul_transpose, lap_one] at h
  simpa [dotProduct, (lap_hermitian G w).isSymm.eq] using h
private lemma shifted_posDef {m : ℕ} (hm : 0 < m) (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) : (wLap (K2m m) w + constProj (2 + m)).PosDef := by
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
private lemma inverse_properties {m : ℕ} (hm : 0 < m) (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) : (shiftInv w).PosDef ∧ wLap (K2m m) w * shiftInv w = 1 - constProj (2 + m) ∧
    shiftInv w * constProj (2 + m) = constProj (2 + m) ∧ constProj (2 + m) * shiftInv w = constProj (2 + m) := by
  have hB := shifted_posDef hm w hw
  have hN : (shiftInv w).PosDef := hB.inv
  have hBN : (wLap (K2m m) w + constProj (2 + m)) * shiftInv w = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hB.isUnit)
  have hNB : shiftInv w * (wLap (K2m m) w + constProj (2 + m)) = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hB.isUnit)
  have hBP : (wLap (K2m m) w + constProj (2 + m)) * constProj (2 + m) = constProj (2 + m) := by
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
def delta {n : ℕ} (p q : Fin n) : Fin n → ℝ := Pi.single p 1 - Pi.single q 1
lemma delta_sum {n : ℕ} (p q : Fin n) : ∑ i, delta p q i = 0 := by simp [delta, Finset.sum_sub_distrib]
lemma delta_dot {n : ℕ} (p q : Fin n) (x : Fin n → ℝ) : dotProduct (delta p q) x = x p - x q := by
  simp [delta, sub_dotProduct]
lemma delta_ne {n : ℕ} {p q : Fin n} (hpq : p ≠ q) : delta p q ≠ 0 := by
  intro h
  have := congrFun h p
  simp [delta, hpq] at this
lemma proj_delta {n : ℕ} (p q : Fin n) : constProj n *ᵥ delta p q = 0 := by
  ext i
  simp [proj_mul, delta_sum]
private lemma inv_delta_equation {m : ℕ} (hm : 0 < m) (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) (p q : Fin (2 + m)) :
    wLap (K2m m) w *ᵥ (shiftInv w *ᵥ delta p q) = delta p q := by
  rw [Matrix.mulVec_mulVec, (inverse_properties hm w hw).2.1, Matrix.sub_mulVec, Matrix.one_mulVec, proj_delta, sub_zero]
private lemma harmonic_unique {m : ℕ} (hm : 0 < m) (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) (p q : Fin (2 + m)) (x y : Fin (2 + m) → ℝ)
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
private lemma harmonic_resistance {m : ℕ} (hm : 0 < m) (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) (p q : Fin (2 + m)) (hpq : p ≠ q) : (∃! x, Harmonic (K2m m) w p q x) ∧
    effRes (K2m m) w p q = (shiftInv w *ᵥ delta p q) p - (shiftInv w *ᵥ delta p q) q := by
  let v := shiftInv w *ᵥ delta p q
  let d := v p - v q
  have hd : 0 < d := by
    have h := (inverse_properties hm w hw).1.dotProduct_mulVec_pos (delta_ne hpq)
    simpa only [star_trivial, delta_dot] using h
  let h : Fin (2 + m) → ℝ := fun i => (v i - v q) / d
  have hLp : wLap (K2m m) w *ᵥ h = d⁻¹ • delta p q := by
    have he : h = d⁻¹ • (v - v q • (1 : Fin (2 + m) → ℝ)) := by ext i; simp [h,div_eq_mul_inv,mul_comm]
    rw [he, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, lap_one, smul_zero, sub_zero, inv_delta_equation hm w hw]
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
private lemma effRes_inverse {m : ℕ} (hm : 0 < m) (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) (p q : Fin (2 + m)) : effRes (K2m m) w p q =
      shiftInv w p p + shiftInv w q q - shiftInv w p q - shiftInv w q p := by
  by_cases hpq : p = q
  · subst q; simp [effRes]
  · rw [(harmonic_resistance hm w hw p q hpq).2]
    simp only [delta, Matrix.mulVec_sub, Matrix.mulVec_single_one, Matrix.col_apply, Pi.sub_apply]
    ring
private lemma pairRes_inverse {m : ℕ} (hm : 0 < m) (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) (p q : Fin (2 + m)) : pairRes (K2m m) w s(p,q) =
      shiftInv w p p + shiftInv w q q - shiftInv w p q - shiftInv w q p := by
  simp only [pairRes, Sym2.lift_mk, effRes_inverse hm w hw]
  rcases le_total p q with hpq | hqp
  · rw [min_eq_left hpq, max_eq_right hpq]
  · rw [min_eq_right hqp, max_eq_left hqp]; ring
lemma double_sum_lt {n : ℕ} (f : Fin n → Fin n → ℝ) (hsymm : ∀ i j, f i j = f j i) (hdiag : ∀ i, f i i = 0) : (∑ i, ∑ j, f i j) = 2 * ∑ i, ∑ j with i < j, f i j := by
  have hsplit : (∑ i, ∑ j, f i j) = (∑ i, ∑ j with i < j, f i j) + (∑ i, ∑ j with j < i, f i j) := by
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
private lemma totalRes_twice {m : ℕ} (hm : 0 < m) (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) : 2 * totalRes (K2m m) w =
      ∑ p, ∑ q, (shiftInv w p p + shiftInv w q q - shiftInv w p q - shiftInv w q p) := by
  let f := fun p q => shiftInv w p p + shiftInv w q q - shiftInv w p q - shiftInv w q p
  have hs : (Finset.univ : Finset (Fin (2+m))).sym2 = Finset.univ := by ext p; simp
  have ht : ((Finset.univ : Finset (Fin (2+m))).offDiag.filter fun p => p.1 < p.2) = (Finset.univ ×ˢ Finset.univ).filter (fun p : Fin (2+m) × Fin (2+m) => p.1 < p.2) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, Finset.mem_product, true_and]
    exact and_iff_right_of_imp (fun h => ne_of_lt h)
  rw [totalRes, ← hs, Finset.sum_sym2_filter_not_isDiag, ht]
  simp only [Finset.sum_filter, Finset.sum_product, pairRes_inverse hm w hw]
  simpa only [f, Finset.sum_filter] using
    (double_sum_lt f (by intro i j; dsimp [f]; ring) (by intro i; dsimp [f]; ring)).symm
private lemma inverse_row_sum {m : ℕ} (hm : 0 < m) (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) (i : Fin (2+m)) : ∑ j, shiftInv w i j = 1 := by
  have h := congrArg (fun M : Matrix (Fin (2+m)) (Fin (2+m)) ℝ => M i 0)
    (inverse_properties hm w hw).2.2.1
  simp only [Matrix.mul_apply, constProj, ← Finset.sum_mul] at h
  have hn : (2+m : ℝ) ≠ 0 := by positivity
  apply mul_right_cancel₀ (inv_ne_zero hn)
  simpa only [one_mul, Nat.cast_add, Nat.cast_ofNat] using h
private lemma totalRes_trace {m : ℕ} (hm : 0 < m) (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) : totalRes (K2m m) w = (2+m : ℕ) * ((shiftInv w).trace - 1) := by
  have h := totalRes_twice hm w hw
  have hsum : (∑ p, ∑ q, shiftInv w p q) = (2+m : ℕ) := by
    simp_rw [inverse_row_sum hm w hw]
    simp
  have hsum' : (∑ p, ∑ q, shiftInv w q p) = (2+m : ℕ) := by rw [Finset.sum_comm]; exact hsum
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_mul, ← Finset.mul_sum, hsum, hsum'] at h
  simp only [Matrix.trace, Matrix.diag_apply]
  nlinarith
private lemma projection_spectral {m : ℕ} (hm : 0 < m) (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) :
    let hL := lap_hermitian (K2m m) w
    Unitary.conjStarAlgAut ℝ _ (star hL.eigenvectorUnitary) (constProj (2+m)) =
      diagonal (fun i => if hL.eigenvalues i = 0 then 1 else 0) := by
  dsimp only
  let hL := lap_hermitian (K2m m) w
  let f := Unitary.conjStarAlgAut ℝ (Matrix (Fin (2+m)) (Fin (2+m)) ℝ)
    (star hL.eigenvectorUnitary)
  have hfL : f (wLap (K2m m) w) = diagonal hL.eigenvalues := by simpa [f] using hL.conjStarAlgAut_star_eigenvectorUnitary
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
lemma zero_eigenvalue_count {m : ℕ} (hm : 0 < m) (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) :
    (Finset.univ.filter (fun i => (lap_hermitian (K2m m) w).eigenvalues i = 0)).card = 1 := by
  let hL := lap_hermitian (K2m m) w
  let f := Unitary.conjStarAlgAut ℝ (Matrix (Fin (2+m)) (Fin (2+m)) ℝ)
    (star hL.eigenvectorUnitary)
  have htr : (f (constProj (2+m))).trace = (constProj (2+m)).trace := trace_map f _
  rw [projection_spectral hm w hw] at htr
  have hn : (2+m : ℝ) ≠ 0 := by positivity
  simp only [Matrix.trace_diagonal, Matrix.trace, Matrix.diag_apply, constProj, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_ofNat, mul_inv_cancel₀ hn] at htr
  simp only [Matrix.diagonal_apply_eq] at htr
  simp only [Finset.sum_boole] at htr
  exact_mod_cast htr
private lemma lap_psd {m : ℕ} (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) : (wLap (K2m m) w).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (lap_hermitian _ _)
  intro x
  simpa only [star_trivial] using energy_nonneg w hw x
private lemma centered_psd {m : ℕ} (hm : 0 < m) (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) (t : ℝ) (ht : ∀ i, (lap_hermitian (K2m m) w).eigenvalues i ≠ 0 →
      t ≤ (lap_hermitian (K2m m) w).eigenvalues i) : (wLap (K2m m) w - t • (1 - constProj (2+m))).PosSemidef := by
  let hL := lap_hermitian (K2m m) w
  let f := Unitary.conjStarAlgAut ℝ (Matrix (Fin (2+m)) (Fin (2+m)) ℝ)
    (star hL.eigenvectorUnitary)
  have hfL : f (wLap (K2m m) w) = diagonal hL.eigenvalues := by simpa [f] using hL.conjStarAlgAut_star_eigenvectorUnitary
  have hM : f (wLap (K2m m) w - t • (1 - constProj (2+m))) = diagonal (fun i => hL.eigenvalues i - t * (1 - if hL.eigenvalues i = 0 then 1 else 0)) := by
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
  simpa only [f, Unitary.conjStarAlgAut_apply, Unitary.isUnit_coe.posSemidef_star_right_conjugate_iff] using hpos
private lemma psd_rayleigh {m : ℕ} (w : Sym2 (Fin (2+m)) → ℝ) (t : ℝ) (hP : (wLap (K2m m) w - t • (1 - constProj (2+m))).PosSemidef) (x : Fin (2+m) → ℝ) (hx : ∑ i, x i = 0) :
    t * dotProduct x x ≤ dotProduct x (wLap (K2m m) w *ᵥ x) := by
  have hp : constProj (2+m) *ᵥ x = 0 := by ext i; simp [proj_mul,hx]
  have h := hP.dotProduct_mulVec_nonneg x
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hp, sub_zero, dotProduct_sub, dotProduct_smul, smul_eq_mul] at h
  linarith
lemma lambda2_spectral {m : ℕ} (hm : 0 < m) (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) : 0 < lambda2 (K2m m) w ∧
    (wLap (K2m m) w - lambda2 (K2m m) w • (1 - constProj (2+m))).PosSemidef ∧ (∀ i, (lap_hermitian (K2m m) w).eigenvalues i ≠ 0 → lambda2 (K2m m) w ≤ (lap_hermitian (K2m m) w).eigenvalues i) := by
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
lemma resistance_spectral {m : ℕ} (hm : 0 < m) (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) : totalRes (K2m m) w = (2+m : ℕ) *
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
  have hPtr : P.trace = 1 := by simp [P,Matrix.trace,constProj,Nat.cast_add,Nat.cast_ofNat,hn]
  rw [totalRes_trace hm w hw]
  congr 1
  rw [h]
  dsimp [T]
  rw [Matrix.trace_sub, hPtr]
def leafSum {m : ℕ} (w : Sym2 (Fin (2+m)) → ℝ) (i : Fin m) : ℝ :=
  w s(hub m 0,leaf m i) + w s(hub m 1,leaf m i)
private lemma delta_leaf_hub {m : ℕ} (i j : Fin m) (k : Fin 2) : delta (leaf m i) (leaf m j) (hub m k) = 0 := by
  have hi := (adj_hub_leaf m k i).ne
  have hj := (adj_hub_leaf m k j).ne
  simp [delta,hi,hj]
private lemma delta_leaf_leaf {m : ℕ} (i j k : Fin m) : delta (leaf m i) (leaf m j) (leaf m k) = (if k = i then 1 else 0) - (if k = j then 1 else 0) := by
  simp [delta,Pi.single_apply,leaf,Fin.ext_iff]
private lemma leaf_delta_norm {m : ℕ} {i j : Fin m} (hij : i ≠ j) : dotProduct (delta (leaf m i) (leaf m j)) (delta (leaf m i) (leaf m j)) = 2 := by
  rw [delta_dot]
  norm_num [delta_leaf_leaf,hij,Ne.symm hij]
private lemma leaf_delta_energy {m : ℕ} (w : Sym2 (Fin (2+m)) → ℝ) {i j : Fin m} (hij : i ≠ j) : dotProduct (delta (leaf m i) (leaf m j))
      (wLap (K2m m) w *ᵥ delta (leaf m i) (leaf m j)) = leafSum w i + leafSum w j := by
  rw [delta_dot,lap_mul_leaf,lap_mul_leaf]
  simp [delta_leaf_leaf,delta_leaf_hub,hij,Ne.symm hij,leafSum]
  <;> ring
private lemma leaf_pair_bound {m : ℕ} (w : Sym2 (Fin (2+m)) → ℝ) (t : ℝ) (hP : (wLap (K2m m) w - t • (1 - constProj (2+m))).PosSemidef)
    {i j : Fin m} (hij : i ≠ j) : 2*t ≤ leafSum w i + leafSum w j := by
  have h := psd_rayleigh w t hP (delta (leaf m i) (leaf m j)) (delta_sum _ _)
  rw [leaf_delta_norm hij,leaf_delta_energy w hij] at h
  linarith
lemma pair_gap_sum {m : ℕ} (s : Fin m → ℝ) (t : ℝ) : (∑ i, ∑ j, if i = j then 0 else s i + s j - 2*t) = 2 * (m-1 : ℝ) * ((∑ i, s i) - m*t) := by
  have he (i j : Fin m) : (if i = j then 0 else s i+s j-2*t) = (s i+s j-2*t) - if i = j then (2*s i-2*t) else 0 := by
    split_ifs with h
    · subst j; ring
    · ring
  simp_rw [he]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_ite_eq, Finset.mem_univ,ite_true,Finset.sum_const,Finset.card_univ,Fintype.card_fin, nsmul_eq_mul,← Finset.mul_sum,Finset.sum_mul]
  ring
private lemma leaf_trace_bound {m : ℕ} (hm : 1 < m) (w : Sym2 (Fin (2+m)) → ℝ) (t : ℝ) (hP : (wLap (K2m m) w - t • (1 - constProj (2+m))).PosSemidef) : m*t ≤ ∑ i, leafSum w i := by
  have hg : 0 ≤ ∑ i, ∑ j, if i = j then 0 else leafSum w i+leafSum w j-2*t := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    split_ifs with hij
    · rfl
    · linarith [leaf_pair_bound w t hP hij]
  rw [pair_gap_sum] at hg
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm
  have hm' : (0 : ℝ) < m-1 := by linarith
  nlinarith
lemma lap_trace {m : ℕ} (w : Sym2 (Fin (2+m)) → ℝ) : (wLap (K2m m) w).trace = 2 * ∑ i, leafSum w i := by
  have hd (k : Fin (2+m)) : wLap (K2m m) w k k = ∑ j with (K2m m).Adj k j, w s(k,j) := by simp [wLap]
  simp only [Matrix.trace,Matrix.diag_apply,sum_vertices,hd,Finset.sum_filter, sum_vertices,adj_hub_hub,adj_hub_leaf,(adj_hub_leaf m 0 _).symm,
    (adj_hub_leaf m 1 _).symm,adj_leaf_leaf,ite_true,ite_false,zero_add, add_zero,Finset.sum_const_zero]
  simp_rw [show ∀ i : Fin m, s(leaf m i,hub m 0) = s(hub m 0,leaf m i) from fun _ => Sym2.eq_swap, show ∀ i : Fin m, s(leaf m i,hub m 1) = s(hub m 1,leaf m i) from fun _ => Sym2.eq_swap]
  simp only [leafSum,Finset.sum_add_distrib]
  ring
private lemma reciprocal_bound {ι : Type*} [Fintype ι] (m : ℕ) (hm : 1 < m) (hcard : Fintype.card ι = m+1) (r : ι → ℝ) (t : ℝ) (ht : 0 < t) (hr : ∀ i, t ≤ r i) (htrace : 2*m*t ≤ ∑ i, r i) :
    t * (∑ i, (r i)⁻¹) ≤ m+1/m ∧ (t * (∑ i, (r i)⁻¹) = m+1/m → (∑ i, r i) = 2*m*t) := by
  let q := fun i => r i/t-1
  let Q := ∑ i, q i
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hrpos (i : ι) : 0 < r i := lt_of_lt_of_le ht (hr i)
  have hq (i : ι) : 0 ≤ q i := by
    dsimp [q]
    rw [sub_nonneg,le_div_iff₀ ht]
    simpa only [one_mul] using hr i
  have hQeq : Q = (∑ i, r i)/t - (m+1) := by simp [Q,q,Finset.sum_sub_distrib,← Finset.sum_div,hcard,Nat.cast_add,Nat.cast_ofNat]
  have hQ : m-1 ≤ Q := by
    have hh : 2*m ≤ (∑ i,r i)/t := (le_div_iff₀ ht).mpr (by nlinarith [htrace])
    linarith
  have hQ0 : 0 < Q := by linarith
  have hQp : 0 < 1+Q := by linarith
  have hqi (i : ι) : q i ≤ Q := Finset.single_le_sum (fun j _ => hq j) (Finset.mem_univ i)
  have hterm (i : ι) : q i/(1+Q) ≤ q i/(1+q i) := by exact div_le_div_of_nonneg_left (hq i) (by linarith [hq i]) (by linarith [hqi i])
  have hsum : Q/(1+Q) ≤ ∑ i, q i/(1+q i) := by
    rw [show Q/(1+Q) = ∑ i, q i/(1+Q) from (Finset.sum_div _ _ _)]
    exact Finset.sum_le_sum fun i _ => hterm i
  have hfrac : (m-1)/m ≤ Q/(1+Q) := by
    rw [div_le_div_iff₀ hm0 hQp]
    nlinarith
  have hid : t * (∑ i, (r i)⁻¹) = (m+1) - ∑ i, q i/(1+q i) := by
    have he (i : ι) : t * (r i)⁻¹ = 1 - q i/(1+q i) := by
      dsimp [q]
      field_simp [ht.ne', (hrpos i).ne']
      <;> ring
    rw [Finset.mul_sum]
    simp_rw [he]
    simp [Finset.sum_sub_distrib,hcard,Nat.cast_add,Nat.cast_ofNat]
  constructor
  · have hnum : (m+1 : ℝ) - (m-1)/m = m+1/m := by field_simp; ring
    linarith
  · intro heq
    have hnum : (m+1 : ℝ) - (m+1/m) = (m-1)/m := by field_simp; ring
    have hh : Q/(1+Q) ≤ (m-1)/m := by linarith
    rw [div_le_div_iff₀ hQp hm0] at hh
    have hQexact : Q = m-1 := by nlinarith
    rw [hQeq] at hQexact
    have hs : (∑ i,r i)/t = 2*m := by linarith
    exact (div_eq_iff ht.ne').mp hs
lemma product_bound_trace {m : ℕ} (hm : 3 ≤ m) (w : Sym2 (Fin (2+m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) : lambda2 (K2m m) w * totalRes (K2m m) w ≤ (m+2 : ℝ) * (m+1/m) ∧
    (lambda2 (K2m m) w * totalRes (K2m m) w = (m+2 : ℝ) * (m+1/m) → (∑ i, leafSum w i) = m * lambda2 (K2m m) w) := by
  let hL := lap_hermitian (K2m m) w
  let e := hL.eigenvalues
  let J := {i : Fin (2+m) // e i ≠ 0}
  let t := lambda2 (K2m m) w
  have hs := lambda2_spectral (by omega) w hw
  have hcard : Fintype.card J = m+1 := by
    rw [Fintype.card_subtype]
    have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => e i = 0)
    rw [zero_eigenvalue_count (by omega) w hw] at hc
    simp only [Finset.card_univ,Fintype.card_fin] at hc
    have hc' : 1 + (Finset.univ.filter (fun i => e i ≠ 0)).card = 2+m := by simpa only [ne_eq] using hc
    omega
  have hsum : (∑ i : J, e i) = (wLap (K2m m) w).trace := by
    rw [hL.trace_eq_sum_eigenvalues]
    change (∑ i : J, e i) = ∑ i, e i
    rw [← Finset.sum_subtype (Finset.univ.filter (fun i => e i ≠ 0)) (by simp) e]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases he : e i = 0 <;> simp [he]
  have hinv : (∑ i : J, (e i)⁻¹) = ∑ i, (e i)⁻¹ := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun i => e i ≠ 0)) (by simp) (fun i => (e i)⁻¹)]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases he : e i = 0 <;> simp [he]
  have htrace : 2*m*t ≤ ∑ i : J, e i := by
    rw [hsum,lap_trace]
    have h := leaf_trace_bound (by omega) w t hs.2.1
    nlinarith
  have hb := reciprocal_bound m (by omega) hcard (fun i : J => e i) t hs.1
    (fun i => hs.2.2 i i.2) htrace
  have hn : (0 : ℝ) < m+2 := by positivity
  have hR : totalRes (K2m m) w = (m+2 : ℝ) * ∑ i : J, (e i)⁻¹ := by
    rw [resistance_spectral (by omega) w hw, hinv]
    simp [e,hL,Nat.cast_add,Nat.cast_ofNat,add_comm]
  constructor
  · rw [hR]
    nlinarith [mul_le_mul_of_nonneg_left hb.1 hn.le]
  · intro heq
    have hh : t * (∑ i : J, (e i)⁻¹) = m+1/m := by
      rw [hR] at heq
      dsimp [t]
      nlinarith
    have htr := hb.2 hh
    rw [hsum,lap_trace] at htr
    linarith
private lemma leaf_eigen_of_trace {m : ℕ} (w : Sym2 (Fin (2+m)) → ℝ) (t : ℝ) (hP : (wLap (K2m m) w - t • (1 - constProj (2+m))).PosSemidef)
    (hsum : (∑ i, leafSum w i) = m*t) {i j : Fin m} (hij : i ≠ j) : wLap (K2m m) w *ᵥ delta (leaf m i) (leaf m j) = t • delta (leaf m i) (leaf m j) := by
  let g := fun i j : Fin m => if i = j then 0 else leafSum w i+leafSum w j-2*t
  have hg (i j : Fin m) : 0 ≤ g i j := by
    dsimp [g]
    split_ifs with h
    · rfl
    · linarith [leaf_pair_bound w t hP h]
  have htot : (∑ i, ∑ j, g i j) = 0 := by
    dsimp [g]
    rw [pair_gap_sum,hsum,sub_self,mul_zero]
  have hrow (i : Fin m) : (∑ j, g i j) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Finset.sum_nonneg (fun l _ => hg k l))).mp
      htot i (Finset.mem_univ _)
  have hgap := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hg i k)).mp
    (hrow i) j (Finset.mem_univ _)
  simp only [g,hij,ite_false] at hgap
  have he : dotProduct (delta (leaf m i) (leaf m j)) ((wLap (K2m m) w - t • (1 - constProj (2+m))) *ᵥ delta (leaf m i) (leaf m j)) = 0 := by
    rw [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec, proj_delta,sub_zero,dotProduct_sub,dotProduct_smul,smul_eq_mul, leaf_delta_norm hij,leaf_delta_energy w hij]
    linarith
  have hz : (wLap (K2m m) w - t • (1 - constProj (2+m))) *ᵥ delta (leaf m i) (leaf m j) = 0 :=
    hP.dotProduct_mulVec_zero_iff.mp (by simpa only [star_trivial] using he)
  rw [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec, proj_delta,sub_zero] at hz
  exact sub_eq_zero.mp hz
private lemma lap_delta_hub {m : ℕ} (w : Sym2 (Fin (2+m)) → ℝ) (i j : Fin m) (k : Fin 2) : (wLap (K2m m) w *ᵥ delta (leaf m i) (leaf m j)) (hub m k) =
      -w s(hub m k,leaf m i) + w s(hub m k,leaf m j) := by
  simp [delta,Matrix.mulVec_sub,Matrix.mulVec_single_one,Matrix.col_apply,wLap, (adj_hub_leaf m k i).ne,(adj_hub_leaf m k j).ne,adj_hub_leaf]
private lemma equality_leaf_uniform {m : ℕ} (hm : 3 ≤ m) (w : Sym2 (Fin (2+m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) (heq : lambda2 (K2m m) w * totalRes (K2m m) w = (m+2 : ℝ) * (m+1/m)) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a+b = lambda2 (K2m m) w ∧ ∀ i, w s(hub m 0,leaf m i) = a ∧ w s(hub m 1,leaf m i) = b := by
  let i0 : Fin m := ⟨0,by omega⟩
  let j0 : Fin m := ⟨1,by omega⟩
  have hi0j0 : i0 ≠ j0 := by
    intro h
    have := congrArg Fin.val h
    norm_num [i0,j0] at this
  have hs := (product_bound_trace hm w hw).2 heq
  have hP := (lambda2_spectral (by omega) w hw).2.1
  have hu (i j : Fin m) (hij : i ≠ j) (k : Fin 2) : w s(hub m k,leaf m i) = w s(hub m k,leaf m j) := by
    have h := congrFun (leaf_eigen_of_trace w _ hP hs hij) (hub m k)
    rw [lap_delta_hub] at h
    simp only [Pi.smul_apply,smul_eq_mul,delta_leaf_hub,mul_zero] at h
    linarith
  refine ⟨w s(hub m 0,leaf m i0),w s(hub m 1,leaf m i0),
    hw _ (by simpa using adj_hub_leaf m 0 i0),
    hw _ (by simpa using adj_hub_leaf m 1 i0), ?_, ?_⟩
  · have h := congrFun (leaf_eigen_of_trace w _ hP hs hi0j0) (leaf m i0)
    rw [lap_mul_leaf] at h
    norm_num only [delta_leaf_hub,delta_leaf_leaf,hi0j0,ite_false,ite_true, Pi.smul_apply,smul_eq_mul,sub_zero,zero_sub,mul_one] at h
    linarith
  · intro i
    by_cases hi : i = i0
    · subst i; exact ⟨rfl,rfl⟩
    · exact ⟨hu i i0 hi 0,hu i i0 hi 1⟩
private lemma resistance_of_current {m : ℕ} (hm : 0 < m) (w : Sym2 (Fin (2+m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) (p q : Fin (2+m)) (hpq : p ≠ q) (x : Fin (2+m) → ℝ)
    (hx : wLap (K2m m) w *ᵥ x = delta p q) : effRes (K2m m) w p q = x p-x q := by
  rw [(harmonic_resistance hm w hw p q hpq).2]
  let v := shiftInv w *ᵥ delta p q
  have hz : wLap (K2m m) w *ᵥ (v-x) = 0 := by rw [Matrix.mulVec_sub,inv_delta_equation hm w hw,hx,sub_self]
  have hE : dotProduct (v-x) (wLap (K2m m) w *ᵥ (v-x)) = 0 := by rw [hz,dotProduct_zero]
  obtain ⟨c,hc⟩ := (energy_zero_iff hm w hw (v-x)).mp hE
  have hp := congrFun hc p
  have hq := congrFun hc q
  change v p-x p = c at hp
  change v q-x q = c at hq
  change v p-v q = x p-x q
  linarith
private def vector {m : ℕ} (u v : ℝ) (z : Fin m → ℝ) : Fin (2+m) → ℝ :=
  Fin.addCases (fun j : Fin 2 => if j = 0 then u else v) z
private lemma vector_hub {m : ℕ} (u v : ℝ) (z : Fin m → ℝ) (j : Fin 2) : vector u v z (hub m j) = if j = 0 then u else v := by simp [vector,hub]
private lemma vector_leaf {m : ℕ} (u v : ℝ) (z : Fin m → ℝ) (i : Fin m) : vector u v z (leaf m i) = z i := by simp [vector,leaf]
private lemma uniform_lap_hub {m : ℕ} (w : Sym2 (Fin (2+m)) → ℝ) (a b : ℝ) (hu : ∀ i, w s(hub m 0,leaf m i) = a ∧ w s(hub m 1,leaf m i) = b) (u v : ℝ) (z : Fin m → ℝ) :
    (wLap (K2m m) w *ᵥ vector u v z) (hub m 0) = a*(m*u-∑ i,z i) ∧ (wLap (K2m m) w *ᵥ vector u v z) (hub m 1) = b*(m*v-∑ i,z i) := by
  constructor
  · rw [lap_mul_hub]
    simp_rw [(hu _).1,vector_hub,vector_leaf]
    simp [Finset.sum_sub_distrib,Finset.sum_const,← Finset.mul_sum,mul_sub,mul_comm,mul_left_comm]
    <;> ring
  · rw [lap_mul_hub]
    simp_rw [(hu _).2,vector_hub,vector_leaf]
    simp [Finset.sum_sub_distrib,Finset.sum_const,← Finset.mul_sum,mul_sub,mul_comm,mul_left_comm]
    <;> ring
private lemma uniform_lap_leaf {m : ℕ} (w : Sym2 (Fin (2+m)) → ℝ) (a b : ℝ) (hu : ∀ i, w s(hub m 0,leaf m i) = a ∧ w s(hub m 1,leaf m i) = b) (u v : ℝ) (z : Fin m → ℝ) (i : Fin m) :
    (wLap (K2m m) w *ᵥ vector u v z) (leaf m i) = (a+b)*z i-a*u-b*v := by
  rw [lap_mul_leaf,(hu i).1,(hu i).2,vector_leaf,vector_hub,vector_hub]
  norm_num
  <;> ring
private lemma uniform_hub_resistance {m : ℕ} (hm : 0 < m) (w : Sym2 (Fin (2+m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hu : ∀ i, w s(hub m 0,leaf m i) = a ∧ w s(hub m 1,leaf m i) = b) : effRes (K2m m) w (hub m 0) (hub m 1) = (a+b)/(m*a*b) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  let z : Fin m → ℝ := fun _ => 1/(m*b)
  let x := vector ((a+b)/(m*a*b)) 0 z
  have hpq : hub m 0 ≠ hub m 1 := by simp [hub,Fin.ext_iff]
  rw [resistance_of_current hm w hw _ _ hpq x ?_]
  · simp [x,vector_hub]
  · dsimp only [x]
    ext k
    refine Fin.addCases (fun j => ?_) (fun i => ?_) k
    · fin_cases j
      · change (wLap (K2m m) w *ᵥ vector ((a+b)/(m*a*b)) 0 z) (hub m 0) = _
        rw [(uniform_lap_hub (m := m) w a b hu _ _ _).1]
        simp [z,delta,Pi.single_apply,hub,Fin.ext_iff]
        <;> field_simp [hm0,ha.ne',hb.ne']
        <;> ring
      · change (wLap (K2m m) w *ᵥ vector ((a+b)/(m*a*b)) 0 z) (hub m 1) = _
        rw [(uniform_lap_hub (m := m) w a b hu _ _ _).2]
        simp [z,delta,Pi.single_apply,hub,Fin.ext_iff]
        <;> field_simp [hm0,ha.ne',hb.ne']
        <;> ring
    · change (wLap (K2m m) w *ᵥ vector ((a+b)/(m*a*b)) 0 z) (leaf m i) = _
      rw [uniform_lap_leaf (m := m) w a b hu]
      have h0 : Fin.natAdd 2 i ≠ hub m 0 := Ne.symm (adj_hub_leaf m 0 i).ne
      have h1 : Fin.natAdd 2 i ≠ hub m 1 := Ne.symm (adj_hub_leaf m 1 i).ne
      simp [z,delta,Pi.single_apply,h0,h1]
      <;> field_simp [hm0,ha.ne',hb.ne']
      <;> ring
private lemma vertex_ext {m : ℕ} {x y : Fin (2+m) → ℝ} (hh : ∀ j, x (hub m j) = y (hub m j)) (hl : ∀ i, x (leaf m i) = y (leaf m i)) : x = y := by
  funext k
  exact Fin.addCases hh hl k
private lemma effRes_comm {m : ℕ} (hm : 0 < m) (w : Sym2 (Fin (2+m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) (p q : Fin (2+m)) : effRes (K2m m) w p q = effRes (K2m m) w q p := by
  rw [effRes_inverse hm w hw,effRes_inverse hm w hw]
  ring
private lemma delta_hub_leaf_at_hub {m : ℕ} (i : Fin m) (j k : Fin 2) : delta (hub m j) (leaf m i) (hub m k) = if k = j then 1 else 0 := by
  have h := (adj_hub_leaf m k i).ne
  simp only [delta,Pi.sub_apply,Pi.single_apply,h,Ne.symm h,ite_false,sub_zero]
  simp [hub,Fin.ext_iff]
private lemma delta_hub_leaf_at_leaf {m : ℕ} (i k : Fin m) (j : Fin 2) : delta (hub m j) (leaf m i) (leaf m k) = -(if k = i then 1 else 0) := by
  have h := (adj_hub_leaf m j k).ne
  simp only [delta,Pi.sub_apply,Pi.single_apply,h,Ne.symm h,ite_false,zero_sub]
  simp [leaf,Fin.ext_iff]
private lemma uniform_hub_leaf_resistance {m : ℕ} (hm : 0 < m) (w : Sym2 (Fin (2+m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hu : ∀ i, w s(hub m 0,leaf m i) = a ∧ w s(hub m 1,leaf m i) = b) (i : Fin m) : effRes (K2m m) w (hub m 0) (leaf m i) = (m*a+b)/(m*a*(a+b)) ∧
    effRes (K2m m) w (hub m 1) (leaf m i) = (a+m*b)/(m*b*(a+b)) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hs0 : a+b ≠ 0 := by positivity
  let z : Fin m → ℝ := fun k => 1/(m*(a+b)) - if k = i then 1/(a+b) else 0
  have hzs : (∑ k,z k) = 0 := by
    simp [z,Finset.sum_sub_distrib]
    field_simp [hm0,hs0]
    <;> ring
  constructor
  · let x := vector (1/(m*a)) 0 z
    have hcur : wLap (K2m m) w *ᵥ x = delta (hub m 0) (leaf m i) := by
      dsimp only [x]
      apply vertex_ext
      · intro j; fin_cases j
        · change (wLap (K2m m) w *ᵥ vector (1/(m*a)) 0 z) (hub m 0) = _
          rw [(uniform_lap_hub (m := m) w a b hu _ _ _).1,hzs]
          simp [delta_hub_leaf_at_hub]
          field_simp [hm0,ha.ne']
        · change (wLap (K2m m) w *ᵥ vector (1/(m*a)) 0 z) (hub m 1) = _
          rw [(uniform_lap_hub (m := m) w a b hu _ _ _).2,hzs]
          simp [delta_hub_leaf_at_hub]
      · intro k
        rw [uniform_lap_leaf (m := m) w a b hu]
        simp only [delta_hub_leaf_at_leaf,z]
        split_ifs <;> field_simp [hm0,ha.ne',hs0] <;> ring
    rw [resistance_of_current hm w hw _ _ (adj_hub_leaf m 0 i).ne x hcur]
    simp [x,z,vector_hub,vector_leaf]
    field_simp
    <;> ring
  · let x := vector 0 (1/(m*b)) z
    have hcur : wLap (K2m m) w *ᵥ x = delta (hub m 1) (leaf m i) := by
      dsimp only [x]
      apply vertex_ext
      · intro j; fin_cases j
        · change (wLap (K2m m) w *ᵥ vector 0 (1/(m*b)) z) (hub m 0) = _
          rw [(uniform_lap_hub (m := m) w a b hu _ _ _).1,hzs]
          simp [delta_hub_leaf_at_hub]
        · change (wLap (K2m m) w *ᵥ vector 0 (1/(m*b)) z) (hub m 1) = _
          rw [(uniform_lap_hub (m := m) w a b hu _ _ _).2,hzs]
          simp [delta_hub_leaf_at_hub]
          field_simp [hm0,hb.ne']
      · intro k
        rw [uniform_lap_leaf (m := m) w a b hu]
        simp only [delta_hub_leaf_at_leaf,z]
        split_ifs <;> field_simp [hm0,hb.ne',hs0] <;> ring
    rw [resistance_of_current hm w hw _ _ (adj_hub_leaf m 1 i).ne x hcur]
    simp [x,z,vector_hub,vector_leaf]
    field_simp
    <;> ring
private lemma uniform_leaf_resistance {m : ℕ} (hm : 0 < m) (w : Sym2 (Fin (2+m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hu : ∀ i, w s(hub m 0,leaf m i) = a ∧ w s(hub m 1,leaf m i) = b) (i j : Fin m) : effRes (K2m m) w (leaf m i) (leaf m j) = if i = j then 0 else 2/(a+b) := by
  by_cases hij : i = j
  · subst j; simp [effRes]
  rw [if_neg hij]
  have hs0 : a+b ≠ 0 := by positivity
  let z : Fin m → ℝ := fun k => delta i j k/(a+b)
  let x := vector 0 0 z
  have hzs : (∑ k,z k) = 0 := by simp [z,← Finset.sum_div,delta_sum]
  have hpq : leaf m i ≠ leaf m j := by simpa [leaf,Fin.ext_iff] using hij
  have hcur : wLap (K2m m) w *ᵥ x = delta (leaf m i) (leaf m j) := by
    dsimp only [x]
    apply vertex_ext
    · intro k; fin_cases k
      · change (wLap (K2m m) w *ᵥ vector 0 0 z) (hub m 0) = _
        rw [(uniform_lap_hub (m := m) w a b hu _ _ _).1,hzs,delta_leaf_hub]; simp
      · change (wLap (K2m m) w *ᵥ vector 0 0 z) (hub m 1) = _
        rw [(uniform_lap_hub (m := m) w a b hu _ _ _).2,hzs,delta_leaf_hub]; simp
    · intro k
      rw [uniform_lap_leaf (m := m) w a b hu,delta_leaf_leaf]
      simp [z,delta,Pi.single_apply]
      field_simp [hs0]
  rw [resistance_of_current hm w hw _ _ hpq x hcur]
  simp [x,z,vector_leaf,delta,Pi.single_apply,hij,Ne.symm hij]
  <;> ring
private lemma uniform_totalRes {m : ℕ} (hm : 0 < m) (w : Sym2 (Fin (2+m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hu : ∀ i, w s(hub m 0,leaf m i) = a ∧ w s(hub m 1,leaf m i) = b) : totalRes (K2m m) w = (m+1 : ℝ)/m * (a+b)/(a*b) + (m*m+m-2 : ℝ)/(a+b) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hs0 : a+b ≠ 0 := by positivity
  have hdiag (p : Fin (2+m)) : effRes (K2m m) w p p = 0 := by simp [effRes]
  have h01 := uniform_hub_resistance hm w hw a b ha hb hu
  have h10 := (effRes_comm hm w hw (hub m 1) (hub m 0)).trans h01
  have h0 (i : Fin m) := (uniform_hub_leaf_resistance hm w hw a b ha hb hu i).1
  have h1 (i : Fin m) := (uniform_hub_leaf_resistance hm w hw a b ha hb hu i).2
  have h0' (i : Fin m) := (effRes_comm hm w hw (leaf m i) (hub m 0)).trans (h0 i)
  have h1' (i : Fin m) := (effRes_comm hm w hw (leaf m i) (hub m 1)).trans (h1 i)
  have hll (i : Fin m) : (∑ j, effRes (K2m m) w (leaf m i) (leaf m j)) = m*(2/(a+b)) - 2/(a+b) := by
    simp_rw [uniform_leaf_resistance hm w hw a b ha hb hu]
    have he (j : Fin m) : (if i=j then (0 : ℝ) else 2/(a+b)) = 2/(a+b) - if i=j then 2/(a+b) else 0 := by split_ifs <;> ring
    simp_rw [he]
    simp [Finset.sum_sub_distrib]
  have hh : 2 * totalRes (K2m m) w = ∑ p, ∑ q, effRes (K2m m) w p q := by simpa only [effRes_inverse hm w hw] using totalRes_twice hm w hw
  simp only [sum_vertices,hdiag,h01,h10,h0,h1,h0',h1',hll,Finset.sum_add_distrib, Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  apply mul_left_cancel₀ (show (2 : ℝ) ≠ 0 by norm_num)
  rw [hh]
  field_simp [hm0,ha.ne',hb.ne',hs0]
  <;> ring
private lemma uniform_energy_difference {m : ℕ} (w : Sym2 (Fin (2+m)) → ℝ) (a b t : ℝ) (hs : a+b=t) (hu : ∀ i, w s(hub m 0,leaf m i) = a ∧ w s(hub m 1,leaf m i) = b)
    (x : Fin (2+m) → ℝ) (hx : ∑ k,x k = 0) : dotProduct x (wLap (K2m m) w *ᵥ x) - t*dotProduct x x = ((m+2)*a-t)*(x (hub m 0))^2 + ((m+2)*b-t)*(x (hub m 1))^2 + 2*t*x (hub m 0)*x (hub m 1) := by
  subst t
  have hz : (∑ i,x (leaf m i)) = -x (hub m 0)-x (hub m 1) := by
    rw [sum_vertices] at hx
    linarith
  have hn : dotProduct x x = (x (hub m 0))^2+(x (hub m 1))^2+∑ i,(x (leaf m i))^2 := by simp only [dotProduct,sum_vertices,pow_two]
  have he (i : Fin m) : a*(x (hub m 0)-x (leaf m i))^2 + b*(x (hub m 1)-x (leaf m i))^2 = (a*(x (hub m 0))^2+b*(x (hub m 1))^2) -
        2*(a*x (hub m 0)+b*x (hub m 1))*x (leaf m i) + (a+b)*(x (leaf m i))^2 := by ring
  rw [energy,hn]
  simp_rw [(hu _).1,(hu _).2,he]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const, Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,← Finset.mul_sum,hz]
  ring
private lemma uniform_lambda2 {m : ℕ} (hm : 3 ≤ m) (w : Sym2 (Fin (2+m)) → ℝ) (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) (hs : a+b=t) (hab : (m+2)*a*b=t^2)
    (hu : ∀ i, w s(hub m 0,leaf m i) = a ∧ w s(hub m 1,leaf m i) = b) : lambda2 (K2m m) w = t := by
  let α := (m+2 : ℝ)*a-t
  let β := (m+2 : ℝ)*b-t
  have hα : 0 < α := by
    have hprod : α*b = t*a := by dsimp [α]; nlinarith [hab]
    by_contra! h
    have hh := mul_nonpos_of_nonpos_of_nonneg h hb.le
    nlinarith [mul_pos ht ha]
  have hαβ : α*β=t^2 := by
    calc
      _ = t^2+(m+2)*((m+2)*a*b-t*(a+b)) := by dsimp [α,β]; ring
      _ = _ := by rw [hab,hs]; ring
  have hlower (x : Fin (2+m) → ℝ) (hx : ∑ k,x k = 0) : t*dotProduct x x ≤ dotProduct x (wLap (K2m m) w *ᵥ x) := by
    have he := uniform_energy_difference w a b t hs hu x hx
    have hid : α*(dotProduct x (wLap (K2m m) w *ᵥ x)-t*dotProduct x x) = (α*x (hub m 0)+t*x (hub m 1))^2 := by
      rw [he]
      change α*(α*(x (hub m 0))^2+β*(x (hub m 1))^2+2*t*x (hub m 0)*x (hub m 1)) = _
      calc
        _ = (α*x (hub m 0)+t*x (hub m 1))^2 + (α*β-t^2)*(x (hub m 1))^2 := by ring
        _ = _ := by rw [hαβ]; ring
    have hnonneg : 0 ≤ α*(dotProduct x (wLap (K2m m) w *ᵥ x)-t*dotProduct x x) := by rw [hid]; exact sq_nonneg _
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hα).mp hnonneg)
  let i0 : Fin m := ⟨0,by omega⟩
  let j0 : Fin m := ⟨1,by omega⟩
  have hij : i0 ≠ j0 := by intro h; have := congrArg Fin.val h; norm_num [i0,j0] at this
  have hpq : leaf m i0 ≠ leaf m j0 := by simpa [leaf,Fin.ext_iff] using hij
  have heigen : wLap (K2m m) w *ᵥ delta (leaf m i0) (leaf m j0) = t • delta (leaf m i0) (leaf m j0) := by
    apply vertex_ext
    · intro k
      rw [lap_delta_hub]
      simp only [Pi.smul_apply,smul_eq_mul,delta_leaf_hub,mul_zero]
      fin_cases k <;> simp [(hu i0).1,(hu i0).2,(hu j0).1,(hu j0).2]
    · intro k
      rw [lap_mul_leaf,(hu k).1,(hu k).2]
      simp only [delta_leaf_hub,sub_zero,Pi.smul_apply,smul_eq_mul]
      rw [← add_mul,hs]
  exact lambda2_eq_of_rayleigh _ _ t hlower _ (delta_ne hpq) (delta_sum _ _) heigen
lemma equality_parameters {m : ℕ} (hm : 3 ≤ m) (w : Sym2 (Fin (2+m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) (heq : lambda2 (K2m m) w * totalRes (K2m m) w = (m+2 : ℝ) * (m+1/m)) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a+b = lambda2 (K2m m) w ∧ (m+2)*a*b = (lambda2 (K2m m) w)^2 ∧ ∀ i, w s(hub m 0,leaf m i) = a ∧ w s(hub m 1,leaf m i) = b := by
  obtain ⟨a,b,ha,hb,hs,hu⟩ := equality_leaf_uniform hm w hw heq
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hs0 : a+b ≠ 0 := by positivity
  rw [uniform_totalRes (by omega) w hw a b ha hb hu,← hs] at heq
  have hid : (a+b)*((m+1 : ℝ)/m*(a+b)/(a*b)+(m*m+m-2 : ℝ)/(a+b)) - (m+2 : ℝ)*(m+1/m) = (m+1)/(m*a*b)*((a+b)^2-(m+2)*a*b) := by
    field_simp [hm0,ha.ne',hb.ne',hs0]
    <;> ring
  have hz : (m+1 : ℝ)/(m*a*b)*((a+b)^2-(m+2)*a*b) = 0 := by rw [← hid,heq]; ring
  have hc : (m+1 : ℝ)/(m*a*b) ≠ 0 := by positivity
  have hab := (mul_eq_zero.mp hz).resolve_left hc
  refine ⟨a,b,ha,hb,hs,?_,hu⟩
  rw [← hs]
  linarith
def sharpConstant (m : ℕ) : ℝ := (m+2 : ℝ)*(m+1/m)
def splitRatio (m : ℕ) : ℝ := Real.sqrt ((m-2 : ℝ)/(m+2))
def maxValue (m : ℕ) (R0 : ℝ) : ℝ := sharpConstant m/R0
def plusConductance (m : ℕ) (R0 : ℝ) : ℝ := maxValue m R0/2*(1+splitRatio m)
def minusConductance (m : ℕ) (R0 : ℝ) : ℝ := maxValue m R0/2*(1-splitRatio m)
def EdgeRestriction (m : ℕ) (a b : ℝ) (w : Sym2 (Fin (2+m)) → ℝ) : Prop :=
  ∀ i, w s(hub m 0,leaf m i) = a ∧ w s(hub m 1,leaf m i) = b
def uniformWeights (m : ℕ) (a b : ℝ) : Sym2 (Fin (2+m)) → ℝ :=
  Sym2.lift ⟨fun p q => if p = hub m 0 ∨ q = hub m 0 then a else b,
    by intro p q; simp only [or_comm]⟩
lemma uniformWeights_edges (m : ℕ) (a b : ℝ) : EdgeRestriction m a b (uniformWeights m a b) := by
  intro i
  have hh : hub m 1 ≠ hub m 0 := by simp [hub,Fin.ext_iff]
  have hl := Ne.symm (adj_hub_leaf m 0 i).ne
  simp [uniformWeights,hh,hl]
private lemma uniformWeights_positive (m : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : ∀ e ∈ (K2m m).edgeSet, 0 < uniformWeights m a b e := by
  intro e he
  induction e using Sym2.ind with
  | _ p q =>
    simp only [uniformWeights,Sym2.lift_mk]
    split_ifs <;> assumption
lemma splitRatio_facts {m : ℕ} (hm : 3 ≤ m) : 0 < splitRatio m ∧ splitRatio m < 1 ∧ (splitRatio m)^2=(m-2 : ℝ)/(m+2) := by
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : (0 : ℝ) < (m-2 : ℝ)/(m+2) := div_pos (by linarith) (by positivity)
  have hlt : (m-2 : ℝ)/(m+2) < 1 := by rw [div_lt_one (by positivity)]; linarith
  refine ⟨Real.sqrt_pos.mpr hpos, ?_, Real.sq_sqrt hpos.le⟩
  change Real.sqrt ((m-2 : ℝ)/(m+2)) < 1
  exact (Real.sqrt_lt' (by norm_num)).mpr (by simpa using hlt)
private lemma conductance_parameters {m : ℕ} (hm : 3 ≤ m) (R0 : ℝ) (hR0 : 0 < R0) : 0 < maxValue m R0 ∧ 0 < plusConductance m R0 ∧ 0 < minusConductance m R0 ∧
    plusConductance m R0 + minusConductance m R0 = maxValue m R0 ∧ (m+2 : ℝ)*plusConductance m R0*minusConductance m R0 = (maxValue m R0)^2 ∧ plusConductance m R0 ≠ minusConductance m R0 := by
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have ht : 0 < maxValue m R0 := by unfold maxValue sharpConstant; positivity
  obtain ⟨hρ,hρ1,hρsq⟩ := splitRatio_facts hm
  have hp : 0 < plusConductance m R0 := by unfold plusConductance; positivity
  have hn : 0 < minusConductance m R0 := by unfold minusConductance; positivity
  have hs : plusConductance m R0 + minusConductance m R0 = maxValue m R0 := by unfold plusConductance minusConductance; ring
  have hab : (m+2 : ℝ)*plusConductance m R0*minusConductance m R0 = (maxValue m R0)^2 := by
    have hr : (m+2 : ℝ)*(splitRatio m)^2=m-2 := by
      have hh := (eq_div_iff (show (m+2 : ℝ) ≠ 0 by positivity)).mp hρsq
      simpa only [mul_comm] using hh
    have hid : (m+2 : ℝ)*plusConductance m R0*minusConductance m R0 = (maxValue m R0)^2/4*((m+2)-(m+2)*(splitRatio m)^2) := by
      unfold plusConductance minusConductance; ring
    rw [hid,hr]; ring
  have hne : plusConductance m R0 ≠ minusConductance m R0 := by
    intro h
    have hd : plusConductance m R0-minusConductance m R0 = maxValue m R0*splitRatio m := by unfold plusConductance minusConductance; ring
    rw [h,sub_self] at hd
    exact (mul_pos ht hρ).ne' hd.symm
  exact ⟨ht,hp,hn,hs,hab,hne⟩
lemma parameter_roots {m : ℕ} (hm : 3 ≤ m) (a b t : ℝ) (hs : a+b=t) (hab : (m+2 : ℝ)*a*b=t^2) : (a=t/2*(1+splitRatio m) ∧ b=t/2*(1-splitRatio m)) ∨
    (a=t/2*(1-splitRatio m) ∧ b=t/2*(1+splitRatio m)) := by
  have hm0 : (m+2 : ℝ) ≠ 0 := by positivity
  have hab' : a*b=t^2/(m+2 : ℝ) := (eq_div_iff hm0).mpr (by nlinarith [hab])
  have hρsq := (splitRatio_facts hm).2.2
  have he : (2*a-t)^2=(t*splitRatio m)^2 := by
    calc
      _ = t^2-4*a*b := by rw [← hs]; ring
      _ = t^2*((m-2 : ℝ)/(m+2)) := by rw [show 4*a*b = 4*(a*b) by ring,hab']; field_simp; ring
      _ = _ := by rw [← hρsq]; ring
  have hz : (2*a-t-t*splitRatio m)*(2*a-t+t*splitRatio m)=0 := by nlinarith [he]
  rcases mul_eq_zero.mp hz with h | h
  · left; constructor <;> linarith
  · right; constructor <;> linarith
lemma uniform_extremal {m : ℕ} (hm : 3 ≤ m) (w : Sym2 (Fin (2+m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 < t)
    (hs : a+b=t) (hab : (m+2 : ℝ)*a*b=t^2) (hu : EdgeRestriction m a b w) : lambda2 (K2m m) w = t ∧ totalRes (K2m m) w = sharpConstant m/t := by
  refine ⟨uniform_lambda2 hm w a b t ha hb ht hs hab hu, ?_⟩
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hm2 : (m+2 : ℝ) ≠ 0 := by positivity
  have hab' : a*b=t^2/(m+2 : ℝ) := (eq_div_iff hm2).mpr (by nlinarith [hab])
  rw [uniform_totalRes (by omega) w hw a b ha hb hu,hs,hab']
  unfold sharpConstant
  field_simp [hm0,hm2,ht.ne']
  <;> ring
def exchangeWeights (m : ℕ) (w : Sym2 (Fin (2+m)) → ℝ) : Sym2 (Fin (2+m)) → ℝ :=
  fun e => w (e.map (Equiv.swap (hub m 0) (hub m 1)))
lemma exchange_edges {m : ℕ} (a b : ℝ) (w : Sym2 (Fin (2+m)) → ℝ) (hu : EdgeRestriction m a b w) : EdgeRestriction m b a (exchangeWeights m w) := by
  intro i
  have hleaf : Equiv.swap (hub m 0) (hub m 1) (leaf m i) = leaf m i :=
    Equiv.swap_apply_of_ne_of_ne (Ne.symm (adj_hub_leaf m 0 i).ne) (Ne.symm (adj_hub_leaf m 1 i).ne)
  simpa only [exchangeWeights,Sym2.map_mk,Equiv.swap_apply_left,Equiv.swap_apply_right,hleaf] using
    And.intro (hu i).2 (hu i).1
private lemma fixed_extremal {m : ℕ} (hm : 3 ≤ m) (R0 : ℝ) (hR0 : 0 < R0) (w : Sym2 (Fin (2+m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hs : a+b=maxValue m R0) (hab : (m+2 : ℝ)*a*b=(maxValue m R0)^2) (hu : EdgeRestriction m a b w) : totalRes (K2m m) w = R0 ∧ lambda2 (K2m m) w = maxValue m R0 := by
  have ht := (conductance_parameters hm R0 hR0).1
  have hC : sharpConstant m ≠ 0 := by unfold sharpConstant; positivity
  have hh := uniform_extremal hm w hw a b _ ha hb ht hs hab hu
  refine ⟨?_,hh.1⟩
  rw [hh.2]
  unfold maxValue
  field_simp [hC,hR0.ne']
def OptimizerClaim (m : ℕ) (R0 : ℝ) : Prop :=
  let t := maxValue m R0
  let a := plusConductance m R0
  let b := minusConductance m R0
  let p := uniformWeights m a b
  let q := uniformWeights m b a
  (∀ w : Sym2 (Fin (2+m)) → ℝ, (∀ e ∈ (K2m m).edgeSet, 0 < w e) → totalRes (K2m m) w = R0 → lambda2 (K2m m) w ≤ t) ∧
  ((∀ e ∈ (K2m m).edgeSet, 0 < p e) ∧ totalRes (K2m m) p = R0 ∧ lambda2 (K2m m) p = t ∧ EdgeRestriction m a b p) ∧
  ((∀ e ∈ (K2m m).edgeSet, 0 < q e) ∧ totalRes (K2m m) q = R0 ∧ lambda2 (K2m m) q = t ∧ EdgeRestriction m b a q) ∧
  (∀ w : Sym2 (Fin (2+m)) → ℝ, (∀ e ∈ (K2m m).edgeSet, 0 < w e) → totalRes (K2m m) w = R0 → (lambda2 (K2m m) w = t ↔ EdgeRestriction m a b w ∨ EdgeRestriction m b a w)) ∧
  (¬ ∃ w, EdgeRestriction m a b w ∧ EdgeRestriction m b a w) ∧
  (∀ w, EdgeRestriction m a b w → EdgeRestriction m b a (exchangeWeights m w)) ∧
  (∀ w, EdgeRestriction m b a w → EdgeRestriction m a b (exchangeWeights m w)) ∧
  (∀ w w', (∀ e ∈ (K2m m).edgeSet, w e = w' e) → lambda2 (K2m m) w = lambda2 (K2m m) w' ∧ totalRes (K2m m) w = totalRes (K2m m) w')
theorem result (m : ℕ) (hm : 3 ≤ m) (R0 : ℝ) (hR0 : 0 < R0) : OptimizerClaim m R0 := by
  obtain ⟨ht,ha,hb,hs,hab,hne⟩ := conductance_parameters hm R0 hR0
  let a := plusConductance m R0
  let b := minusConductance m R0
  have hs' : b+a=maxValue m R0 := by dsimp [a,b]; linarith
  have hab' : (m+2 : ℝ)*b*a=(maxValue m R0)^2 := by
    dsimp [a,b]
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hab
  have hp := uniformWeights_positive m a b ha hb
  have hq := uniformWeights_positive m b a hb ha
  have hpE := uniformWeights_edges m a b
  have hqE := uniformWeights_edges m b a
  have hpV := fixed_extremal hm R0 hR0 _ hp a b ha hb hs hab hpE
  have hqV := fixed_extremal hm R0 hR0 _ hq b a hb ha hs' hab' hqE
  refine ⟨?_,⟨hp,hpV.1,hpV.2,hpE⟩,⟨hq,hqV.1,hqV.2,hqE⟩,?_,?_,?_,?_,?_⟩
  · intro w hw hR
    have h := (product_bound_trace hm w hw).1
    rw [hR] at h
    exact (le_div_iff₀ hR0).mpr h
  · intro w hw hR
    constructor
    · intro heq
      have hprod : lambda2 (K2m m) w * totalRes (K2m m) w = sharpConstant m := by
        rw [hR,heq]
        exact div_mul_cancel₀ _ hR0.ne'
      obtain ⟨c,d,hc,hd,hcd,hcdp,hE⟩ := equality_parameters hm w hw hprod
      rw [heq] at hcd hcdp
      rcases parameter_roots hm c d _ hcd hcdp with h | h
      · left
        simpa only [EdgeRestriction,a,b,plusConductance,minusConductance,h.1,h.2] using hE
      · right
        simpa only [EdgeRestriction,a,b,plusConductance,minusConductance,h.1,h.2] using hE
    · rintro (hE | hE)
      · exact (fixed_extremal hm R0 hR0 w hw a b ha hb hs hab hE).2
      · exact (fixed_extremal hm R0 hR0 w hw b a hb ha hs' hab' hE).2
  · rintro ⟨w,hpE,hqE⟩
    let i : Fin m := ⟨0,by omega⟩
    exact hne ((hpE i).1.symm.trans (hqE i).1)
  · intro w hE; exact exchange_edges a b w hE
  · intro w hE; exact exchange_edges b a w hE
  · intro w w' hE; exact invariants_congr _ w w' hE
end D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer
