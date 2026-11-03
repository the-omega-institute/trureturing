/- GID: D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceTripartiteOptimizer
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/FiedlerResistanceTripartiteOptimizer
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Original labelled tripartite Laplacians and their harmonic resistance ceiling. -/
import D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceTripartiteOptimizer
open FiedlerResistanceInvariantWeightsRefutation FiedlerResistanceK2mOptimizer

private lemma energy_double {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (x : Fin n → ℝ) :
    2 * dotProduct x (wLap G w *ᵥ x) =
      ∑ i, ∑ j with G.Adj i j, w s(i,j) * (x i - x j)^2 := by
  have hs : (∑ i, ∑ j with G.Adj i j, x j * (w s(i,j) * (x j-x i))) =
      ∑ i, ∑ j with G.Adj i j, x i * (w s(i,j) * (x i-x j)) := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [G.adj_comm j i, Sym2.eq_swap]
  simp only [dotProduct, lap_mul, Finset.mul_sum]
  rw [show (2:ℝ) * (∑ i, ∑ j with G.Adj i j, x i * (w s(i,j)*(x i-x j))) =
    (∑ i, ∑ j with G.Adj i j, x i * (w s(i,j)*(x i-x j))) +
    (∑ i, ∑ j with G.Adj i j, x j * (w s(i,j)*(x j-x i))) by rw [hs]; ring]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private lemma lap_psd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (hw : ∀ i j, G.Adj i j → 0 ≤ w s(i,j)) :
    (wLap G w).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (lap_hermitian G w)
  intro x
  have h : 0 ≤ ∑ i, ∑ j with G.Adj i j, w s(i,j)*(x i-x j)^2 := by
    apply Finset.sum_nonneg
    intro i hi
    exact Finset.sum_nonneg fun j hj => mul_nonneg (hw i j (Finset.mem_filter.mp hj).2) (sq_nonneg _)
  rw [← energy_double] at h
  simp only [star_trivial]
  linarith

private lemma rayleigh_lower {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (hw : (wLap G w).PosSemidef)
    (x : Fin n → ℝ) (hx : ∑ i, x i = 0) :
    lambda2 G w * dotProduct x x ≤ dotProduct x (wLap G w *ᵥ x) := by
  by_cases hz : x = 0
  · subst x; simp
  have hn : 0 < dotProduct x x := by
    exact dotProduct_self_pos_iff.mpr hz
  have hB : BddBelow {r : ℝ | ∃ y : Fin n → ℝ, y ≠ 0 ∧ ∑ i, y i=0 ∧
      r=dotProduct y (wLap G w *ᵥ y)/dotProduct y y} := by
    refine ⟨0, ?_⟩
    rintro r ⟨y,hy,hs,rfl⟩
    exact div_nonneg (by simpa only [star_trivial] using hw.dotProduct_mulVec_nonneg y)
      (dotProduct_self_nonneg y)
  exact (le_div_iff₀ hn).mp (csInf_le hB ⟨x,hz,hx,rfl⟩)

private lemma centered_psd {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℝ)
    (hR : ∀ x : Fin n → ℝ, ∑ i, x i=0 →
      dotProduct x x ≤ dotProduct x (wLap G w *ᵥ x)) :
    (wLap G w - (1-constProj n)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((lap_hermitian G w).sub ((Matrix.isHermitian_one).sub (proj_hermitian n)))
  intro x
  let c : ℝ := (∑ i, x i)/n
  let y : Fin n → ℝ := x-c • (1 : Fin n → ℝ)
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  have hy : ∑ i, y i=0 := by
    simp [y,c,Finset.sum_sub_distrib,hn0]
  have hLy : wLap G w *ᵥ y = wLap G w *ᵥ x := by
    simp [y,Matrix.mulVec_sub,Matrix.mulVec_smul,lap_one]
  have hE : dotProduct y (wLap G w *ᵥ y) = dotProduct x (wLap G w *ᵥ x) := by
    rw [hLy]
    simp [y,sub_dotProduct,smul_dotProduct,dotProduct,← Finset.mul_sum,lap_sum]
  have hN : dotProduct y y = dotProduct x x - (∑ i,x i)^2/n := by
    simp only [y,dotProduct,Pi.sub_apply,Pi.smul_apply,Pi.one_apply,smul_eq_mul,mul_one]
    simp_rw [show ∀ i, (x i-c)*(x i-c)=x i*x i-2*c*x i+c*c from fun i => by ring]
    simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    dsimp [c]
    field_simp
    <;> ring
  have h := hR y hy
  rw [hE,hN] at h
  simp only [star_trivial,Matrix.sub_mulVec,Matrix.one_mulVec,dotProduct_sub]
  rw [proj_energy]
  linarith

end D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceTripartiteOptimizer
