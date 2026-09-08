/- GID: D5/S3/Arith/GoldenResource/WeightedDiscreteLogNoGo
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource/WeightedDiscreteLogNoGo
   mirror-E: none(waiver:exact-real-inequalities)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/GoldenResource/WeightedDiscreteLogNoGo.uniformSelection
   digest: Unequal coordinate prices uniquely select the nonscalar integral matrix diag(2,3). -/

import D5.S3.Arith.GoldenResource.DiscreteLogSelector
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

namespace D5.S3.Arith.GoldenResource.WeightedDiscreteLogNoGo

noncomputable section

/-- The real matrix associated to an integral two by two matrix. -/
def realMatrix (T : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  T.map (Int.castRingHom ℝ)

/-- The open window for the two effective prices. -/
def priceWindow (p : ℝ) : Prop :=
  (Real.log (3 / 2 : ℝ) < 3 * p ∧ 3 * p < Real.log 2) ∧
  (Real.log (4 / 3 : ℝ) < 2 * p ∧ 2 * p < Real.log (3 / 2 : ℝ))

/-- The weighted logarithmic objective on integral matrices. -/
def objective (p : ℝ) (T : Matrix (Fin 2) (Fin 2) ℤ) : ℝ :=
  Real.log (realMatrix T).det - p * (3 * (T 0 0 : ℝ) + 2 * (T 1 1 : ℝ))

/-- The selected matrix has distinct diagonal entries. -/
def selectedMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![2, 0; 0, 3]

/-- The assertion that uniqueness throughout such a price window forces equal diagonals. -/
def uniformSelection : Prop :=
  ∀ p : ℝ, priceWindow p → ∀ T : Matrix (Fin 2) (Fin 2) ℤ,
    (realMatrix T).PosDef →
    (∀ U : Matrix (Fin 2) (Fin 2) ℤ, (realMatrix U).PosDef →
      U ≠ T → objective p U < objective p T) → T 0 0 = T 1 1

/-- All four strict inequalities hold at the rational price one sixth. -/
theorem one_sixth_mem_priceWindow : priceWindow (1 / 6) := by
  have h32 := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
    (by norm_num : (3 / 2 : ℝ) ≠ 1)
  have h43 := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
    (by norm_num : (4 / 3 : ℝ) ≠ 1)
  have h12 := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)
    (by norm_num : (2⁻¹ : ℝ) ≠ 1)
  have h23 := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < (3 / 2)⁻¹)
    (by norm_num : ((3 / 2)⁻¹ : ℝ) ≠ 1)
  rw [Real.log_inv] at h12 h23
  norm_num at h32 h43 h12 h23
  unfold priceWindow
  constructor <;> constructor <;> norm_num <;> linarith

/-- The specified price window is nonempty. -/
theorem priceWindow_nonempty : ∃ p : ℝ, priceWindow p :=
  ⟨1 / 6, one_sixth_mem_priceWindow⟩

/-- The proposed optimizer is positive definite over the reals. -/
theorem selectedMatrix_posDef : (realMatrix selectedMatrix).PosDef := by
  have heq : realMatrix selectedMatrix = Matrix.diagonal ![2, 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [realMatrix, selectedMatrix, Matrix.diagonal]
  rw [heq]
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i <;> norm_num

private theorem symmetric_entries {T : Matrix (Fin 2) (Fin 2) ℤ}
    (hT : (realMatrix T).PosDef) : T 1 0 = T 0 1 := by
  have h := hT.isHermitian.apply 0 1
  simpa [realMatrix] using h

/-- A nonzero integral off-diagonal entry costs at least one unit of determinant. -/
theorem off_diagonal_det_loss {T : Matrix (Fin 2) (Fin 2) ℤ}
    (hT : (realMatrix T).PosDef) (h01 : T 0 1 ≠ 0) :
    (realMatrix T).det ≤ (T 0 0 : ℝ) * (T 1 1 : ℝ) - 1 := by
  have hs : (1 : ℤ) ≤ T 0 1 * T 0 1 := by
    have := sq_pos_of_ne_zero h01
    nlinarith
  have hs' : (1 : ℝ) ≤ (T 0 1 : ℝ) * (T 0 1 : ℝ) := by exact_mod_cast hs
  simp only [Matrix.det_fin_two, realMatrix, Matrix.map_apply, Int.coe_castRingHom]
  rw [symmetric_entries hT]
  linarith

private theorem integer_log_bound {k : ℕ} (hk : 2 ≤ k) {q : ℝ}
    (hlo : Real.log (((k + 1 : ℕ) : ℝ) / k) < q)
    (hhi : q < Real.log ((k : ℝ) / (k - 1 : ℕ))) {z : ℤ} (hz : 0 < z) :
    Real.log (z : ℝ) - q * z ≤ Real.log (k : ℝ) - q * k ∧
    (z ≠ k → Real.log (z : ℝ) - q * z < Real.log (k : ℝ) - q * k) := by
  have h := DiscreteLogSelector.discrete_log_unique_maximum hk hlo hhi z.toNat
    (by omega)
  change Real.log (z.toNat : ℝ) - q * z.toNat ≤ Real.log (k : ℝ) - q * k ∧
    (z.toNat ≠ k → min (Real.log ((k : ℝ) / (k - 1 : ℕ)) - q)
      (q - Real.log (((k + 1 : ℕ) : ℝ) / k)) ≤
        (Real.log (k : ℝ) - q * k) - (Real.log (z.toNat : ℝ) - q * z.toNat)) at h
  have hcast : (z.toNat : ℝ) = z := by
    exact_mod_cast Int.toNat_of_nonneg hz.le
  rw [hcast] at h
  refine ⟨h.1, fun hzk => ?_⟩
  have hne : z.toNat ≠ k := by omega
  have hgap := h.2 hne
  have hpos := lt_min (sub_pos.mpr hhi) (sub_pos.mpr hlo)
  linarith

private theorem diagonal_bounds {p : ℝ} {T : Matrix (Fin 2) (Fin 2) ℤ}
    (hT : (realMatrix T).PosDef) :
    objective p T ≤
      (Real.log (T 0 0 : ℝ) - (3 * p) * T 0 0) +
      (Real.log (T 1 1 : ℝ) - (2 * p) * T 1 1) ∧
    (T 0 1 ≠ 0 → objective p T <
      (Real.log (T 0 0 : ℝ) - (3 * p) * T 0 0) +
      (Real.log (T 1 1 : ℝ) - (2 * p) * T 1 1)) := by
  have ha : (0 : ℝ) < T 0 0 := hT.diag_pos (i := 0)
  have hc : (0 : ℝ) < T 1 1 := hT.diag_pos (i := 1)
  have hdet : (realMatrix T).det ≤ (T 0 0 : ℝ) * T 1 1 := by
    simp only [Matrix.det_fin_two, realMatrix, Matrix.map_apply, Int.coe_castRingHom]
    rw [symmetric_entries hT]
    nlinarith [sq_nonneg (T 0 1 : ℝ)]
  have hle := Real.log_le_log hT.det_pos hdet
  rw [Real.log_mul ha.ne' hc.ne'] at hle
  constructor
  · unfold objective
    nlinarith
  · intro h01
    have hlt : (realMatrix T).det < (T 0 0 : ℝ) * T 1 1 := by
      linarith [off_diagonal_det_loss hT h01]
    have hlog := Real.log_lt_log hT.det_pos hlt
    rw [Real.log_mul ha.ne' hc.ne'] at hlog
    unfold objective
    nlinarith

private theorem coordinate_bounds {p : ℝ} (hp : priceWindow p)
    {T : Matrix (Fin 2) (Fin 2) ℤ} (hT : (realMatrix T).PosDef) :
    (Real.log (T 0 0 : ℝ) - (3 * p) * T 0 0 ≤ Real.log 2 - (3 * p) * 2 ∧
      (T 0 0 ≠ 2 → Real.log (T 0 0 : ℝ) - (3 * p) * T 0 0 <
        Real.log 2 - (3 * p) * 2)) ∧
    (Real.log (T 1 1 : ℝ) - (2 * p) * T 1 1 ≤ Real.log 3 - (2 * p) * 3 ∧
      (T 1 1 ≠ 3 → Real.log (T 1 1 : ℝ) - (2 * p) * T 1 1 <
        Real.log 3 - (2 * p) * 3)) := by
  have haR : (0 : ℝ) < T 0 0 := hT.diag_pos (i := 0)
  have hcR : (0 : ℝ) < T 1 1 := hT.diag_pos (i := 1)
  have ha : (0 : ℤ) < T 0 0 := by exact_mod_cast haR
  have hc : (0 : ℤ) < T 1 1 := by exact_mod_cast hcR
  constructor
  · simpa using integer_log_bound (k := 2) (q := 3 * p) (by norm_num)
      (by simpa using hp.1.1) (by simpa using hp.1.2) ha
  · simpa using integer_log_bound (k := 3) (q := 2 * p) (by norm_num)
      (by simpa using hp.2.1) (by simpa using hp.2.2) hc

private theorem selected_objective (p : ℝ) :
    objective p selectedMatrix =
      (Real.log 2 - (3 * p) * 2) + (Real.log 3 - (2 * p) * 3) := by
  have hlog : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    simpa only [show (2 : ℝ) * 3 = 6 by norm_num] using
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)
  norm_num [objective, realMatrix, selectedMatrix, Matrix.det_fin_two]
  rw [hlog]
  ring

/-- The nonscalar diagonal matrix maximizes the objective over all admissible integer matrices. -/
theorem weighted_unique_maximum {p : ℝ} (hp : priceWindow p)
    (T : Matrix (Fin 2) (Fin 2) ℤ) (hT : (realMatrix T).PosDef) :
    objective p T ≤ objective p selectedMatrix ∧
    (T ≠ selectedMatrix → objective p T < objective p selectedMatrix) := by
  obtain ⟨ha, hc⟩ := coordinate_bounds hp hT
  obtain ⟨hle, hstrict⟩ := diagonal_bounds (p := p) hT
  rw [selected_objective]
  constructor
  · linarith [ha.1, hc.1]
  · intro hne
    by_cases h01 : T 0 1 = 0
    · by_cases h00 : T 0 0 = 2
      · have h11 : T 1 1 ≠ 3 := by
          intro h11
          apply hne
          have h10 : T 1 0 = 0 := (symmetric_entries hT).trans h01
          ext i j
          fin_cases i <;> fin_cases j <;> simp [selectedMatrix, h00, h01, h10, h11]
        linarith [ha.1, hc.2 h11]
      · linarith [ha.2 h00, hc.1]
    · linarith [hstrict h01, ha.1, hc.1]

/-- The selected matrix has unequal diagonals and is no real scalar matrix. -/
theorem selectedMatrix_not_scalar :
    selectedMatrix 0 0 ≠ selectedMatrix 1 1 ∧
    ∀ c : ℝ, realMatrix selectedMatrix ≠ c • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  constructor
  · norm_num [selectedMatrix]
  · intro c h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
    have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) h
    norm_num [realMatrix, selectedMatrix] at h00 h11
    linarith

/-- A nonempty strict price window and a unique integral optimum do not force equal diagonals. -/
theorem weighted_selector_refutes_uniformity : ¬ uniformSelection := by
  intro h
  have heq := h (1 / 6) one_sixth_mem_priceWindow selectedMatrix selectedMatrix_posDef
    (fun T hT hne => (weighted_unique_maximum one_sixth_mem_priceWindow T hT).2 hne)
  exact selectedMatrix_not_scalar.1 heq

#print axioms one_sixth_mem_priceWindow
#print axioms priceWindow_nonempty
#print axioms selectedMatrix_posDef
#print axioms off_diagonal_det_loss
#print axioms weighted_unique_maximum
#print axioms selectedMatrix_not_scalar
#print axioms weighted_selector_refutes_uniformity

end
end D5.S3.Arith.GoldenResource.WeightedDiscreteLogNoGo
