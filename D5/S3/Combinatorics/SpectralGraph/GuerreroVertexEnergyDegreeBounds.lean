/- GID: D5/S3/Combinatorics/SpectralGraph/GuerreroVertexEnergyDegreeBounds
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/GuerreroVertexEnergyDegreeBounds
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/SpectralGraph/GuerreroVertexEnergyDegreeBounds.claim; result=D5/S3/Combinatorics/SpectralGraph/GuerreroVertexEnergyDegreeBounds.result; claim=D5/S3/Combinatorics/SpectralGraph/GuerreroVertexEnergyDegreeBounds.claim
   digest: The upper vertex-energy degree bound fails on the six-vertex path. -/

/-
result: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#19702; Refuted).
Direct frozen dependencies: none.
exists_b: proof_shape: bind-only; escape_witness: none; consumers: result.
aMat_eq: proof_shape: bind-only; escape_witness: none; consumers: aMat_herm, adjacency_energy, normLap_shift.
aMat_herm: proof_shape: bind-only; escape_witness: none; consumers: abs_a.
cubic_fourth: proof_shape: bind-only; escape_witness: none; consumers: x_square, x_factor.
x_square: proof_shape: bind-only; escape_witness: none; consumers: abs_a.
x_factor: proof_shape: bind-only; escape_witness: none; consumers: x_pos.
x_pos: proof_shape: bind-only; escape_witness: none; consumers: abs_a.
abs_a: proof_shape: bind-only; escape_witness: none; consumers: adjacency_energy.
adjacency_energy: proof_shape: bind-only; escape_witness: none; consumers: adjacency_lower.
adjacency_lower: proof_shape: bind-only; escape_witness: none; consumers: result.
path_degree: proof_shape: bind-only; escape_witness: none; consumers: normLap_shift.
path_max: proof_shape: bind-only; escape_witness: none; consumers: normalized_upper.
normLap_shift: proof_shape: bind-only; escape_witness: none; consumers: normalized_energy.
rMat_herm: proof_shape: bind-only; escape_witness: none; consumers: abs_neg_r.
y_square: proof_shape: bind-only; escape_witness: none; consumers: abs_neg_r.
y_factor: proof_shape: bind-only; escape_witness: none; consumers: y_pos.
y_pos: proof_shape: bind-only; escape_witness: none; consumers: abs_neg_r.
abs_neg_r: proof_shape: bind-only; escape_witness: none; consumers: normalized_energy.
normalized_energy: proof_shape: bind-only; escape_witness: none; consumers: normalized_upper.
normalized_upper: proof_shape: bind-only; escape_witness: none; consumers: result.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
The source definitions are the real-matrix expressions stated in #19702.
The conjecture is refuted at index 2 of SimpleGraph.pathGraph 6; the blow-up family and the universal lower bound are not asserted.
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

/-! Binding conventions for J. Guerrero, "Laplacian Energies of Vertices", arXiv:2201.01252v1 (Linear Algebra Appl. 706
(2025) 124–143): the energy of a vertex `E_G(v_i) := |A|_ii`, the normalized Laplacian
`L := I − D^{−1/2} A D^{−1/2}`, the normalized Laplacian energy of a vertex `LE_G(v_i) := φ_i(|L − I|)`, and Remark 6
(Conjecture): "According to numerical experiments the analog result is true for the energy of vertices, that is:
d_min LE_G(v) ≤ E_G(v) ≤ d_max LE_G(v) for all v ∈ V", for simple connected graphs. The absolute value of a real
symmetric matrix is Mathlib's continuous functional calculus `cfc (fun x => |x|)`. -/

namespace D5.S3.Combinatorics.SpectralGraph.GuerreroVertexEnergyDegreeBounds

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `|M| = cfc (fun x => |x|) M`, the absolute value of a real symmetric matrix. -/
noncomputable def matAbs (M : Matrix V V ℝ) : Matrix V V ℝ :=
  cfc (fun x : ℝ => |x|) M

/-- `E_G(v) := |A|_vv`. -/
noncomputable def vertexEnergy (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℝ :=
  matAbs (G.adjMatrix ℝ) v v

/-- `D^{−1/2}`, the diagonal matrix with entries `1 / √d_v`. -/
noncomputable def degInvSqrt (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  Matrix.diagonal fun v => 1 / Real.sqrt (G.degree v)

/-- The normalized Laplacian `L := I − D^{−1/2} A D^{−1/2}`. -/
noncomputable def normLap (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  1 - degInvSqrt G * G.adjMatrix ℝ * degInvSqrt G

/-- `LE_G(v) := φ_v(|L − I|) = |L − I|_vv`. -/
noncomputable def normLapVertexEnergy (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℝ :=
  matAbs (normLap G - 1) v v


/-- Remark 6 (Conjecture): for every finite simple connected graph `G` and every vertex `v`,
`d_min LE_G(v) ≤ E_G(v) ≤ d_max LE_G(v)`. -/
def claim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
    ∀ v : V, (G.minDegree : ℝ) * normLapVertexEnergy G v ≤ vertexEnergy G v ∧
      vertexEnergy G v ≤ (G.maxDegree : ℝ) * normLapVertexEnergy G v

end D5.S3.Combinatorics.SpectralGraph.GuerreroVertexEnergyDegreeBounds

open scoped MatrixOrder
open Matrix
namespace D5.S3.Combinatorics.SpectralGraph.GuerreroVertexEnergyDegreeBounds
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000
set_option maxHeartbeats 800000

private theorem exists_b : ∃ b : ℝ, 1 < b ∧ b < 4/3 ∧ b^3+b^2-2*b-1 = 0 := by
  obtain ⟨b, hb, he⟩ := intermediate_value_Icc (a := (1 : ℝ)) (b := 4/3)
    (f := fun x : ℝ => x^3+x^2-2*x-1) (by norm_num) (by fun_prop)
    (show (0 : ℝ) ∈ Set.Icc _ _ by norm_num)
  refine ⟨b, ?_, ?_, he⟩
  · rcases lt_or_eq_of_le hb.1 with h | h
    · exact h
    · subst b; norm_num at he
  · rcases lt_or_eq_of_le hb.2 with h | h
    · exact h
    · subst b; norm_num at he

private def aMat : Matrix (Fin 6) (Fin 6) ℝ := ![![0, 1, 0, 0, 0, 0],
  ![1, 0, 1, 0, 0, 0],
  ![0, 1, 0, 1, 0, 0],
  ![0, 0, 1, 0, 1, 0],
  ![0, 0, 0, 1, 0, 1],
  ![0, 0, 0, 0, 1, 0]]
private noncomputable def xMat (b : ℝ) : Matrix (Fin 6) (Fin 6) ℝ := ![![2*(b ^ 2)/7 + 4*b/7 + (-2 / 7), 0, -2*(b ^ 2)/7 + 2*b/7 + (4 / 7), 0, -2*(b ^ 2)/7 - 2*b/7 + (5 / 7), 0],
  ![0, 6*b/7 + (2 / 7), 0, (9 / 7) - 4*(b ^ 2)/7, 0, -2*(b ^ 2)/7 - 2*b/7 + (5 / 7)],
  ![-2*(b ^ 2)/7 + 2*b/7 + (4 / 7), 0, -2*(b ^ 2)/7 + 4*b/7 + 1, 0, (9 / 7) - 4*(b ^ 2)/7, 0],
  ![0, (9 / 7) - 4*(b ^ 2)/7, 0, -2*(b ^ 2)/7 + 4*b/7 + 1, 0, -2*(b ^ 2)/7 + 2*b/7 + (4 / 7)],
  ![-2*(b ^ 2)/7 - 2*b/7 + (5 / 7), 0, (9 / 7) - 4*(b ^ 2)/7, 0, 6*b/7 + (2 / 7), 0],
  ![0, -2*(b ^ 2)/7 - 2*b/7 + (5 / 7), 0, -2*(b ^ 2)/7 + 2*b/7 + (4 / 7), 0, 2*(b ^ 2)/7 + 4*b/7 + (-2 / 7)]]
private noncomputable def xFactor (b : ℝ) : Matrix (Fin 6) (Fin 6) ℝ := ![![1, 0, 0, 0, 0, 0],
  ![0, 1, 0, 2 - (b ^ 2), 0, (b ^ 2)/2 + b/2 + (-3 / 2)],
  ![(b ^ 2) - 1, 0, 1, 0, 0, 0],
  ![0, 0, 0, 1, 0, (b ^ 2) - 1],
  ![(b ^ 2)/2 + b/2 + (-3 / 2), 0, 2 - (b ^ 2), 0, 1, 0],
  ![0, 0, 0, 0, 0, 1]]
private noncomputable def xDiag (b : ℝ) : Fin 6 → ℝ := ![2*(b ^ 2)/7 + 4*b/7 + (-2 / 7), (b ^ 2)/2 + 3*b/2 + (-3 / 2), 1, 1, (b ^ 2)/2 + 3*b/2 + (-3 / 2), 2*(b ^ 2)/7 + 4*b/7 + (-2 / 7)]

private theorem aMat_eq : (SimpleGraph.pathGraph 6).adjMatrix ℝ = aMat := by
  exact Matrix.ext_iff_trace_mul_left.mpr (congrFun rfl)

private theorem aMat_herm : aMat.IsHermitian := by
  rw [← aMat_eq]
  exact Matrix.isHermitian_iff_isSymm.mpr (SimpleGraph.pathGraph 6).isSymm_adjMatrix

private theorem cubic_fourth (b : ℝ) (hb : b^3+b^2-2*b-1=0) :
    b^4 = 3*b^2-b-1 := by
  linear_combination (b-1)*hb

private theorem x_square (b : ℝ) (hb : b^3+b^2-2*b-1=0) :
    xMat b * xMat b = aMat * aMat := by
  have hb4 := cubic_fourth b hb
  ext i j
  simp only [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [xMat, aMat, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> linarith only [hb, hb4]


private theorem x_factor (b : ℝ) (hb : b^3+b^2-2*b-1=0) :
    xFactor b * Matrix.diagonal (xDiag b) * (xFactor b)ᴴ = xMat b := by
  have hb4 := cubic_fourth b hb
  have hb5 : b^5 = -4*b^2+5*b+3 := by linear_combination (b^2-b+3)*hb
  have hb6 : b^6 = 9*b^2-5*b-4 := by linear_combination (b^3-b^2+3*b-4)*hb
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [xFactor, xDiag, xMat, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.diagonal_apply, Matrix.conjTranspose_apply] <;>
    ring_nf <;> linarith only [hb, hb4, hb5, hb6]


private theorem x_pos (b : ℝ) (hb : b^3+b^2-2*b-1=0) (h1 : 1 < b) :
    (xMat b).PosSemidef := by
  rw [← x_factor b hb]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> dsimp [xDiag] <;> nlinarith [sq_nonneg b]

private theorem abs_a (b : ℝ) (hb : b^3+b^2-2*b-1=0) (h1 : 1 < b) :
    matAbs aMat = xMat b := by
  unfold matAbs
  rw [show (fun x : ℝ => |x|) = (fun x : ℝ => ‖x‖) by ext; exact Real.norm_eq_abs _ |>.symm,
    ← CFC.abs_eq_cfc_norm aMat aMat_herm, CFC.abs, aMat_herm.isSelfAdjoint.star_eq]
  exact CFC.sqrt_unique (x_square b hb) (x_pos b hb h1).nonneg

private theorem adjacency_energy (b : ℝ) (hb : b^3+b^2-2*b-1=0) (h1 : 1 < b) :
    vertexEnergy (SimpleGraph.pathGraph 6) 2 = (7+4*b-2*b^2)/7 := by
  rw [vertexEnergy, aMat_eq, abs_a b hb h1]
  norm_num [xMat]
  ring

private theorem adjacency_lower (b : ℝ) (hb : b^3+b^2-2*b-1=0)
    (h1 : 1 < b) (h4 : b < 4/3) : (5/4 : ℝ) < vertexEnergy (SimpleGraph.pathGraph 6) 2 := by
  rw [adjacency_energy b hb h1]
  have hsq : (b-1)^2 < (1/3 : ℝ)^2 := by
    exact (sq_lt_sq₀ (sub_nonneg.mpr h1.le) (by norm_num : (0 : ℝ) ≤ 1/3)).2 (by linarith)
  nlinarith


private noncomputable def rMat (r : ℝ) : Matrix (Fin 6) (Fin 6) ℝ := ![![0, r/2, 0, 0, 0, 0],
  ![r/2, 0, (1 / 2), 0, 0, 0],
  ![0, (1 / 2), 0, (1 / 2), 0, 0],
  ![0, 0, (1 / 2), 0, (1 / 2), 0],
  ![0, 0, 0, (1 / 2), 0, r/2],
  ![0, 0, 0, 0, r/2, 0]]
private noncomputable def yMat (r t : ℝ) : Matrix (Fin 6) (Fin 6) ℝ := ![![t/5 + (1 / 5), 0, r/5, 0, -r*t/10 + r/5, 0],
  ![0, t/5 + (2 / 5), 0, (2 / 5) - t/10, 0, -r*t/10 + r/5],
  ![r/5, 0, t/10 + (2 / 5), 0, (2 / 5) - t/10, 0],
  ![0, (2 / 5) - t/10, 0, t/10 + (2 / 5), 0, r/5],
  ![-r*t/10 + r/5, 0, (2 / 5) - t/10, 0, t/5 + (2 / 5), 0],
  ![0, -r*t/10 + r/5, 0, r/5, 0, t/5 + (1 / 5)]]
private noncomputable def yFactor (r t : ℝ) : Matrix (Fin 6) (Fin 6) ℝ := ![![1, 0, 0, 0, 0, 0],
  ![0, 1, 0, (3 / 2) - t/2, 0, 3*r*t/8 - 7*r/8],
  ![r*t/4 - r/4, 0, 1, 0, 0, 0],
  ![0, 0, 0, 1, 0, r*t/4 - r/4],
  ![3*r*t/8 - 7*r/8, 0, (3 / 2) - t/2, 0, 1, 0],
  ![0, 0, 0, 0, 0, 1]]
private noncomputable def yDiag (t : ℝ) : Fin 6 → ℝ := ![t/5 + (1 / 5), 5*t/8 + (-5 / 8), (1 / 2), (1 / 2), 5*t/8 + (-5 / 8), t/5 + (1 / 5)]

private theorem path_degree (i : Fin 6) : (SimpleGraph.pathGraph 6).degree i = (![1,2,2,2,2,1] : Fin 6 → ℕ) i := by
  fin_cases i <;> decide

private theorem path_max : (SimpleGraph.pathGraph 6).maxDegree = 2 := by
  exact Eq.symm (Nat.eq_of_beq_eq_true rfl)

private theorem normLap_shift : normLap (SimpleGraph.pathGraph 6) - 1 = - rMat (Real.sqrt 2) := by
  have hr0 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
  have hr2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold normLap degInvSqrt
  rw [aMat_eq]
  ext i j
  simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.mul_apply, Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [rMat, aMat, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply,
      Fin.sum_univ_succ, path_degree, Real.sqrt_one] <;>
    field_simp <;> nlinarith

private theorem rMat_herm (r : ℝ) : (rMat r).IsHermitian := by
  apply Matrix.ext
  intro i j
  change rMat r j i = rMat r i j
  fin_cases i <;> fin_cases j <;> norm_num [rMat]

private theorem y_square (r t : ℝ) (hr : r^2=2) (ht : t^2=5) :
    yMat r t * yMat r t = rMat r * rMat r := by
  ext i j
  simp only [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [yMat, rMat, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [hr, ht] <;> ring

private theorem y_factor (r t : ℝ) (hr : r^2=2) (ht : t^2=5) :
    yFactor r t * Matrix.diagonal (yDiag t) * (yFactor r t)ᴴ = yMat r t := by
  have ht3 : t^3 = 5*t := by linear_combination t*ht
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [yMat, yFactor, yDiag, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.diagonal_apply, Matrix.conjTranspose_apply] <;>
    ring_nf <;> simp only [hr, ht, ht3] <;> ring

private theorem y_pos (r t : ℝ) (hr : r^2=2) (ht : t^2=5) (h1 : 1 < t) :
    (yMat r t).PosSemidef := by
  rw [← y_factor r t hr ht]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> dsimp [yDiag] <;> linarith

private theorem abs_neg_r (r t : ℝ) (hr : r^2=2) (ht : t^2=5) (h1 : 1 < t) :
    matAbs (- rMat r) = yMat r t := by
  unfold matAbs
  have hh : IsSelfAdjoint (-rMat r) := (rMat_herm r).isSelfAdjoint.neg
  rw [show (fun x : ℝ => |x|) = (fun x : ℝ => ‖x‖) by ext; exact Real.norm_eq_abs _ |>.symm,
    ← CFC.abs_eq_cfc_norm (-rMat r) hh, CFC.abs, hh.star_eq, neg_mul_neg]
  exact CFC.sqrt_unique (y_square r t hr ht) (y_pos r t hr ht h1).nonneg

private theorem normalized_energy : normLapVertexEnergy (SimpleGraph.pathGraph 6) 2 = (4+Real.sqrt 5)/10 := by
  have ht2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have ht1 : 1 < Real.sqrt 5 := by
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  rw [normLapVertexEnergy, normLap_shift, abs_neg_r (Real.sqrt 2) (Real.sqrt 5)
    (Real.sq_sqrt (by norm_num)) ht2 ht1]
  norm_num [yMat]
  ring

private theorem normalized_upper : ((SimpleGraph.pathGraph 6).maxDegree : ℝ) * normLapVertexEnergy (SimpleGraph.pathGraph 6) 2 < 5/4 := by
  rw [normalized_energy, path_max]
  have ht : Real.sqrt 5 < (9/4 : ℝ) :=
    (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 9/4)).2 (by norm_num)
  norm_num
  linarith

theorem result : ¬ claim := by
  intro h
  obtain ⟨b, hb1, hb4, hb⟩ := exists_b
  have hc : (SimpleGraph.pathGraph 6).Connected := SimpleGraph.connected_pathGraph_add_one 5
  have hu := (h (Fin 6) (SimpleGraph.pathGraph 6) hc 2).2
  have hl := adjacency_lower b hb hb1 hb4
  have hr := normalized_upper
  linarith

end D5.S3.Combinatorics.SpectralGraph.GuerreroVertexEnergyDegreeBounds
