/- GID: D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/RossettiW3PPTMeasurement
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.claim; result=D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.result; claim=D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.claim
   digest: The optimal three-qubit W-state PPT measurement is not fully separable. -/

/-
admission_basis: open-problem-resolution (#19016; Refuted)
escape_witness: none
proof_shape: result: bind-only; consumers: none (settling result).
proof_shape: diagonal_pair: bind-only; escape_witness: none; consumers: product_mass_ratio.
proof_shape: tensor_psd: bind-only; escape_witness: none; consumers: pt_tensor_psd, separable_mass_ratio.
proof_shape: pt_tensor: bind-only; escape_witness: none; consumers: pt_tensor_psd.
proof_shape: pt_tensor_psd: bind-only; escape_witness: none; consumers: separable_mass_ratio.
proof_shape: mulVec_w: bind-only; escape_witness: none; consumers: product_mass_ratio, kernel_quadratics.
proof_shape: mulVec_z: bind-only; escape_witness: none; consumers: product_mass_ratio, kernel_quadratics.
proof_shape: product_mass_ratio: bind-only; escape_witness: none; consumers: separable_mass_ratio.
proof_shape: w_projectors: bind-only; escape_witness: none; consumers: remainder_formula.
proof_shape: remainder_formula: bind-only; escape_witness: none; consumers: kernel_quadratics, remainder_masses.
proof_shape: kernel_quadratics: bind-only; escape_witness: none; consumers: result.
proof_shape: remainder_masses: bind-only; escape_witness: none; consumers: result.
proof_shape: separable_mass_ratio: bind-only; escape_witness: none; consumers: result.
Direct frozen dependencies:
  D5/S3/Quantum/Entanglement/FullySeparableExchangeObstruction.IsFullySeparableLocal
    statement_id: sha256:ecad6b2f6fffd2c28d0b5dc3b13ef1a5af9ce5e3e792e1142f685a52b45b7550
  D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState
    statement_id: sha256:4607242f5ca0464588fa7eea47cf23ce7ba387f9018664f7796740270945b0f5
  D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.tensor
    statement_id: sha256:7b55bb55c89484c1d11f702d9e6d7d499b9be33a40639b276a9a07e732124f7a
The same-delivery publication density_psd is inlined for this dependency list.
Escape audit unfinished for that publication: https://github.com/the-omega-institute/trureturing/issues/19102.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
The source's computational basis indicator and rank-one projector are written with
Pi.single and Matrix.vecMulVec; no duplicate ket or proj declaration is introduced.
The tensor product is the existing PronkoFredkinNonCyclicAnnihilation.tensor.
-/

import D5.S3.Quantum.Entanglement.FullySeparableExchangeObstruction
import D5.S3.Quantum.Dynamics.PronkoFredkinNonCyclicAnnihilation

/-! Binding conventions for arXiv:2510.10058v1, Sec. X.0.4 (W states), Eqs. (62), (79), (83).
Three qubits; a basis label `x : Fin 3 → Fin 2` lists the bits of qubits 1, 2, 3. -/

open D5.S3.Quantum.Dynamics.PronkoFredkinNonCyclicAnnihilation (tensor)

noncomputable section
namespace D5.S3.Quantum.Measurement.RossettiW3PPTMeasurement

open D5.S3.Quantum.Entanglement.FullySeparableExchangeObstruction (IsFullySeparableLocal density_psd)
open Matrix


/-- `|W₃⟩ = √(1/3) (|100⟩ + |010⟩ + |001⟩)`. -/
def W3 : (Fin 3 → Fin 2) → ℂ :=
  ((Real.sqrt (1 / 3) : ℝ) : ℂ) • ((Pi.single ![1, 0, 0] (1 : ℂ)) + (Pi.single ![0, 1, 0] (1 : ℂ)) + (Pi.single ![0, 0, 1] (1 : ℂ)))

/-- The anti-W state `|W̄₃⟩ = √(1/3) (|011⟩ + |101⟩ + |110⟩)`. -/
def W3bar : (Fin 3 → Fin 2) → ℂ :=
  ((Real.sqrt (1 / 3) : ℝ) : ℂ) • ((Pi.single ![0, 1, 1] (1 : ℂ)) + (Pi.single ![1, 0, 1] (1 : ℂ)) + (Pi.single ![1, 1, 0] (1 : ℂ)))


/-- `P₁ = |100⟩⟨100| + |010⟩⟨010| + |001⟩⟨001|`. -/
def P1 : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ :=
  (Matrix.vecMulVec ((Pi.single ![1, 0, 0] (1 : ℂ))) (star ((Pi.single ![1, 0, 0] (1 : ℂ))))) + (Matrix.vecMulVec ((Pi.single ![0, 1, 0] (1 : ℂ))) (star ((Pi.single ![0, 1, 0] (1 : ℂ))))) + (Matrix.vecMulVec ((Pi.single ![0, 0, 1] (1 : ℂ))) (star ((Pi.single ![0, 0, 1] (1 : ℂ)))))

/-- `P₂ = |011⟩⟨011| + |101⟩⟨101| + |110⟩⟨110|`. -/
def P2 : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ :=
  (Matrix.vecMulVec ((Pi.single ![0, 1, 1] (1 : ℂ))) (star ((Pi.single ![0, 1, 1] (1 : ℂ))))) + (Matrix.vecMulVec ((Pi.single ![1, 0, 1] (1 : ℂ))) (star ((Pi.single ![1, 0, 1] (1 : ℂ))))) + (Matrix.vecMulVec ((Pi.single ![1, 1, 0] (1 : ℂ))) (star ((Pi.single ![1, 1, 0] (1 : ℂ)))))

/-- The six invariant projectors `Q₁, …, Q₆`. -/
def Q1 : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ := (Matrix.vecMulVec W3 (star W3))
def Q2 : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ := (Matrix.vecMulVec W3bar (star W3bar))
def Q3 : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ := P1 - (Matrix.vecMulVec W3 (star W3))
def Q4 : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ := P2 - (Matrix.vecMulVec W3bar (star W3bar))
def Q5 : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ := (Matrix.vecMulVec ((Pi.single ![0, 0, 0] (1 : ℂ))) (star ((Pi.single ![0, 0, 0] (1 : ℂ)))))
def Q6 : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ := (Matrix.vecMulVec ((Pi.single ![1, 1, 1] (1 : ℂ))) (star ((Pi.single ![1, 1, 1] (1 : ℂ)))))

/-- Eq. (83): `M′ = Q₁ + Σₐ tₐ Qₐ` with `t₂ = 1/2`, `t₃ = t₄ = 0`, `t₅ = 2/3`, `t₆ = 1/12`. -/
def Mprime : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ :=
  Q1 + (1 / 2 : ℂ) • Q2 + (0 : ℂ) • Q3 + (0 : ℂ) • Q4 + (2 / 3 : ℂ) • Q5 + (1 / 12 : ℂ) • Q6

/-- Eq. (62): a SEP POVM element is proportional to a (fully) separable state. -/
def IsSEPEffect (E : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ) : Prop :=
  ∃ (c : ℝ) (ρ : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ),
    0 ≤ c ∧ IsFullySeparableLocal ρ ∧ E = (c : ℂ) • ρ

/-- The two-outcome POVM `(M′, 𝟙 − M′)` belongs to the SEP class. -/
def claim : Prop := IsSEPEffect Mprime ∧ IsSEPEffect (1 - Mprime)

end D5.S3.Quantum.Measurement.RossettiW3PPTMeasurement

namespace D5.S3.Quantum.Measurement.RossettiW3PPTMeasurement


open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open D5.S3.Quantum.Foundation.FiniteStateChannel




private def w : (Fin 3 → Fin 2) → ℂ := (Pi.single ![1,0,0] (1 : ℂ)) + (Pi.single ![0,1,0] (1 : ℂ)) + (Pi.single ![0,0,1] (1 : ℂ))
private def z (i : Fin 3) : (Fin 3 → Fin 2) → ℂ :=
  if i = 0 then 2 • (Pi.single ![0,0,0] (1 : ℂ)) + (Pi.single ![1,1,0] (1 : ℂ)) + (Pi.single ![1,0,1] (1 : ℂ))
  else if i = 1 then 2 • (Pi.single ![0,0,0] (1 : ℂ)) + (Pi.single ![1,1,0] (1 : ℂ)) + (Pi.single ![0,1,1] (1 : ℂ))
  else 2 • (Pi.single ![0,0,0] (1 : ℂ)) + (Pi.single ![1,0,1] (1 : ℂ)) + (Pi.single ![0,1,1] (1 : ℂ))

private def mass1 (X : (Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ)) : ℂ := X ![1,0,0] ![1,0,0] +
  X ![0,1,0] ![0,1,0] + X ![0,0,1] ![0,0,1]
private def mass2 (X : (Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ)) : ℂ := X ![1,1,0] ![1,1,0] +
  X ![1,0,1] ![1,0,1] + X ![0,1,1] ![0,1,1]

private theorem diagonal_pair (a b c d e x y t : ℂ)
    (hax : a = 0 → x = 0) (hby : b = 0 → y = 0)
    (h1 : d*b*c = 2*a*b*c) (h2 : a*e*c = 2*a*b*c)
    (hp : 2*x*y*c + d*e*c + d*y*t = 0) : d*e*c = 4*a*b*c := by
  by_cases hc : c = 0
  · simp [hc]
  by_cases ha : a = 0
  · have hh : d*b*c = 0 := by simpa [ha] using h1
    rcases mul_eq_zero.mp hh with hdb | hh
    · rcases mul_eq_zero.mp hdb with hd | hb
      · simp [hd, ha]
      · have hx := hax ha
        have hy := hby hb
        simpa [hx, hy, ha] using hp
    · exact (hc hh).elim
  by_cases hb : b = 0
  · have hh : a*e*c = 0 := by simpa [hb] using h2
    have he : e = 0 := by
      rcases mul_eq_zero.mp hh with hae | hcz
      · exact (mul_eq_zero.mp hae).resolve_left ha
      · exact (hc hcz).elim
    simp [hb, he]
  have hd : d = 2*a := by
    apply mul_right_cancel₀ (mul_ne_zero hb hc)
    linear_combination h1
  have he : e = 2*b := by
    apply mul_left_cancel₀ ha
    apply mul_right_cancel₀ hc
    linear_combination h2
  rw [hd, he]
  ring

private theorem tensor_psd (A : Fin 3 → (Matrix (Fin 2) (Fin 2) ℂ))
    (hA : ∀ i, (A i).PosSemidef) : (tensor 3 A).PosSemidef := by
  convert ((hA 0).kronecker ((hA 1).kronecker (hA 2))).submatrix
    (fun x : (Fin 3 → Fin 2) => (x 0, x 1, x 2)) using 1
  ext x y
  simp [tensor, Fin.prod_univ_succ, Matrix.kroneckerMap_apply]

private theorem pt_tensor (A : Fin 3 → (Matrix (Fin 2) (Fin 2) ℂ)) (i : Fin 3) :
    Matrix.of (fun x y => tensor 3 A (Function.update x i (y i)) (Function.update y i (x i))) = tensor 3 (fun v => if v = i then (A v)ᵀ else A v) := by
  ext x y
  unfold tensor
  simp only [Matrix.of_apply]
  apply Finset.prod_congr rfl
  intro v _
  by_cases hv : v = i
  · subst v
    simp
  · simp [hv]

private theorem pt_tensor_psd (A : Fin 3 → (Matrix (Fin 2) (Fin 2) ℂ))
    (hA : ∀ i, (A i).PosSemidef) (i : Fin 3) : (Matrix.of (fun x y => tensor 3 A (Function.update x i (y i)) (Function.update y i (x i)))).PosSemidef := by
  rw [pt_tensor]
  apply tensor_psd
  intro v
  split_ifs
  · exact (hA v).transpose
  · exact hA v

private theorem mulVec_w (X : (Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ)) (x : (Fin 3 → Fin 2)) :
    (X *ᵥ w) x = X x ![1,0,0] + X x ![0,1,0] + X x ![0,0,1] := by
  simp only [w, Matrix.mulVec_add, Matrix.mulVec_single_one, Pi.add_apply, Matrix.col_apply]

private theorem mulVec_z (X : (Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ)) (i : Fin 3) (x : (Fin 3 → Fin 2)) :
    (X *ᵥ z i) x = if i = 0 then
      2 * X x ![0,0,0] + X x ![1,1,0] + X x ![1,0,1]
    else if i = 1 then
      2 * X x ![0,0,0] + X x ![1,1,0] + X x ![0,1,1]
    else 2 * X x ![0,0,0] + X x ![1,0,1] + X x ![0,1,1] := by
  unfold z
  split_ifs <;>
    simp only [two_smul ℕ, Matrix.mulVec_add, Matrix.mulVec_single_one,
      Pi.add_apply, Matrix.col_apply] <;> ring

end D5.S3.Quantum.Measurement.RossettiW3PPTMeasurement

namespace D5.S3.Quantum.Measurement.RossettiW3PPTMeasurement
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix

private theorem product_mass_ratio (A : Fin 3 → (Matrix (Fin 2) (Fin 2) ℂ))
    (hA : ∀ i, (A i).PosSemidef)
    (hw : tensor 3 A *ᵥ w = 0)
    (hz : ∀ i, Matrix.of (fun x y => tensor 3 A (Function.update x i (y i)) (Function.update y i (x i))) *ᵥ z i = 0) :
    mass2 (tensor 3 A) = 2 * mass1 (tensor 3 A) := by
  have hzero (i : Fin 3) (j : (Fin 2)) (h : A i 0 0 = 0) : A i j 0 = 0 := by
    have hq : star (Pi.single (0 : (Fin 2)) (1 : ℂ)) ⬝ᵥ
        (A i *ᵥ Pi.single 0 1) = 0 := by
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using
      congrFun (((hA i).dotProduct_mulVec_zero_iff).mp hq) j
  have hzeroR (i : Fin 3) (h : A i 0 0 = 0) : A i 0 1 = 0 := by
    have hh := (hA i).isHermitian.apply 0 1
    rw [hzero i 1 h, star_zero] at hh
    exact hh.symm
  have hw0 := congrFun hw ![1,0,0]
  have hw1 := congrFun hw ![0,1,0]
  have hw2 := congrFun hw ![0,0,1]
  rw [mulVec_w] at hw0 hw1 hw2
  simp [tensor, Fin.prod_univ_three] at hw0 hw1 hw2
  have hz0 := congrFun (hz 0) ![0,0,0]
  have hz1 := congrFun (hz 1) ![0,0,0]
  have hz2 := congrFun (hz 2) ![0,0,0]
  rw [mulVec_z] at hz0 hz1 hz2
  norm_num [tensor, Fin.prod_univ_three] at hz0 hz1 hz2
  have h1 : A 0 1 1 * A 1 0 0 * A 2 0 0 =
      2 * A 0 0 0 * A 1 0 0 * A 2 0 0 := by
    linear_combination hw0 - hz0
  have h2 : A 0 0 0 * A 1 1 1 * A 2 0 0 =
      2 * A 0 0 0 * A 1 0 0 * A 2 0 0 := by
    linear_combination hw1 - hz1
  have h3 : A 0 0 0 * A 1 0 0 * A 2 1 1 =
      2 * A 0 0 0 * A 1 0 0 * A 2 0 0 := by
    linear_combination hw2 - hz2
  have hp01 := congrFun (hz 0) ![1,1,0]
  have hp02 := congrFun (hz 0) ![1,0,1]
  have hp12 := congrFun (hz 1) ![0,1,1]
  rw [mulVec_z] at hp01 hp02 hp12
  norm_num [tensor, Fin.prod_univ_three] at hp01 hp02 hp12
  have h01 := diagonal_pair (A 0 0 0) (A 1 0 0) (A 2 0 0)
    (A 0 1 1) (A 1 1 1) (A 0 0 1) (A 1 1 0) (A 2 0 1)
    (hzeroR 0) (hzero 1 1) h1 h2 (by linear_combination hp01)
  have h02 := diagonal_pair (A 0 0 0) (A 2 0 0) (A 1 0 0)
    (A 0 1 1) (A 2 1 1) (A 0 0 1) (A 2 1 0) (A 1 0 1)
    (hzeroR 0) (hzero 2 1)
    (by linear_combination h1) (by linear_combination h3)
    (by linear_combination hp02)
  have h12 := diagonal_pair (A 1 0 0) (A 2 0 0) (A 0 0 0)
    (A 1 1 1) (A 2 1 1) (A 1 0 1) (A 2 1 0) (A 0 0 1)
    (hzeroR 1) (hzero 2 1)
    (by linear_combination h2) (by linear_combination h3)
    (by linear_combination hp12)
  simp [mass1, mass2, tensor, Fin.prod_univ_three]
  linear_combination h01 + h02 + h12 - 2*h1 - 2*h2 - 2*h3

end D5.S3.Quantum.Measurement.RossettiW3PPTMeasurement

namespace D5.S3.Quantum.Measurement.RossettiW3PPTMeasurement
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

private def wb : (Fin 3 → Fin 2) → ℂ := (Pi.single ![0,1,1] (1 : ℂ)) + (Pi.single ![1,0,1] (1 : ℂ)) + (Pi.single ![1,1,0] (1 : ℂ))

private theorem w_projectors : Q1 = (1/3 : ℂ) • (Matrix.vecMulVec w (star w)) ∧
    Q2 = (1/3 : ℂ) • (Matrix.vecMulVec wb (star wb)) := by
  have hs : ((Real.sqrt (1/3) : ℝ) : ℂ) * ((Real.sqrt (1/3) : ℝ) : ℂ) = 1/3 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hp (u : (Fin 3 → Fin 2) → ℂ) :
      (Matrix.vecMulVec ((((Real.sqrt (1/3) : ℝ) : ℂ)) • u) (star ((((Real.sqrt (1/3) : ℝ) : ℂ)) • u))) = (1/3 : ℂ) • (Matrix.vecMulVec u (star u)) := by
    simp only [star_smul, Complex.star_def, Complex.conj_ofReal,
      Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul, hs]
  constructor
  · exact hp w
  · exact hp wb

private theorem remainder_formula : (1 : (Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ)) - Mprime =
    1 - (1/3 : ℂ) • (Matrix.vecMulVec w (star w)) - (1/6 : ℂ) • (Matrix.vecMulVec wb (star wb)) -
      (2/3 : ℂ) • (Matrix.vecMulVec ((Pi.single ![0,0,0] (1 : ℂ))) (star ((Pi.single ![0,0,0] (1 : ℂ))))) - (1/12 : ℂ) • (Matrix.vecMulVec ((Pi.single ![1,1,1] (1 : ℂ))) (star ((Pi.single ![1,1,1] (1 : ℂ))))) := by
  have h1 := w_projectors.1
  have h2 := w_projectors.2
  unfold Mprime
  rw [h1, h2]
  ext x y
  simp [Q5, Q6, Matrix.smul_apply, Matrix.sub_apply]
  ring

set_option maxHeartbeats 2000000 in
private theorem kernel_quadratics :
    star w ⬝ᵥ (((1 : (Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ)) - Mprime) *ᵥ w) = 0 ∧
    ∀ i, star (z i) ⬝ᵥ (Matrix.of (fun x y => ((1 : (Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ)) - Mprime) (Function.update x i (y i)) (Function.update y i (x i))) *ᵥ z i) = 0 := by
  have wd (u : (Fin 3 → Fin 2) → ℂ) : star w ⬝ᵥ u = u ![1,0,0] + u ![0,1,0] + u ![0,0,1] := by
    simp only [w, star_add, add_dotProduct, Pi.star_single, star_one]
    simp only [single_one_dotProduct]
  have zd (i : Fin 3) (u : (Fin 3 → Fin 2) → ℂ) : star (z i) ⬝ᵥ u =
      if i = 0 then 2 * u ![0,0,0] + u ![1,1,0] + u ![1,0,1]
      else if i = 1 then 2 * u ![0,0,0] + u ![1,1,0] + u ![0,1,1]
      else 2 * u ![0,0,0] + u ![1,0,1] + u ![0,1,1] := by
    unfold z
    split_ifs <;>
      simp only [two_smul ℕ, star_add, add_dotProduct, Pi.star_single, star_one] <;>
      simp only [single_one_dotProduct] <;> ring
  rw [remainder_formula]
  constructor
  · rw [wd]
    simp only [mulVec_w]
    norm_num [w, wb, Pi.single_apply, Matrix.vecMulVec_apply, Matrix.one_apply,
      Matrix.sub_apply, Matrix.smul_apply, funext_iff, Fin.forall_fin_succ]
  · intro i
    rw [zd]
    simp only [mulVec_z]
    fin_cases i <;>
      norm_num [Function.update_apply, w, wb, Pi.single_apply, Matrix.vecMulVec_apply, Matrix.one_apply,
        Matrix.sub_apply, Matrix.smul_apply, funext_iff, Fin.forall_fin_succ]

private theorem remainder_masses :
    mass1 ((1 : (Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ)) - Mprime) = 2 ∧
    mass2 ((1 : (Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ)) - Mprime) = 5/2 := by
  rw [remainder_formula]
  norm_num [mass1, mass2, Pi.single_apply, Matrix.vecMulVec_apply, w, wb,
    Matrix.one_apply, funext_iff, Fin.forall_fin_succ]

end D5.S3.Quantum.Measurement.RossettiW3PPTMeasurement

namespace D5.S3.Quantum.Measurement.RossettiW3PPTMeasurement
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel

private theorem separable_mass_ratio (E : (Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ)) (hE : IsSEPEffect E)
    (hw : star w ⬝ᵥ (E *ᵥ w) = 0)
    (hz : ∀ i, star (z i) ⬝ᵥ (Matrix.of (fun x y => E (Function.update x i (y i)) (Function.update y i (x i))) *ᵥ z i) = 0) :
    mass2 E = 2 * mass1 E := by
  obtain ⟨c, ρ, hc, ⟨k, p, σ, hp, _hsum, hρ⟩, he⟩ := hE
  let A : Fin k → Fin 3 → (Matrix (Fin 2) (Fin 2) ℂ) := fun j v =>
    if v = 0 then (c * p j : ℝ) • CStarMatrix.ofMatrix.symm (σ j v).val
    else CStarMatrix.ofMatrix.symm (σ j v).val
  have hd (j : Fin k) (v : Fin 3) :
      (CStarMatrix.ofMatrix.symm (σ j v).val).PosSemidef :=
    D5.S3.Quantum.Entanglement.FullySeparableExchangeObstruction.density_psd (σ j v)
  have hA (j : Fin k) (v : Fin 3) : (A j v).PosSemidef := by
    dsimp only [A]
    split_ifs
    · exact (hd j v).smul (mul_nonneg hc (hp j))
    · exact hd j v
  have hdecomp : E = ∑ j, tensor 3 (A j) := by
    ext x y
    calc
      E x y = (c : ℂ) * ρ x y := by rw [he]; rfl
      _ = ∑ j, (c : ℂ) * ((p j : ℂ) * ∏ v, (σ j v).val (x v) (y v)) := by
        rw [hρ, Finset.mul_sum]
      _ = _ := by
        simp only [Matrix.sum_apply]
        apply Finset.sum_congr rfl
        intro j _
        simp [tensor, A, Fin.prod_univ_three, Complex.real_smul]
        ring
  have kills (F : Fin k → (Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ)) (hF : ∀ j, (F j).PosSemidef)
      (u : (Fin 3 → Fin 2) → ℂ) (h : star u ⬝ᵥ ((∑ j, F j) *ᵥ u) = 0) :
      ∀ j, F j *ᵥ u = 0 := by
    have hs : (∑ j, star u ⬝ᵥ (F j *ᵥ u)) = 0 := by
      rw [← dotProduct_sum, ← Matrix.sum_mulVec]
      exact h
    have hn (j : Fin k) (_ : j ∈ (Finset.univ : Finset (Fin k))) :
        0 ≤ star u ⬝ᵥ (F j *ᵥ u) := (hF j).dotProduct_mulVec_nonneg u
    intro j
    apply (hF j).dotProduct_mulVec_zero_iff.mp
    exact (Finset.sum_eq_zero_iff_of_nonneg hn).mp hs j (Finset.mem_univ j)
  have kw (j : Fin k) : tensor 3 (A j) *ᵥ w = 0 :=
    kills (fun j => tensor 3 (A j)) (fun j => tensor_psd (A j) (hA j)) w
      (by rw [← hdecomp]; exact hw) j
  have kz (i : Fin 3) (j : Fin k) : Matrix.of (fun x y => tensor 3 (A j) (Function.update x i (y i)) (Function.update y i (x i))) *ᵥ z i = 0 := by
    have hpt : Matrix.of (fun x y => E (Function.update x i (y i)) (Function.update y i (x i))) = ∑ j, Matrix.of (fun x y => tensor 3 (A j) (Function.update x i (y i)) (Function.update y i (x i))) := by
      ext x y
      simp only [hdecomp, Matrix.sum_apply, Matrix.of_apply]
    exact kills (fun j => Matrix.of (fun x y => tensor 3 (A j) (Function.update x i (y i)) (Function.update y i (x i))))
      (fun j => pt_tensor_psd (A j) (hA j) i) (z i)
      (by rw [← hpt]; exact hz i) j
  have hr (j : Fin k) := product_mass_ratio (A j) (hA j) (kw j) (fun i => kz i j)
  rw [hdecomp]
  simp only [mass1, mass2, Matrix.sum_apply, ← Finset.sum_add_distrib,
    Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => hr j)

theorem result : ¬ claim := by
  intro h
  have hh := separable_mass_ratio (1 - Mprime) h.2
    kernel_quadratics.1 kernel_quadratics.2
  rw [remainder_masses.1, remainder_masses.2] at hh
  norm_num at hh


end D5.S3.Quantum.Measurement.RossettiW3PPTMeasurement
