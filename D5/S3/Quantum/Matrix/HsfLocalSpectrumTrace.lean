/- GID: D5/S3/Quantum/Matrix/HsfLocalSpectrumTrace
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HsfLocalSpectrumTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Trace]
   utility: none
   digest: General actual two-thirds CFC trace normalization from ordered root jets. -/

import D5.S3.Quantum.Matrix.RpowPencilTaylor

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped ComplexOrder MatrixOrder
namespace D5.S3.Quantum.Matrix.HsfLocalSpectrumTrace
variable {n : Type*} [Fintype n] [DecidableEq n]

private def tr (M : Matrix n n ℂ) : ℂ := M.trace

private theorem tr_comm (A B : Matrix n n ℂ) : tr (A*B) = tr (B*A) :=
  Matrix.trace_mul_comm A B

private theorem tr_cycle (A B C : Matrix n n ℂ) : tr (A*B*C) = tr (B*C*A) :=
  (Matrix.trace_mul_cycle B C A).symm

private structure Jet where
  first : Matrix n n ℂ
  second : Matrix n n ℂ
  third : Matrix n n ℂ

private def Jet.mul (a b : Jet (n := n)) : Jet (n := n) :=
  ⟨a.first+b.first, a.second+a.first*b.first+b.second,
    a.third+a.second*b.first+a.first*b.second+b.third⟩

private def Jet.log2 (a : Jet (n := n)) : ℂ :=
  tr a.second - tr (a.first*a.first)/2

private def Jet.log3 (a : Jet (n := n)) : ℂ :=
  tr a.third - tr (a.first*a.second) + tr (a.first*a.first*a.first)/3

private theorem Jet.log2_mul (a b : Jet (n := n)) :
    (a.mul b).log2 = a.log2+b.log2 := by
  simp only [Jet.log2, Jet.mul, tr, add_mul, mul_add, Matrix.trace_add]
  rw [Matrix.trace_mul_comm b.first a.first]
  ring

private theorem Jet.log3_mul (a b : Jet (n := n)) :
    (a.mul b).log3 = a.log3+b.log3 := by
  simp only [Jet.log3, Jet.mul, tr, add_mul, mul_add, Matrix.trace_add]
  rw [Matrix.trace_mul_comm a.second b.first]
  simp only [← mul_assoc]
  have ha := tr_cycle a.first b.first a.first
  have hb := tr_cycle b.first a.first a.first
  have hc := tr_cycle b.first a.first b.first
  have hd := tr_cycle a.first b.first b.first
  dsimp only [tr] at ha hb hc hd
  rw [ha, hb, hc, hd]
  ring

private def Jet.conj (u : (Matrix n n ℂ)ˣ) (a : Jet (n := n)) : Jet (n := n) :=
  ⟨u.val*a.first*u.inv, u.val*a.second*u.inv, u.val*a.third*u.inv⟩

private theorem tr_conj (u : (Matrix n n ℂ)ˣ) (M : Matrix n n ℂ) :
    tr (u.val*M*u.inv) = tr M := by
  rw [tr_cycle]
  simp [Units.inv_eq_val_inv, mul_assoc]

private theorem Jet.log2_conj (u : (Matrix n n ℂ)ˣ) (a : Jet (n := n)) :
    (a.conj u).log2 = a.log2 := by
  simp only [Jet.log2, Jet.conj]
  rw [show (u.val*a.first*u.inv)*(u.val*a.first*u.inv) =
    u.val*(a.first*a.first)*u.inv by simp [mul_assoc], tr_conj, tr_conj]

private theorem Jet.log3_conj (u : (Matrix n n ℂ)ˣ) (a : Jet (n := n)) :
    (a.conj u).log3 = a.log3 := by
  simp only [Jet.log3, Jet.conj]
  rw [show (u.val*a.first*u.inv)*(u.val*a.second*u.inv) =
    u.val*(a.first*a.second)*u.inv by simp [mul_assoc]]
  rw [show (u.val*a.first*u.inv)*(u.val*a.first*u.inv)*(u.val*a.first*u.inv) =
    u.val*(a.first*a.first*a.first)*u.inv by simp [mul_assoc]]
  rw [tr_conj, tr_conj, tr_conj]

private def rootJet (u : (Matrix n n ℂ)ˣ) (C₁ C₂ C₃ : Matrix n n ℂ) : Jet (n := n) :=
  ⟨C₁*u.inv, C₂*u.inv, C₃*u.inv⟩

private theorem rootJet_cubic (u : (Matrix n n ℂ)ˣ)
    (C₁ C₂ C₃ : Matrix n n ℂ) :
    let P : Matrix n n ℂ := u.val
    let D : Matrix n n ℂ := u.inv
    let a := rootJet u C₁ C₂ C₃
    let t := (a.mul (a.conj u)).mul (a.conj (u^2))
    t.first = (P*P*C₁+P*C₁*P+C₁*P*P)*D^3 ∧
    t.second = (P*P*C₂+P*C₂*P+C₂*P*P+
      P*C₁*C₁+C₁*P*C₁+C₁*C₁*P)*D^3 ∧
    t.third = (P*P*C₃+P*C₃*P+C₃*P*P+
      P*C₁*C₂+P*C₂*C₁+C₁*P*C₂+C₂*P*C₁+C₁*C₂*P+C₂*C₁*P+
      C₁*C₁*C₁)*D^3 := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Jet.mul, Jet.conj, rootJet, Units.inv_eq_val_inv,
      pow_succ, pow_two, mul_add, add_mul, mul_assoc] <;> abel

private theorem rootJet_square (u : (Matrix n n ℂ)ˣ)
    (C₁ C₂ C₃ : Matrix n n ℂ) :
    let P : Matrix n n ℂ := u.val
    let D : Matrix n n ℂ := u.inv
    let a := rootJet u C₁ C₂ C₃
    let b := (a.conj u⁻¹).mul a
    b.first = D*(P*C₁+C₁*P)*D ∧
    b.second = D*(P*C₂+C₁*C₁+C₂*P)*D ∧
    b.third = D*(P*C₃+C₁*C₂+C₂*C₁+C₃*P)*D := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Jet.mul, Jet.conj, rootJet, Units.inv_eq_val_inv,
      mul_add, add_mul, mul_assoc] <;> abel

/-- Finite trace-log coefficient algebra of the ordered cubic equations.
This lemma uses no determinant or analytic logarithm. -/
private theorem trace_normalization_of_recurrences (u : (Matrix n n ℂ)ˣ)
    (K C₁ C₂ C₃ : Matrix n n ℂ)
    (h₁ : u.val*u.val*C₁+u.val*C₁*u.val+C₁*u.val*u.val = K)
    (h₂ : u.val*u.val*C₂+u.val*C₂*u.val+C₂*u.val*u.val =
      -(u.val*C₁*C₁+C₁*u.val*C₁+C₁*C₁*u.val))
    (h₃ : u.val*u.val*C₃+u.val*C₃*u.val+C₃*u.val*u.val =
      -(u.val*C₁*C₂+u.val*C₂*C₁+C₁*u.val*C₂+C₂*u.val*C₁+C₁*C₂*u.val+C₂*C₁*u.val+
        C₁*C₁*C₁)) :
    let D : Matrix n n ℂ := u.inv
    let B₁ := D*(u.val*C₁+C₁*u.val)*D
    let B₂ := D*(u.val*C₂+C₁*C₁+C₂*u.val)*D
    let B₃ := D*(u.val*C₃+C₁*C₂+C₂*C₁+C₃*u.val)*D
    tr B₂ - tr (B₁*B₁)/2 = -tr ((K*D^3)^2)/3 ∧
    tr B₃ - tr (B₁*B₂) + tr (B₁*B₁*B₁)/3 = 2*tr ((K*D^3)^3)/9 := by
  let a := rootJet u C₁ C₂ C₃
  let b := (a.conj u⁻¹).mul a
  let t := (a.mul (a.conj u)).mul (a.conj (u^2))
  have ht := rootJet_cubic u C₁ C₂ C₃
  change t.first = _ ∧ t.second = _ ∧ t.third = _ at ht
  have ht₁ : t.first = K*u.inv^3 := by rw [ht.1, h₁]
  have ht₂ : t.second = 0 := by
    rw [ht.2.1]
    have h : u.val*u.val*C₂+u.val*C₂*u.val+C₂*u.val*u.val+
        u.val*C₁*C₁+C₁*u.val*C₁+C₁*C₁*u.val = 0 := by rw [h₂]; abel
    rw [h, zero_mul]
  have ht₃ : t.third = 0 := by
    rw [ht.2.2]
    have h : u.val*u.val*C₃+u.val*C₃*u.val+C₃*u.val*u.val+
        u.val*C₁*C₂+u.val*C₂*C₁+C₁*u.val*C₂+C₂*u.val*C₁+C₁*C₂*u.val+C₂*C₁*u.val+
        C₁*C₁*C₁ = 0 := by rw [h₃]; abel
    rw [h, zero_mul]
  have hlt₂ : t.log2 = 3*a.log2 := by
    dsimp only [t]
    rw [Jet.log2_mul, Jet.log2_mul, Jet.log2_conj, Jet.log2_conj]
    ring
  have hlt₃ : t.log3 = 3*a.log3 := by
    dsimp only [t]
    rw [Jet.log3_mul, Jet.log3_mul, Jet.log3_conj, Jet.log3_conj]
    ring
  have hlb₂ : b.log2 = 2*a.log2 := by
    dsimp only [b]
    rw [Jet.log2_mul, Jet.log2_conj]
    ring
  have hlb₃ : b.log3 = 2*a.log3 := by
    dsimp only [b]
    rw [Jet.log3_mul, Jet.log3_conj]
    ring
  have hb := rootJet_square u C₁ C₂ C₃
  change b.first = _ ∧ b.second = _ ∧ b.third = _ at hb
  change _ ∧ _
  rw [← hb.1, ← hb.2.1, ← hb.2.2]
  change b.log2 = _ ∧ b.log3 = _
  rw [hlb₂, hlb₃]
  simp only [Jet.log2, Jet.log3, ht₁, ht₂, ht₃, mul_zero, tr,
    Matrix.trace_zero, sub_zero, zero_sub, zero_add, pow_succ, pow_zero, mul_one, one_mul] at hlt₂ hlt₃ ⊢
  constructor
  · linear_combination -(2/3 : ℂ)*hlt₂
  · linear_combination -(2/3 : ℂ)*hlt₃

section Actual
open scoped Matrix.Norms.L2Operator

/-- Trace normalization for the actual factorial derivatives of an arbitrary
positive definite pencil, with no spectral-level restriction. -/
theorem actual_trace_normalization {Y K : Matrix n n ℂ}
    (hY : Y.PosDef) (hK : K.IsHermitian) :
    let P := CFC.rpow Y (1/3 : ℝ)
    let B := RpowPencilTaylor.jetCoeff
      (fun t : ℝ => P⁻¹*CFC.rpow (Y+t • K) (2/3 : ℝ)*P⁻¹)
    let Q := K*(P⁻¹)^3
    Matrix.trace (B 2)-Matrix.trace (B 1*B 1)/2 = -Matrix.trace (Q^2)/3 ∧
      Matrix.trace (B 3)-Matrix.trace (B 1*B 2)+Matrix.trace (B 1*B 1*B 1)/3 = 2*Matrix.trace (Q^3)/9 := by
  let P := CFC.rpow Y (1/3 : ℝ)
  let C := RpowPencilTaylor.jetCoeff
    (fun t : ℝ => CFC.rpow (Y+t • K) (1/3 : ℝ))
  have hP : P.PosDef :=
    (IsStrictlyPositive.rpow Y (1/3 : ℝ) hY.isStrictlyPositive).posDef
  let u := hP.isUnit.unit
  have hu : u.val = P := hP.isUnit.unit_spec
  have hd : P⁻¹ = u.inv := Matrix.inv_eq_right_inv (by rw [← hu]; exact u.val_inv)
  have hc := RpowPencilTaylor.cubeRoot_jet_recurrences hY hK
  change C 0 = P ∧ _ at hc
  have hc₁ := hc.2.1
  have hc₂ := hc.2.2.1
  have hc₃ := hc.2.2.2
  change P*P*C 1+P*C 1*P+C 1*P*P = K at hc₁
  change P*P*C 2+P*C 2*P+C 2*P*P = _ at hc₂
  change P*P*C 3+P*C 3*P+C 3*P*P = _ at hc₃
  have h₁ : u.val*u.val*C 1+u.val*C 1*u.val+C 1*u.val*u.val = K := by
    simpa only [hu] using hc₁
  have h₂ : u.val*u.val*C 2+u.val*C 2*u.val+C 2*u.val*u.val =
      -(u.val*C 1*C 1+C 1*u.val*C 1+C 1*C 1*u.val) := by
    simpa only [hu] using hc₂
  have h₃ : u.val*u.val*C 3+u.val*C 3*u.val+C 3*u.val*u.val =
      -(u.val*C 1*C 2+u.val*C 2*C 1+C 1*u.val*C 2+C 2*u.val*C 1+
        C 1*C 2*u.val+C 2*C 1*u.val+C 1*C 1*C 1) := by
    simpa only [hu] using hc₃
  have ht := trace_normalization_of_recurrences u K (C 1) (C 2) (C 3) h₁ h₂ h₃
  have hj (j : ℕ) (hj : j ≤ 3) :=
    RpowPencilTaylor.normalized_twoThirds_jet hY hK j hj
  have hj₁ := hj 1 (by omega)
  have hj₂ := hj 2 (by omega)
  have hj₃ := hj 3 (by omega)
  change RpowPencilTaylor.jetCoeff _ 1 = P⁻¹*(∑ a ∈ Finset.range (1+1),
    C a*C (1-a))*P⁻¹ at hj₁
  change RpowPencilTaylor.jetCoeff _ 2 = P⁻¹*(∑ a ∈ Finset.range (2+1),
    C a*C (2-a))*P⁻¹ at hj₂
  change RpowPencilTaylor.jetCoeff _ 3 = P⁻¹*(∑ a ∈ Finset.range (3+1),
    C a*C (3-a))*P⁻¹ at hj₃
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd,
    Nat.reduceSub, hc.1, zero_add] at hj₁ hj₂ hj₃
  dsimp only
  rw [hj₁, hj₂, hj₃]
  simpa only [tr, hu, ← hd] using ht

#print axioms actual_trace_normalization
end Actual

end D5.S3.Quantum.Matrix.HsfLocalSpectrumTrace
