/- GID: D5/S3/Analytic/Spectral/FillmanLimPositiveSemigroup
   generality: G
   mirror-B: D5/B/S3/Analytic/Spectral/FillmanLimPositiveSemigroup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A hyperbolic relative matrix forces a hyperbolic positive product. -/

/-
admission_basis: escape-witness
escape_witness: positiveRelativeCriterion
Four-slot escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/30475
Direct frozen dependencies (declaration identities):
F1: D5/S0/Observation/MatrixTracePowerSum.pow_add_two @ sha256:477f52a1cada3768c6c6695f7bf1e92216cc53ac6f22ad3f67270f1f31f452be
F2: D5/S0/Observation/MatrixTracePowerSum.trace_pow_add_two @ sha256:c3a059dba6dacff2daf43a6483f3e2bb7036930561a43d038fdbb8225d03adff
Per-declaration classification; definitions specify objects rather than theorem assertions.
Consumed bind-only helpers organize proofs and supply no independent escape witness.
cayley_two: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: F1; consumers: elliptic_complex_structure,unipotent_square_zero
circle_rep_continuous: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: circle_rep_inverse_closure
circle_rep_inverse_closure: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: elliptic_adjugate_in_closure
elliptic_complex_structure: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: F1; consumers: elliptic_adjugate_in_closure
elliptic_adjugate_in_closure: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: F1; consumers: elliptic_positive_product
trace_relative: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: boundary_positive_product,elliptic_positive_product,positiveRelativeCriterion,unipotent_positive_product
elliptic_positive_product: proof_shape: content; escape_witness: none; Direct frozen dependencies: F1; consumers: positiveRelativeCriterion
unipotent_square_zero: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: F1; consumers: unipotent_power
unipotent_power: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: F1; consumers: unipotent_trace_power
unipotent_trace_power: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: F1; consumers: unipotent_positive_product
unipotent_positive_product: proof_shape: content; escape_witness: none; Direct frozen dependencies: F1; consumers: boundary_positive_product
boundary_sign: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: boundary_positive_product
boundary_positive_product: proof_shape: content; escape_witness: none; Direct frozen dependencies: F1; consumers: positiveRelativeCriterion
positiveRelativeCriterion: proof_shape: content; escape_witness: positiveRelativeCriterion; Direct frozen dependencies: F1; consumers: gap_rich_components
positive_trace_power: proof_shape: content; escape_witness: none; Direct frozen dependencies: F2; consumers: hyperbolicTracePower
hyperbolicTracePower: proof_shape: content; escape_witness: none; Direct frozen dependencies: F2; consumers: gap_rich_components
utility: none; the payload uses infinite alphabets, arbitrary positive word lengths,
and an unrestricted positive-semigroup criterion, rather than a finite checker.
-/

import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Instances.Matrix
import D5.S0.Observation.MatrixTracePowerSum

namespace D5.S3.Analytic.Spectral.FillmanLimPositiveSemigroup

noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
open Set
open scoped Topology Pointwise

private theorem cayley_two (A : (Matrix (Fin 2) (Fin 2) ℝ)) :
    A^2 - Matrix.trace A • A + Matrix.det A • (1 : (Matrix (Fin 2) (Fin 2) ℝ)) = 0 := by
  have h : A^2 = Matrix.trace A • A - Matrix.det A • (1 : (Matrix (Fin 2) (Fin 2) ℝ)) := by
    simpa using D5.S0.Observation.MatrixTracePowerSum.pow_add_two A 0
  rw [h]
  module

private theorem circle_rep_continuous (J : (Matrix (Fin 2) (Fin 2) ℝ)) (hJ : J * J = -1) :
    Continuous (fun z : Circle => Complex.liftAux J hJ (z : ℂ)) := by
  simp only [Complex.liftAux_apply, Algebra.algebraMap_eq_smul_one]
  change Continuous (fun z : Circle => (z : ℂ).re • (1 : (Matrix (Fin 2) (Fin 2) ℝ)) + (z : ℂ).im • J)
  fun_prop

private theorem circle_rep_inverse_closure (J : (Matrix (Fin 2) (Fin 2) ℝ)) (hJ : J * J = -1) (z : Circle) :
    Complex.liftAux J hJ ((z⁻¹ : Circle) : ℂ) ∈ closure (range fun n : ℕ => (Complex.liftAux J hJ (z : ℂ))^n) := by
  have hz : z⁻¹ ∈ closure (range fun n : ℕ => z^n) := by
    rw [← closure_range_zpow_eq_pow]
    exact subset_closure ⟨(-1 : ℤ), by simp⟩
  have hm := mem_closure_image (circle_rep_continuous J hJ).continuousAt hz
  simpa only [← Set.range_comp, Function.comp_def, Circle.coe_pow, map_pow] using hm

private theorem elliptic_complex_structure (A : (Matrix (Fin 2) (Fin 2) ℝ)) (hd : Matrix.det A = 1)
    (ht : |Matrix.trace A| < 2) :
    ∃ (J : (Matrix (Fin 2) (Fin 2) ℝ)) (hJ : J * J = -1) (z : Circle),
      Complex.liftAux J hJ (z : ℂ) = A ∧ Complex.liftAux J hJ ((z⁻¹ : Circle) : ℂ) = Matrix.adjugate A := by
  let a : ℝ := Matrix.trace A / 2
  let b : ℝ := Real.sqrt (1-a^2)
  have ha : -1 < a ∧ a < 1 := by
    rcases abs_lt.mp ht with ⟨h₁,h₂⟩
    dsimp [a]
    constructor <;> linarith
  have hb0 : 0 < 1-a^2 := by nlinarith [ha.1,ha.2]
  have hb : 0 < b := Real.sqrt_pos.mpr hb0
  have hbsq : b^2 = 1-a^2 := Real.sq_sqrt (le_of_lt hb0)
  let J : (Matrix (Fin 2) (Fin 2) ℝ) := b⁻¹ • (A-a • (1 : (Matrix (Fin 2) (Fin 2) ℝ)))
  have hJ : J * J = -1 := by
    have hc := cayley_two A
    rw [hd] at hc
    have hc' : A*A - (2*a) • A + (1 : (Matrix (Fin 2) (Fin 2) ℝ)) = 0 := by
      convert hc using 1 <;> simp [a, pow_two] <;> ring
    have heq : (A-a • (1 : (Matrix (Fin 2) (Fin 2) ℝ))) * (A-a • (1 : (Matrix (Fin 2) (Fin 2) ℝ))) = -(b^2) • (1 : (Matrix (Fin 2) (Fin 2) ℝ)) := by
      calc
        _ = (A*A - (2*a) • A + 1) + (a*a-1) • (1 : (Matrix (Fin 2) (Fin 2) ℝ)) := by
          simp only [sub_mul, mul_sub, mul_smul_comm, smul_mul_assoc, one_mul, mul_one]
          module
        _ = (a*a-1) • (1 : (Matrix (Fin 2) (Fin 2) ℝ)) := by rw [hc',zero_add]
        _ = -(b^2) • (1 : (Matrix (Fin 2) (Fin 2) ℝ)) := by rw [hbsq]; congr 1 <;> ring
    dsimp [J]
    rw [smul_mul_assoc, mul_smul_comm, heq, smul_smul, smul_smul]
    have hcoeff : b⁻¹ * b⁻¹ * -(b^2) = -1 := by field_simp
    rw [hcoeff, neg_one_smul]
  let z : Circle := ⟨⟨a,b⟩, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, one_pow]
    nlinarith [hbsq]⟩
  refine ⟨J,hJ,z,?_,?_⟩
  all_goals simp only [Complex.liftAux_apply, Algebra.algebraMap_eq_smul_one]
  · change a • (1 : (Matrix (Fin 2) (Fin 2) ℝ)) + b • (b⁻¹ • (A-a • (1 : (Matrix (Fin 2) (Fin 2) ℝ)))) = A
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hb), one_smul]
    module
  · change ((z⁻¹ : Circle) : ℂ).re • (1 : (Matrix (Fin 2) (Fin 2) ℝ)) +
        ((z⁻¹ : Circle) : ℂ).im • J = Matrix.adjugate A
    rw [Circle.coe_inv_eq_conj]
    change a • (1 : (Matrix (Fin 2) (Fin 2) ℝ)) + (-b) • (b⁻¹ • (A-a • (1 : (Matrix (Fin 2) (Fin 2) ℝ)))) = Matrix.adjugate A
    rw [smul_smul, neg_mul, mul_inv_cancel₀ (ne_of_gt hb), neg_one_smul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [a, Matrix.trace_fin_two, Matrix.adjugate_fin_two] <;> ring

private theorem elliptic_adjugate_in_closure (A : (Matrix (Fin 2) (Fin 2) ℝ)) (hd : Matrix.det A = 1)
    (ht : |Matrix.trace A| < 2) :
    Matrix.adjugate A ∈ closure (range fun n : ℕ => A^n) := by
  obtain ⟨J,hJ,z,hA,hInv⟩ := elliptic_complex_structure A hd ht
  simpa only [hA,hInv] using circle_rep_inverse_closure J hJ z

private theorem trace_relative (A B : (Matrix (Fin 2) (Fin 2) ℝ)) :
    Matrix.trace (A * Matrix.adjugate B) =
      Matrix.trace A * Matrix.trace B - Matrix.trace (A*B) := by
  simp [Matrix.trace_fin_two, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem elliptic_positive_product (A B : (Matrix (Fin 2) (Fin 2) ℝ)) (hd : Matrix.det A = 1)
    (ht : |Matrix.trace A| < 2)
    (hrel : 2 < |Matrix.trace (A * Matrix.adjugate B)|) :
    ∃ n : ℕ, 2 < |Matrix.trace (B * A^n)| := by
  by_contra hn
  have hb (n : ℕ) : |Matrix.trace (B * A^n)| ≤ 2 :=
    le_of_not_gt (fun h => hn ⟨n,h⟩)
  have hc : IsClosed {C : (Matrix (Fin 2) (Fin 2) ℝ) | |Matrix.trace (B*C)| ≤ 2} := by
    apply isClosed_le _ continuous_const
    simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    fun_prop
  have hrange : Set.range (fun n : ℕ => A^n) ⊆ {C : (Matrix (Fin 2) (Fin 2) ℝ) | |Matrix.trace (B*C)| ≤ 2} :=
    by rintro C ⟨n,rfl⟩; exact hb n
  have hInv := (closure_minimal hrange hc) (elliptic_adjugate_in_closure A hd ht)
  change |Matrix.trace (B * Matrix.adjugate A)| ≤ 2 at hInv
  have heq : Matrix.trace (B * Matrix.adjugate A) =
      Matrix.trace (A * Matrix.adjugate B) := by
    rw [trace_relative, trace_relative, Matrix.trace_mul_comm A B]
    ring
  rw [heq] at hInv
  exact (not_lt_of_ge hInv) hrel

private theorem unipotent_square_zero (A : (Matrix (Fin 2) (Fin 2) ℝ)) (hd : Matrix.det A = 1)
    (ht : Matrix.trace A = 2) : (A-1)*(A-1)=0 := by
  have h := cayley_two A
  rw [hd,ht] at h
  calc
    (A-1)*(A-1) = A^2 - (2 : ℝ) • A + (1 : ℝ) • (1 : (Matrix (Fin 2) (Fin 2) ℝ)) := by
      simp only [pow_two, two_smul, one_smul]
      noncomm_ring
    _ = 0 := h

private theorem unipotent_power (A : (Matrix (Fin 2) (Fin 2) ℝ)) (hd : Matrix.det A = 1)
    (ht : Matrix.trace A = 2) (n : ℕ) : A^n = 1 + (n : ℝ) • (A-1) := by
  have hs := unipotent_square_zero A hd ht
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    have ha : A = 1+(A-1) := by exact Eq.symm (add_sub_cancel 1 A)
    calc
      (1+(n : ℝ) • (A-1))*A =
        1 + ((n : ℝ)+1) • (A-1) + (n : ℝ) • ((A-1)*(A-1)) := by
          conv_lhs => rhs; rw [ha]
          simp only [add_mul,mul_add,one_mul,mul_one,smul_mul_assoc]
          module
      _ = 1 + ((n+1 : ℕ) : ℝ) • (A-1) := by rw [hs]; simp

private theorem unipotent_trace_power (A B : (Matrix (Fin 2) (Fin 2) ℝ)) (hd : Matrix.det A = 1)
    (ht : Matrix.trace A = 2) (htB : Matrix.trace B = 2) (n : ℕ) :
    Matrix.trace (A^n*B) = 2+(n : ℝ)*(Matrix.trace (A*B)-2) := by
  rw [unipotent_power A hd ht,add_mul,one_mul,smul_mul_assoc,sub_mul,one_mul,
    Matrix.trace_add,Matrix.trace_smul,Matrix.trace_sub,htB]
  rfl

private theorem unipotent_positive_product (A B : (Matrix (Fin 2) (Fin 2) ℝ)) (hd : Matrix.det A = 1)
    (ht : Matrix.trace A = 2) (htB : Matrix.trace B = 2)
    (hrel : 2 < |Matrix.trace (A * Matrix.adjugate B)|) :
    ∃ n : ℕ, 2 < |Matrix.trace (A^n * B)| := by
  have hc : Matrix.trace (A*B)-2 ≠ 0 := by
    intro hc
    rw [trace_relative,ht,htB] at hrel
    have hAB : Matrix.trace (A*B) = 2 := by linarith
    norm_num [hAB] at hrel
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · obtain ⟨n,hn⟩ := exists_nat_gt (4 / -(Matrix.trace (A*B)-2))
    have hg : 4 < (n : ℝ)* -(Matrix.trace (A*B)-2) :=
      (div_lt_iff₀ (neg_pos.mpr hneg)).mp hn
    refine ⟨n,?_⟩
    rw [unipotent_trace_power A B hd ht htB]
    apply lt_of_lt_of_le _ (neg_le_abs _)
    linarith
  · refine ⟨1,?_⟩
    simp only [pow_one]
    exact lt_of_lt_of_le (by linarith) (le_abs_self _)

private theorem boundary_sign (A : (Matrix (Fin 2) (Fin 2) ℝ)) (hd : Matrix.det A = 1)
    (ht : |Matrix.trace A| = 2) :
    ∃ s : ℝ, |s|=1 ∧ Matrix.trace (s • A)=2 ∧ Matrix.det (s • A)=1 := by
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 2)).mp ht with h | h
  · exact ⟨1,by norm_num,by simpa using h,by simpa using hd⟩
  · refine ⟨-1,by norm_num,?_,?_⟩
    · simp [Matrix.trace_smul,h]
    · simp [neg_one_smul,Matrix.det_neg,hd]

private theorem boundary_positive_product (A B : (Matrix (Fin 2) (Fin 2) ℝ)) (hdA : Matrix.det A = 1)
    (hdB : Matrix.det B = 1) (htA : |Matrix.trace A|=2) (htB : |Matrix.trace B|=2)
    (hrel : 2 < |Matrix.trace (A*Matrix.adjugate B)|) :
    ∃ n : ℕ, 2 < |Matrix.trace (A^n*B)| := by
  obtain ⟨s,hs,hsT,hsD⟩ := boundary_sign A hdA htA
  obtain ⟨t,ht,htT,htD⟩ := boundary_sign B hdB htB
  have hr : 2 < |Matrix.trace ((s • A)*Matrix.adjugate (t • B))| := by
    have heq : Matrix.trace ((s • A)*Matrix.adjugate (t • B)) =
        s*t*Matrix.trace (A*Matrix.adjugate B) := by
      rw [trace_relative,trace_relative]
      simp only [smul_mul_assoc,mul_smul_comm,smul_smul,Matrix.trace_smul]
      ring
    simpa only [heq,abs_mul,hs,ht,one_mul] using hrel
  obtain ⟨n,hn⟩ := unipotent_positive_product (s • A) (t • B) hsD hsT htT hr
  refine ⟨n,?_⟩
  simpa only [smul_pow,smul_mul_assoc,mul_smul_comm,smul_smul,
    Matrix.trace_smul,smul_eq_mul,abs_mul,abs_pow,hs,ht,one_pow,one_mul] using hn

theorem positiveRelativeCriterion (A B : (Matrix (Fin 2) (Fin 2) ℝ))
    (hdA : Matrix.det A=1) (hdB : Matrix.det B=1)
    (hrel : 2 < |Matrix.trace (A*Matrix.adjugate B)|) :
    ∃ C ∈ Submonoid.closure ({A,B} : Set (Matrix (Fin 2) (Fin 2) ℝ)), 2 < |Matrix.trace C| := by
  have ha : A ∈ Submonoid.closure ({A,B} : Set (Matrix (Fin 2) (Fin 2) ℝ)) := Submonoid.subset_closure (by simp)
  have hb : B ∈ Submonoid.closure ({A,B} : Set (Matrix (Fin 2) (Fin 2) ℝ)) := Submonoid.subset_closure (by simp)
  by_cases htA : 2 < |Matrix.trace A|
  · exact ⟨A,ha,htA⟩
  by_cases htB : 2 < |Matrix.trace B|
  · exact ⟨B,hb,htB⟩
  rcases lt_or_eq_of_le (le_of_not_gt htA) with hA | hA
  · obtain ⟨n,hn⟩ := elliptic_positive_product A B hdA hA hrel
    exact ⟨B*A^n,mul_mem hb (pow_mem ha n),hn⟩
  rcases lt_or_eq_of_le (le_of_not_gt htB) with hB | hB
  · have hr : 2 < |Matrix.trace (B*Matrix.adjugate A)| := by
      convert hrel using 2
      rw [trace_relative,trace_relative,Matrix.trace_mul_comm A B]
      ring
    obtain ⟨n,hn⟩ := elliptic_positive_product B A hdB hB hr
    exact ⟨A*B^n,mul_mem ha (pow_mem hb n),hn⟩
  · obtain ⟨n,hn⟩ := boundary_positive_product A B hdA hdB hA hB hrel
    exact ⟨A^n*B,mul_mem (pow_mem ha n) hb,hn⟩

private theorem positive_trace_power (A : (Matrix (Fin 2) (Fin 2) ℝ)) (hd : Matrix.det A=1)
    (ht : 2 < Matrix.trace A) :
    ∀ n : ℕ, 2 < Matrix.trace (A^(n+1)) := by
  have hrec (n : ℕ) : Matrix.trace (A^(n+2)) =
      Matrix.trace A * Matrix.trace (A^(n+1)) - Matrix.trace (A^n) := by
    simpa [hd] using D5.S0.Observation.MatrixTracePowerSum.trace_pow_add_two A n
  have hinc : ∀ n : ℕ,
      2 ≤ Matrix.trace (A^n) ∧ Matrix.trace (A^n) < Matrix.trace (A^(n+1)) := by
    intro n
    induction n with
    | zero => simpa [Matrix.trace_fin_two] using And.intro (le_refl (2 : ℝ)) ht
    | succ n ih =>
      have hpos : 0 < Matrix.trace (A^(n+1)) := lt_of_lt_of_le (by norm_num) (le_trans ih.1 ih.2.le)
      have hprod := mul_lt_mul_of_pos_right ht hpos
      refine ⟨le_trans ih.1 ih.2.le,?_⟩
      rw [show n+1+1=n+2 by omega,hrec]
      linarith [ih.2]
  intro n
  exact lt_of_le_of_lt (hinc n).1 (hinc n).2

theorem hyperbolicTracePower (A : (Matrix (Fin 2) (Fin 2) ℝ)) (hd : Matrix.det A=1)
    (ht : 2 < |Matrix.trace A|) (n : ℕ) (hn : 0 < n) :
    2 < |Matrix.trace (A^n)| := by
  rcases lt_abs.mp ht with hpos | hneg
  · obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    exact lt_of_lt_of_le (positive_trace_power A hd hpos m) (le_abs_self _)
  · have hdneg : Matrix.det (-A)=1 := by simpa [Matrix.det_neg] using hd
    have htneg : 2 < Matrix.trace (-A) := by simp only [Matrix.trace_neg]; linarith
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    have hh := lt_of_lt_of_le (positive_trace_power (-A) hdneg htneg m) (le_abs_self _)
    simpa only [← neg_one_smul ℝ A,smul_pow,Matrix.trace_smul,smul_eq_mul,
      abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul] using hh

end
end D5.S3.Analytic.Spectral.FillmanLimPositiveSemigroup
