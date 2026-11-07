/- GID: D5/S3/Quantum/Matrix/HsfThreeLevelOrdered
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HsfThreeLevelOrdered
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Normed]
   utility: none
   digest: Ordered finite-index transfer and matrix square identities for arbitrary fibers. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Matrix.HsfThreeLevelGram

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Matrix.HsfThreeLevelSupplier

universe u

open private q g psi
  from D5.S3.Quantum.Matrix.HsfThreeLevelPolynomial
open private q_symm Coeff v m dot tau
  beta v_gram mixed_moment cyclic_moment
  from D5.S3.Quantum.Matrix.HsfThreeLevelGram

section OrderedSquares
variable {n : Type u} [Fintype n] [DecidableEq n]
private def realTrace (A : Matrix n n ℂ) : ℝ := A.trace.re
private theorem realTrace_comm (A B : Matrix n n ℂ) :
    realTrace (A*B) = realTrace (B*A) :=
  congrArg Complex.re (Matrix.trace_mul_comm A B)
private theorem realTrace_add (A B : Matrix n n ℂ) :
    realTrace (A+B) = realTrace A+realTrace B := by
  simp [realTrace, Matrix.trace_add]
private theorem realTrace_sub (A B : Matrix n n ℂ) :
    realTrace (A-B) = realTrace A-realTrace B := by
  simp [realTrace, Matrix.trace_sub]
private theorem realTrace_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix n n ℂ) :
    realTrace (∑ i ∈ s, A i) = ∑ i ∈ s, realTrace (A i) := by
  simp [realTrace, Matrix.trace_sum, Complex.re_sum]

/-- An unconditional identity in ordered matrices. M and V need not be
Hermitian. The only Hermitian hypothesis is the prescribed all-Z shift W. -/
private theorem one_ordered_square (S W M V : Matrix n n ℂ) (hW : W.IsHermitian) :
    realTrace ((M-(V*W+V*W))ᴴ*S*(M-(V*W+V*W))) =
      realTrace (Mᴴ*S*M)-2*realTrace ((Vᴴ*S*M+Mᴴ*S*V)*W)+
        4*realTrace ((Vᴴ*S*V)*W*W) := by
  have hexpand : (M-(V*W+V*W))ᴴ*S*(M-(V*W+V*W)) =
      Mᴴ*S*M-(Mᴴ*S*V*W+Mᴴ*S*V*W)-
        (W*Vᴴ*S*M+W*Vᴴ*S*M)+
        (W*Vᴴ*S*V*W+W*Vᴴ*S*V*W+
          W*Vᴴ*S*V*W+W*Vᴴ*S*V*W) := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
      Matrix.conjTranspose_mul, hW.eq]
    noncomm_ring
  rw [hexpand]
  simp only [realTrace_add, realTrace_sub, add_mul]
  have hcross : realTrace (W*Vᴴ*S*M) = realTrace (Vᴴ*S*M*W) := by
    simpa only [mul_assoc] using realTrace_comm W (Vᴴ*S*M)
  have hquad : realTrace (W*Vᴴ*S*V*W) = realTrace (Vᴴ*S*V*W*W) := by
    simpa only [mul_assoc] using realTrace_comm W (Vᴴ*S*V*W)
  rw [hcross, hquad]
  ring

private def rowEnergy {ι : Type*} [Fintype ι]
    (S W : Matrix n n ℂ) (M V : ι → Matrix n n ℂ) : ℝ :=
  ∑ a, realTrace ((M a-(V a*W+V a*W))ᴴ*S*(M a-(V a*W+V a*W)))
private theorem ordered_row_square {ι : Type*} [Fintype ι]
    (S W : Matrix n n ℂ) (M V : ι → Matrix n n ℂ) (hW : W.IsHermitian) :
    rowEnergy S W M V =
      (∑ a, realTrace ((M a)ᴴ*S*M a))-
        2*realTrace ((∑ a, ((V a)ᴴ*S*M a+(M a)ᴴ*S*V a))*W)+
        4*realTrace ((∑ a, (V a)ᴴ*S*V a)*W*W) := by
  unfold rowEnergy
  simp_rw [one_ordered_square S W _ _ hW]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_mul, realTrace_sum]
  simp only [add_mul, realTrace_add, Finset.sum_mul, realTrace_sum,
    Finset.sum_add_distrib]
private theorem rowEnergy_nonneg {ι : Type*} [Fintype ι]
    (S W : Matrix n n ℂ) (M V : ι → Matrix n n ℂ) (hS : S.PosSemidef) :
    0 ≤ rowEnergy S W M V := by
  exact Finset.sum_nonneg fun a _ =>
    (Complex.nonneg_iff.mp
      (hS.conjTranspose_mul_mul_same (M a-(V a*W+V a*W))).trace_nonneg).1

private def liftedV (level : n → Fin 3) (p : Fin 3 → ℝ) (a : Coeff) : Matrix n n ℂ :=
  diagonal (fun i => (v p (level i) a : ℂ))
private def liftedM (level : n → Fin 3) (p : Fin 3 → ℝ)
    (S : Matrix n n ℂ) (a : Coeff) : Matrix n n ℂ :=
  fun i j => (m p (level i) (level j) a : ℂ)*S i j
private def firstMatrix (level : n → Fin 3) (p : Fin 3 → ℝ)
    (S : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j => (HsfLocalSpectrumSupplier.spectralTau (p (level i)) (p (level j)) : ℂ)*S i j
private def qMatrix (level : n → Fin 3) (p : Fin 3 → ℝ)
    (S : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j => ∑ k,
    (((2/3 : ℝ)*HsfLocalSpectrumSupplier.spectralTau (p (level i)) (p (level k))*
      HsfLocalSpectrumSupplier.spectralTau (p (level k)) (p (level j))+
      3*HsfLocalSpectrumSupplier.spectralKernel (p (level i)) (p (level j))
        (p (level k)) : ℝ) : ℂ)*S i k*S k j

private theorem tau_spectral (a b : ℝ) :
    tau a b = HsfLocalSpectrumSupplier.spectralTau a b := by
  unfold tau g q HsfLocalSpectrumSupplier.spectralTau
    HsfLocalSpectrumSupplier.spectralDen
  ring

private theorem sqrt_chain {a b c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Real.sqrt (a*c)*Real.sqrt (c*b) = c*Real.sqrt (a*b) := by
  rw [Real.sqrt_mul ha.le, Real.sqrt_mul hc.le, Real.sqrt_mul ha.le]
  calc
    _ = (Real.sqrt c*Real.sqrt c)*(Real.sqrt a*Real.sqrt b) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hc.le]

/-- The normalized beta is exactly the original ordered Q coefficient. -/
private theorem beta_spectral {a b c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    beta a b c = (2/3 : ℝ)*HsfLocalSpectrumSupplier.spectralTau a c*
      HsfLocalSpectrumSupplier.spectralTau c b+
      3*HsfLocalSpectrumSupplier.spectralKernel a b c := by
  rw [← tau_spectral a c, ← tau_spectral c b]
  have hk : HsfLocalSpectrumSupplier.spectralKernel a b c =
      Real.sqrt (a*b)*c^3*(a*b+c*(a+b))/(q a b*q a c*q b c) := by
    unfold HsfLocalSpectrumSupplier.spectralKernel HsfLocalSpectrumSupplier.spectralDen
    change Real.sqrt (a*b)*c^3*(a*b+c*(a+b))/(q a b*q a c*q c b) = _
    rw [q_symm c b]
  rw [hk]
  calc
    _ = (2/3 : ℝ)*(c*Real.sqrt (a*b))*g a c*g c b+
        3*(Real.sqrt (a*b)*c^3*(a*b+c*(a+b))/(q a b*q a c*q b c)) := by
      unfold beta psi
      ring
    _ = _ := by
      rw [← sqrt_chain ha hc]
      unfold tau
      ring

private theorem liftedV_hermitian (level : n → Fin 3) (p : Fin 3 → ℝ) (a : Coeff) :
    (liftedV level p a)ᴴ = liftedV level p a := by
  simp [liftedV, Matrix.diagonal_conjTranspose]

private theorem liftedM_star (level : n → Fin 3) (p : Fin 3 → ℝ)
    (S : Matrix n n ℂ) (hS : S.IsHermitian) (a : Coeff) (i j : n) :
    (liftedM level p S a)ᴴ i j = (m p (level j) (level i) a : ℂ)*S i j := by
  simp [liftedM, Matrix.conjTranspose_apply, hS.apply i j, mul_comm]

private theorem ordered_first_moment (level : n → Fin 3) (p : Fin 3 → ℝ)
    (hp : ∀ i, 0 < p i) (hinj : Function.Injective p) (S : Matrix n n ℂ) :
    (∑ a, (liftedV level p a)ᴴ*S*liftedV level p a) = firstMatrix level p S := by
  ext i j
  calc
    _ = ∑ a, ((v p (level i) a*v p (level j) a : ℝ) : ℂ)*S i j := by
      simp only [Matrix.sum_apply]
      apply Finset.sum_congr rfl
      intro a _
      rw [liftedV_hermitian]
      change (diagonal (fun t => (v p (level t) a : ℂ))*S*
        diagonal (fun t => (v p (level t) a : ℂ))) i j = _
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      push_cast
      ring
    _ = (dot (v p (level i)) (v p (level j)) : ℂ)*S i j := by
      unfold dot
      push_cast
      rw [Finset.sum_mul]
    _ = _ := by
      change (dot (v p (level i)) (v p (level j)) : ℂ)*S i j =
        (HsfLocalSpectrumSupplier.spectralTau (p (level i)) (p (level j)) : ℂ)*S i j
      rw [v_gram p hp hinj, tau_spectral]

private theorem lifted_cross_entry (level : n → Fin 3) (p : Fin 3 → ℝ)
    (S : Matrix n n ℂ) (hS : S.IsHermitian) (a : Coeff) (i j : n) :
    ((liftedV level p a)ᴴ*S*liftedM level p S a+
      (liftedM level p S a)ᴴ*S*liftedV level p a) i j =
      ∑ k, ((v p (level i) a*m p (level k) (level j) a+
        m p (level k) (level i) a*v p (level j) a : ℝ) : ℂ)*S i k*S k j := by
  have hleft : ((liftedV level p a)ᴴ*S*liftedM level p S a) i j =
      ∑ k, (v p (level i) a : ℂ)*S i k*
        ((m p (level k) (level j) a : ℂ)*S k j) := by
    rw [liftedV_hermitian]
    change (diagonal (fun t => (v p (level t) a : ℂ))*S*liftedM level p S a) i j = _
    rw [Matrix.mul_apply]
    simp only [Matrix.diagonal_mul, liftedM]
  have hright : ((liftedM level p S a)ᴴ*S*liftedV level p a) i j =
      ∑ k, ((m p (level k) (level i) a : ℂ)*S i k)*S k j*
        (v p (level j) a : ℂ) := by
    change ((liftedM level p S a)ᴴ*S*
      diagonal (fun t => (v p (level t) a : ℂ))) i j = _
    rw [Matrix.mul_diagonal, Matrix.mul_apply, Finset.sum_mul]
    simp only [liftedM_star level p S hS]
  change ((liftedV level p a)ᴴ*S*liftedM level p S a) i j+
    ((liftedM level p S a)ᴴ*S*liftedV level p a) i j = _
  rw [hleft, hright, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  ring

private theorem ordered_mixed_moment (level : n → Fin 3) (p : Fin 3 → ℝ)
    (hp : ∀ i, 0 < p i) (hinj : Function.Injective p)
    (S : Matrix n n ℂ) (hS : S.IsHermitian) :
    (∑ a, ((liftedV level p a)ᴴ*S*liftedM level p S a+
      (liftedM level p S a)ᴴ*S*liftedV level p a)) =
      (2 : ℝ) • qMatrix level p S := by
  ext i j
  calc
    _ = ∑ k, ((dot (v p (level i)) (m p (level k) (level j))+
        dot (m p (level k) (level i)) (v p (level j)) : ℝ) : ℂ)*S i k*S k j := by
      simp only [Matrix.sum_apply, lifted_cross_entry level p S hS]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 1
      unfold dot
      push_cast
      rw [Finset.sum_add_distrib]
    _ = ∑ k, ((2*beta (p (level i)) (p (level j)) (p (level k)) : ℝ) : ℂ)*
        S i k*S k j := by
      apply Finset.sum_congr rfl
      intro k _
      have hc : dot (v p (level i)) (m p (level k) (level j))+
          dot (m p (level k) (level i)) (v p (level j)) =
          2*beta (p (level i)) (p (level j)) (p (level k)) := by
        linarith only [mixed_moment p hp hinj (level i) (level j) (level k)]
      rw [hc]
    _ = _ := by
      simp only [qMatrix, Matrix.smul_apply, Complex.real_smul]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [beta_spectral (hp (level i)) (hp (level k))]
      push_cast
      ring

/-- Ordered scalar entry triangles. The two orientations are separate
summands throughout; no entrywise or real-triangle positivity is used. -/
private def triangle (S : Matrix n n ℂ) (i j k : n) : ℂ := S i j*S j k*S k i
private def sum3 (f : n → n → n → ℂ) : ℂ := ∑ i, ∑ j, ∑ k, f i j k

private theorem sum3_congr {f g : n → n → n → ℂ}
    (h : ∀ i j k, f i j k = g i j k) : sum3 f = sum3 g := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  exact h i j k

private theorem sum3_add (f g : n → n → n → ℂ) :
    sum3 (fun i j k => f i j k+g i j k) = sum3 f+sum3 g := by
  simp only [sum3, Finset.sum_add_distrib]

private theorem sum3_sub (f g : n → n → n → ℂ) :
    sum3 (fun i j k => f i j k-g i j k) = sum3 f-sum3 g := by
  simp only [sum3, Finset.sum_sub_distrib]

private theorem sum3_scale (r : ℂ) (f : n → n → n → ℂ) :
    sum3 (fun i j k => r*f i j k) = r*sum3 f := by
  simp only [sum3, Finset.mul_sum]

private theorem sum3_rotate (f : n → n → n → ℂ) :
    sum3 f = sum3 (fun i j k => f j k i) := by
  unfold sum3
  calc
    _ = ∑ i, ∑ k, ∑ j, f i j k := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, f i j k := by rw [Finset.sum_comm]
    _ = _ := rfl

private theorem sum3_sum {ι : Type*} [Fintype ι] (f : ι → n → n → n → ℂ) :
    (∑ a, sum3 (f a)) = sum3 (fun i j k => ∑ a, f a i j k) := by
  unfold sum3
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]

private theorem triangle_rotate (S : Matrix n n ℂ) (i j k : n) :
    triangle S j k i = triangle S i j k := by unfold triangle; ring

private theorem weighted_triangle_rotate (S : Matrix n n ℂ) (f : n → n → n → ℝ) :
    sum3 (fun i j k => (f i j k : ℂ)*triangle S i j k) =
      sum3 (fun i j k => (f j k i : ℂ)*triangle S i j k) := by
  rw [sum3_rotate]
  apply sum3_congr
  intro i j k
  rw [triangle_rotate]

private theorem trace_cube_entries (A : Matrix n n ℂ) :
    (A^3).trace = sum3 (triangle A) := by
  rw [show A^3 = A*A*A by noncomm_ring]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Finset.sum_mul, sum3]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  rfl

private theorem lifted_cubic_trace_entries (level : n → Fin 3) (p : Fin 3 → ℝ)
    (S : Matrix n n ℂ) (hS : S.IsHermitian) :
    (∑ a, ((liftedM level p S a)ᴴ*S*liftedM level p S a).trace) =
      sum3 (fun i j k =>
        (dot (m p (level j) (level i)) (m p (level k) (level i)) : ℂ)*
          triangle S i j k) := by
  have ha (a : Coeff) : ((liftedM level p S a)ᴴ*S*liftedM level p S a).trace =
      sum3 (fun i j k => ((m p (level j) (level i) a*
        m p (level k) (level i) a : ℝ) : ℂ)*triangle S i j k) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Finset.sum_mul, sum3]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [liftedM_star level p S hS]
    dsimp only [liftedM, triangle]
    push_cast
    ring
  simp_rw [ha]
  rw [sum3_sum]
  apply sum3_congr
  intro i j k
  rw [← Finset.sum_mul]
  congr 1
  unfold dot
  push_cast
  rfl

private theorem firstMatrix_cube_entries (level : n → Fin 3) (p : Fin 3 → ℝ)
    (S : Matrix n n ℂ) :
    ((firstMatrix level p S)^3).trace = sum3 (fun i j k =>
      ((tau (p (level i)) (p (level j))*tau (p (level j)) (p (level k))*
        tau (p (level k)) (p (level i)) : ℝ) : ℂ)*triangle S i j k) := by
  rw [trace_cube_entries]
  apply sum3_congr
  intro i j k
  dsimp only [triangle, firstMatrix]
  simp only [tau_spectral]
  push_cast
  ring

private theorem ordered_cubic_moment (level : n → Fin 3) (p : Fin 3 → ℝ)
    (hp : ∀ i, 0 < p i) (hinj : Function.Injective p)
    (S : Matrix n n ℂ) (hS : S.IsHermitian) :
    (∑ a, realTrace ((liftedM level p S a)ᴴ*S*liftedM level p S a)) =
      (4*realTrace (S^3)-realTrace ((firstMatrix level p S)^3))/3 := by
  let A : n → n → n → ℝ := fun i j k =>
    dot (m p (level j) (level i)) (m p (level k) (level i))
  let L : ℂ := sum3 (fun i j k => (A i j k : ℂ)*triangle S i j k)
  have hrot1 : L = sum3 (fun i j k => (A j k i : ℂ)*triangle S i j k) :=
    weighted_triangle_rotate S A
  have hrot2 : L = sum3 (fun i j k => (A k i j : ℂ)*triangle S i j k) := by
    rw [hrot1]
    exact weighted_triangle_rotate S (fun i j k => A j k i)
  have hthree : sum3 (fun i j k =>
      ((A i j k : ℂ)+(A j k i : ℂ)+(A k i j : ℂ))*triangle S i j k) = 3*L := by
    simp only [add_mul, sum3_add]
    rw [← hrot1, ← hrot2]
    change L+L+L = 3*L
    ring
  have hcoeff : sum3 (fun i j k =>
      ((A i j k : ℂ)+(A j k i : ℂ)+(A k i j : ℂ))*triangle S i j k) =
      4*(S^3).trace-((firstMatrix level p S)^3).trace := by
    rw [trace_cube_entries, firstMatrix_cube_entries]
    calc
      _ = sum3 (fun i j k =>
          (4-((tau (p (level i)) (p (level j))*tau (p (level j)) (p (level k))*
            tau (p (level k)) (p (level i)) : ℝ) : ℂ))*triangle S i j k) := by
        apply sum3_congr
        intro i j k
        have hc := congrArg (fun r : ℝ => (r : ℂ))
          (cyclic_moment p hp hinj (level i) (level j) (level k))
        change ((A i j k : ℂ)+(A j k i : ℂ)+(A k i j : ℂ))*triangle S i j k = _
        push_cast at hc ⊢
        exact congrArg (fun z : ℂ => z*triangle S i j k) hc
      _ = _ := by simp only [sub_mul, sum3_sub, sum3_scale]
  have hcomplex : (3 : ℂ)*(∑ a,
      ((liftedM level p S a)ᴴ*S*liftedM level p S a).trace) =
      4*(S^3).trace-((firstMatrix level p S)^3).trace := by
    rw [lifted_cubic_trace_entries level p S hS]
    change 3*L = _
    exact hthree.symm.trans hcoeff
  have hreal : 3*(∑ a, realTrace ((liftedM level p S a)ᴴ*S*liftedM level p S a)) =
      4*realTrace (S^3)-realTrace ((firstMatrix level p S)^3) := by
    have hr := congrArg Complex.re hcomplex
    simpa [realTrace, Complex.mul_re, Complex.re_sum] using hr
  linarith only [hreal]

/-- Proposed actual-jet bridge consumes the owner's coordinate proofs.
It has no assumed jet, recurrence, or spectral formula in its telescope. -/
private theorem actual_shifted_identity (p : n → ℝ) (hp : ∀ i, 0 < p i)
    (S Z : Matrix n n ℂ) (hS : S.IsHermitian) :
    let P : Matrix n n ℂ := diagonal (fun i => (p i : ℂ))
    let F := fun t : ℝ => P⁻¹*CFC.rpow (P^3+t •
      (CFC.rpow P (3/2 : ℝ)*S*CFC.rpow P (3/2 : ℝ))) (2/3 : ℝ)*P⁻¹
    let B := fun j : ℕ => (j.factorial : ℝ)⁻¹ • iteratedDeriv j F 0
    let X : Matrix n n ℂ := fun i j =>
      (HsfLocalSpectrumSupplier.spectralTau (p i) (p j) : ℂ)*S i j
    let Q : Matrix n n ℂ := fun i j => ∑ k,
      (((2/3 : ℝ)*HsfLocalSpectrumSupplier.spectralTau (p i) (p k)*
        HsfLocalSpectrumSupplier.spectralTau (p k) (p j)+
        3*HsfLocalSpectrumSupplier.spectralKernel (p i) (p j) (p k) : ℝ) : ℂ)*S i k*S k j
    let W := Z+(1/3 : ℝ) • X
    6*(B 3+(2 : ℝ) • (Z*B 2)+B 1*Z^2-(5/48 : ℝ) • (B 1)^3).trace.re =
      (4*(S^3).trace.re-(X^3).trace.re)/3-
        4*(Q*W).trace.re+4*(X*W*W).trace.re := by
  exact HsfLocalSpectrumSupplier.actual_shifted_supplier_identity p hp S Z hS

end OrderedSquares

end D5.S3.Quantum.Matrix.HsfThreeLevelSupplier
