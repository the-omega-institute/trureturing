/- GID: D5/S3/Quantum/Matrix/HsfThreeLevelSupplier
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HsfThreeLevelSupplier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Normed]
   utility: none
   digest: Actual three-level CFC positivity and positive-definite Sylvester rigidity. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Matrix.HsfThreeLevelOrdered
import D5.S3.Quantum.Matrix.HsfThreeLevelCoincident

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

open private q left right third column_indices residualE
  residualY
  from D5.S3.Quantum.Matrix.HsfThreeLevelPolynomial
open private residualE_pos canonical_residual_blocks residualFirst residualSecond Coeff v
  m dot tau beta m_diagonal v_gram
  off_column_cases tau_self
  from D5.S3.Quantum.Matrix.HsfThreeLevelGram
open private realTrace realTrace_comm realTrace_add realTrace_sub rowEnergy ordered_row_square
  rowEnergy_nonneg liftedV liftedM firstMatrix qMatrix tau_spectral
  ordered_first_moment ordered_mixed_moment triangle ordered_cubic_moment actual_shifted_identity
  from D5.S3.Quantum.Matrix.HsfThreeLevelOrdered
open private coincidentLevel_proof
  from D5.S3.Quantum.Matrix.HsfThreeLevelCoincident

/-- Exact supplier proposition, retaining the actual CFC factorial derivatives.
`level` need not be surjective and `p` need not be injective. The finite carrier
is arbitrary and may be empty. This is a proposition definition, not a theorem. -/
def ThreeLevelSupplierTarget : Prop :=
  ∀ (n : Type u) [Fintype n] [DecidableEq n]
    (level : n → Fin 3) (p : Fin 3 → ℝ), (∀ i, 0 < p i) →
    ∀ (S : Matrix n n ℂ), S.PosSemidef →
    ∀ (Z : Matrix n n ℂ), Z.IsHermitian →
    let P : Matrix n n ℂ := diagonal (fun i => (p (level i) : ℂ))
    let F := fun t : ℝ => P⁻¹ *
      CFC.rpow (P^3 + t • (CFC.rpow P (3/2 : ℝ) * S *
        CFC.rpow P (3/2 : ℝ))) (2/3 : ℝ) * P⁻¹
    let B := fun j : ℕ => (j.factorial : ℝ)⁻¹ • iteratedDeriv j F 0
    0 ≤ (B 3 + (2 : ℝ) • (Z * B 2) + B 1 * Z^2 -
      (5/48 : ℝ) • (B 1)^3).trace.re

/- Auxiliary propositions keep the exact coefficient and ordered-moment laws. -/



/-- O2. Complete the coefficient Gram laws from the rational formulas and
CFC.sqrt realization, including all 27 triples, not only distinct triples. -/
private def CanonicalGramObligation : Prop :=
  ∀ (p : Fin 3 → ℝ), (∀ i, 0 < p i) → Function.Injective p →
    (∀ i j k, (dot (v p i) (m p k j)+dot (m p k i) (v p j))/2 =
      beta (p i) (p j) (p k)) ∧
    (∀ i j k, dot (m p j i) (m p k i)+dot (m p k j) (m p i j)+
      dot (m p i k) (m p j k) =
        4-tau (p i) (p j)*tau (p j) (p k)*tau (p k) (p i))

/-- O3. Ordered finite-index transfer. No scalar-matrix or real-triangle
restriction occurs; arbitrary fiber sizes, zero fibers, and phases remain. -/
private def OrderedMomentObligation : Prop :=
  ∀ (n : Type u) [Fintype n] [DecidableEq n]
    (level : n → Fin 3) (p : Fin 3 → ℝ),
    (∀ i, 0 < p i) → Function.Injective p →
    ∀ (S : Matrix n n ℂ), S.IsHermitian →
    (∑ a, (liftedV level p a)ᴴ*S*liftedV level p a) = firstMatrix level p S ∧
    (∑ a, ((liftedV level p a)ᴴ*S*liftedM level p S a+
      (liftedM level p S a)ᴴ*S*liftedV level p a)) =
      (2 : ℝ) • qMatrix level p S ∧
    (∑ a, realTrace ((liftedM level p S a)ᴴ*S*liftedM level p S a)) =
      (4*realTrace (S^3)-realTrace ((firstMatrix level p S)^3))/3


private theorem orderedMoment_proof : OrderedMomentObligation.{u} := by
  intro n instFinite instDecEq level p hp hinj S hS
  exact ⟨ordered_first_moment level p hp hinj S,
    ordered_mixed_moment level p hp hinj S hS,
    ordered_cubic_moment level p hp hinj S hS⟩

/-- Exact additional PD statement. This retains the Sylvester operator and
its Hermitian solution, rather than an ordinary matrix inverse surrogate.
No such statement is asserted for singular PSD directions. -/
private def PDSylvesterObligation : Prop :=
  ∀ (n : Type u) [Fintype n] [DecidableEq n]
    (level : n → Fin 3) (p : Fin 3 → ℝ), (∀ i, 0 < p i) →
    ∀ (S : Matrix n n ℂ), S.PosDef →
    let P : Matrix n n ℂ := diagonal (fun i => (p (level i) : ℂ))
    let X := firstMatrix level p S
    let D := qMatrix level p S-X^2
    X.PosDef ∧ ∃ Y : Matrix n n ℂ, Y.IsHermitian ∧ X*Y+Y*X = D ∧
      0 ≤ 4*(S^3-X^3).trace.re-6*(X*D).trace.re-6*(D*Y).trace.re ∧
      ((4*(S^3-X^3).trace.re-6*(X*D).trace.re-6*(D*Y).trace.re = 0) ↔ P*S = S*P)

/- Singular PSD directions receive the supplier statement. The additional
Sylvester energy and rigidity below require a positive-definite direction. -/



/-- Actual at-most-three-positive-level supplier, with the unchanged original
factorial CFC jets, arbitrary finite complex matrices and all Hermitian Z. -/
theorem actual_threeLevel_supplier : ThreeLevelSupplierTarget.{u} := by
  classical
  intro n _ _ level p hp S hS Z hZ
  by_cases hinj : Function.Injective p
  · let X : Matrix n n ℂ := firstMatrix level p S
    let Q : Matrix n n ℂ := qMatrix level p S
    let W : Matrix n n ℂ := Z+(1/3 : ℝ) • X
    obtain ⟨hfirst, hmixed, hcubic⟩ :=
      orderedMoment_proof n level p hp hinj S hS.isHermitian
    -- Hermiticity uses the ordered congruence sum, with no commutation
    -- assumption on S, Z, Q, X or the lifted coefficient matrices.
    have hX : X.IsHermitian := by
      change Xᴴ = X
      calc
        Xᴴ = (∑ a, (liftedV level p a)ᴴ*S*liftedV level p a)ᴴ :=
          congrArg (fun A : Matrix n n ℂ => Aᴴ) hfirst.symm
        _ = ∑ a, (liftedV level p a)ᴴ*S*liftedV level p a := by
          simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose, hS.isHermitian.eq, mul_assoc]
        _ = X := hfirst
    have hW : W.IsHermitian := by
      exact hZ.add (hX.smul (show IsSelfAdjoint (1/3 : ℝ) from rfl))
    have henergy := ordered_row_square S W
      (liftedM level p S) (liftedV level p) hW
    rw [hcubic, hmixed, hfirst] at henergy
    -- The mixed moment is 2 • Q; the square contributes -2 times its
    -- real trace. Thus the ordered cross term is -4 Re tr(Q*W).
    simp only [realTrace, Matrix.smul_mul, Matrix.trace_smul,
      Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] at henergy
    change rowEnergy S W (liftedM level p S) (liftedV level p) =
      (4*(S^3).trace.re-(X^3).trace.re)/3-
        2*(2*(Q*W).trace.re)+4*(X*W*W).trace.re at henergy
    have hpositive := rowEnergy_nonneg S W
      (liftedM level p S) (liftedV level p) hS
    let P : Matrix n n ℂ := diagonal (fun i => (p (level i) : ℂ))
    let F := fun t : ℝ => P⁻¹ *
      CFC.rpow (P^3 + t • (CFC.rpow P (3/2 : ℝ) * S *
        CFC.rpow P (3/2 : ℝ))) (2/3 : ℝ) * P⁻¹
    let B := fun j : ℕ => (j.factorial : ℝ)⁻¹ • iteratedDeriv j F 0
    change 0 ≤ (B 3 + (2 : ℝ) • (Z * B 2) + B 1 * Z^2 -
      (5/48 : ℝ) • (B 1)^3).trace.re
    have hshift := actual_shifted_identity (fun i => p (level i))
      (fun i => hp (level i)) S Z hS.isHermitian
    -- firstMatrix and qMatrix are definitionally the owner's X and Q
    -- after pulling p back along level. The curve and factorial jets
    -- above are definitionally the original target, including singular S.
    change 6*(B 3 + (2 : ℝ) • (Z * B 2) + B 1 * Z^2 -
      (5/48 : ℝ) • (B 1)^3).trace.re =
      (4*(S^3).trace.re-(X^3).trace.re)/3-
        4*(Q*W).trace.re+4*(X*W*W).trace.re at hshift
    linarith only [hpositive, henergy, hshift]
  · exact coincidentLevel_proof n level p hp hinj S hS Z hZ


section PDContinuation
variable {n : Type u} [Fintype n] [DecidableEq n]

private theorem pd_realTrace_smul (r : ℝ) (A : Matrix n n ℂ) :
    realTrace (r • A) = r * realTrace A := by
  simp only [realTrace, Matrix.trace_smul, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, smul_eq_mul]

/-- A weighted square has zero real trace precisely when its row matrix
vanishes. This uses strict positivity of S, not entrywise positivity. -/
private theorem pd_weighted_trace_zero (S N : Matrix n n ℂ) (hS : S.PosDef) :
    realTrace (Nᴴ*S*N) = 0 ↔ N = 0 := by
  constructor
  · intro h
    have hT := hS.posSemidef.conjTranspose_mul_mul_same N
    have ht : (Nᴴ*S*N).trace = 0 := by
      apply Complex.ext
      · exact h
      · exact (Complex.nonneg_iff.mp hT.trace_nonneg).2.symm
    have hmat : Nᴴ*S*N = 0 := hT.trace_eq_zero_iff.mp ht
    have hcol (j : n) : (fun i => N i j) = 0 := by
      by_contra hj
      have hp := hS.re_dotProduct_pos hj
      have he : star (fun i => N i j) ⬝ᵥ (S *ᵥ (fun i => N i j)) = 0 := by
        change (Nᴴ*(S*N)) j j = 0
        rw [← mul_assoc, hmat]
        rfl
      rw [he] at hp
      exact (lt_irrefl 0) hp
    ext i j
    exact congrFun (hcol j) i
  · rintro rfl
    simp [realTrace]

private theorem pd_rowEnergy_zero {ι : Type*} [Fintype ι]
    (S W : Matrix n n ℂ) (M V : ι → Matrix n n ℂ) (hS : S.PosDef)
    (h : rowEnergy S W M V = 0) :
    ∀ a, M a-(V a*W+V a*W) = 0 := by
  have hnonneg (a : ι) :
      0 ≤ realTrace ((M a-(V a*W+V a*W))ᴴ*S*(M a-(V a*W+V a*W))) :=
    (Complex.nonneg_iff.mp
      (hS.posSemidef.conjTranspose_mul_mul_same (M a-(V a*W+V a*W))).trace_nonneg).1
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun a (_ : a ∈ (Finset.univ : Finset ι)) => hnonneg a)).mp h
  intro a
  exact (pd_weighted_trace_zero S _ hS).mp (hz a (Finset.mem_univ a))

/-- Common kernel of the diagonal V maps is zero, since their squared
coefficients sum to tau(a,a)=1. No fiber inhabitance is used. -/
private theorem pd_first_posDef (level : n → Fin 3) (p : Fin 3 → ℝ)
    (hp : ∀ i, 0 < p i) (hinj : Function.Injective p)
    (S : Matrix n n ℂ) (hS : S.PosDef) : (firstMatrix level p S).PosDef := by
  have hfirst := ordered_first_moment level p hp hinj S
  have hps : (firstMatrix level p S).PosSemidef := by
    rw [← hfirst]
    exact Matrix.posSemidef_sum _ fun a _ =>
      hS.posSemidef.conjTranspose_mul_mul_same (liftedV level p a)
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hps.isHermitian
  intro z hz
  have hi : ∃ i, z i ≠ 0 := by
    by_contra! h
    exact hz (funext h)
  obtain ⟨i, hi⟩ := hi
  have hv : dot (v p (level i)) (v p (level i)) = 1 := by
    rw [v_gram p hp hinj, tau_self (hp (level i))]
  have ha : ∃ a, v p (level i) a ≠ 0 := by
    by_contra! h
    simp only [dot, h, zero_mul, Finset.sum_const_zero] at hv
    norm_num at hv
  obtain ⟨a, ha⟩ := ha
  have hvz : liftedV level p a *ᵥ z ≠ 0 := by
    intro h
    have he := congrFun h i
    have hc : (v p (level i) a : ℂ) ≠ 0 := by exact_mod_cast ha
    exact (mul_ne_zero hc hi) (by simpa only [liftedV, Matrix.mulVec_diagonal,
      Pi.zero_apply] using he)
  have hform : star z ⬝ᵥ (firstMatrix level p S *ᵥ z) =
      ∑ b, star (liftedV level p b *ᵥ z) ⬝ᵥ
        (S *ᵥ (liftedV level p b *ᵥ z)) := by
    rw [← hfirst, Matrix.sum_mulVec, dotProduct_sum]
    apply Finset.sum_congr rfl
    intro b _
    simp only [star_mulVec, dotProduct_mulVec, vecMul_vecMul]
  have hpos : 0 < (star z ⬝ᵥ (firstMatrix level p S *ᵥ z)).re := by
    rw [hform, Complex.re_sum]
    exact Finset.sum_pos'
      (fun b _ => hS.posSemidef.re_dotProduct_nonneg _)
      ⟨a, Finset.mem_univ a, hS.re_dotProduct_pos hvz⟩
  exact Complex.pos_iff.mpr
    ⟨hpos, (Complex.nonneg_iff.mp (hps.dotProduct_mulVec_nonneg z)).2⟩

private theorem pd_q_hermitian (level : n → Fin 3) (p : Fin 3 → ℝ)
    (hp : ∀ i, 0 < p i) (hinj : Function.Injective p)
    (S : Matrix n n ℂ) (hS : S.IsHermitian) : (qMatrix level p S).IsHermitian := by
  let A := ∑ a, ((liftedV level p a)ᴴ*S*liftedM level p S a+
    (liftedM level p S a)ᴴ*S*liftedV level p a)
  have hA : A.IsHermitian := by
    change Aᴴ = A
    dsimp only [A]
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_add,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hS.eq,
      mul_assoc, add_comm]
  have he : qMatrix level p S = (1/2 : ℝ) • A := by
    dsimp only [A]
    rw [ordered_mixed_moment level p hp hinj S hS, smul_smul]
    norm_num
  rw [he]
  exact hA.smul (show IsSelfAdjoint (1/2 : ℝ) from rfl)

/-- Solve the actual Sylvester equation in a unitary eigenbasis. The
entrywise denominator is lambda_i+lambda_j, never an ordinary inverse of X.
The final clause proves injectivity on ALL matrices, hence uniqueness. -/
private theorem pd_sylvester_spectral (X D : Matrix n n ℂ)
    (hX : X.PosDef) (hD : D.IsHermitian) :
    ∃ Y : Matrix n n ℂ, Y.IsHermitian ∧ X*Y+Y*X = D ∧
      ∀ Z : Matrix n n ℂ, X*Z+Z*X = 0 → Z = 0 := by
  let U := hX.isHermitian.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U
  let l : n → ℝ := hX.isHermitian.eigenvalues
  let L : Matrix n n ℂ := diagonal (fun i => (l i : ℂ))
  have hspec : X = φ L := hX.isHermitian.spectral_theorem
  have hl (i : n) : 0 < l i := hX.eigenvalues_pos i
  have hden (i j : n) : (l i : ℂ)+(l j : ℂ) ≠ 0 := by
    exact_mod_cast (add_pos (hl i) (hl j)).ne'
  let E : Matrix n n ℂ := φ.symm D
  let T : Matrix n n ℂ := fun i j => E i j / ((l i : ℂ)+(l j : ℂ))
  have hE : E.IsHermitian := (hD.isSelfAdjoint.map φ.symm).isHermitian
  have hT : T.IsHermitian := by
    ext i j
    change star (E j i / ((l j : ℂ)+(l i : ℂ))) =
      E i j / ((l i : ℂ)+(l j : ℂ))
    rw [star_div₀, hE.apply i j]
    congr 1
    simp [add_comm]
  have hsolve : L*T+T*L = E := by
    ext i j
    simp only [Matrix.add_apply, L, Matrix.diagonal_mul, Matrix.mul_diagonal, T]
    field_simp [hden i j] <;> ring
  refine ⟨φ T, ?_, ?_, ?_⟩
  · exact (hT.isSelfAdjoint.map φ).isHermitian
  · calc
      X*φ T+φ T*X = φ (L*T+T*L) := by
        rw [map_add, map_mul, map_mul, ← hspec]
      _ = φ E := congrArg φ hsolve
      _ = D := φ.apply_symm_apply D
  · intro Z hZ
    have hd : L*φ.symm Z+φ.symm Z*L = 0 := by
      have h := congrArg φ.symm hZ
      simpa only [hspec, map_add, map_mul, φ.symm_apply_apply, map_zero] using h
    have hz : φ.symm Z = 0 := by
      ext i j
      have he := congrArg (fun A : Matrix n n ℂ => A i j) hd
      simp only [Matrix.add_apply, L, Matrix.diagonal_mul, Matrix.mul_diagonal,
        Matrix.zero_apply] at he
      have he' : ((l i : ℂ)+(l j : ℂ)) * (φ.symm Z) i j = 0 := by
        linear_combination he
      exact (mul_eq_zero.mp he').resolve_left (hden i j)
    have h := congrArg φ hz
    simpa only [φ.apply_symm_apply, map_zero] using h

/-- Pure cyclic-trace calculation at an actual Sylvester solution. In
particular it assumes no commutation between X, D and Y. -/
private theorem pd_energy_identity (S X D Y : Matrix n n ℂ)
    (h : X*Y+Y*X = D) :
    4*realTrace (S^3-X^3)-6*realTrace (X*D)-6*realTrace (D*Y) =
      3*((4*realTrace (S^3)-realTrace (X^3))/3-
        4*realTrace ((X^2+D)*((1/2 : ℝ) • X+Y))+
        4*realTrace (X*((1/2 : ℝ) • X+Y)*((1/2 : ℝ) • X+Y))) := by
  have hxyx : realTrace (X*Y*X) = realTrace (X*X*Y) := by
    simpa only [mul_assoc] using realTrace_comm (X*Y) X
  have hyxy : realTrace (Y*X*Y) = realTrace (X*Y*Y) := by
    simpa only [mul_assoc] using realTrace_comm Y (X*Y)
  have hdy : realTrace (D*Y) = 2*realTrace (X*Y*Y) := by
    rw [← h, add_mul, realTrace_add, hyxy]
    ring
  simp only [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul,
    realTrace_add, realTrace_sub, pd_realTrace_smul, smul_smul,
    pow_succ, pow_zero, mul_one, one_mul, ← mul_assoc]
  rw [hxyx]
  linarith only [hdy, realTrace_comm D X]

private theorem pd_residual_nonzero (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hinj : Function.Injective p) (i j : Fin 3) (hij : i ≠ j) :
    ∃ a : Fin 2, m p i j (.inr (j,a)) ≠ 0 := by
  have hi := column_indices j
  have hr := residualE_pos p hp hinj (left j) j hi.1
  have hdet := (canonical_residual_blocks p hp hinj).2 j
  have hrad : 0 < residualE p (right j) j-
      (residualY p j)^2/residualE p (left j) j := by
    apply (div_pos hdet hr).trans_eq
    field_simp [hr.ne'] <;> ring
  rcases off_column_cases i j hij with hleft | hright
  · subst i
    refine ⟨0, ?_⟩
    simpa only [ite_true, ite_false, m, if_neg hi.1, ite_true, residualFirst,
      Matrix.cons_val_zero] using (Real.sqrt_pos.mpr hr).ne'
  · subst i
    refine ⟨1, ?_⟩
    simpa only [ite_true, ite_false, m, if_neg hi.2.1, ite_true, if_neg hi.2.2.1.symm,
      residualSecond, Matrix.cons_val_one, Matrix.cons_val_zero]
      using (Real.sqrt_pos.mpr hrad).ne'

private theorem pd_commute_iff (level : n → Fin 3) (p : Fin 3 → ℝ)
    (S : Matrix n n ℂ) :
    diagonal (fun i => (p (level i) : ℂ))*S =
      S*diagonal (fun i => (p (level i) : ℂ)) ↔
    ∀ i j, p (level i) ≠ p (level j) → S i j = 0 := by
  constructor
  · intro h i j hij
    have he := congrArg (fun A : Matrix n n ℂ => A i j) h
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at he
    have hz : ((p (level i) : ℂ)-(p (level j) : ℂ))*S i j = 0 := by
      linear_combination he
    have hc : (p (level i) : ℂ)-(p (level j) : ℂ) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr hij
    exact (mul_eq_zero.mp hz).resolve_left hc
  · intro h
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases he : p (level i) = p (level j)
    · rw [he, mul_comm]
    · rw [h i j he, mul_zero, zero_mul]

/-- The W-independent residual coordinates force off-level entries to zero.
There is no argument from merely pointwise positivity or an unattained infimum. -/
private theorem pd_zero_row_commutes (level : n → Fin 3) (p : Fin 3 → ℝ)
    (hp : ∀ i, 0 < p i) (hinj : Function.Injective p)
    (S W : Matrix n n ℂ) (hS : S.PosDef)
    (h : rowEnergy S W (liftedM level p S) (liftedV level p) = 0) :
    diagonal (fun i => (p (level i) : ℂ))*S =
      S*diagonal (fun i => (p (level i) : ℂ)) := by
  have hrow := pd_rowEnergy_zero S W (liftedM level p S) (liftedV level p) hS h
  have hV (a : Fin 3 × Fin 2) : liftedV level p (.inr a) = 0 := by
    ext i j
    simp [liftedV, v]
  have hM (a : Fin 3 × Fin 2) : liftedM level p S (.inr a) = 0 := by
    simpa only [hV, zero_mul, zero_add, sub_zero] using hrow (.inr a)
  apply (pd_commute_iff level p S).mpr
  intro i j hij
  have hlev : level i ≠ level j := fun he => hij (congrArg p he)
  obtain ⟨a, ha⟩ := pd_residual_nonzero p hp hinj (level i) (level j) hlev
  have he := congrArg (fun A : Matrix n n ℂ => A i j) (hM (level j,a))
  change (m p (level i) (level j) (.inr (level j,a)) : ℂ)*S i j = 0 at he
  have hc : (m p (level i) (level j) (.inr (level j,a)) : ℂ) ≠ 0 := by
    exact_mod_cast ha
  exact (mul_eq_zero.mp he).resolve_left hc

/-- Under the desired commutation conclusion, the original X and Q reduce
to S and S^2. Q is identified by the ordered mixed moment, not by imposing
commutativity on arbitrary intermediate matrices. -/
private theorem pd_commuting_moments (level : n → Fin 3) (p : Fin 3 → ℝ)
    (hp : ∀ i, 0 < p i) (hinj : Function.Injective p)
    (S : Matrix n n ℂ) (hS : S.IsHermitian)
    (hc : diagonal (fun i => (p (level i) : ℂ))*S =
      S*diagonal (fun i => (p (level i) : ℂ))) :
    firstMatrix level p S = S ∧ qMatrix level p S = S^2 := by
  have hoff (i j : n) (hij : level i ≠ level j) : S i j = 0 :=
    (pd_commute_iff level p S).mp hc i j (fun h => hij (hinj h))
  have hX : firstMatrix level p S = S := by
    ext i j
    by_cases he : level i = level j
    · change (HsfLocalSpectrumSupplier.spectralTau (p (level i))
        (p (level j)) : ℂ)*S i j = S i j
      rw [← tau_spectral, he, tau_self (hp (level j))]
      simp
    · simp only [firstMatrix, hoff i j he, mul_zero]
  have hM (a : Coeff) : liftedM level p S a = liftedV level p a*S := by
    ext i j
    change (m p (level i) (level j) a : ℂ)*S i j =
      (diagonal (fun k => (v p (level k) a : ℂ))*S) i j
    rw [Matrix.diagonal_mul]
    by_cases he : level i = level j
    · rw [he, m_diagonal]
    · rw [hoff i j he, mul_zero, mul_zero]
  have hfirst := ordered_first_moment level p hp hinj S
  have hmixed := ordered_mixed_moment level p hp hinj S hS
  have hcross :
      (∑ a, ((liftedV level p a)ᴴ*S*liftedM level p S a+
        (liftedM level p S a)ᴴ*S*liftedV level p a)) =
      firstMatrix level p S*S+S*firstMatrix level p S := by
    have ha (a : Coeff) :
        (liftedV level p a)ᴴ*S*liftedM level p S a+
          (liftedM level p S a)ᴴ*S*liftedV level p a =
        ((liftedV level p a)ᴴ*S*liftedV level p a)*S+
          S*((liftedV level p a)ᴴ*S*liftedV level p a) := by
      rw [hM]
      simp only [Matrix.conjTranspose_mul, hS.eq]
      noncomm_ring
    simp_rw [ha]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hfirst]
  have htwo : (2 : ℝ) • qMatrix level p S = (2 : ℝ) • S^2 := by
    rw [← hmixed, hcross, hX, pow_two, two_smul]
  have hQ := congrArg (fun A : Matrix n n ℂ => (1/2 : ℝ) • A) htwo
  norm_num [smul_smul] at hQ
  exact ⟨hX, hQ⟩

/-- Exact original PD target for injective labels. All witnesses and both
rigidity implications are supplied; the next lemma removes injectivity. -/
private theorem pd_sylvester_injective (level : n → Fin 3) (p : Fin 3 → ℝ)
    (hp : ∀ i, 0 < p i) (hinj : Function.Injective p)
    (S : Matrix n n ℂ) (hS : S.PosDef) :
    let P : Matrix n n ℂ := diagonal (fun i => (p (level i) : ℂ))
    let X := firstMatrix level p S
    let D := qMatrix level p S-X^2
    X.PosDef ∧ ∃ Y : Matrix n n ℂ, Y.IsHermitian ∧ X*Y+Y*X = D ∧
      0 ≤ 4*(S^3-X^3).trace.re-6*(X*D).trace.re-6*(D*Y).trace.re ∧
      ((4*(S^3-X^3).trace.re-6*(X*D).trace.re-6*(D*Y).trace.re = 0) ↔ P*S = S*P) := by
  let P : Matrix n n ℂ := diagonal (fun i => (p (level i) : ℂ))
  let X := firstMatrix level p S
  let Q := qMatrix level p S
  let D := Q-X^2
  have hX : X.PosDef := pd_first_posDef level p hp hinj S hS
  have hQ : Q.IsHermitian := pd_q_hermitian level p hp hinj S hS.isHermitian
  have hD : D.IsHermitian := hQ.sub (hX.isHermitian.pow 2)
  obtain ⟨Y, hY, hsolve, huniq⟩ := pd_sylvester_spectral X D hX hD
  let W := (1/2 : ℝ) • X+Y
  have hW : W.IsHermitian :=
    (hX.isHermitian.smul (show IsSelfAdjoint (1/2 : ℝ) from rfl)).add hY
  obtain ⟨hfirst, hmixed, hcubic⟩ :=
    orderedMoment_proof n level p hp hinj S hS.isHermitian
  have hrow := ordered_row_square S W (liftedM level p S) (liftedV level p) hW
  rw [hcubic, hmixed, hfirst] at hrow
  simp only [Matrix.smul_mul, pd_realTrace_smul] at hrow
  change rowEnergy S W (liftedM level p S) (liftedV level p) =
    (4*realTrace (S^3)-realTrace (X^3))/3-
      2*(2*realTrace (Q*W))+4*realTrace (X*W*W) at hrow
  have hQD : Q = X^2+D := by
    dsimp only [D]
    abel
  have hid := pd_energy_identity S X D Y hsolve
  have henergy :
      4*realTrace (S^3-X^3)-6*realTrace (X*D)-6*realTrace (D*Y) =
        3*rowEnergy S W (liftedM level p S) (liftedV level p) := by
    rw [hrow, hQD]
    dsimp only [W]
    linarith only [hid]
  have hnonneg := rowEnergy_nonneg S W (liftedM level p S) (liftedV level p)
    hS.posSemidef
  change X.PosDef ∧ ∃ Y : Matrix n n ℂ, Y.IsHermitian ∧ X*Y+Y*X = D ∧
    0 ≤ 4*realTrace (S^3-X^3)-6*realTrace (X*D)-6*realTrace (D*Y) ∧
    ((4*realTrace (S^3-X^3)-6*realTrace (X*D)-6*realTrace (D*Y) = 0) ↔ P*S = S*P)
  refine ⟨hX, Y, hY, hsolve, ?_, ?_⟩
  · rw [henergy]
    exact mul_nonneg (by norm_num) hnonneg
  · constructor
    · intro hzero
      have hr : rowEnergy S W (liftedM level p S) (liftedV level p) = 0 := by
        linarith only [henergy, hzero]
      exact pd_zero_row_commutes level p hp hinj S W hS hr
    · intro hcomm
      obtain ⟨hXS, hQS⟩ := pd_commuting_moments level p hp hinj S hS.isHermitian hcomm
      have hDz : D = 0 := by
        dsimp only [D, Q, X]
        rw [hXS, hQS, sub_self]
      have hYz : Y = 0 := huniq Y (hsolve.trans hDz)
      change X = S at hXS
      rw [hXS, hDz, hYz]
      simp [realTrace]

/-- Three positive distinct slots retaining any two prescribed distinct
values. The unused third value exceeds both. -/
private theorem pd_two_slot_completion (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) :
    (∀ i : Fin 3, 0 < (![a,b,a+b+1] : Fin 3 → ℝ) i) ∧
      Function.Injective (![a,b,a+b+1] : Fin 3 → ℝ) := by
  constructor
  · intro i
    fin_cases i
    · exact ha
    · exact hb
    · change 0 < a+b+1
      linarith
  · intro i j h
    fin_cases i <;> fin_cases j <;>
      norm_num at h
    all_goals first | rfl | exact False.elim (hab h) |
      exact False.elim (hab h.symm) | linarith

/-- Faithful positive injective relabeling, including repeated labels and
unused fibers. This changes no pulled-back spectral value. -/
private theorem pd_faithful_relabel (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i) :
    ∃ (q : Fin 3 → ℝ) (r : Fin 3 → Fin 3),
      (∀ i, 0 < q i) ∧ Function.Injective q ∧ ∀ i, q (r i) = p i := by
  classical
  by_cases h01 : p 0 = p 1
  · by_cases h02 : p 0 = p 2
    · let q : Fin 3 → ℝ := ![p 0, p 0+1, p 0+(p 0+1)+1]
      have hq := pd_two_slot_completion (p 0) (p 0+1) (hp 0)
        (by linarith [hp 0]) (by linarith)
      refine ⟨q, fun _ => 0, hq.1, hq.2, ?_⟩
      intro i
      fin_cases i
      · rfl
      · exact h01
      · exact h02
    · let q : Fin 3 → ℝ := ![p 0, p 2, p 0+p 2+1]
      have hq := pd_two_slot_completion (p 0) (p 2) (hp 0) (hp 2) h02
      refine ⟨q, ![0,0,1], hq.1, hq.2, ?_⟩
      intro i
      fin_cases i
      · rfl
      · exact h01
      · rfl
  · by_cases h02 : p 0 = p 2
    · let q : Fin 3 → ℝ := ![p 0, p 1, p 0+p 1+1]
      have hq := pd_two_slot_completion (p 0) (p 1) (hp 0) (hp 1) h01
      refine ⟨q, ![0,1,0], hq.1, hq.2, ?_⟩
      intro i
      fin_cases i
      · rfl
      · rfl
      · exact h02
    · by_cases h12 : p 1 = p 2
      · let q : Fin 3 → ℝ := ![p 0, p 1, p 0+p 1+1]
        have hq := pd_two_slot_completion (p 0) (p 1) (hp 0) (hp 1) h01
        refine ⟨q, ![0,1,1], hq.1, hq.2, ?_⟩
        intro i
        fin_cases i
        · rfl
        · rfl
        · exact h12
      · refine ⟨p, id, hp, ?_, fun _ => rfl⟩
        intro i j he
        fin_cases i <;> fin_cases j <;> simp_all

/-- Closed source proof of the exact ORIGINAL private PD obligation.
There is no supplier, Sylvester-solvability, or commutativity premise. -/
private theorem pdSylvester_proof : PDSylvesterObligation.{u} := by
  classical
  intro n _ _ level p hp S hS
  obtain ⟨q, r, hq, hqi, hr⟩ := pd_faithful_relabel p hp
  have ht := pd_sylvester_injective (r ∘ level) q hq hqi S hS
  have hX : firstMatrix (r ∘ level) q S = firstMatrix level p S := by
    ext i j
    simp only [firstMatrix, Function.comp_apply, hr]
  have hQ : qMatrix (r ∘ level) q S = qMatrix level p S := by
    ext i j
    simp only [qMatrix, Function.comp_apply, hr]
  rw [hX, hQ] at ht
  simpa only [Function.comp_apply, hr] using ht

end PDContinuation

/-- Original Hermitian Sylvester energy and exact rigidity for at most three
positive spectral levels, arbitrary finite complex PD directions, including
empty carriers and repeated labels. -/
theorem actual_threeLevel_PD_sylvester
    (n : Type u) [Fintype n] [DecidableEq n]
    (level : n → Fin 3) (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (S : Matrix n n ℂ) (hS : S.PosDef) :
    let P : Matrix n n ℂ := diagonal (fun i => (p (level i) : ℂ))
    let X : Matrix n n ℂ := fun i j =>
      (HsfLocalSpectrumSupplier.spectralTau (p (level i)) (p (level j)) : ℂ)*S i j
    let Q : Matrix n n ℂ := fun i j => ∑ k,
      (((2/3 : ℝ)*HsfLocalSpectrumSupplier.spectralTau (p (level i)) (p (level k))*
        HsfLocalSpectrumSupplier.spectralTau (p (level k)) (p (level j))+
        3*HsfLocalSpectrumSupplier.spectralKernel (p (level i)) (p (level j))
          (p (level k)) : ℝ) : ℂ)*S i k*S k j
    let D := Q-X^2
    X.PosDef ∧ ∃ Y : Matrix n n ℂ, Y.IsHermitian ∧ X*Y+Y*X = D ∧
      0 ≤ 4*(S^3-X^3).trace.re-6*(X*D).trace.re-6*(D*Y).trace.re ∧
      ((4*(S^3-X^3).trace.re-6*(X*D).trace.re-6*(D*Y).trace.re = 0) ↔ P*S = S*P) := by
  exact pdSylvester_proof n level p hp S hS

end D5.S3.Quantum.Matrix.HsfThreeLevelSupplier
