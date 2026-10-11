/- GID: D5/S3/Quantum/RandomCircuits/PermutedBrickworkEvenRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/RandomCircuits/PermutedBrickworkEvenRefutation
   mirror-E: none(waiver:kernel-checked-content)
   anchors: []
   utility: none
   digest: Every even PB depth on four sites has a negative Haar-moment quadratic form. -/

/-
proof_shape: result: content; literal Haar action and length induction yield a negative form.
escape_witness: even_physical_quadratic_negative on the live path to result.
admission_basis: open-problem-resolution (#13744; Refuted)
Direct frozen dependencies: none on the implementation baseline; HaarTwoCopyTwirl is delivered
as the content prerequisite and must be frozen before this host.
The new content is the literal Haar-to-layer bridge and induction over every word length.
The finite coefficient identities are consumed normalization helpers; no bounded enumeration,
checker, numerical certificate or positive finite instance is retained.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
import Mathlib.Analysis.Matrix.PosDef

open Matrix MeasureTheory
open scoped Kronecker ComplexOrder Matrix.Norms.Elementwise
noncomputable section

open D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl

namespace D5.S3.Quantum.RandomCircuits.PermutedBrickworkEvenRefutation

def matching (m : Fin 3) : Fin 2 → (Fin 4 × Fin 4) :=
  if m = 0 then ![(0,1),(2,3)]
  else if m = 1 then ![(0,2),(1,3)]
  else ![(0,3),(1,2)]

def restrictReplica (p : Fin 4 × Fin 4) (r : (((Fin 4 → Fin q) × (Fin 4 → Fin q)) × ((Fin 4 → Fin q) × (Fin 4 → Fin q)))) :
    (((Fin q × Fin q) × (Fin q × Fin q)) × ((Fin q × Fin q) × (Fin q × Fin q))) :=
  (((r.1.1 p.1,r.1.1 p.2),(r.1.2 p.1,r.1.2 p.2)),
   ((r.2.1 p.1,r.2.1 p.2),(r.2.2 p.1,r.2.2 p.2)))

/-- Independent gates on the two disjoint matching edges. -/
def layerMoment (q : ℕ) (m : Fin 3) :
    Matrix ((((Fin 4 → Fin q) × (Fin 4 → Fin q)) × ((Fin 4 → Fin q) × (Fin 4 → Fin q)))) ((((Fin 4 → Fin q) × (Fin 4 → Fin q)) × ((Fin 4 → Fin q) × (Fin 4 → Fin q)))) ℂ :=
  fun r c => ∏ e : Fin 2, haarAverage (Fin q × Fin q)
    (restrictReplica (matching m e) r) (restrictReplica (matching m e) c)

/-- Products are in circuit order U_(d-1)...U_0. -/
def wordMoment (q d : ℕ) (w : Fin d → Fin 3) :
    Matrix ((((Fin 4 → Fin q) × (Fin 4 → Fin q)) × ((Fin 4 → Fin q) × (Fin 4 → Fin q)))) ((((Fin 4 → Fin q) × (Fin 4 → Fin q)) × ((Fin 4 → Fin q) × (Fin 4 → Fin q)))) ℂ :=
  (((List.finRange d).reverse).map (fun i => layerMoment q (w i))).prod

def NoRepeat (d : ℕ) (w : Fin d → Fin 3) : Prop :=
  ∀ i : ℕ, ∀ hi : i+1<d, w ⟨i,by omega⟩ ≠ w ⟨i+1,hi⟩

def admissibleWords (d : ℕ) : Finset (Fin d → Fin 3) := by
  classical
  exact Finset.univ.filter (NoRepeat d)

/-- Uniform no-repeat matching-word expectation; no Haar/projector substitution. -/
def vecPhi (q d : ℕ) :
    Matrix ((((Fin 4 → Fin q) × (Fin 4 → Fin q)) × ((Fin 4 → Fin q) × (Fin 4 → Fin q)))) ((((Fin 4 → Fin q) × (Fin 4 → Fin q)) × ((Fin 4 → Fin q) × (Fin 4 → Fin q)))) ℂ :=
  ((admissibleWords d).card : ℂ)⁻¹ •
    ∑ w ∈ admissibleWords d, wordMoment q d w

def claim : Prop :=
  ∀ q : ℕ, 2 ≤ q → ∀ d : ℕ, 2 ≤ d → Even d → ¬ (vecPhi q d).PosSemidef

/-- One-site identity/swap permutation vectors with norm 1. -/
def permutationVector (q : ℕ) (b : Fin 4 → Fin 2)
    (r : (((Fin 4 → Fin q) × (Fin 4 → Fin q)) × ((Fin 4 → Fin q) × (Fin 4 → Fin q)))) : ℂ :=
  ∏ s : Fin 4, sitePermutation q (b s)
    ((r.1.1 s,r.1.2 s),(r.2.1 s,r.2.2 s))

def physicalWitness (q : ℕ) : (((Fin 4 → Fin q) × (Fin 4 → Fin q)) × ((Fin 4 → Fin q) × (Fin 4 → Fin q))) → ℂ :=
  permutationVector q ![0,1,0,1] - permutationVector q ![0,1,1,0] -
    permutationVector q ![1,0,0,1] + permutationVector q ![1,0,1,0]

end D5.S3.Quantum.RandomCircuits.PermutedBrickworkEvenRefutation

namespace D5.S3.Quantum.RandomCircuits.PermutedBrickworkEvenRefutation.Walk
variable {R : Type*} [Ring R]

private def endpoint (P : Fin 3 → R) : ℕ → Fin 3 → R
  | 0, i => P i
  | d+1, i => P i * ∑ j : Fin 3, if j ≠ i then endpoint P d j else 0

private def sumWalk (P : Fin 3 → R) (d : ℕ) : R := ∑ i : Fin 3, endpoint P d i

private theorem endpoint_left_fixed (P : Fin 3 → R) (hP : ∀ i, P i * P i = P i)
    (d : ℕ) (i : Fin 3) : P i * endpoint P d i = endpoint P d i := by
  cases d with
  | zero => exact hP i
  | succ d => simp only [endpoint, ← mul_assoc, hP i]

private theorem sumWalk_succ (P : Fin 3 → R) (hP : ∀ i, P i * P i = P i)
    (d : ℕ) : sumWalk P (d+1) = ((∑ i, P i)-1)*sumWalk P d := by
  have h0 := endpoint_left_fixed P hP d 0
  have h1 := endpoint_left_fixed P hP d 1
  have h2 := endpoint_left_fixed P hP d 2
  simp only [sumWalk, Fin.sum_univ_three, endpoint]
  simp
  simp only [mul_add, add_mul, sub_mul, one_mul, h0, h1, h2]
  abel

private theorem sumWalk_formula (P : Fin 3 → R) (hP : ∀ i, P i * P i = P i)
    (d : ℕ) : sumWalk P d = ((∑ i, P i)-1)^d * (∑ i, P i) := by
  induction d with
  | zero => simp [sumWalk, endpoint]
  | succ d hd => rw [sumWalk_succ P hP, hd, pow_succ', mul_assoc]

end D5.S3.Quantum.RandomCircuits.PermutedBrickworkEvenRefutation.Walk

namespace D5.S3.Quantum.RandomCircuits.PermutedBrickworkEvenRefutation.FiniteModel

/-- Coefficients in the actual nonorthogonal identity/swap vectors. -/
private def localRule (a : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := fun r c =>
  if r.1=r.2 then
    if c.1=c.2 then if r=c then 1 else 0 else a
  else 0

private def pA (a : ℝ) : Matrix ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ℝ := localRule a ⊗ₖ localRule a

private def pB (a : ℝ) := (pA a).submatrix (Equiv.prodProdProdComm (Fin 2) (Fin 2) (Fin 2) (Fin 2)) (Equiv.prodProdProdComm (Fin 2) (Fin 2) (Fin 2) (Fin 2))
private def pC (a : ℝ) := (pA a).submatrix ((Equiv.prodCongr (Equiv.refl (Fin 2 × Fin 2)) (Equiv.prodComm (Fin 2) (Fin 2))).trans
    (Equiv.prodProdProdComm (Fin 2) (Fin 2) (Fin 2) (Fin 2))) ((Equiv.prodCongr (Equiv.refl (Fin 2 × Fin 2)) (Equiv.prodComm (Fin 2) (Fin 2))).trans
    (Equiv.prodProdProdComm (Fin 2) (Fin 2) (Fin 2) (Fin 2)))

private def antisym (r : (Fin 2 × Fin 2)) : ℝ :=
  if r=(0,1) then 1 else if r=(1,0) then -1 else 0

private def witness (r : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))) : ℝ := antisym r.1 * antisym r.2

private def total (a : ℝ) := pA a+pB a+pC a

private def gramLocal (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := fun i j => if i=j then 1 else r

private def gram (r : ℝ) : Matrix ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ℝ :=
  (gramLocal r ⊗ₖ gramLocal r) ⊗ₖ (gramLocal r ⊗ₖ gramLocal r)

private theorem total_eigenvector (a : ℝ) :
    (total a).mulVec witness = (1-2*a^2) • witness := by
  ext ⟨⟨i,j⟩,⟨k,l⟩⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      total, pA, pB, pC, localRule, witness, antisym, Equiv.prodProdProdComm, Equiv.prodCongr, Equiv.prodComm, Equiv.refl, Equiv.trans,
      Matrix.kronecker_apply] <;> ring

private theorem gram_norm (r : ℝ) : witness ⬝ᵥ (gram r).mulVec witness = 4*(1-r^2)^2 := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
    gram, gramLocal, witness, antisym, Matrix.kronecker_apply]
  ring

private theorem localRule_idempotent (a : ℝ) : localRule a * localRule a = localRule a := by
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, localRule]

private theorem pa_idempotent (a : ℝ) : pA a * pA a = pA a := by
  simp [pA, ← Matrix.mul_kronecker_mul, localRule_idempotent]

private theorem pb_idempotent (a : ℝ) : pB a * pB a = pB a := by
  change (pA a).submatrix (Equiv.prodProdProdComm (Fin 2) (Fin 2) (Fin 2) (Fin 2)) (Equiv.prodProdProdComm (Fin 2) (Fin 2) (Fin 2) (Fin 2)) * (pA a).submatrix (Equiv.prodProdProdComm (Fin 2) (Fin 2) (Fin 2) (Fin 2)) (Equiv.prodProdProdComm (Fin 2) (Fin 2) (Fin 2) (Fin 2)) = _
  rw [Matrix.submatrix_mul_equiv, pa_idempotent]
  rfl

private theorem pc_idempotent (a : ℝ) : pC a * pC a = pC a := by
  change (pA a).submatrix ((Equiv.prodCongr (Equiv.refl (Fin 2 × Fin 2)) (Equiv.prodComm (Fin 2) (Fin 2))).trans
    (Equiv.prodProdProdComm (Fin 2) (Fin 2) (Fin 2) (Fin 2))) ((Equiv.prodCongr (Equiv.refl (Fin 2 × Fin 2)) (Equiv.prodComm (Fin 2) (Fin 2))).trans
    (Equiv.prodProdProdComm (Fin 2) (Fin 2) (Fin 2) (Fin 2))) * (pA a).submatrix ((Equiv.prodCongr (Equiv.refl (Fin 2 × Fin 2)) (Equiv.prodComm (Fin 2) (Fin 2))).trans
    (Equiv.prodProdProdComm (Fin 2) (Fin 2) (Fin 2) (Fin 2))) ((Equiv.prodCongr (Equiv.refl (Fin 2 × Fin 2)) (Equiv.prodComm (Fin 2) (Fin 2))).trans
    (Equiv.prodProdProdComm (Fin 2) (Fin 2) (Fin 2) (Fin 2))) = _
  rw [Matrix.submatrix_mul_equiv, pa_idempotent]
  rfl

private def projection (a : ℝ) : Fin 3 → Matrix ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ℝ := ![pA a,pB a,pC a]

private theorem projection_idempotent (a : ℝ) (i : Fin 3) :
    projection a i * projection a i = projection a i := by
  fin_cases i
  · exact pa_idempotent a
  · exact pb_idempotent a
  · exact pc_idempotent a

private theorem sum_projection (a : ℝ) : (∑ i, projection a i) = total a := by
  simp [projection,Fin.sum_univ_three,total]

/-- k is the positive depth minus one. -/
private def walkSum (a : ℝ) (k : ℕ) := Walk.sumWalk (projection a) k

private theorem walk_recurrence (a : ℝ) (k : ℕ) :
    walkSum a (k+1) = (total a-1)*walkSum a k := by
  simpa [walkSum,sum_projection] using
    Walk.sumWalk_succ (projection a) (projection_idempotent a) k

private theorem walk_eigenvector (a : ℝ) (k : ℕ) :
    (walkSum a k).mulVec witness =
      ((1-2*a^2)*(-2*a^2)^k) • witness := by
  induction k with
  | zero =>
    simpa [walkSum,Walk.sumWalk, Walk.endpoint,sum_projection] using total_eigenvector a
  | succ k hk =>
    rw [walk_recurrence,← Matrix.mulVec_mulVec,hk,Matrix.mulVec_smul,
      Matrix.sub_mulVec,Matrix.one_mulVec,total_eigenvector]
    ext r
    simp only [Pi.smul_apply,smul_eq_mul,Pi.sub_apply,pow_succ]
    ring

private def moment (a : ℝ) (k : ℕ) : Matrix ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ℝ :=
  (3*2^k : ℝ)⁻¹ • walkSum a k

private theorem moment_eigenvector (a : ℝ) (k : ℕ) :
    (moment a k).mulVec witness =
      (((1-2*a^2)/3)*(-a^2)^k) • witness := by
  rw [moment,Matrix.smul_mulVec,walk_eigenvector,smul_smul]
  congr 1
  have hk : (2:ℝ)^k≠0 := pow_ne_zero _ (by norm_num)
  field_simp
  rw [show -(2*a^2) = 2*(-a^2) by ring, mul_pow]
  ring

private theorem moment_quadratic (a r : ℝ) (k : ℕ) :
    witness ⬝ᵥ (gram r).mulVec ((moment a k).mulVec witness) =
      (((1-2*a^2)/3)*(-a^2)^k)*(4*(1-r^2)^2) := by
  rw [moment_eigenvector,Matrix.mulVec_smul,dotProduct_smul,gram_norm]
  simp only [smul_eq_mul]

private theorem even_quadratic_negative (q : ℝ) (hq : 2≤q) (m : ℕ) :
    witness ⬝ᵥ (gram q⁻¹).mulVec
      ((moment (q/(q^2+1)) (2*m+1)).mulVec witness) < 0 := by
  rw [moment_quadratic]
  have hq0 : 0<q := by linarith
  have hden : 0<q^2+1 := by positivity
  have ha : 0<q/(q^2+1) := div_pos hq0 hden
  have hid : 1-2*(q/(q^2+1))^2 = (q^4+1)/(q^2+1)^2 := by
    field_simp
    ring
  have hh : 0<1-2*(q/(q^2+1))^2 := by rw [hid]; positivity
  have hp : (-(q/(q^2+1))^2)^(2*m+1) < 0 := by
    rw [pow_add,pow_mul,pow_one]
    exact mul_neg_of_pos_of_neg (pow_pos (sq_pos_of_neg (by nlinarith [sq_pos_of_pos ha])) _)
      (by nlinarith [sq_pos_of_pos ha])
  have hi : 0<q⁻¹ := inv_pos.mpr hq0
  have hi1 : q⁻¹<1 := (inv_lt_one₀ hq0).mpr (by linarith)
  have hn : 0<4*(1-(q⁻¹)^2)^2 := by
    have : 0<1-(q⁻¹)^2 := by nlinarith
    positivity
  exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) hp) hn

end D5.S3.Quantum.RandomCircuits.PermutedBrickworkEvenRefutation.FiniteModel

namespace D5.S3.Quantum.RandomCircuits.PermutedBrickworkEvenRefutation

private def parameter (q : ℕ) : ℝ := (q:ℝ)/((q:ℝ)^2+1)

private theorem gate_local_model (q : ℕ) (hq : 2≤q) (b : Fin 2 × Fin 2) :
    (haarAverage (Fin q × Fin q)).mulVec (localPermutation q b) =
      ∑ c : Fin 2 × Fin 2,
        (FiniteModel.localRule (parameter q) c b : ℂ) • localPermutation q c := by
  have ha : (parameter q : ℂ) = (q:ℂ)/((q:ℂ)^2+1) := by simp [parameter]
  rcases b with ⟨b,c⟩
  fin_cases b <;> fin_cases c
  · simpa [FiniteModel.localRule,Fintype.sum_prod_type,Fin.sum_univ_two] using local_identity_fixed q
  · rw [gate_mixed_rule q hq _ (by decide),← ha]
    simp [FiniteModel.localRule,Fintype.sum_prod_type,Fin.sum_univ_two,smul_add]
  · rw [gate_mixed_rule q hq _ (by decide),← ha]
    simp [FiniteModel.localRule,Fintype.sum_prod_type,Fin.sum_univ_two,smul_add]
  · simpa [FiniteModel.localRule,Fintype.sum_prod_type,Fin.sum_univ_two] using local_swap_fixed q

end D5.S3.Quantum.RandomCircuits.PermutedBrickworkEvenRefutation

namespace D5.S3.Quantum.RandomCircuits.PermutedBrickworkEvenRefutation

private def splitA (q : ℕ) : (Fin 4 → Fin q) ≃ (Fin q × Fin q) × (Fin q × Fin q) :=
  ⟨fun x => ((x 0,x 1),(x 2,x 3)),
    fun x => ![x.1.1,x.1.2,x.2.1,x.2.2],
    by intro x; funext i; fin_cases i <;> rfl,
    by rintro ⟨⟨a,b⟩,⟨c,d⟩⟩; rfl⟩
private def splitB (q : ℕ) : (Fin 4 → Fin q) ≃ (Fin q × Fin q) × (Fin q × Fin q) :=
  ⟨fun x => ((x 0,x 2),(x 1,x 3)),
    fun x => ![x.1.1,x.2.1,x.1.2,x.2.2],
    by intro x; funext i; fin_cases i <;> rfl,
    by rintro ⟨⟨a,b⟩,⟨c,d⟩⟩; rfl⟩
private def splitC (q : ℕ) : (Fin 4 → Fin q) ≃ (Fin q × Fin q) × (Fin q × Fin q) :=
  ⟨fun x => ((x 0,x 3),(x 1,x 2)),
    fun x => ![x.1.1,x.2.1,x.2.2,x.1.2],
    by intro x; funext i; fin_cases i <;> rfl,
    by rintro ⟨⟨a,b⟩,⟨c,d⟩⟩; rfl⟩

private def siteSplit (q : ℕ) (m : Fin 3) := if m=0 then splitA q else if m=1 then splitB q else splitC q

private def layerSplit (q : ℕ) (m : Fin 3) : (((Fin 4 → Fin q) × (Fin 4 → Fin q)) × ((Fin 4 → Fin q) × (Fin 4 → Fin q))) ≃ (((Fin q × Fin q) × (Fin q × Fin q)) × ((Fin q × Fin q) × (Fin q × Fin q))) × (((Fin q × Fin q) × (Fin q × Fin q)) × ((Fin q × Fin q) × (Fin q × Fin q))) :=
  ⟨fun r =>
      ((((siteSplit q m r.1.1).1,(siteSplit q m r.1.2).1),
        ((siteSplit q m r.2.1).1,(siteSplit q m r.2.2).1)),
       (((siteSplit q m r.1.1).2,(siteSplit q m r.1.2).2),
        ((siteSplit q m r.2.1).2,(siteSplit q m r.2.2).2))),
    fun r =>
      (((siteSplit q m).symm (r.1.1.1,r.2.1.1),(siteSplit q m).symm (r.1.1.2,r.2.1.2)),
       ((siteSplit q m).symm (r.1.2.1,r.2.2.1),(siteSplit q m).symm (r.1.2.2,r.2.2.2))),
    by intro r; simp,
    by rintro ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩; simp⟩

private theorem layer_kronecker (q : ℕ) (m : Fin 3) :
    layerMoment q m = (haarAverage (Fin q × Fin q) ⊗ₖ haarAverage (Fin q × Fin q)).submatrix
      (layerSplit q m) (layerSplit q m) := by
  ext r c
  fin_cases m <;> simp [layerMoment,Fin.prod_univ_two,matching,layerSplit,
    siteSplit,splitA,splitB,splitC,restrictReplica,Matrix.kronecker_apply]

private theorem layer_idempotent (q : ℕ) (m : Fin 3) :
    layerMoment q m * layerMoment q m = layerMoment q m := by
  rw [layer_kronecker,Matrix.submatrix_mul_equiv,← Matrix.mul_kronecker_mul]
  change ((haarAverage ((Fin q × Fin q))*haarAverage ((Fin q × Fin q))) ⊗ₖ
      (haarAverage ((Fin q × Fin q))*haarAverage ((Fin q × Fin q)))).submatrix _ _ = _
  rw [haarAverage_idempotent]

private def configBits (c : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))) : Fin 4 → Fin 2 := ![c.1.1,c.1.2,c.2.1,c.2.2]
private def basisVector (q : ℕ) (c : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))) : (((Fin 4 → Fin q) × (Fin 4 → Fin q)) × ((Fin 4 → Fin q) × (Fin 4 → Fin q))) → ℂ := permutationVector q (configBits c)
private def splitConfig (m : Fin 3) (c : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))) : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) :=
  if m=0 then c else if m=1 then (Equiv.prodProdProdComm (Fin 2) (Fin 2) (Fin 2) (Fin 2)) c else ((Equiv.prodCongr (Equiv.refl (Fin 2 × Fin 2)) (Equiv.prodComm (Fin 2) (Fin 2))).trans
    (Equiv.prodProdProdComm (Fin 2) (Fin 2) (Fin 2) (Fin 2))) c

private theorem basis_tensor (q : ℕ) (m : Fin 3) (c : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))) (r : (((Fin 4 → Fin q) × (Fin 4 → Fin q)) × ((Fin 4 → Fin q) × (Fin 4 → Fin q)))) :
    basisVector q c r =
      localPermutation q (splitConfig m c).1 ((layerSplit q m) r).1 *
      localPermutation q (splitConfig m c).2 ((layerSplit q m) r).2 := by
  let u (i : Fin 4) := sitePermutation q (configBits c i)
    ((r.1.1 i,r.1.2 i),(r.2.1 i,r.2.2 i))
  unfold basisVector permutationVector
  rw [Fin.prod_univ_four]
  fin_cases m
  · change u 0*u 1*u 2*u 3 = (u 0*u 1)*(u 2*u 3)
    ring
  · change u 0*u 1*u 2*u 3 = (u 0*u 2)*(u 1*u 3)
    ring
  · change u 0*u 1*u 2*u 3 = (u 0*u 3)*(u 1*u 2)
    ring

private theorem layer_basis_action_tensor (q : ℕ) (m : Fin 3) (c : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))) (r : (((Fin 4 → Fin q) × (Fin 4 → Fin q)) × ((Fin 4 → Fin q) × (Fin 4 → Fin q)))) :
    (layerMoment q m).mulVec (basisVector q c) r =
      (haarAverage (Fin q × Fin q)).mulVec (localPermutation q (splitConfig m c).1)
        ((layerSplit q m) r).1 *
      (haarAverage (Fin q × Fin q)).mulVec (localPermutation q (splitConfig m c).2)
        ((layerSplit q m) r).2 := by
  rw [layer_kronecker]
  simp only [Matrix.mulVec,dotProduct,Matrix.submatrix_apply,Matrix.kroneckerMap_apply]
  simp_rw [basis_tensor q m]
  rw [(layerSplit q m).sum_comp
    (fun t : (((Fin q × Fin q) × (Fin q × Fin q)) × ((Fin q × Fin q) × (Fin q × Fin q))) × (((Fin q × Fin q) × (Fin q × Fin q)) × ((Fin q × Fin q) × (Fin q × Fin q))) =>
      (haarAverage (Fin q × Fin q) ((layerSplit q m) r).1 t.1 *
       haarAverage (Fin q × Fin q) ((layerSplit q m) r).2 t.2) *
      (localPermutation q (splitConfig m c).1 t.1 *
       localPermutation q (splitConfig m c).2 t.2))]
  rw [Fintype.sum_prod_type,Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end D5.S3.Quantum.RandomCircuits.PermutedBrickworkEvenRefutation

namespace D5.S3.Quantum.RandomCircuits.PermutedBrickworkEvenRefutation

private def configEquiv (m : Fin 3) : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ≃ ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) :=
  if m=0 then Equiv.refl _ else if m=1 then (Equiv.prodProdProdComm (Fin 2) (Fin 2) (Fin 2) (Fin 2)) else ((Equiv.prodCongr (Equiv.refl (Fin 2 × Fin 2)) (Equiv.prodComm (Fin 2) (Fin 2))).trans
    (Equiv.prodProdProdComm (Fin 2) (Fin 2) (Fin 2) (Fin 2)))

private theorem configEquiv_apply (m : Fin 3) (c : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))) :
    configEquiv m c = splitConfig m c := by
  fin_cases m <;> rfl

private theorem projection_entry (a : ℝ) (m : Fin 3) (s c : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))) :
    FiniteModel.projection a m s c =
      FiniteModel.localRule a (splitConfig m s).1 (splitConfig m c).1 *
      FiniteModel.localRule a (splitConfig m s).2 (splitConfig m c).2 := by
  fin_cases m <;> rfl

private def embedding (q : ℕ) : Matrix ((((Fin 4 → Fin q) × (Fin 4 → Fin q)) × ((Fin 4 → Fin q) × (Fin 4 → Fin q)))) ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ℂ := fun r c => basisVector q c r

private theorem layer_embedding (q : ℕ) (hq : 2≤q) (m : Fin 3) :
    layerMoment q m * embedding q =
      embedding q * (FiniteModel.projection (parameter q) m).map Complex.ofReal := by
  ext r c
  change (layerMoment q m).mulVec (basisVector q c) r = _
  rw [layer_basis_action_tensor,gate_local_model q hq,gate_local_model q hq]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [Finset.sum_mul_sum]
  let f (s : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))) : ℂ :=
    ((FiniteModel.localRule (parameter q) s.1 (splitConfig m c).1 : ℂ)*
      (FiniteModel.localRule (parameter q) s.2 (splitConfig m c).2 : ℂ))*
      (localPermutation q s.1 ((layerSplit q m) r).1 *
       localPermutation q s.2 ((layerSplit q m) r).2)
  calc
    _ = ∑ s : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)), f s := by
      conv_rhs => rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [f]
      ring
    _ = ∑ s : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)), f (configEquiv m s) := ((configEquiv m).sum_comp f).symm
    _ = _ := by
      simp only [Matrix.mul_apply,embedding,Matrix.map_apply,projection_entry,
        Complex.ofReal_mul,configEquiv_apply]
      apply Finset.sum_congr rfl
      intro s hs
      dsimp [f]
      rw [basis_tensor q m]
      ring

private theorem basis_gram (q : ℕ) (hq : 0<q) (b c : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))) :
    star (basisVector q b) ⬝ᵥ basisVector q c =
      (FiniteModel.gram ((q:ℝ)⁻¹) b c : ℂ) := by
  simp only [dotProduct,Pi.star_apply]
  simp_rw [basis_tensor q 0]
  simp only [star_mul,splitConfig,ite_true]
  rw [(layerSplit q 0).sum_comp
    (fun t : (((Fin q × Fin q) × (Fin q × Fin q)) × ((Fin q × Fin q) × (Fin q × Fin q))) × (((Fin q × Fin q) × (Fin q × Fin q)) × ((Fin q × Fin q) × (Fin q × Fin q))) =>
      (star (localPermutation q b.2 t.2) * star (localPermutation q b.1 t.1)) *
      (localPermutation q c.1 t.1 * localPermutation q c.2 t.2))]
  rw [Fintype.sum_prod_type]
  calc
    _ = (star (localPermutation q b.1) ⬝ᵥ localPermutation q c.1)*
      (star (localPermutation q b.2) ⬝ᵥ localPermutation q c.2) := by
      simp only [dotProduct,Pi.star_apply,Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      rw [localPermutation_gram q hq,localPermutation_gram q hq]
      simp only [FiniteModel.gram,FiniteModel.gramLocal,Matrix.kroneckerMap_apply,
        Complex.ofReal_mul]
      split_ifs <;> simp [*] <;> ring

private theorem embedding_gram (q : ℕ) (hq : 0<q) :
    (embedding q)ᴴ*embedding q = (FiniteModel.gram ((q:ℝ)⁻¹)).map Complex.ofReal := by
  ext b c
  change star (basisVector q b) ⬝ᵥ basisVector q c = _
  exact basis_gram q hq b c

end D5.S3.Quantum.RandomCircuits.PermutedBrickworkEvenRefutation

namespace D5.S3.Quantum.RandomCircuits.PermutedBrickworkEvenRefutation
variable {R : Type*} [Ring R]

private def genericWord (P : Fin 3 → R) (d : ℕ) (w : Fin d → Fin 3) : R :=
  (((List.finRange d).reverse).map (fun i => P (w i))).prod

private theorem genericWord_snoc (P : Fin 3 → R) (d : ℕ) (w : Fin d → Fin 3) (i : Fin 3) :
    genericWord P (d+1) (Fin.snoc (α := fun _ => Fin 3) w i) = P i * genericWord P d w := by
  simp [genericWord,List.finRange_succ_last,List.reverse_append,List.map_map,
    Function.comp_def]

private theorem noRepeat_snoc (d : ℕ) (w : Fin (d+1) → Fin 3) (i : Fin 3) :
    NoRepeat (d+2) (Fin.snoc (α := fun _ => Fin 3) w i) ↔ NoRepeat (d+1) w ∧ w (Fin.last d)≠i := by
  constructor
  · intro h
    constructor
    · intro j hj
      have hh := h j (by omega)
      change (Fin.snoc (α := fun _ => Fin 3) w i) (Fin.castSucc (⟨j,by omega⟩ : Fin (d+1))) ≠
        (Fin.snoc (α := fun _ => Fin 3) w i) (Fin.castSucc (⟨j+1,hj⟩ : Fin (d+1))) at hh
      simpa only [Fin.snoc_castSucc] using hh
    · have hh := h d (by omega)
      change (Fin.snoc (α := fun _ => Fin 3) w i) (Fin.castSucc (Fin.last d) : Fin (d+2)) ≠
        (Fin.snoc (α := fun _ => Fin 3) w i) (Fin.last (d+1)) at hh
      simpa only [Fin.snoc_castSucc,Fin.snoc_last] using hh
  · rintro ⟨h,hi⟩ j hj
    by_cases hlast : j=d
    · subst j
      change (Fin.snoc (α := fun _ => Fin 3) w i) (Fin.castSucc (Fin.last d) : Fin (d+2)) ≠
        (Fin.snoc (α := fun _ => Fin 3) w i) (Fin.last (d+1))
      simpa only [Fin.snoc_castSucc,Fin.snoc_last] using hi
    · have hj' : j+1<d+1 := by omega
      change (Fin.snoc (α := fun _ => Fin 3) w i) (Fin.castSucc (⟨j,by omega⟩ : Fin (d+1))) ≠
        (Fin.snoc (α := fun _ => Fin 3) w i) (Fin.castSucc (⟨j+1,hj'⟩ : Fin (d+1)))
      simpa only [Fin.snoc_castSucc] using h j hj'

private def endpointWordSum (P : Fin 3 → R) (k : ℕ) (i : Fin 3) : R := by
  classical
  exact ∑ w : Fin (k+1) → Fin 3,
    if NoRepeat (k+1) w ∧ w (Fin.last k)=i then genericWord P (k+1) w else 0

private theorem endpointWordSum_zero (P : Fin 3 → R) (i : Fin 3) :
    endpointWordSum P 0 i = P i := by
  classical
  unfold endpointWordSum
  rw [← (Fin.snocEquiv (fun _ : Fin 1 => Fin 3)).sum_comp]
  simp [Fintype.sum_prod_type,Fin.snocEquiv,NoRepeat,genericWord,List.finRange_succ,Fin.snoc]

private theorem endpointWordSum_succ (P : Fin 3 → R) (k : ℕ) (i : Fin 3) :
    endpointWordSum P (k+1) i =
      P i * ∑ j : Fin 3, if j≠i then endpointWordSum P k j else 0 := by
  classical
  unfold endpointWordSum
  rw [← (Fin.snocEquiv (fun _ : Fin (k+2) => Fin 3)).sum_comp]
  dsimp only [Fin.snocEquiv,Equiv.coe_fn_mk]
  simp only [Fintype.sum_prod_type,Fin.snoc_last,noRepeat_snoc,
    genericWord_snoc]
  have hp (w : Fin (k+1) → Fin 3) (j : Fin 3) :
      ((NoRepeat (k+1) w ∧ w (Fin.last k)≠j) ∧ j=i) ↔
      (j=i ∧ NoRepeat (k+1) w ∧ w (Fin.last k)≠i) := by aesop
  simp only [hp,ite_and]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [Finset.mul_sum,mul_ite,mul_zero]
  symm
  calc
    _ = ∑ j : Fin 3, ∑ w : Fin (k+1) → Fin 3,
      if j≠i then if NoRepeat (k+1) w then
        if w (Fin.last k)=j then P i*genericWord P (k+1) w else 0 else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : j≠i <;> simp [h]
    _ = ∑ w : Fin (k+1) → Fin 3, ∑ j : Fin 3,
      if j≠i then if NoRepeat (k+1) w then
        if w (Fin.last k)=j then P i*genericWord P (k+1) w else 0 else 0 else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w hw
      by_cases h : NoRepeat (k+1) w
      · simp only [h,ite_true]
        rw [Finset.sum_eq_single (w (Fin.last k))]
        · simp
        · intro j hj hji
          simp [Ne.symm hji]
        · simp
      · simp [h]

private theorem endpointWordSum_eq (P : Fin 3 → R) (k : ℕ) (i : Fin 3) :
    endpointWordSum P k i = Walk.endpoint P k i := by
  induction k generalizing i with
  | zero => exact endpointWordSum_zero P i
  | succ k hk =>
    rw [endpointWordSum_succ,Walk.endpoint]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [hk]

private theorem sum_words_eq (P : Fin 3 → R) (k : ℕ) :
    (∑ w ∈ admissibleWords (k+1), genericWord P (k+1) w) = Walk.sumWalk P k := by
  classical
  calc
    _ = ∑ w : Fin (k+1) → Fin 3,
      if NoRepeat (k+1) w then genericWord P (k+1) w else 0 := by
      simp only [admissibleWords,Finset.sum_filter]
    _ = ∑ i : Fin 3, endpointWordSum P k i := by
      unfold endpointWordSum
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w hw
      simp only [ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero,
        Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    _ = _ := by simp only [endpointWordSum_eq,Walk.sumWalk]

private theorem genericWord_one (d : ℕ) (w : Fin d → Fin 3) :
    genericWord (fun _ => (1:ℤ)) d w = 1 := by
  unfold genericWord
  apply List.prod_eq_one
  intro x hx
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
  rfl

private theorem admissibleWords_card (k : ℕ) : (admissibleWords (k+1)).card = 3*2^k := by
  have h := sum_words_eq (fun _ => (1:ℤ)) k
  simp only [genericWord_one,Finset.sum_const,Finset.sum_const_zero,
    nsmul_eq_mul,mul_one] at h
  rw [Walk.sumWalk_formula (fun _ => (1:ℤ)) (by intro i; simp)] at h
  norm_num [Fin.sum_univ_three] at h
  rw [mul_comm] at h
  exact_mod_cast h

private theorem vecPhi_walk (q k : ℕ) : vecPhi q (k+1) =
    (3*2^k : ℂ)⁻¹ • Walk.sumWalk (layerMoment q) k := by
  unfold vecPhi
  rw [admissibleWords_card]
  have h := sum_words_eq (layerMoment q) k
  change (∑ w ∈ admissibleWords (k+1),wordMoment q (k+1) w) = _ at h
  rw [h]
  simp

end D5.S3.Quantum.RandomCircuits.PermutedBrickworkEvenRefutation

namespace D5.S3.Quantum.RandomCircuits.PermutedBrickworkEvenRefutation

private def realLift (q : ℕ) (x : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) → ℝ) : (((Fin 4 → Fin q) × (Fin 4 → Fin q)) × ((Fin 4 → Fin q) × (Fin 4 → Fin q))) → ℂ := (embedding q).mulVec ((fun c => (x c : ℂ)))

private theorem complexify_mulVec (A : Matrix ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ℝ) (x : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) → ℝ) :
    (A.map Complex.ofReal).mulVec ((fun c => (x c : ℂ))) = (fun c => (A.mulVec x c : ℂ)) := by
  ext c
  exact (RingHom.map_mulVec Complex.ofRealHom A x c).symm

private theorem realLift_add (q : ℕ) (x y : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) → ℝ) :
    realLift q (x+y) = realLift q x+realLift q y := by
  have h : (fun c => ((x+y) c : ℂ)) = (fun c => (x c : ℂ))+(fun c => (y c : ℂ)) := by
    ext c; simp [Pi.add_apply,Pi.sub_apply,Pi.smul_apply]
  unfold realLift
  rw [h,Matrix.mulVec_add]

private theorem realLift_sub (q : ℕ) (x y : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) → ℝ) :
    realLift q (x-y) = realLift q x-realLift q y := by
  have h : (fun c => ((x-y) c : ℂ)) = (fun c => (x c : ℂ))-(fun c => (y c : ℂ)) := by
    ext c; simp [Pi.add_apply,Pi.sub_apply,Pi.smul_apply]
  unfold realLift
  rw [h,Matrix.mulVec_sub]

private theorem realLift_smul (q : ℕ) (a : ℝ) (x : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) → ℝ) :
    realLift q (a • x) = (a:ℂ) • realLift q x := by
  have h : (fun c => ((a • x) c : ℂ)) = (a:ℂ) • (fun c => (x c : ℂ)) := by
    ext c; simp [Pi.add_apply,Pi.sub_apply,Pi.smul_apply]
  unfold realLift
  rw [h,Matrix.mulVec_smul]

private theorem layer_lift (q : ℕ) (hq : 2≤q) (m : Fin 3) (x : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) → ℝ) :
    (layerMoment q m).mulVec (realLift q x) =
      realLift q ((FiniteModel.projection (parameter q) m).mulVec x) := by
  unfold realLift
  rw [Matrix.mulVec_mulVec,layer_embedding q hq,← Matrix.mulVec_mulVec,complexify_mulVec]

private theorem total_lift (q : ℕ) (hq : 2≤q) (x : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) → ℝ) :
    (∑ m,layerMoment q m).mulVec (realLift q x) =
      realLift q ((FiniteModel.total (parameter q)).mulVec x) := by
  rw [Matrix.sum_mulVec]
  simp only [Fin.sum_univ_three,layer_lift q hq]
  rw [← FiniteModel.sum_projection]
  simp only [Fin.sum_univ_three,Matrix.add_mulVec,realLift_add]

private theorem walk_lift (q : ℕ) (hq : 2≤q) (k : ℕ) (x : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) → ℝ) :
    (Walk.sumWalk (layerMoment q) k).mulVec (realLift q x) =
      realLift q ((FiniteModel.walkSum (parameter q) k).mulVec x) := by
  induction k with
  | zero => simpa [Walk.sumWalk, Walk.endpoint,FiniteModel.walkSum,
      FiniteModel.sum_projection] using total_lift q hq x
  | succ k hk =>
    rw [Walk.sumWalk_succ (layerMoment q) (layer_idempotent q),
      ← Matrix.mulVec_mulVec,hk,Matrix.sub_mulVec,Matrix.one_mulVec,total_lift q hq,
      ← realLift_sub,FiniteModel.walk_recurrence,← Matrix.mulVec_mulVec,
      Matrix.sub_mulVec,Matrix.one_mulVec]

private theorem moment_lift (q : ℕ) (hq : 2≤q) (k : ℕ) (x : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) → ℝ) :
    (vecPhi q (k+1)).mulVec (realLift q x) =
      realLift q ((FiniteModel.moment (parameter q) k).mulVec x) := by
  rw [vecPhi_walk,Matrix.smul_mulVec,walk_lift q hq,FiniteModel.moment,
    Matrix.smul_mulVec,realLift_smul]
  simp

private theorem lift_inner (q : ℕ) (hq : 0<q) (x y : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) → ℝ) :
    star (realLift q x) ⬝ᵥ realLift q y =
      ((x ⬝ᵥ (FiniteModel.gram ((q:ℝ)⁻¹)).mulVec y : ℝ) : ℂ) := by
  unfold realLift
  rw [Matrix.star_mulVec,dotProduct_mulVec,Matrix.vecMul_vecMul,
    embedding_gram q hq]
  have hs : star ((fun c => (x c : ℂ))) = (fun c => (x c : ℂ)) := by ext c; simp [Pi.add_apply,Pi.sub_apply,Pi.smul_apply]
  rw [hs,← dotProduct_mulVec,complexify_mulVec]
  exact (RingHom.map_dotProduct Complex.ofRealHom x
    ((FiniteModel.gram ((q:ℝ)⁻¹)).mulVec y)).symm

private theorem witness_lift : realLift q FiniteModel.witness = physicalWitness q := by
  ext r
  simp [realLift,embedding,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,
    Fin.sum_univ_two,FiniteModel.witness,FiniteModel.antisym,basisVector,configBits,
    physicalWitness]
  ring

private theorem physical_quadratic (q : ℕ) (hq : 2≤q) (k : ℕ) :
    star (physicalWitness q) ⬝ᵥ (vecPhi q (k+1)).mulVec (physicalWitness q) =
      Complex.ofReal ((((1-2*(parameter q)^2)/3)*(-(parameter q)^2)^k)*
        (4*(1-((q:ℝ)⁻¹)^2)^2)) := by
  rw [← witness_lift,moment_lift q hq,lift_inner q (by omega),FiniteModel.moment_quadratic]

private theorem even_physical_quadratic_negative (q : ℕ) (hq : 2≤q) (m : ℕ) :
    (star (physicalWitness q) ⬝ᵥ (vecPhi q (2*m+2)).mulVec (physicalWitness q)).re < 0 := by
  have h := FiniteModel.even_quadratic_negative (q:ℝ) (by exact_mod_cast hq) m
  rw [FiniteModel.moment_quadratic] at h
  simpa only [physical_quadratic q hq (2*m+1),Complex.ofReal_re,parameter] using h

theorem result : claim := by
  intro q hq d hd he
  obtain ⟨m,hm⟩ := he
  have hm1 : 1≤m := by omega
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hm1
  have hdepth : d=2*k+2 := by omega
  rw [hdepth]
  intro hpsd
  have hnonneg := hpsd.dotProduct_mulVec_nonneg (physicalWitness q)
  have hreal : 0≤(star (physicalWitness q) ⬝ᵥ
      (vecPhi q (2*k+2)).mulVec (physicalWitness q)).re := hnonneg.1
  exact (not_lt_of_ge hreal) (even_physical_quadratic_negative q hq k)

end D5.S3.Quantum.RandomCircuits.PermutedBrickworkEvenRefutation

