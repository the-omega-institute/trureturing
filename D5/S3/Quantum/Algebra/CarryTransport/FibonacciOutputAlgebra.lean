/- GID: D5/S3/Quantum/Algebra/CarryTransport/FibonacciOutputAlgebra
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/CarryTransport/FibonacciOutputAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The maximal one-step low-output algebra of the actual Fibonacci carry transport. -/

import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.FixedAlgebra.RecordFixedAlgebraDecomposition
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix ComplexStarModule

namespace D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra

abbrev Labels (r : ℕ) := ZMod r × ZMod r
/-- The Hilbert space carries the Euclidean, rather than the supremum, norm. -/
abbrev Hilbert (r : ℕ) := EuclideanSpace ℂ (Labels r)

def fibonacci (r : ℕ) : Equiv.Perm (Labels r) where
  toFun x := (x.2, x.1 + x.2)
  invFun y := (y.2 - y.1, y.1)
  left_inv x := by ext <;> simp
  right_inv y := by ext <;> simp

/-- The canonical digit identification; no coprimality is required. -/
def digit (d e : ℕ) [NeZero d] [NeZero e] : ZMod d × ZMod e ≃ ZMod (d * e) where
  toFun p := (p.1.val + d * p.2.val : ℕ)
  invFun x := ((x.val : ZMod d), (x.val / d : ZMod e))
  left_inv p := by
    have hb : p.1.val + d * p.2.val < d * e := by
      have h₁ := p.1.val_lt
      have h₂ := p.2.val_lt
      nlinarith
    simp only [ZMod.val_natCast_of_lt hb]
    apply Prod.ext
    · simp
    · rw [Nat.add_mul_div_left _ _ (NeZero.pos d), Nat.div_eq_of_lt p.1.val_lt]
      simp
  right_inv x := by
    have hb : x.val / d < e := (Nat.div_lt_iff_lt_mul (NeZero.pos d)).mpr (by
      simpa [Nat.mul_comm] using x.val_lt)
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hb]
    rw [Nat.mod_add_div]
    exact ZMod.natCast_zmod_val x

def digitJoin (d e : ℕ) [NeZero d] [NeZero e] :
    Labels d × Labels e ≃ Labels (d * e) :=
  (Equiv.prodProdProdComm (ZMod d) (ZMod d) (ZMod e) (ZMod e)).trans
    (Equiv.prodCongr (digit d e) (digit d e))

/-- U_de transported through the specified x=a+d*h identification. -/
def transport (d e : ℕ) [NeZero d] [NeZero e] : Equiv.Perm (Labels d × Labels e) :=
  ((digitJoin d e).trans (fibonacci (d * e))).trans (digitJoin d e).symm

def carry (d : ℕ) (a : Labels d) : ℕ := (a.1.val + a.2.val) / d

def sector (d : ℕ) [NeZero d] (i : ℕ) : Submodule ℂ (Hilbert d) :=
  Submodule.span ℂ (Set.range fun a : {a : Labels d // carry d a = i} =>
    EuclideanSpace.basisFun (Labels d) ℂ a.1)

/-- Inverse permutation matrices implement the column-ket convention. -/
def lowUnitary (d : ℕ) [NeZero d] : Matrix (Labels d) (Labels d) ℂ :=
  Matrix.permMatrixHom (R := ℂ) (fibonacci d)

def jointUnitary (d e : ℕ) [NeZero d] [NeZero e] :
    Matrix (Labels d × Labels e) (Labels d × Labels e) ℂ :=
  Matrix.permMatrixHom (R := ℂ) (transport d e)

def lowTensor (d e : ℕ) [NeZero d] [NeZero e] :
    Matrix (Labels d) (Labels d) ℂ →ₐ[ℂ]
      Matrix (Labels d × Labels e) (Labels d × Labels e) ℂ where
  toFun B := B ⊗ₖ (1 : Matrix (Labels e) (Labels e) ℂ)
  map_zero' := by simp
  map_one' := by simp
  map_add' B C := by simp [Matrix.add_kronecker]
  map_mul' B C := by simp [← Matrix.mul_kronecker_mul]
  commutes' z := by
    ext ⟨a,h⟩ ⟨b,g⟩
    simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply,
      Matrix.kronecker_apply, Matrix.one_apply, Prod.ext_iff]
    split_ifs <;> simp_all

/-- Algebraic pullback, defined from the actual digit-transported permutation. -/
def pullback (d e : ℕ) [NeZero d] [NeZero e] :=
  (Matrix.reindexAlgEquiv ℂ ℂ (transport d e).symm).toAlgHom.comp (lowTensor d e)

/-- Operational definition: the actual pullback belongs to low operators tensor I. -/
def outputAlgebra (d e : ℕ) [NeZero d] [NeZero e] :
    Subalgebra ℂ (Matrix (Labels d) (Labels d) ℂ) :=
  (lowTensor d e).range.comap (pullback d e)

def alpha (d : ℕ) [NeZero d] :=
  Matrix.reindexAlgEquiv ℂ ℂ (fibonacci d).symm

/-- The actual real self-adjoint carrier of the operator-defined output algebra. -/
def selfAdjointOutput (d e : ℕ) [NeZero d] [NeZero e] :
    Submodule ℝ (Matrix (Labels d) (Labels d) ℂ) :=
  (outputAlgebra d e).toSubmodule.restrictScalars ℝ ⊓ selfAdjoint.submodule ℝ _

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation

def outputExpectation (d e : ℕ) [NeZero d] [NeZero e]
    (B : Matrix (Labels d) (Labels d) ℂ) (rho : DensityState (Labels d × Labels e)) : ℂ :=
  Matrix.trace ((lowTensor d e B) * jointUnitary d e *
    CStarMatrix.ofMatrix.symm rho.1 * (jointUnitary d e)ᴴ)

/-- The two actual carry fibers, in the computational basis. -/
def carryClass (d : ℕ) (a : Labels d) : Bool := decide (carry d a = 1)
abbrev SectorLabels (d : ℕ) (i : Bool) := {a : Labels d // carryClass d a = i}
abbrev Blocks (d : ℕ) [NeZero d] :=
  ∀ i : Bool, Matrix (SectorLabels d i) (SectorLabels d i) ℂ

/-- The full sector matrix algebras, embedded by the canonical fiber identification. -/
def blockEmbedding (d : ℕ) [NeZero d] : Blocks d →ₐ[ℂ] Matrix (Labels d) (Labels d) ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ (Equiv.sigmaFiberEquiv (carryClass d))).toAlgHom.comp
    (D5.S3.Quantum.FixedAlgebra.RecordFixedAlgebraDecomposition.blockDiagonalAlgHom
      (SectorLabels d))

def conjugatedBlocks (d : ℕ) [NeZero d] : Subalgebra ℂ (Matrix (Labels d) (Labels d) ℂ) :=
  (blockEmbedding d).range.map (alpha d).symm.toAlgHom

/-- Complete source Theorem 3.2, including physical maximality and the actual-carrier dimensions. -/
theorem result (d e : ℕ) (hd : 2 ≤ d) (he : 2 ≤ e) :
    letI : NeZero d := ⟨by omega⟩
    letI : NeZero e := ⟨by omega⟩
    (∀ a h, transport d e (a,h) =
      (fibonacci d a, (h.2, h.1 + h.2 + (carry d a : ZMod e)))) ∧
    (∀ B : Matrix (Labels d) (Labels d) ℂ,
      B ∈ outputAlgebra d e ↔
        ∀ a b, carry d a ≠ carry d b → alpha d B a b = 0) ∧
    (∀ B ∈ outputAlgebra d e,
      (jointUnitary d e)ᴴ * lowTensor d e B * jointUnitary d e =
        lowTensor d e (alpha d B)) ∧
    (∀ B : Matrix (Labels d) (Labels d) ℂ,
      B ∈ outputAlgebra d e ↔ ∃ F : DensityState (Labels d) → ℂ,
        ∀ rho : DensityState (Labels d × Labels e),
          outputExpectation d e B rho = F (marginalRight rho)) ∧
    (∀ B : Matrix (Labels d) (Labels d) ℂ,
      alpha d B = (lowUnitary d)ᴴ * B * lowUnitary d) ∧
    outputAlgebra d e = conjugatedBlocks d ∧
    Module.finrank ℂ (sector d 0) = d*(d+1)/2 ∧
    Module.finrank ℂ (sector d 1) = d*(d-1)/2 ∧
    Module.finrank ℂ (outputAlgebra d e) = d^2*(d^2+1)/2 ∧
    Module.finrank ℝ (selfAdjointOutput d e) = d^2*(d^2+1)/2 := by
  classical
  letI : NeZero d := ⟨by omega⟩
  letI : NeZero e := ⟨by omega⟩
  haveI : Fact (1 < e) := ⟨by omega⟩
  have hscale (n : ℕ) :
      ((d : ℕ) : ZMod (d*e)) * ((n % e : ℕ) : ZMod (d*e)) =
        (d : ZMod (d*e)) * (n : ZMod (d*e)) := by
    have hz : (d : ZMod (d*e)) * (e : ZMod (d*e)) = 0 := by
      rw [← Nat.cast_mul, ZMod.natCast_self]
    conv_rhs => rw [← Nat.mod_add_div n e]
    push_cast
    rw [mul_add, ← mul_assoc, hz, zero_mul, add_zero]
  have hjoin (a : Labels d) (h : Labels e) :
      digitJoin d e (fibonacci d a, (h.2, h.1+h.2+(carry d a : ZMod e))) =
        fibonacci (d*e) (digitJoin d e (a,h)) := by
    apply Prod.ext
    · rfl
    · change (((a.1+a.2).val + d * (h.1+h.2+(carry d a : ZMod e)).val : ℕ) :
          ZMod (d*e)) =
        ((a.1.val+d*h.1.val : ℕ) : ZMod (d*e)) +
          ((a.2.val+d*h.2.val : ℕ) : ZMod (d*e))
      rw [ZMod.val_add]
      have hh : h.1+h.2+(carry d a : ZMod e) =
          ((h.1.val+h.2.val+carry d a : ℕ) : ZMod e) := by simp
      rw [hh, ZMod.val_natCast]
      push_cast
      rw [hscale]
      have hs := congrArg (fun n : ℕ => (n : ZMod (d*e)))
        (Nat.mod_add_div (a.1.val+a.2.val) d)
      dsimp [carry] at *
      push_cast at hs
      push_cast
      linear_combination hs
  have hact (a : Labels d) (h : Labels e) :
      transport d e (a,h) =
        (fibonacci d a, (h.2, h.1+h.2+(carry d a : ZMod e))) := by
    apply (digitJoin d e).injective
    simpa [transport] using (hjoin a h).symm
  have hk (a : Labels d) : carry d a = 0 ∨ carry d a = 1 := by
    have h₁ := a.1.val_lt
    have h₂ := a.2.val_lt
    have hh : a.1.val + a.2.val < 2*d := by omega
    have hh' : (a.1.val+a.2.val) / d < 2 :=
      (Nat.div_lt_iff_lt_mul (NeZero.pos d)).mpr hh
    change (a.1.val+a.2.val) / d = 0 ∨ (a.1.val+a.2.val) / d = 1
    generalize (a.1.val+a.2.val) / d = n at hh' ⊢
    omega
  have hkinj {a b : Labels d} (h : carry d a ≠ carry d b) :
      (carry d a : ZMod e) ≠ (carry d b : ZMod e) := by
    rcases hk a with ha | ha <;> rcases hk b with hb | hb
    all_goals simp_all
  have hentry (B : Matrix (Labels d) (Labels d) ℂ) (a b : Labels d) (h g : Labels e) :
      pullback d e B (a,h) (b,g) =
        B (fibonacci d a) (fibonacci d b) *
          if (h.2, h.1+h.2+(carry d a : ZMod e)) =
            (g.2, g.1+g.2+(carry d b : ZMod e)) then 1 else 0 := by
    change (lowTensor d e B) (transport d e (a,h)) (transport d e (b,g)) = _
    rw [hact, hact]
    rfl
  have hconj (B : Matrix (Labels d) (Labels d) ℂ) :
      (jointUnitary d e)ᴴ * lowTensor d e B * jointUnitary d e = pullback d e B := by
    simp only [jointUnitary, Matrix.permMatrixHom_apply, Matrix.conjTranspose_permMatrix,
      inv_inv, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
      PEquiv.mul_toMatrix_toPEquiv]
    rfl
  have halpha (B : Matrix (Labels d) (Labels d) ℂ) :
      alpha d B = (lowUnitary d)ᴴ * B * lowUnitary d := by
    symm
    simp only [lowUnitary, Matrix.permMatrixHom_apply, Matrix.conjTranspose_permMatrix,
      inv_inv, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
      PEquiv.mul_toMatrix_toPEquiv]
    rfl
  have hfrom (B : Matrix (Labels d) (Labels d) ℂ)
      (hB : ∀ a b, carry d a ≠ carry d b → alpha d B a b = 0) :
      lowTensor d e (alpha d B) = pullback d e B := by
    ext ⟨a,h⟩ ⟨b,g⟩
    symm
    rw [hentry]
    change (alpha d B) a b * (if _ then 1 else 0) =
      (alpha d B) a b * (1 : Matrix (Labels e) (Labels e) ℂ) h g
    by_cases hk : carry d a = carry d b
    · have hh : (h.2,h.1+h.2+(carry d a : ZMod e)) =
          (g.2,g.1+g.2+(carry d b : ZMod e)) ↔ h = g := by
        rw [hk]
        constructor
        · intro hp
          have hp₁ := congrArg Prod.fst hp
          have hp₂ := congrArg Prod.snd hp
          apply Prod.ext
          · dsimp at hp₁ hp₂
            rw [hp₁] at hp₂
            exact add_right_cancel (add_right_cancel hp₂)
          · exact hp₁
        · rintro rfl; rfl
      simp only [hh, Matrix.one_apply]
    · rw [hB a b hk]
      simp
  have hchar (B : Matrix (Labels d) (Labels d) ℂ) :
      B ∈ outputAlgebra d e ↔
        ∀ a b, carry d a ≠ carry d b → alpha d B a b = 0 := by
    constructor
    · intro hB a b hab
      change ∃ C, lowTensor d e C = pullback d e B at hB
      obtain ⟨C,hC⟩ := hB
      have hc := congrArg (fun X : Matrix (Labels d × Labels e) _ ℂ =>
        X (a, ((carry d b : ZMod e),0)) (b, ((carry d a : ZMod e),0))) hC
      change lowTensor d e C (a, ((carry d b : ZMod e),0))
        (b, ((carry d a : ZMod e),0)) =
        pullback d e B (a, ((carry d b : ZMod e),0))
          (b, ((carry d a : ZMod e),0)) at hc
      rw [hentry] at hc
      have hh : (((carry d b : ZMod e),0) : Labels e) ≠ ((carry d a : ZMod e),0) := by
        intro hh
        exact hkinj hab (congrArg Prod.fst hh).symm
      simpa [lowTensor, Matrix.kronecker_apply, Matrix.one_apply, hh,
        add_comm, alpha, Matrix.reindexAlgEquiv, Matrix.reindex_apply] using hc.symm
    · intro hB
      change ∃ C, lowTensor d e C = pullback d e B
      exact ⟨alpha d B, hfrom B hB⟩
  have hpull (B : Matrix (Labels d) (Labels d) ℂ) (hB : B ∈ outputAlgebra d e) :
      (jointUnitary d e)ᴴ * lowTensor d e B * jointUnitary d e =
        lowTensor d e (alpha d B) :=
    (hconj B).trans (hfrom B ((hchar B).mp hB)).symm
  have hexpect (B : Matrix (Labels d) (Labels d) ℂ)
      (rho : DensityState (Labels d × Labels e)) :
      outputExpectation d e B rho =
        Matrix.trace (pullback d e B * CStarMatrix.ofMatrix.symm rho.1) := by
    rw [outputExpectation, Matrix.trace_mul_comm _ (jointUnitary d e)ᴴ]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hconj]
  have hphysical {a b : Labels d} (hab : carry d a ≠ carry d b)
      (B : Matrix (Labels d) (Labels d) ℂ) (hx : alpha d B a b ≠ 0) :
      ∃ rho sigma : DensityState (Labels d × Labels e),
        marginalRight rho = marginalRight sigma ∧
          outputExpectation d e B rho ≠ outputExpectation d e B sigma := by
    let p : Labels d × Labels e := (a, ((carry d b : ZMod e),0))
    let q : Labels d × Labels e := (b, ((carry d a : ZMod e),0))
    have hpq : p ≠ q := by
      intro hh
      exact hab (congrArg (carry d) (congrArg Prod.fst hh))
    have hpqh : p.2 ≠ q.2 := by
      intro hh
      exact hkinj hab (congrArg Prod.fst hh).symm
    let v (t : ℂ) : Labels d × Labels e → ℂ := Pi.single p 1 + Pi.single q t
    let mat (t : ℂ) : Matrix (Labels d × Labels e) _ ℂ :=
      (1/2 : ℝ) • Matrix.vecMulVec (v t) (star (v t))
    have htrace (t : ℂ) (ht : star t * t = 1) : Matrix.trace (mat t) = 1 := by
      change Matrix.trace ((1/2 : ℝ) • Matrix.vecMulVec (v t) (star (v t))) = 1
      rw [Matrix.trace_smul, Matrix.trace_vecMulVec]
      simp only [v, star_add, add_dotProduct, dotProduct_add]
      have ht' : t * star t = 1 := by simpa [mul_comm] using ht
      simp only [Pi.star_single, single_dotProduct, Pi.single_apply,
        if_pos rfl, if_neg hpq, if_neg (Ne.symm hpq), one_mul, zero_mul, add_zero, zero_add]
      simp only [if_true, star_one, mul_zero, add_zero]
      rw [ht']
      norm_num
    let state (t : ℂ) (ht : star t * t = 1) : DensityState (Labels d × Labels e) :=
      ⟨CStarMatrix.ofMatrix (mat t),
        map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
          ((Matrix.posSemidef_vecMulVec_self_star (v t)).smul
            (by norm_num : (0 : ℝ) ≤ 1/2)).nonneg,
        htrace t ht⟩
    have hdiff (t : ℂ) (ht : star t * t = 1) :
        mat t - mat (-t) =
          (t • Matrix.single q p 1) + (star t • Matrix.single p q 1) := by
      ext i j
      simp only [mat, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
        Pi.star_apply, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one,
        Complex.ofReal_ofNat]
      by_cases hip : i = p <;> by_cases hiq : i = q <;>
        by_cases hjp : j = p <;> by_cases hjq : j = q
      all_goals simp [v, Pi.single_apply, Matrix.single_apply, hip, hiq, hjp, hjq,
        Matrix.smul_apply, Matrix.add_apply, hpq, Ne.symm hpq, eq_comm] <;> ring
    have hmarg (t : ℂ) (ht : star t * t = 1) :
        marginalRight (state t ht) = marginalRight (state (-t) (by simpa using ht)) := by
      apply Subtype.ext
      apply congrArg CStarMatrix.ofMatrix
      change partialTraceRight (mat t) = partialTraceRight (mat (-t))
      apply sub_eq_zero.mp
      have hsub : partialTraceRight (mat t) - partialTraceRight (mat (-t)) =
          partialTraceRight (mat t - mat (-t)) := by
        ext i j
        simp [partialTraceRight, Finset.sum_sub_distrib]
      rw [hsub, hdiff t ht]
      ext i j
      have hsum (h : Labels e) :
          ((t • Matrix.single q p 1 + star t • Matrix.single p q 1) :
            Matrix (Labels d × Labels e) (Labels d × Labels e) ℂ) (i,h) (j,h) = 0 := by
        have h₁ : ¬ ((i,h) = q ∧ (j,h) = p) := by
          rintro ⟨hq,hp⟩
          have hhp : h = p.2 := congrArg Prod.snd hp
          have hhq : h = q.2 := congrArg Prod.snd hq
          exact hpqh (hhp.symm.trans hhq)
        have h₂ : ¬ ((i,h) = p ∧ (j,h) = q) := by
          rintro ⟨hp,hq⟩
          have hhp : h = p.2 := congrArg Prod.snd hp
          have hhq : h = q.2 := congrArg Prod.snd hq
          exact hpqh (hhp.symm.trans hhq)
        simp [Matrix.single_apply, h₁, h₂, Matrix.add_apply, Matrix.smul_apply, eq_comm]
      exact Finset.sum_eq_zero (fun h _ => hsum h)
    have hsep (t : ℂ) (ht : star t * t = 1) :
        outputExpectation d e B (state t ht) -
          outputExpectation d e B (state (-t) (by simpa using ht)) =
            t * alpha d B a b + star t * alpha d B b a := by
      rw [hexpect, hexpect]
      change Matrix.trace (pullback d e B * mat t) -
        Matrix.trace (pullback d e B * mat (-t)) = _
      rw [← Matrix.trace_sub, ← Matrix.mul_sub, hdiff t ht]
      simp only [Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul, Matrix.trace_smul]
      have hs (i j : Labels d × Labels e) :
          Matrix.trace (pullback d e B * Matrix.single i j 1) = pullback d e B j i := by
        simp [Matrix.trace_mul_single]
      rw [hs, hs, hentry, hentry]
      simp [p, q, alpha, Matrix.reindexAlgEquiv, Matrix.reindex_apply, add_comm,
        mul_comm]
    by_cases hh : alpha d B a b + alpha d B b a = 0
    · refine ⟨state Complex.I (by simp), state (-Complex.I) (by simp),
        hmarg Complex.I (by simp), ?_⟩
      intro heq
      have hzero := hsep Complex.I (by simp)
      rw [heq, sub_self] at hzero
      have hy : alpha d B b a = -alpha d B a b := by linear_combination hh
      rw [hy] at hzero
      simp only [Complex.star_def, Complex.conj_I] at hzero
      have hz : (2*Complex.I) * alpha d B a b = 0 := by linear_combination -hzero
      exact hx ((mul_eq_zero.mp hz).resolve_left (by norm_num))
    · refine ⟨state 1 (by simp), state (-1) (by simp), hmarg 1 (by simp), ?_⟩
      intro heq
      have hzero := hsep 1 (by simp)
      rw [heq, sub_self] at hzero
      exact hh (by simpa using hzero.symm)
  have hoperational : ∀ B : Matrix (Labels d) (Labels d) ℂ,
      B ∈ outputAlgebra d e ↔ ∃ F : DensityState (Labels d) → ℂ,
        ∀ rho : DensityState (Labels d × Labels e),
          outputExpectation d e B rho = F (marginalRight rho) := by
    intro B
    constructor
    · intro hB
      refine ⟨fun tau => Matrix.trace (alpha d B * CStarMatrix.ofMatrix.symm tau.1), ?_⟩
      intro rho
      rw [hexpect, ← hfrom B ((hchar B).mp hB)]
      change Matrix.trace ((alpha d B ⊗ₖ (1 : Matrix (Labels e) _ ℂ)) *
        CStarMatrix.ofMatrix.symm rho.1) =
        Matrix.trace (alpha d B * partialTraceRight (CStarMatrix.ofMatrix.symm rho.1))
      let R : Matrix (Labels d × Labels e) _ ℂ := CStarMatrix.ofMatrix.symm rho.1
      change (∑ p : Labels d × Labels e,
        ∑ q : Labels d × Labels e, (alpha d B) p.1 q.1 *
          (if p.2 = q.2 then 1 else 0) * R q p) =
        ∑ a : Labels d, ∑ b : Labels d, (alpha d B) a b * ∑ h : Labels e, R (b,h) (a,h)
      rw [Fintype.sum_prod_type (fun p : Labels d × Labels e =>
        ∑ q : Labels d × Labels e, (alpha d B) p.1 q.1 *
          (if p.2 = q.2 then 1 else 0) * R q p)]
      have hsum (a : Labels d) (h : Labels e) :
          (∑ q : Labels d × Labels e, (alpha d B) a q.1 *
            (if h = q.2 then 1 else 0) * R q (a,h)) =
          ∑ b : Labels d, (alpha d B) a b * R (b,h) (a,h) := by
        rw [Fintype.sum_prod_type (fun q : Labels d × Labels e =>
          (alpha d B) a q.1 * (if h = q.2 then 1 else 0) * R q (a,h))]
        simp [mul_ite, ite_mul]
      simp_rw [hsum]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    · rintro ⟨F,hF⟩
      by_contra hB
      have hnot := mt (hchar B).mpr hB
      push_neg at hnot
      obtain ⟨a,b,hab,hx⟩ := hnot
      obtain ⟨rho,sigma,hm,hs⟩ := hphysical hab B hx
      exact hs ((hF rho).trans (hm ▸ (hF sigma).symm))
  have hkey (a : Labels d) (i : Bool) :
      carryClass d a = i ↔ carry d a = if i then 1 else 0 := by
    cases i <;> simp [carryClass, hk a]
    rcases hk a with h | h <;> simp [h]
  have hkeyeq (a b : Labels d) : carryClass d a = carryClass d b ↔ carry d a = carry d b := by
    constructor
    · intro h
      have ha := (hkey a (carryClass d a)).mp rfl
      have hb := (hkey b (carryClass d b)).mp rfl
      rw [h] at ha
      exact ha.trans hb.symm
    · rintro h
      simp [carryClass, h]
  have hblocks (B : Matrix (Labels d) (Labels d) ℂ) :
      B ∈ (blockEmbedding d).range ↔
        ∀ a b, carry d a ≠ carry d b → B a b = 0 := by
    constructor
    · rintro ⟨blocks,rfl⟩ a b hab
      have hkeyne : carryClass d a ≠ carryClass d b := mt (hkeyeq a b).mp hab
      change Matrix.blockDiagonal' blocks
        ⟨carryClass d a, a, rfl⟩ ⟨carryClass d b, b, rfl⟩ = 0
      simp [Matrix.blockDiagonal'_apply, hkeyne]
    · intro hB
      let blocks : Blocks d := fun i a b => B a.1 b.1
      refine ⟨blocks, ?_⟩
      ext a b
      change Matrix.blockDiagonal' blocks
        ⟨carryClass d a, a, rfl⟩ ⟨carryClass d b, b, rfl⟩ = B a b
      by_cases h : carryClass d a = carryClass d b
      · let bb : SectorLabels d (carryClass d a) := ⟨b,h.symm⟩
        have hbb : (⟨carryClass d b, b, rfl⟩ : Sigma (SectorLabels d)) =
            ⟨carryClass d a, bb⟩ := by
          apply (Equiv.sigmaFiberEquiv (carryClass d)).injective
          rfl
        rw [hbb, Matrix.blockDiagonal'_apply_eq]
      · rw [hB a b (mt (hkeyeq a b).mpr h)]
        simp [Matrix.blockDiagonal'_apply, h]
  have heq : outputAlgebra d e = conjugatedBlocks d := by
    ext B
    rw [hchar]
    change (∀ a b, carry d a ≠ carry d b → alpha d B a b = 0) ↔
      B ∈ (blockEmbedding d).range.map (alpha d).symm.toAlgHom
    rw [← hblocks]
    constructor
    · intro h
      exact ⟨alpha d B, h, (alpha d).symm_apply_apply B⟩
    · rintro ⟨C,hC,h⟩
      have hh : alpha d B = C := by rw [← h]; exact (alpha d).apply_symm_apply C
      exact hh ▸ hC
  have hcard1 : Fintype.card (SectorLabels d true) = d*(d-1)/2 := by
    let E : Labels d ≃ Fin d × Fin d :=
      (Equiv.prodComm (ZMod d) (ZMod d)).trans
        (Equiv.prodCongr ((ZMod.finEquiv d).symm.toEquiv.trans Fin.revPerm)
          (ZMod.finEquiv d).symm.toEquiv)
    have hpred (a : Labels d) : carryClass d a = true ↔ (E a).1 < (E a).2 := by
      rw [hkey a true]
      have h₁ := a.1.val_lt
      have h₂ := a.2.val_lt
      have hdiv : carry d a = 1 ↔ d ≤ a.1.val+a.2.val := by
        rcases hk a with h | h
        · simp [h]
          dsimp [carry] at h
          have hz : a.1.val+a.2.val < d := (Nat.div_eq_zero_iff.mp h).resolve_left (NeZero.ne d)
          omega
        · simp [h]
          dsimp [carry] at h
          have hlo := (Nat.le_div_iff_mul_le (NeZero.pos d)).mp (show 1 ≤
            (a.1.val+a.2.val)/d by omega)
          omega
      simp only [if_true] 
      rw [hdiv]
      have hv (z : ZMod d) : ((ZMod.finEquiv d).symm z).val = z.val := by
        cases d with
        | zero => exact (NeZero.ne 0 rfl).elim
        | succ n => rfl
      change d ≤ a.1.val+a.2.val ↔
        ((ZMod.finEquiv d).symm a.2).rev.val < ((ZMod.finEquiv d).symm a.1).val
      simp only [Fin.val_rev, hv]
      omega
    have hc := Fintype.card_congr (E.subtypeEquiv
      (p := fun a => carryClass d a = true)
      (q := fun x : Fin d × Fin d => x.1 < x.2) hpred)
    rw [hc, Fintype.card_subtype]
    have hf : (Finset.univ.filter fun a : Fin d × Fin d => a.1 < a.2).card =
        (Finset.univ : Finset (Fin d)).card.choose 2 := by
      simpa [Finset.univ_product_univ] using
        (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin d))))
    rw [hf]
    simp [Nat.choose_two_right]
  have hcard0 : Fintype.card (SectorLabels d false) = d*(d+1)/2 := by
    have hc : Fintype.card (SectorLabels d false) =
        Fintype.card (Labels d) - Fintype.card (SectorLabels d true) := by
      have hh (a : Labels d) : carryClass d a = false ↔ ¬ carryClass d a = true := by
        cases carryClass d a <;> simp
      exact (Fintype.card_congr (Equiv.subtypeEquivRight hh)).trans
        (Fintype.card_subtype_compl (fun a => carryClass d a = true))
    rw [hc, hcard1]
    simp only [Labels, Fintype.card_prod, ZMod.card]
    have hpar : 2 ∣ d*(d-1) := (Nat.even_mul_pred_self d).two_dvd
    have hpar' : 2 ∣ d*(d+1) := (Nat.even_mul_succ_self d).two_dvd
    have h₀ := Nat.div_mul_cancel hpar'
    have h₁ := Nat.div_mul_cancel hpar
    have hdsub : d-1+1=d := by omega
    have hb : d*(d-1)/2 ≤ d*d := by
      have hb' := Nat.div_le_self (d*(d-1)) 2
      nlinarith
    have hsub := Nat.sub_add_cancel hb
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2)
    nlinarith
  have hsector (i : Bool) : Module.finrank ℂ (sector d (if i then 1 else 0)) =
      Fintype.card (SectorLabels d i) := by
    have hi := (EuclideanSpace.basisFun (Labels d) ℂ).toBasis.linearIndependent.comp
      (fun a : SectorLabels d i => a.1) Subtype.val_injective
    have hs : Set.range (fun a : SectorLabels d i =>
        EuclideanSpace.basisFun (Labels d) ℂ a.1) =
      Set.range (fun a : {a : Labels d // carry d a = if i then 1 else 0} =>
        EuclideanSpace.basisFun (Labels d) ℂ a.1) := by
      ext x
      constructor
      · rintro ⟨a,rfl⟩
        exact ⟨⟨a.1, (hkey a.1 i).mp a.2⟩, rfl⟩
      · rintro ⟨a,rfl⟩
        exact ⟨⟨a.1, (hkey a.1 i).mpr a.2⟩, rfl⟩
    change Module.finrank ℂ (Submodule.span ℂ _) = _
    rw [← hs]
    exact finrank_span_eq_card hi
  let hom : Blocks d →ₐ[ℂ] Matrix (Labels d) (Labels d) ℂ :=
    (alpha d).symm.toAlgHom.comp (blockEmbedding d)
  have hinj : Function.Injective hom := by
    intro X Y h
    apply Matrix.blockDiagonal'_injective
    apply (Matrix.reindexAlgEquiv ℂ ℂ (Equiv.sigmaFiberEquiv (carryClass d))).injective
    apply (alpha d).symm.injective
    exact h
  have hrange : hom.range = outputAlgebra d e := by
    rw [heq]
    exact AlgHom.range_comp _ _
  let E := (AlgEquiv.ofBijective hom.rangeRestrict
    ⟨fun X Y h => hinj (congrArg Subtype.val h),
      fun B => by obtain ⟨X,hX⟩ := B.2; exact ⟨X, Subtype.ext hX⟩⟩).trans
      (Subalgebra.equivOfEq _ _ hrange)
  have hdim : Module.finrank ℂ (outputAlgebra d e) =
      Fintype.card (SectorLabels d false)^2 + Fintype.card (SectorLabels d true)^2 := by
    rw [← E.toLinearEquiv.finrank_eq]
    rw [Module.finrank_pi_fintype]
    simp [Module.finrank_matrix, sq, add_comm]
  have hdim' : Module.finrank ℂ (outputAlgebra d e) = d^2*(d^2+1)/2 := by
    rw [hdim, hcard0, hcard1]
    have hpar : 2 ∣ d*(d-1) := (Nat.even_mul_pred_self d).two_dvd
    have hpar' : 2 ∣ d*(d+1) := (Nat.even_mul_succ_self d).two_dvd
    have h₀ := Nat.div_mul_cancel hpar'
    have h₁ := Nat.div_mul_cancel hpar
    have hs₀ := congrArg (fun n : ℕ => n^2) h₀
    have hs₁ := congrArg (fun n : ℕ => n^2) h₁
    have hsub : d-1+1=d := by omega
    have ht : ((d*(d+1)/2)^2+(d*(d-1)/2)^2)*2 = d^2*(d^2+1) := by
      have h₀Q : ((d*(d+1)/2 : ℕ) : ℚ)*2 = (d:ℚ)*(d+1) := by exact_mod_cast h₀
      have h₁Q : ((d*(d-1)/2 : ℕ) : ℚ)*2 = (d:ℚ)*(d-1) := by
        have hh := congrArg (fun n : ℕ => (n:ℚ)) h₁
        push_cast [Nat.cast_sub (by omega : 1 ≤ d)] at hh
        exact hh
      have hs₀Q := congrArg (fun n : ℚ => n^2) h₀Q
      have hs₁Q := congrArg (fun n : ℚ => n^2) h₁Q
      have htQ : (((d*(d+1)/2 : ℕ):ℚ)^2+((d*(d-1)/2 : ℕ):ℚ)^2)*2 =
          (d:ℚ)^2*((d:ℚ)^2+1) := by
        linear_combination (1/2 : ℚ)*hs₀Q + (1/2 : ℚ)*hs₁Q
      exact_mod_cast htQ
    have hdiv := Nat.div_mul_cancel (Nat.even_mul_succ_self (d^2)).two_dvd
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2)
    exact ht.trans hdiv.symm
  have hstar (B : Matrix (Labels d) (Labels d) ℂ) (hB : B ∈ outputAlgebra d e) :
      star B ∈ outputAlgebra d e := by
    apply (hchar (star B)).mpr
    intro a b hab
    change star (B (fibonacci d b) (fibonacci d a)) = 0
    have hh := (hchar B).mp hB b a (Ne.symm hab)
    change B (fibonacci d b) (fibonacci d a) = 0 at hh
    rw [hh, star_zero]
  have hreal (B : Matrix (Labels d) (Labels d) ℂ) (hB : B ∈ outputAlgebra d e) :
      (ℜ B : Matrix (Labels d) (Labels d) ℂ) ∈ outputAlgebra d e := by
    rw [realPart_apply_coe]
    exact ((outputAlgebra d e).toSubmodule.restrictScalars ℝ).smul_mem _
      ((outputAlgebra d e).add_mem hB (hstar B hB))
  have himag (B : Matrix (Labels d) (Labels d) ℂ) (hB : B ∈ outputAlgebra d e) :
      (ℑ B : Matrix (Labels d) (Labels d) ℂ) ∈ outputAlgebra d e := by
    rw [imaginaryPart_apply_coe]
    exact (outputAlgebra d e).toSubmodule.smul_mem _
      (((outputAlgebra d e).toSubmodule.restrictScalars ℝ).smul_mem _
        ((outputAlgebra d e).sub_mem hB (hstar B hB)))
  let pair : (outputAlgebra d e) ≃ₗ[ℝ]
      selfAdjointOutput d e × selfAdjointOutput d e := {
    toFun := fun X => (⟨(ℜ X.1 : Matrix (Labels d) (Labels d) ℂ), hreal X.1 X.2, (ℜ X.1).2⟩,
      ⟨(ℑ X.1 : Matrix (Labels d) (Labels d) ℂ), himag X.1 X.2, (ℑ X.1).2⟩)
    invFun := fun X => ⟨X.1.1 + Complex.I • X.2.1,
      (outputAlgebra d e).add_mem X.1.2.1
        ((outputAlgebra d e).toSubmodule.smul_mem _ X.2.2.1)⟩
    left_inv := fun X => Subtype.ext (realPart_add_I_smul_imaginaryPart X.1)
    right_inv := by
      intro X
      have hx : IsSelfAdjoint X.1.1 := X.1.2.2
      have hy : IsSelfAdjoint X.2.1 := X.2.2.2
      apply Prod.ext
      · apply Subtype.ext
        change (ℜ (X.1.1 + Complex.I • X.2.1) : Matrix (Labels d) (Labels d) ℂ) = X.1.1
        rw [(realPart (A := Matrix (Labels d) (Labels d) ℂ)).map_add, realPart_smul]
        simp [hx.coe_realPart, congrArg Subtype.val hy.imaginaryPart]
      · apply Subtype.ext
        change (ℑ (X.1.1 + Complex.I • X.2.1) : Matrix (Labels d) (Labels d) ℂ) = X.2.1
        rw [(imaginaryPart (A := Matrix (Labels d) (Labels d) ℂ)).map_add, imaginaryPart_smul]
        simp [congrArg Subtype.val hx.imaginaryPart, hy.coe_realPart]
    map_add' := by
      intro X Y
      apply Prod.ext <;> apply Subtype.ext
      · change (ℜ (X.1+Y.1) : Matrix (Labels d) (Labels d) ℂ) =
          (ℜ X.1 : Matrix (Labels d) (Labels d) ℂ) + (ℜ Y.1 : Matrix (Labels d) (Labels d) ℂ)
        exact congrArg (fun Z : selfAdjoint (Matrix (Labels d) (Labels d) ℂ) => Z.1)
          ((realPart (A := Matrix (Labels d) (Labels d) ℂ)).map_add X.1 Y.1)
      · change (ℑ (X.1+Y.1) : Matrix (Labels d) (Labels d) ℂ) =
          (ℑ X.1 : Matrix (Labels d) (Labels d) ℂ) + (ℑ Y.1 : Matrix (Labels d) (Labels d) ℂ)
        exact congrArg (fun Z : selfAdjoint (Matrix (Labels d) (Labels d) ℂ) => Z.1)
          ((imaginaryPart (A := Matrix (Labels d) (Labels d) ℂ)).map_add X.1 Y.1)
    map_smul' := by
      intro r X
      apply Prod.ext <;> apply Subtype.ext
      · change (ℜ (r • X.1) : Matrix (Labels d) (Labels d) ℂ) = r • (ℜ X.1 : Matrix (Labels d) (Labels d) ℂ)
        exact congrArg (fun Z : selfAdjoint (Matrix (Labels d) (Labels d) ℂ) => Z.1)
          ((realPart (A := Matrix (Labels d) (Labels d) ℂ)).map_smul r X.1)
      · change (ℑ (r • X.1) : Matrix (Labels d) (Labels d) ℂ) = r • (ℑ X.1 : Matrix (Labels d) (Labels d) ℂ)
        exact congrArg (fun Z : selfAdjoint (Matrix (Labels d) (Labels d) ℂ) => Z.1)
          ((imaginaryPart (A := Matrix (Labels d) (Labels d) ℂ)).map_smul r X.1) }
  have hpair := pair.finrank_eq
  rw [Module.finrank_prod] at hpair
  have htower := Module.finrank_mul_finrank ℝ ℂ (outputAlgebra d e)
  rw [Complex.finrank_real_complex] at htower
  have hsa : Module.finrank ℝ (selfAdjointOutput d e) =
      Module.finrank ℂ (outputAlgebra d e) := by omega
  exact ⟨hact,hchar,hpull,hoperational,halpha,heq,
    (hsector false).trans hcard0, (hsector true).trans hcard1, hdim', hsa.trans hdim'⟩

#print axioms Labels
#print axioms Hilbert
#print axioms fibonacci
#print axioms digit
#print axioms digitJoin
#print axioms transport
#print axioms carry
#print axioms sector
#print axioms lowUnitary
#print axioms jointUnitary
#print axioms lowTensor
#print axioms pullback
#print axioms outputAlgebra
#print axioms alpha
#print axioms selfAdjointOutput
#print axioms outputExpectation
#print axioms carryClass
#print axioms SectorLabels
#print axioms Blocks
#print axioms blockEmbedding
#print axioms conjugatedBlocks
#print axioms result

end D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra
