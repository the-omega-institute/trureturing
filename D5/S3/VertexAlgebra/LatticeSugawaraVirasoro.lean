/- GID: D5/S3/VertexAlgebra/LatticeSugawaraVirasoro
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeSugawaraVirasoro
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual all-charge matrix Sugawara modes satisfy Virasoro with central charge equal to rank. -/

/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the repository root LICENSE.
Authors of the upstream Sugawara architecture: Kalle Kytölä
Modified source: the statewise normal-ordering and commutator architecture of
VirasoroProject revision 5ff4245383b2cdd4eea7a0524bc1274c32041eb4 is adapted
here to the actual matrix lattice currents and every integral charge sector.
The charged-ground cancellation, inverse-Gram trace and actual translation
identification concern the existing lattice carrier, without a Fock transfer.
Classical source: Bakalov--Kac, Twisted Modules over Lattice Vertex Algebras,
arXiv math/0402315v1, section 4.1, equations (4.12)--(4.16).

proof_shape: centralDefect_ground_diagonal: content
proof_shape: sugawaraMode_virasoro: content
admission_basis: escape-witness
escape_witness: Sectorwise scalarity and weighted Euler reduce the actual
defect to the diagonal; evaluating it on each charged ground cancels both
charge boundary terms and computes the inverse-Gram rank cubic.
proof_shape: ground_frequency_bound: bind-only; consumed by
sugawaraMode_ground_positive, centralDefect_ground_diagonal and
sugawaraMode_ground_minus_one
proof_shape: neutralMode_zero_single: bind-only; consumed by
sugawaraMode_ground_zero, centralDefect_ground_diagonal and
sugawaraMode_ground_minus_one
The scalar-commutant and Euler-current laws are used also by the actual
minus-one and zero-mode identification in LatticeSugawaraConformal.
The frozen private eq_constant_of_partials_zero is applied directly,
without reproof. Utility is none: every assertion is a general algebraic
operator law, not a computational-content instance or numerical reduction.
-/

import D5.S3.VertexAlgebra.LatticeSugawaraCurrents
import Mathlib.RingTheory.Derivation.Lie

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeSugawaraVirasoro

open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open D5.S3.VertexAlgebra.FieldNormalProduct
open D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open MvPolynomial
open scoped BigOperators VertexOperator

noncomputable section

/-- The unsimplified Virasoro defect of the actual modes. -/
def centralDefect (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m n : ℤ) : Module.End ℂ (Carrier D) :=
  sugawaraMode D H m * sugawaraMode D H n - sugawaraMode D H n * sugawaraMode D H m -
    ((m-n : ℤ) : ℂ) • sugawaraMode D H (m+n)

/-- The actual central defect commutes with every current, in every charge sector. -/
theorem centralDefect_current_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Fin D.rank) (m n q : ℤ) :
    centralDefect D H m n * neutralMode D a q -
      neutralMode D a q * centralDefect D H m n = 0 := by
  have h := sugawaraMode_current_commutator D H hHG hGH
  have jacobi :
      (sugawaraMode D H m * sugawaraMode D H n - sugawaraMode D H n * sugawaraMode D H m) *
          neutralMode D a q - neutralMode D a q *
        (sugawaraMode D H m * sugawaraMode D H n - sugawaraMode D H n * sugawaraMode D H m) =
      sugawaraMode D H m * (sugawaraMode D H n * neutralMode D a q -
          neutralMode D a q * sugawaraMode D H n) -
        (sugawaraMode D H n * neutralMode D a q - neutralMode D a q * sugawaraMode D H n) *
          sugawaraMode D H m -
      (sugawaraMode D H n * (sugawaraMode D H m * neutralMode D a q -
          neutralMode D a q * sugawaraMode D H m) -
        (sugawaraMode D H m * neutralMode D a q - neutralMode D a q * sugawaraMode D H m) *
          sugawaraMode D H n) := by noncomm_ring
  have hexp :
      (sugawaraMode D H m * sugawaraMode D H n - sugawaraMode D H n * sugawaraMode D H m -
        ((m-n : ℤ) : ℂ) • sugawaraMode D H (m+n)) * neutralMode D a q -
        neutralMode D a q * (sugawaraMode D H m * sugawaraMode D H n -
          sugawaraMode D H n * sugawaraMode D H m - ((m-n : ℤ) : ℂ) • sugawaraMode D H (m+n)) =
      -(q : ℂ) • (sugawaraMode D H m * neutralMode D a (n+q) -
          neutralMode D a (n+q) * sugawaraMode D H m) -
        -(q : ℂ) • (sugawaraMode D H n * neutralMode D a (m+q) -
          neutralMode D a (m+q) * sugawaraMode D H n) -
        ((m-n : ℤ) : ℂ) • (sugawaraMode D H (m+n) * neutralMode D a q -
          neutralMode D a q * sugawaraMode D H (m+n)) := by
    rw [show ∀ x y z t : Module.End ℂ (Carrier D), (x-y-z)*t-t*(x-y-z) =
      ((x-y)*t-t*(x-y))- (z*t-t*z) by intros; noncomm_ring]
    rw [jacobi, h a n q, h a m q]
    simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub]
  change (sugawaraMode D H m * sugawaraMode D H n -
    sugawaraMode D H n * sugawaraMode D H m -
    ((m-n : ℤ) : ℂ) • sugawaraMode D H (m+n)) * neutralMode D a q -
    neutralMode D a q * (sugawaraMode D H m * sugawaraMode D H n -
      sugawaraMode D H n * sugawaraMode D H m -
      ((m-n : ℤ) : ℂ) • sugawaraMode D H (m+n)) = 0
  rw [hexp, h a m (n+q), h a n (m+q), h a (m+n) q]
  rw [show m+(n+q) = m+n+q by omega, show n+(m+q) = m+n+q by omega]
  simp only [smul_smul, ← sub_smul]
  have hc : -(q : ℂ) * -((n+q : ℤ) : ℂ) - -(q : ℂ) * -((m+q : ℤ) : ℂ) -
      ((m-n : ℤ) : ℂ) * -(q : ℂ) = 0 := by push_cast; ring
  rw [hc, zero_smul]

/-- Restriction of the actual Sugawara mode to one actual charge sector. -/
def sectorSugawaraMode (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (β : Charge D) (m : ℤ) :
    Module.End ℂ (Oscillator D) :=
  (Finsupp.lapply β).comp ((sugawaraMode D H m).comp (Finsupp.lsingle β))

/-- The actual field coefficients preserve each charge; restriction loses no action. -/
theorem sugawaraMode_single_sector (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (β : Charge D) (m : ℤ) (p : Oscillator D) :
    sugawaraMode D H m (Finsupp.single β p) =
      Finsupp.single β (sectorSugawaraMode D H β m p) := by
  classical
  let P : Module.End ℂ (Carrier D) := (Finsupp.lsingle β).comp (Finsupp.lapply β)
  have term (i j : Fin D.rank) (k : ℤ) :
      P (normalSummand D i j k (m-k) (Finsupp.single β p)) =
        normalSummand D i j k (m-k) (Finsupp.single β p) := by
    unfold normalSummand
    split_ifs <;> simp [P, Module.End.mul_apply]
  have hP : P (sugawaraMode D H m (Finsupp.single β p)) =
      sugawaraMode D H m (Finsupp.single β p) := by
    rw [sugawaraMode_finsum]
    simp only [map_smul, map_sum]
    apply congrArg (fun v : Carrier D => (2 : ℂ)⁻¹ • v)
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply congrArg (fun v : Carrier D => H i j • v)
    rw [map_finsum P (normalSummand_finite D i j m (Finsupp.single β p))]
    exact finsum_congr (term i j)
  simpa only [P, sectorSugawaraMode, LinearMap.comp_apply, Finsupp.lapply_apply,
    Finsupp.lsingle_apply] using hP.symm

/-- The sector defect is the faithful restriction of the actual central defect. -/
def sectorCentralDefect (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (β : Charge D) (m n : ℤ) :
    Module.End ℂ (Oscillator D) :=
  sectorSugawaraMode D H β m * sectorSugawaraMode D H β n -
    sectorSugawaraMode D H β n * sectorSugawaraMode D H β m -
    ((m-n : ℤ) : ℂ) • sectorSugawaraMode D H β (m+n)

private theorem centralDefect_single_sector (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (β : Charge D) (m n : ℤ) (p : Oscillator D) :
    centralDefect D H m n (Finsupp.single β p) =
      Finsupp.single β (sectorCentralDefect D H β m n p) := by
  simp only [centralDefect, sectorCentralDefect, LinearMap.sub_apply, Module.End.mul_apply,
    sugawaraMode_single_sector, LinearMap.smul_apply, ← Finsupp.single_sub, Finsupp.smul_single]

private theorem sectorCentralDefect_current_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (β : Charge D) (a : Fin D.rank) (m n q : ℤ) :
    sectorCentralDefect D H β m n * neutralPolynomialMode D a β q -
      neutralPolynomialMode D a β q * sectorCentralDefect D H β m n = 0 := by
  apply LinearMap.ext
  intro p
  have h := congrArg (fun F : Module.End ℂ (Carrier D) => F (Finsupp.single β p))
    (centralDefect_current_commutator D H hHG hGH a m n q)
  have hx := congrArg (fun v : Carrier D => v β) h
  simpa only [LinearMap.sub_apply, Module.End.mul_apply, neutralMode_single,
    centralDefect_single_sector, Finsupp.sub_apply, Finsupp.single_eq_same,
    LinearMap.zero_apply, Finsupp.zero_apply] using hx

theorem polynomial_current_commutant_scalar (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1)
    (β : Charge D) (A : Module.End ℂ (Oscillator D))
    (hA : ∀ (a : Fin D.rank) (q : ℤ),
      A * neutralPolynomialMode D a β q - neutralPolynomialMode D a β q * A = 0) :
    A = constantCoeff (A 1) • (1 : Module.End ℂ (Oscillator D)) := by
  classical
  have hweighted (i : Fin D.rank) (r : ℕ) : weightedPartial D i r (A 1) = 0 := by
    have h := congrArg (fun F : Module.End ℂ (Oscillator D) => F 1)
      (hA i ((r : ℤ)+1))
    rw [neutralPolynomialMode_positive] at h
    have hone : weightedPartial D i r (1 : Oscillator D) = 0 := by
      simp [weightedPartial, pderiv_one]
    have hs : (r+1 : ℂ) • weightedPartial D i r (A 1) = 0 := by
      simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
        hone, smul_zero, map_zero, zero_sub, neg_eq_zero, LinearMap.zero_apply] using h
    have hc : (r+1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero r)
    exact (smul_eq_zero.mp hs).resolve_left hc
  have hpartial (x : Index D) : pderiv x (A 1) = 0 := by
    have reconstruct : (∑ i : Fin D.rank, H x.1 i • weightedPartial D i x.2 (A 1)) =
        pderiv x (A 1) := by
      simp only [weightedPartial, LinearMap.sum_apply, LinearMap.smul_apply,
        Derivation.coeFn_coe, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul]
      have row (j : Fin D.rank) : ∑ i, H x.1 i * (D.G i j : ℂ) =
          if x.1 = j then 1 else 0 := by
        simpa [Matrix.mul_apply, gramComplex, Matrix.one_apply] using
          congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℂ => M x.1 j) hHG
      simp_rw [row]
      simp
    rw [← reconstruct]
    simp [hweighted]
  have hconstant : A 1 = C (constantCoeff (A 1)) := by
    run_tac
      let supplier := (Lean.Name.num
        `_private.D5.S3.Quantum.Algebra.ConditionalPolynomialRigidity 0).append
        `D5.S3.Quantum.Algebra.ConditionalPolynomialRigidity.eq_constant_of_partials_zero
      Lean.Elab.Tactic.evalTactic
        (← `(tactic| exact ($(Lean.mkIdent supplier)) _ $(Lean.mkIdent `hpartial)))
  apply LinearMap.ext
  intro p
  change A p = constantCoeff (A 1) • p
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [show (C c : Oscillator D) = c • 1 by simp [smul_eq_C_mul], map_smul, hconstant]
    simp [smul_eq_C_mul, mul_comm]
  | add p q hp hq => simp [map_add, hp, hq, smul_add]
  | mul_X p x hp =>
    have h := congrArg (fun F : Module.End ℂ (Oscillator D) => F p)
      (hA x.1 (-(x.2 : ℤ)-1))
    rw [neutralPolynomialMode_negative] at h
    change A (X x * p) - X x * A p = 0 at h
    rw [mul_comm p (X x), sub_eq_zero.mp h, hp]
    simp [mul_smul_comm]

/-- Scalarity is proved independently on every integral charge sector. -/
theorem centralDefect_sector_scalar (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (β : Charge D) (m n : ℤ) :
    sectorCentralDefect D H β m n =
      constantCoeff (sectorCentralDefect D H β m n 1) •
        (1 : Module.End ℂ (Oscillator D)) :=
  polynomial_current_commutant_scalar D H hHG β (sectorCentralDefect D H β m n)
    (fun a q => sectorCentralDefect_current_commutator D H hHG hGH β a m n q)

/-- Weighted Euler derivation on the actual oscillator variables. -/
def oscillatorEuler (D : LatticeData) : Derivation ℂ (Oscillator D) (Oscillator D) :=
  mkDerivation ℂ (fun x : Index D => (x.2+1 : ℂ) • X x)

/-- The charge-preserving weighted Euler operator on the actual carrier. -/
def eulerMode (D : LatticeData) : Module.End ℂ (Carrier D) :=
  Finsupp.lsum ℂ (fun β => (Finsupp.lsingle β).comp (oscillatorEuler D).toLinearMap)

@[simp] private theorem eulerMode_single (D : LatticeData) (β : Charge D) (p : Oscillator D) :
    eulerMode D (Finsupp.single β p) = Finsupp.single β (oscillatorEuler D p) := by
  simp [eulerMode]

private theorem oscillatorEuler_partial (D : LatticeData) (j : Fin D.rank) (r : ℕ) :
    (oscillatorEuler D).toLinearMap * (pderiv (j,r)).toLinearMap -
      (pderiv (j,r)).toLinearMap * (oscillatorEuler D).toLinearMap =
      -(r+1 : ℂ) • (pderiv (j,r)).toLinearMap := by
  classical
  have h : ⁅oscillatorEuler D, pderiv (j,r)⁆ =
      -(r+1 : ℂ) • (pderiv (j,r) : Derivation ℂ (Oscillator D) (Oscillator D)) := by
    apply MvPolynomial.derivation_ext
    intro x
    by_cases hx : x = (j,r)
    · subst x
      simp [Derivation.commutator_apply, oscillatorEuler, Pi.single_apply]
      rw [← neg_smul]
      congr 1
      ring
    · simp [Derivation.commutator_apply, oscillatorEuler, Pi.single_apply, hx]
  apply LinearMap.ext
  intro p
  exact congrArg (fun δ : Derivation ℂ (Oscillator D) (Oscillator D) => δ p) h

private theorem oscillatorEuler_weightedPartial (D : LatticeData) (i : Fin D.rank) (r : ℕ) :
    (oscillatorEuler D).toLinearMap * weightedPartial D i r -
      weightedPartial D i r * (oscillatorEuler D).toLinearMap =
      -(r+1 : ℂ) • weightedPartial D i r := by
  classical
  simp only [weightedPartial, Finset.mul_sum, Finset.sum_mul,
    Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← smul_sub, oscillatorEuler_partial, smul_comm (D.G i _ : ℂ) (-(r+1 : ℂ))]
  rw [← Finset.smul_sum]

theorem oscillatorEuler_current (D : LatticeData) (i : Fin D.rank)
    (β : Charge D) (q : ℤ) :
    (oscillatorEuler D).toLinearMap * neutralPolynomialMode D i β q -
      neutralPolynomialMode D i β q * (oscillatorEuler D).toLinearMap =
      -(q : ℂ) • neutralPolynomialMode D i β q := by
  cases q with
  | ofNat a =>
    cases a with
    | zero =>
      have hz : neutralPolynomialMode D i β 0 =
          (bilinear D (unitCharge D i) β : ℂ) • (1 : Module.End ℂ (Oscillator D)) := by
        simp [neutralPolynomialMode, Module.End.one_eq_id]
      simp only [Int.ofNat_eq_natCast, Nat.cast_zero, Int.cast_zero, neg_zero, zero_smul]
      rw [hz]
      simp [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
    | succ r =>
      rw [show Int.ofNat (r+1) = (r : ℤ)+1 by simp, neutralPolynomialMode_positive]
      rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← smul_sub,
        oscillatorEuler_weightedPartial]
      simp only [Int.cast_add, Int.cast_natCast, Int.cast_one]
      exact smul_comm _ _ _
  | negSucc r =>
    rw [show Int.negSucc r = -(r : ℤ)-1 by omega, neutralPolynomialMode_negative]
    apply LinearMap.ext
    intro p
    change oscillatorEuler D (X (i,r) * p) - X (i,r) * oscillatorEuler D p =
      -((-(r : ℤ)-1 : ℤ) : ℂ) • (X (i,r)*p)
    rw [(oscillatorEuler D).leibniz]
    simp [oscillatorEuler, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, add_comm,
      Int.cast_sub, Int.cast_neg, Int.cast_natCast, smul_eq_C_mul]

/-- Weighted Euler gives the current its actual frequency, including all zero modes. -/
theorem eulerMode_current_commutator (D : LatticeData) (i : Fin D.rank) (q : ℤ) :
    eulerMode D * neutralMode D i q - neutralMode D i q * eulerMode D =
      -(q : ℂ) • neutralMode D i q := by
  apply Finsupp.lhom_ext'
  intro β
  apply LinearMap.ext
  intro p
  have h := congrArg (fun F : Module.End ℂ (Oscillator D) => F p)
    (oscillatorEuler_current D i β q)
  simpa only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.sub_apply,
    Module.End.mul_apply, neutralMode_single, eulerMode_single, LinearMap.smul_apply,
    ← Finsupp.single_sub, Finsupp.smul_single, Derivation.coeFn_coe] using
      congrArg (Finsupp.single β) h

private theorem normalSummand_euler_commutator (D : LatticeData)
    (i j : Fin D.rank) (k l : ℤ) :
    eulerMode D * normalSummand D i j k l - normalSummand D i j k l * eulerMode D =
      -((k+l : ℤ) : ℂ) • normalSummand D i j k l := by
  have product (i j : Fin D.rank) (k l : ℤ) :
      eulerMode D * (neutralMode D i k * neutralMode D j l) -
        (neutralMode D i k * neutralMode D j l) * eulerMode D =
        -((k+l : ℤ) : ℂ) • (neutralMode D i k * neutralMode D j l) := by
    calc
      _ = (eulerMode D * neutralMode D i k - neutralMode D i k * eulerMode D) *
          neutralMode D j l + neutralMode D i k *
        (eulerMode D * neutralMode D j l - neutralMode D j l * eulerMode D) := by
        noncomm_ring
      _ = _ := by
        rw [eulerMode_current_commutator, eulerMode_current_commutator]
        simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ← add_smul]
        congr 1
        push_cast
        ring
  by_cases hk : k < 0
  · rw [normalSummand, if_pos hk]
    exact product i j k l
  · rw [normalSummand, if_neg hk]
    simpa only [add_comm] using product j i l k

private theorem quadraticSummand_euler_commutator (D : LatticeData)
    (i j : Fin D.rank) (m : ℤ) :
    eulerMode D * (quadraticSummand D i j)[[m+1]] -
      (quadraticSummand D i j)[[m+1]] * eulerMode D =
      -(m : ℂ) • (quadraticSummand D i j)[[m+1]] := by
  apply LinearMap.ext
  intro v
  have hv := normalSummand_finite D i j m v
  have hw := normalSummand_finite D i j m (eulerMode D v)
  have hmap := hv.fun_comp (map_zero (eulerMode D))
  change eulerMode D (((quadraticSummand D i j)[[m+1]]) v) -
    ((quadraticSummand D i j)[[m+1]]) (eulerMode D v) =
    -(m : ℂ) • ((quadraticSummand D i j)[[m+1]]) v
  rw [quadraticSummand_coefficient, quadraticSummand_coefficient,
    map_finsum (eulerMode D) hv,
    ← finsum_sub_distrib hmap hw]
  calc
    _ = ∑ᶠ k : ℤ, -(m : ℂ) • normalSummand D i j k (m-k) v := by
      apply finsum_congr
      intro k
      have h := congrArg (fun A : Module.End ℂ (Carrier D) => A v)
        (normalSummand_euler_commutator D i j k (m-k))
      simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
        show k+(m-k) = m by omega] using h
    _ = _ := (smul_finsum' _ hv).symm

/-- Euler measures the degree of the actual Sugawara modes on every vector. -/
theorem eulerMode_sugawara_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ) :
    eulerMode D * sugawaraMode D H m - sugawaraMode D H m * eulerMode D =
      -(m : ℂ) • sugawaraMode D H m := by
  classical
  rw [sugawaraMode_coefficient_sum]
  simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
    Finset.mul_sum, Finset.sum_mul, ← smul_sub]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← smul_sub, quadraticSummand_euler_commutator,
    smul_comm (H _ _) (-(m : ℂ)), ← Finset.smul_sum]
  exact smul_comm _ _ _

private theorem eulerMode_defect_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m n : ℤ) :
    eulerMode D * centralDefect D H m n - centralDefect D H m n * eulerMode D =
      -((m+n : ℤ) : ℂ) • centralDefect D H m n := by
  have product (m n : ℤ) :
      eulerMode D * (sugawaraMode D H m * sugawaraMode D H n) -
        (sugawaraMode D H m * sugawaraMode D H n) * eulerMode D =
        -((m+n : ℤ) : ℂ) • (sugawaraMode D H m * sugawaraMode D H n) := by
    calc
      _ = (eulerMode D * sugawaraMode D H m - sugawaraMode D H m * eulerMode D) *
          sugawaraMode D H n + sugawaraMode D H m *
        (eulerMode D * sugawaraMode D H n - sugawaraMode D H n * eulerMode D) := by
        noncomm_ring
      _ = _ := by
        rw [eulerMode_sugawara_commutator, eulerMode_sugawara_commutator]
        simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ← add_smul]
        congr 1
        push_cast
        ring
  unfold centralDefect
  calc
    _ = (eulerMode D * (sugawaraMode D H m * sugawaraMode D H n) -
          (sugawaraMode D H m * sugawaraMode D H n) * eulerMode D) -
        (eulerMode D * (sugawaraMode D H n * sugawaraMode D H m) -
          (sugawaraMode D H n * sugawaraMode D H m) * eulerMode D) -
        ((m-n : ℤ) : ℂ) • (eulerMode D * sugawaraMode D H (m+n) -
          sugawaraMode D H (m+n) * eulerMode D) := by
      simp only [mul_sub, sub_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub]
      abel
    _ = _ := by
      rw [product, product, eulerMode_sugawara_commutator, add_comm n m]
      simp only [smul_sub, smul_comm ((m-n : ℤ) : ℂ) (-((m+n : ℤ) : ℂ))]

/-- Off the contraction diagonal the actual central defect vanishes on all charges. -/
theorem centralDefect_off_diagonal (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (m n : ℤ) (hmn : m + n ≠ 0) : centralDefect D H m n = 0 := by
  apply Finsupp.lhom_ext'
  intro β
  apply LinearMap.ext
  intro p
  let c := constantCoeff (sectorCentralDefect D H β m n 1)
  have hs (p : Oscillator D) : centralDefect D H m n (Finsupp.single β p) =
      c • Finsupp.single β p := by
    rw [centralDefect_single_sector, centralDefect_sector_scalar D H hHG hGH]
    simp [c, Finsupp.smul_single]
  have h := congrArg (fun A : Module.End ℂ (Carrier D) => A (Finsupp.single β p))
    (eulerMode_defect_commutator D H m n)
  have hc : -((m+n : ℤ) : ℂ) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast hmn)
  have hz : -((m+n : ℤ) : ℂ) • centralDefect D H m n (Finsupp.single β p) = 0 := by
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      eulerMode_single, hs, map_smul, sub_self] using h.symm
  have hout := (smul_eq_zero.mp hz).resolve_left hc
  simpa only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_apply] using hout

/-- The charge scalar carried by the actual zero current. -/
abbrev chargeScalar (D : LatticeData) (β : Charge D) (i : Fin D.rank) : ℂ :=
  (bilinear D (unitCharge D i) β : ℂ)

/-- The matrix quadratic zero-mode charge contribution. -/
def chargeQuadratic (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (β : Charge D) : ℂ :=
  (2 : ℂ)⁻¹ * ∑ i : Fin D.rank, ∑ j : Fin D.rank,
    H i j * chargeScalar D β i * chargeScalar D β j

theorem ground_frequency_bound (D : LatticeData) (β : Charge D) :
    vectorFrequencyBound D (Finsupp.single β (1 : Oscillator D)) = 0 := by
  classical
  simp [vectorFrequencyBound, polynomialFrequencyBound]

theorem neutralMode_zero_single (D : LatticeData) (i : Fin D.rank)
    (β : Charge D) (p : Oscillator D) :
    neutralMode D i 0 (Finsupp.single β p) = chargeScalar D β i • Finsupp.single β p := by
  simp [neutralPolynomialMode, chargeScalar, Finsupp.smul_single]

private theorem neutralMode_ground_positive (D : LatticeData) (i : Fin D.rank)
    (β : Charge D) (q : ℤ) (hq : 0 < q) :
    neutralMode D i q (Finsupp.single β (1 : Oscillator D)) = 0 := by
  apply neutralMode_vanish
  simpa only [ground_frequency_bound, Nat.cast_zero] using hq

/-- Every positive actual Sugawara mode kills every charged ground state. -/
theorem sugawaraMode_ground_positive (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (β : Charge D) (m : ℤ) (hm : 0 < m) :
    sugawaraMode D H m (Finsupp.single β (1 : Oscillator D)) = 0 := by
  classical
  rw [sugawaraMode_interval_sum, ground_frequency_bound]
  simp only [Nat.cast_zero, sub_zero, min_eq_left hm.le, Finset.Icc_self,
    Finset.sum_singleton]
  have term (i j : Fin D.rank) :
      normalSummand D i j 0 m (Finsupp.single β (1 : Oscillator D)) = 0 := by
    rw [normalSummand, if_neg (by omega), Module.End.mul_apply, neutralMode_zero_single,
      map_smul, neutralMode_ground_positive D j β m hm, smul_zero]
  simp [term]

/-- The charged ground contribution is present on every sector. -/
theorem sugawaraMode_ground_zero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (β : Charge D) :
    sugawaraMode D H 0 (Finsupp.single β (1 : Oscillator D)) =
      chargeQuadratic D H β • Finsupp.single β (1 : Oscillator D) := by
  classical
  rw [sugawaraMode_interval_sum, ground_frequency_bound]
  simp only [Nat.cast_zero, sub_zero, min_self, Finset.Icc_self, Finset.sum_singleton]
  have term (i j : Fin D.rank) :
      normalSummand D i j 0 0 (Finsupp.single β (1 : Oscillator D)) =
        (chargeScalar D β i * chargeScalar D β j) • Finsupp.single β (1 : Oscillator D) := by
    rw [normalSummand, if_neg (by omega), Module.End.mul_apply, neutralMode_zero_single,
      map_smul, neutralMode_zero_single, smul_smul]
  simp_rw [term, smul_smul]
  simp_rw [← Finset.sum_smul]
  simp only [chargeQuadratic, smul_smul, mul_assoc]

private theorem sugawara_current_product (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (i j : Fin D.rank) (a k l : ℤ) :
    sugawaraMode D H a * (neutralMode D i k * neutralMode D j l) -
      (neutralMode D i k * neutralMode D j l) * sugawaraMode D H a =
      -(k : ℂ) • (neutralMode D i (a+k) * neutralMode D j l) +
        -(l : ℂ) • (neutralMode D i k * neutralMode D j (a+l)) := by
  calc
    _ = (sugawaraMode D H a * neutralMode D i k - neutralMode D i k * sugawaraMode D H a) *
        neutralMode D j l + neutralMode D i k *
      (sugawaraMode D H a * neutralMode D j l - neutralMode D j l * sugawaraMode D H a) := by
      noncomm_ring
    _ = _ := by
      rw [sugawaraMode_current_commutator D H hHG hGH,
        sugawaraMode_current_commutator D H hHG hGH]
      simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]

private theorem sugawara_normal_ground (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (β : Charge D) (i j : Fin D.rank) (a k : ℤ) (ha : 0 < a)
    (hk : k ∈ Finset.Icc (-a) 0) :
    sugawaraMode D H a (normalSummand D i j k (-a-k) (Finsupp.single β 1)) =
      ((if k = -a then (a : ℂ) * chargeScalar D β i * chargeScalar D β j else 0) +
        (if k = 0 then (a : ℂ) * chargeScalar D β i * chargeScalar D β j else 0) +
        (-(k : ℂ) * ((a+k : ℤ) : ℂ) * (D.G i j : ℂ))) • Finsupp.single β 1 := by
  classical
  have hkb : -a ≤ k ∧ k ≤ 0 := Finset.mem_Icc.mp hk
  have product (i j : Fin D.rank) (k l : ℤ) :
      sugawaraMode D H a (neutralMode D i k (neutralMode D j l (Finsupp.single β 1))) =
      -(k : ℂ) • neutralMode D i (a+k) (neutralMode D j l (Finsupp.single β 1)) +
        -(l : ℂ) • neutralMode D i k (neutralMode D j (a+l) (Finsupp.single β 1)) := by
    have h := congrArg (fun A : Module.End ℂ (Carrier D) => A (Finsupp.single β 1))
      (sugawara_current_product D H hHG hGH i j a k l)
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
      LinearMap.smul_apply, sugawaraMode_ground_positive D H β a ha, map_zero, sub_zero] using h
  by_cases hk0 : k = 0
  · subst k
    have hna : (0 : ℤ) ≠ -a := by omega
    rw [normalSummand, if_neg (by omega), Module.End.mul_apply, sub_zero, product j i (-a) 0]
    simp only [Int.cast_zero, Int.cast_neg, neg_zero, neg_neg, zero_smul, add_zero,
      add_neg_cancel, if_neg hna, if_true, zero_add, mul_zero, zero_mul]
    simp only [neutralMode_zero_single, map_smul, smul_smul]
    rw [mul_assoc]
  · have hkneg : k < 0 := by omega
    rw [normalSummand, if_pos hkneg, Module.End.mul_apply, product i j k (-a-k)]
    have hz : neutralMode D j (a+(-a-k)) (Finsupp.single β (1 : Oscillator D)) = 0 :=
      neutralMode_ground_positive D j β _ (by omega)
    rw [hz, map_zero, smul_zero, add_zero]
    by_cases hka : k = -a
    · subst k
      simp only [add_neg_cancel, sub_self, Int.cast_neg, neg_neg, Int.cast_zero,
        mul_zero, add_zero, if_true, if_neg hk0, zero_add]
      simp only [neutralMode_zero_single, map_smul, smul_smul]
      congr 1
      ring
    · have hpositive : 0 < a+k := by omega
      have hcomm := congrArg (fun A : Module.End ℂ (Carrier D) => A (Finsupp.single β 1))
        (neutralMode_heisenberg D i j (a+k) (-a-k))
      rw [if_pos (by omega)] at hcomm
      have hcontract : neutralMode D i (a+k) (neutralMode D j (-a-k) (Finsupp.single β 1)) =
          (((a+k : ℤ) : ℂ)*(D.G i j : ℂ)) • Finsupp.single β 1 := by
        simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
          Module.End.one_apply, neutralMode_ground_positive D i β (a+k) hpositive,
          map_zero, sub_zero] using hcomm
      rw [hcontract, smul_smul, if_neg hka, if_neg hk0, zero_add, zero_add]
      rw [mul_assoc]

private theorem contraction_sum (a : ℕ) :
    ∑ k ∈ Finset.Icc (-(a : ℤ)) 0,
      -(k : ℂ) * (((a : ℤ)+k : ℤ) : ℂ) = ((a : ℂ)^3-a)/6 := by
  classical
  have reindex : (∑ k ∈ Finset.Icc (-(a : ℤ)) 0,
      -(k : ℂ) * (((a : ℤ)+k : ℤ) : ℂ)) =
      ∑ s ∈ Finset.range (a+1), (s : ℂ)*((a : ℂ)-s) := by
    apply Finset.sum_bij (fun k hk => (-k).toNat)
    · intro k hk
      have hb := Finset.mem_Icc.mp hk
      have hc : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      simp only [Finset.mem_range]
      omega
    · intro k hk l hl he
      have hb := Finset.mem_Icc.mp hk
      have hc := Finset.mem_Icc.mp hl
      have hkcast : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      have hlcast : ((-l).toNat : ℤ) = -l := Int.toNat_of_nonneg (by omega)
      omega
    · intro s hs
      have hsle : s ≤ a := by have hb := Finset.mem_range.mp hs; omega
      refine ⟨-(s : ℤ), Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      simp
    · intro k hk
      have hb := Finset.mem_Icc.mp hk
      have hcast : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      have hc : ((-k).toNat : ℂ) = -(k : ℂ) := by exact_mod_cast hcast
      rw [hc]
      push_cast
      ring
  rw [reindex]
  let F (s : ℕ) : ℂ := (a : ℂ)*(s : ℂ)*((s : ℂ)-1)/2 -
    ((s : ℂ)-1)*(s : ℂ)*(2*(s : ℂ)-1)/6
  have hterm (s : ℕ) : (s : ℂ)*((a : ℂ)-s) = F (s+1)-F s := by
    simp only [F, Nat.cast_add, Nat.cast_one]
    ring
  simp_rw [hterm]
  rw [Finset.sum_range_sub]
  simp only [F, Nat.cast_zero, Nat.cast_add, Nat.cast_one]
  ring

private theorem inverse_gram_trace (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) :
    ∑ i : Fin D.rank, ∑ j : Fin D.rank, H i j * (D.G i j : ℂ) = (D.rank : ℂ) := by
  classical
  have diag (i : Fin D.rank) : ∑ j, H i j * (D.G i j : ℂ) = 1 := by
    simpa [Matrix.mul_apply, gramComplex, Matrix.one_apply, D.symmetric i] using
      congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℂ => M i i) hHG
  simp_rw [diag]
  simp

/-- Diagonal charged-ground cancellation leaves only the cubic inverse-Gram trace. -/
theorem centralDefect_ground_diagonal (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (β : Charge D) (a : ℕ) (ha : 0 < a) :
    centralDefect D H (a : ℤ) (-(a : ℤ)) (Finsupp.single β (1 : Oscillator D)) =
      ((D.rank : ℂ)/12*((a : ℂ)^3-a)) • Finsupp.single β (1 : Oscillator D) := by
  classical
  let v : Carrier D := Finsupp.single β 1
  have hapos : (0 : ℤ) < a := by exact_mod_cast ha
  have inner (i j : Fin D.rank) :
      ∑ k ∈ Finset.Icc (-(a : ℤ)) 0,
        sugawaraMode D H (a : ℤ) (normalSummand D i j k (-(a : ℤ)-k) v) =
      ((2*(a : ℂ)*chargeScalar D β i*chargeScalar D β j) +
        (((a : ℂ)^3-a)/6)*(D.G i j : ℂ)) • v := by
    have term (k : ℤ) (hk : k ∈ Finset.Icc (-(a : ℤ)) 0) :=
      sugawara_normal_ground D H hHG hGH β i j (a : ℤ) k hapos hk
    change (∑ k ∈ Finset.Icc (-(a : ℤ)) 0,
      sugawaraMode D H (a : ℤ) (normalSummand D i j k (-(a : ℤ)-k) (Finsupp.single β 1))) = _
    rw [Finset.sum_congr rfl term]
    simp only [← Finset.sum_smul, Finset.sum_add_distrib]
    have hsum : (∑ k ∈ Finset.Icc (-(a : ℤ)) 0,
        -(k : ℂ) * (((a : ℤ)+k : ℤ) : ℂ) * (D.G i j : ℂ)) =
        (((a : ℂ)^3-a)/6) * (D.G i j : ℂ) := by
      rw [← Finset.sum_mul, contraction_sum]
    rw [hsum]
    simp only [Finset.sum_ite_eq', Finset.mem_Icc, le_refl, Int.natCast_nonneg,
      neg_nonpos.mpr (Int.natCast_nonneg a), and_self, if_true]
    apply congrArg (fun c : ℂ => c • v)
    simp only [Int.cast_natCast]
    ring
  have hLL : sugawaraMode D H (a : ℤ) (sugawaraMode D H (-(a : ℤ)) v) =
      (2*(a : ℂ)*chargeQuadratic D H β +
        ((D.rank : ℂ)/12*((a : ℂ)^3-a))) • v := by
    rw [sugawaraMode_interval_sum D H (-(a : ℤ)) v,
      show vectorFrequencyBound D v = 0 from ground_frequency_bound D β]
    simp only [Nat.cast_zero, sub_zero, min_eq_right (by omega : -(a : ℤ) ≤ 0)]
    simp only [map_smul, map_sum]
    simp_rw [inner, smul_smul]
    simp_rw [← Finset.sum_smul]
    rw [smul_smul]
    apply congrArg (fun c : ℂ => c • v)
    simp only [mul_add, Finset.sum_add_distrib]
    have charge : ∑ i : Fin D.rank, ∑ j : Fin D.rank,
        H i j * (2*(a : ℂ)*chargeScalar D β i*chargeScalar D β j) =
        (2*(a : ℂ)) * ∑ i : Fin D.rank, ∑ j : Fin D.rank,
          H i j*chargeScalar D β i*chargeScalar D β j := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have central : ∑ i : Fin D.rank, ∑ j : Fin D.rank,
        H i j * ((((a : ℂ)^3-a)/6)*(D.G i j : ℂ)) =
        (((a : ℂ)^3-a)/6)*(D.rank : ℂ) := by
      rw [← inverse_gram_trace D H hHG]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [charge, central]
    simp only [chargeQuadratic]
    ring
  simp only [centralDefect, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    sugawaraMode_ground_positive D H β (a : ℤ) hapos, map_zero, sub_zero,
    add_neg_cancel, sub_neg_eq_add]
  change sugawaraMode D H (a : ℤ) (sugawaraMode D H (-(a : ℤ)) v) -
    (((a : ℤ)+(a : ℤ) : ℤ) : ℂ) • sugawaraMode D H 0 v = _
  rw [hLL, sugawaraMode_ground_zero]
  simp only [v, smul_smul, ← sub_smul, Int.cast_add, Int.cast_natCast]
  apply congrArg (fun c : ℂ => c • Finsupp.single β (1 : Oscillator D))
  ring


/-- The charged-ground value propagates to every oscillator in every charge sector. -/
theorem centralDefect_diagonal_positive (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : ℕ) (ha : 0 < a) :
    centralDefect D H (a : ℤ) (-(a : ℤ)) =
      ((D.rank : ℂ)/12*((a : ℂ)^3-a)) • (1 : Module.End ℂ (Carrier D)) := by
  apply Finsupp.lhom_ext'
  intro β
  have hc := congrArg (fun v : Carrier D => constantCoeff (v β))
    (centralDefect_ground_diagonal D H hHG hGH β a ha)
  simp [centralDefect_single_sector, Finsupp.smul_single] at hc
  apply LinearMap.ext
  intro p
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.smul_apply,
    Module.End.one_apply, centralDefect_single_sector]
  rw [centralDefect_sector_scalar D H hHG hGH, hc]
  simp [Finsupp.smul_single]

private theorem centralDefect_skew (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m n : ℤ) :
    centralDefect D H m n = -centralDefect D H n m := by
  have hc : ((n-m : ℤ) : ℂ) = -((m-n : ℤ) : ℂ) := by push_cast; ring
  simp only [centralDefect, hc, add_comm n m, neg_smul]
  abel

/-- The all-integer diagonal defect has the rank cubic, including zero and negative modes. -/
theorem centralDefect_diagonal (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (m : ℤ) :
    centralDefect D H m (-m) =
      ((D.rank : ℂ)/12*((m : ℂ)^3-m)) • (1 : Module.End ℂ (Carrier D)) := by
  rcases lt_trichotomy m 0 with hm | hm | hm
  · let a := (-m).toNat
    have hcast : (a : ℤ) = -m := Int.toNat_of_nonneg (by omega)
    have ha : 0 < a := by omega
    have hp := centralDefect_diagonal_positive D H hHG hGH a ha
    rw [hcast] at hp
    simp only [neg_neg] at hp
    rw [centralDefect_skew, hp, ← neg_smul]
    have hc : (a : ℂ) = -(m : ℂ) := by exact_mod_cast hcast
    rw [hc]
    congr 1
    ring
  · subst m
    simp [centralDefect]
  · let a := m.toNat
    have hcast : (a : ℤ) = m := Int.toNat_of_nonneg hm.le
    have ha : 0 < a := by omega
    have hp := centralDefect_diagonal_positive D H hHG hGH a ha
    rw [hcast] at hp
    have hc : (a : ℂ) = (m : ℂ) := by exact_mod_cast hcast
    simpa only [hc] using hp

/-- The actual central defect is scalar, uniformly over all integral charges. -/
theorem centralDefect_formula (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (m n : ℤ) :
    centralDefect D H m n =
      (if m+n = 0 then (D.rank : ℂ)/12*((m : ℂ)^3-m) else 0) •
        (1 : Module.End ℂ (Carrier D)) := by
  by_cases hmn : m+n = 0
  · have hn : n = -m := by omega
    subst n
    simpa only [add_neg_cancel, if_true] using centralDefect_diagonal D H hHG hGH m
  · rw [if_neg hmn, zero_smul, centralDefect_off_diagonal D H hHG hGH m n hmn]

/-- Virasoro on the actual finite-charge lattice carrier, with central charge equal to rank. -/
theorem sugawaraMode_virasoro (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (m n : ℤ) :
    sugawaraMode D H m * sugawaraMode D H n - sugawaraMode D H n * sugawaraMode D H m =
      ((m-n : ℤ) : ℂ) • sugawaraMode D H (m+n) +
        (if m+n = 0 then (D.rank : ℂ)/12*((m : ℂ)^3-m) else 0) •
          (1 : Module.End ℂ (Carrier D)) := by
  have h := centralDefect_formula D H hHG hGH m n
  unfold centralDefect at h
  simpa only [add_comm] using sub_eq_iff_eq_add.mp h


attribute [-instance] PowerSeries.algebraPolynomial

end
end D5.S3.VertexAlgebra.LatticeSugawaraVirasoro
