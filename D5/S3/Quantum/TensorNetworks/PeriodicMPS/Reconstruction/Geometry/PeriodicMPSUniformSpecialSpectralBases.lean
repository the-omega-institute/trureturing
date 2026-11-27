/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformSpecialSpectralBases
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformSpecialSpectralBases
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: The zero-root and repeated-root coefficient loci have reduced prime vanishing ideals. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformSpectralCoefficients
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformTransferSpectrum
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSCommonSpectralAllLengths
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic

/-!
# Special coefficient loci of the trace-aligned uniform transfer

The coordinates are ordered as `(a, b, c)` for the transfer quartic
`X^4 - X^3 + a X^2 - b X + c`. The rational common point comes from
the literal mixed transfer and the checked all-length Jacobian minor.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformSpecialSpectralBases

open Polynomial
open scoped Kronecker

noncomputable section

variable {K : Type*}

/-- The trace-one transfer quartic with elementary spectral coefficients `a,b,c`. -/
def quartic [CommRing K] (a b c : K) : K[X] :=
  X ^ 4 - X ^ 3 + C a * X ^ 2 - C b * X + C c

abbrev Coefficients (K : Type*) := Fin 3 → K
abbrev Parameters (K : Type*) := Fin 2 → K

def transferPolynomial [CommRing K] (p : Coefficients K) : K[X] :=
  quartic (p 0) (p 1) (p 2)

private theorem quartic_derivative [CommRing K] (a b c : K) :
    (quartic a b c).derivative =
      C (4 : K) * X ^ 3 - C (3 : K) * X ^ 2 + C (2 * a) * X - C b := by
  simp only [quartic, map_add, map_sub, derivative_X_pow, derivative_C_mul_X_sq,
    derivative_C_mul_X, derivative_C, Nat.reduceSub, Nat.cast_ofNat, add_zero, mul_comm a 2]

private theorem quartic_natDegree [CommRing K] [Nontrivial K] (a b c : K) :
    (quartic a b c).natDegree = 4 := by
  unfold quartic
  compute_degree!

private theorem quartic_derivative_natDegree [CommRing K] [CharZero K] (a b c : K) :
    (quartic a b c).derivative.natDegree = 3 := by
  rw [quartic_derivative]
  compute_degree!

private theorem quartic_ne_zero [CommRing K] [Nontrivial K] (a b c : K) :
    quartic a b c ≠ 0 := by
  intro h
  have hn := quartic_natDegree a b c
  rw [h, natDegree_zero] at hn
  omega

/-- Solving the simultaneous root and derivative equations for the last two coefficients. -/
theorem one_lt_rootMultiplicity_iff [Field K] (a b c x : K) :
    1 < (quartic a b c).rootMultiplicity x ↔
      b = 4 * x ^ 3 - 3 * x ^ 2 + 2 * a * x ∧
      c = 3 * x ^ 4 - 2 * x ^ 3 + a * x ^ 2 := by
  rw [Polynomial.one_lt_rootMultiplicity_iff_isRoot (quartic_ne_zero a b c)]
  simp only [Polynomial.IsRoot, quartic_derivative]
  simp only [quartic, eval_sub, eval_add, eval_mul,
    eval_pow, eval_X, eval_C]
  constructor
  · rintro ⟨hp, hd⟩
    have hb : b = 4 * x ^ 3 - 3 * x ^ 2 + 2 * a * x := by
      linear_combination -hd
    exact ⟨hb, by linear_combination hp - x * hd⟩
  · rintro ⟨rfl, rfl⟩
    constructor <;> ring

/-- Coefficients for which zero is a characteristic root. -/
def zeroRootLocus [Field K] : Set (Coefficients K) :=
  {p | (transferPolynomial p).IsRoot 0}

/-- Coefficients with a repeated characteristic root in the coefficient field. -/
def repeatedRootLocus [Field K] : Set (Coefficients K) :=
  {p | ∃ x : K, 1 < (transferPolynomial p).rootMultiplicity x}

@[simp] theorem mem_zeroRootLocus_iff [Field K] (p : Coefficients K) :
    p ∈ zeroRootLocus ↔ p 2 = 0 := by
  simp [zeroRootLocus, transferPolynomial, Polynomial.IsRoot, quartic]

theorem one_lt_zero_rootMultiplicity_iff [Field K] (p : Coefficients K) :
    1 < (transferPolynomial p).rootMultiplicity 0 ↔ p 1 = 0 ∧ p 2 = 0 := by
  simp [transferPolynomial, one_lt_rootMultiplicity_iff]

/-- The affine coordinates `(a,b)` on the zero-root hyperplane. -/
def zeroRootParam [Field K] (t : Parameters K) : Coefficients K :=
  ![t 0, t 1, 0]

/-- The affine parameters `(a,x)` where `x` is a repeated root. -/
def repeatedRootParam [Field K] (t : Parameters K) : Coefficients K :=
  ![t 0, 4 * (t 1)^3 - 3 * (t 1)^2 + 2 * t 0 * t 1,
    3 * (t 1)^4 - 2 * (t 1)^3 + t 0 * (t 1)^2]

theorem zeroRootLocus_eq_range [Field K] :
    (zeroRootLocus : Set (Coefficients K)) = Set.range zeroRootParam := by
  ext p
  rw [mem_zeroRootLocus_iff]
  constructor
  · intro hc
    refine ⟨![p 0, p 1], ?_⟩
    funext i
    fin_cases i <;> simp [zeroRootParam, hc]
  · rintro ⟨t, rfl⟩
    simp [zeroRootParam]

theorem repeatedRootLocus_eq_range [Field K] :
    (repeatedRootLocus : Set (Coefficients K)) = Set.range repeatedRootParam := by
  ext p
  change (∃ x : K, 1 < (transferPolynomial p).rootMultiplicity x) ↔
    p ∈ Set.range repeatedRootParam
  simp only [transferPolynomial, one_lt_rootMultiplicity_iff]
  constructor
  · rintro ⟨x, hb, hc⟩
    refine ⟨![p 0, x], ?_⟩
    funext i
    fin_cases i <;> simp [repeatedRootParam, ← hb, ← hc]
  · rintro ⟨t, rfl⟩
    exact ⟨t 1, by simp [repeatedRootParam]⟩

abbrev ParameterRing (K : Type*) [CommSemiring K] := MvPolynomial (Fin 2) K

/-- Substitution of the zero-root hyperplane into coefficient polynomials. -/
def zeroRootSubstitution [Field K] : CoefficientRing K →ₐ[K] ParameterRing K :=
  MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 1, 0]

/-- Substitution of the two-parameter repeated-root map into coefficient polynomials. -/
def repeatedRootSubstitution [Field K] : CoefficientRing K →ₐ[K] ParameterRing K :=
  let a : ParameterRing K := MvPolynomial.X 0
  let x : ParameterRing K := MvPolynomial.X 1
  MvPolynomial.aeval ![a, 4 * x^3 - 3 * x^2 + 2 * a * x, 3 * x^4 - 2 * x^3 + a * x^2]

private theorem eval_zeroRootSubstitution [Field K] (t : Parameters K) (f : CoefficientRing K) :
    MvPolynomial.eval t (zeroRootSubstitution f) = MvPolynomial.eval (zeroRootParam t) f := by
  rw [zeroRootSubstitution, ← MvPolynomial.aeval_eq_eval, MvPolynomial.comp_aeval_apply,
    MvPolynomial.aeval_eq_eval]
  apply congrArg (fun v : Coefficients K => MvPolynomial.eval v f)
  funext i
  fin_cases i <;> simp [zeroRootParam, MvPolynomial.aeval_eq_eval]

private theorem eval_repeatedRootSubstitution [Field K]
    (t : Parameters K) (f : CoefficientRing K) :
    MvPolynomial.eval t (repeatedRootSubstitution f) =
      MvPolynomial.eval (repeatedRootParam t) f := by
  rw [repeatedRootSubstitution, ← MvPolynomial.aeval_eq_eval, MvPolynomial.comp_aeval_apply,
    MvPolynomial.aeval_eq_eval]
  apply congrArg (fun v : Coefficients K => MvPolynomial.eval v f)
  funext i
  fin_cases i <;> simp [repeatedRootParam, MvPolynomial.aeval_eq_eval]

variable [Field K]

private theorem vanishingIdeal_range_eq_ker [Infinite K]
    (s : Parameters K → Coefficients K) (S : CoefficientRing K →ₐ[K] ParameterRing K)
    (hs : ∀ t f, MvPolynomial.eval t (S f) = MvPolynomial.eval (s t) f) :
    MvPolynomial.vanishingIdeal K (Set.range s) = RingHom.ker S.toRingHom := by
  ext f
  rw [MvPolynomial.mem_vanishingIdeal_iff, RingHom.mem_ker]
  change (∀ p ∈ Set.range s, MvPolynomial.eval p f = 0) ↔ S f = 0
  constructor
  · intro hf
    apply MvPolynomial.funext
    intro t
    rw [hs, map_zero]
    exact hf (s t) (Set.mem_range_self t)
  · rintro hf _ ⟨t, rfl⟩
    rw [← hs, hf, map_zero]

theorem zeroRoot_vanishingIdeal_eq_ker [Infinite K] :
    MvPolynomial.vanishingIdeal K (zeroRootLocus (K := K)) = RingHom.ker
      (zeroRootSubstitution (K := K)).toRingHom := by
  rw [zeroRootLocus_eq_range]
  exact vanishingIdeal_range_eq_ker _ _ eval_zeroRootSubstitution

theorem repeatedRoot_vanishingIdeal_eq_ker [Infinite K] :
    MvPolynomial.vanishingIdeal K (repeatedRootLocus (K := K)) = RingHom.ker
      (repeatedRootSubstitution (K := K)).toRingHom := by
  rw [repeatedRootLocus_eq_range]
  exact vanishingIdeal_range_eq_ker _ _ eval_repeatedRootSubstitution

theorem zeroRoot_vanishingIdeal_isPrime [Infinite K] :
    (MvPolynomial.vanishingIdeal K (zeroRootLocus (K := K))).IsPrime := by
  rw [zeroRoot_vanishingIdeal_eq_ker]
  exact RingHom.ker_isPrime _

theorem repeatedRoot_vanishingIdeal_isPrime [Infinite K] :
    (MvPolynomial.vanishingIdeal K (repeatedRootLocus (K := K))).IsPrime := by
  rw [repeatedRoot_vanishingIdeal_eq_ker]
  exact RingHom.ker_isPrime _

/-- The zero-root locus is the ordinary third-coordinate hyperplane. -/
theorem zeroRootLocus_eq_zeroLocus :
    (zeroRootLocus : Set (Coefficients K)) =
      MvPolynomial.zeroLocus K (Ideal.span {(MvPolynomial.X 2 : CoefficientRing K)}) := by
  ext p
  rw [mem_zeroRootLocus_iff, MvPolynomial.zeroLocus_span]
  simp

theorem mem_repeatedRootLocus_iff_not_squarefree [CharZero K] (p : Coefficients K)
    (hs : (transferPolynomial p).Splits) :
    p ∈ repeatedRootLocus ↔ ¬ Squarefree (transferPolynomial p) := by
  classical
  have hne : transferPolynomial p ≠ 0 := quartic_ne_zero _ _ _
  rw [← PerfectField.separable_iff_squarefree, ← Polynomial.nodup_roots_iff_of_splits hne hs]
  simp only [Multiset.nodup_iff_count_le_one, not_forall, not_le, Polynomial.count_roots]
  rfl

/-- The universal quartic's Sylvester determinant, of degrees four and three. -/
def discriminant : CoefficientRing K :=
  let F := quartic (MvPolynomial.X 0 : CoefficientRing K)
    (MvPolynomial.X 1) (MvPolynomial.X 2)
  F.resultant F.derivative 4 3

theorem eval_discriminant [CharZero K] (p : Coefficients K) :
    MvPolynomial.eval p discriminant =
      (transferPolynomial p).resultant (transferPolynomial p).derivative := by
  let F := quartic (MvPolynomial.X 0 : CoefficientRing K)
    (MvPolynomial.X 1) (MvPolynomial.X 2)
  have hmap : F.map (MvPolynomial.eval p) = transferPolynomial p := by
    simp [F, transferPolynomial, quartic, MvPolynomial.eval_X]
  change MvPolynomial.eval p (F.resultant F.derivative 4 3) = _
  rw [← Polynomial.resultant_map_map, ← Polynomial.derivative_map, hmap]
  unfold transferPolynomial
  rw [quartic_natDegree, quartic_derivative_natDegree]

/-- Over an algebraically closed characteristic-zero field the polynomial image is closed. -/
theorem repeatedRootLocus_eq_zeroLocus [CharZero K] [IsAlgClosed K] :
    (repeatedRootLocus : Set (Coefficients K)) =
      MvPolynomial.zeroLocus K (Ideal.span {(discriminant : CoefficientRing K)}) := by
  ext p
  have hne : transferPolynomial p ≠ 0 := quartic_ne_zero _ _ _
  rw [mem_repeatedRootLocus_iff_not_squarefree p (IsAlgClosed.splits _),
    ← PerfectField.separable_iff_squarefree, Polynomial.separable_def,
    MvPolynomial.zeroLocus_span]
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, forall_eq, MvPolynomial.aeval_eq_eval,
    eval_discriminant, Polynomial.resultant_eq_zero_iff]
  exact ⟨fun h => ⟨Or.inl hne, h⟩, And.right⟩

theorem repeatedRoot_vanishingIdeal_eq_radical [CharZero K] [IsAlgClosed K] :
    MvPolynomial.vanishingIdeal K (repeatedRootLocus (K := K)) =
      (Ideal.span {(discriminant : CoefficientRing K)}).radical := by
  rw [repeatedRootLocus_eq_zeroLocus, MvPolynomial.vanishingIdeal_zeroLocus_eq_radical]

/-- The coefficient guard used in the transfer radical chart. -/

@[simp] theorem eval_guard (p : Coefficients K) :
    MvPolynomial.eval p guard = p 2 - (p 1)^2 := by
  simp [guard, MvPolynomial.eval_X]

/-- On the zero-root hyperplane, the guard is nonzero exactly when the zero root is simple. -/
theorem zeroRoot_guard_ne_zero_iff (p : Coefficients K) (hp : p ∈ zeroRootLocus) :
    MvPolynomial.eval p guard ≠ 0 ↔ (transferPolynomial p).rootMultiplicity 0 = 1 := by
  have hc := (mem_zeroRootLocus_iff p).mp hp
  have hpos : 0 < (transferPolynomial p).rootMultiplicity 0 :=
    (Polynomial.rootMultiplicity_pos (quartic_ne_zero (p 0) (p 1) (p 2))).mpr hp
  rw [eval_guard, hc, zero_sub, neg_ne_zero, pow_ne_zero_iff two_ne_zero]
  rw [show (transferPolynomial p).rootMultiplicity 0 = 1 ↔
      ¬ 1 < (transferPolynomial p).rootMultiplicity 0 by omega,
    one_lt_zero_rootMultiplicity_iff, and_iff_left hc]

/-- The coefficients of the common rational witness, also usable in characteristic zero. -/
def commonCoefficients : Coefficients K := ![-5, 3, 0]

theorem commonCoefficients_spec [CharZero K] :
    (commonCoefficients : Coefficients K) ∈ zeroRootLocus ∧
    1 < (transferPolynomial (commonCoefficients : Coefficients K)).rootMultiplicity (-1) ∧
    MvPolynomial.eval (commonCoefficients : Coefficients K) (guard : CoefficientRing K) = -9 := by
  rw [mem_zeroRootLocus_iff, eval_guard]
  simp only [transferPolynomial, one_lt_rootMultiplicity_iff]
  norm_num [commonCoefficients]

theorem commonCoefficients_mem_repeatedRootLocus [CharZero K] :
    (commonCoefficients : Coefficients K) ∈ repeatedRootLocus :=
  ⟨-1, commonCoefficients_spec.2.1⟩

private theorem guard_notMem_vanishingIdeal [CharZero K] {V : Set (Coefficients K)}
    (hV : commonCoefficients ∈ V) :
    (guard : CoefficientRing K) ∉ MvPolynomial.vanishingIdeal K V := by
  intro h
  have he : MvPolynomial.eval (commonCoefficients : Coefficients K) (guard : CoefficientRing K) = 0 :=
    MvPolynomial.mem_vanishingIdeal_iff.mp h _ hV
  rw [commonCoefficients_spec.2.2] at he
  norm_num at he

theorem guard_notMem_zeroRoot_ideal [CharZero K] :
    (guard : CoefficientRing K) ∉ MvPolynomial.vanishingIdeal K (zeroRootLocus (K := K)) :=
  guard_notMem_vanishingIdeal commonCoefficients_spec.1

theorem guard_notMem_repeatedRoot_ideal [CharZero K] :
    (guard : CoefficientRing K) ∉ MvPolynomial.vanishingIdeal K (repeatedRootLocus (K := K)) :=
  guard_notMem_vanishingIdeal commonCoefficients_mem_repeatedRootLocus

/-- On a prime coefficient locus, removing the vanishing set of a nonzero class
preserves the vanishing ideal. -/
private theorem vanishingIdeal_guard_open {V : Set (Coefficients K)}
    (hprime : (MvPolynomial.vanishingIdeal K V).IsPrime)
    (hg : (guard : CoefficientRing K) ∉ MvPolynomial.vanishingIdeal K V) :
    MvPolynomial.vanishingIdeal K {p ∈ V | MvPolynomial.eval p guard ≠ 0} =
      MvPolynomial.vanishingIdeal K V := by
  refine le_antisymm ?_ (MvPolynomial.vanishingIdeal_anti_mono fun _ hp => hp.1)
  intro f hf
  have hprod : guard * f ∈ MvPolynomial.vanishingIdeal K V := by
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    intro p hp
    rw [MvPolynomial.aeval_eq_eval, map_mul]
    by_cases hz : MvPolynomial.eval p (guard : CoefficientRing K) = 0
    · rw [hz, zero_mul]
    · exact mul_eq_zero_of_right _ (MvPolynomial.mem_vanishingIdeal_iff.mp hf p ⟨hp, hz⟩)
  exact (hprime.mem_or_mem hprod).resolve_left hg

theorem zeroRoot_vanishingIdeal_guard_open [CharZero K] :
    MvPolynomial.vanishingIdeal K
        {p ∈ zeroRootLocus (K := K) | MvPolynomial.eval p guard ≠ 0} =
      MvPolynomial.vanishingIdeal K (zeroRootLocus (K := K)) :=
  vanishingIdeal_guard_open zeroRoot_vanishingIdeal_isPrime guard_notMem_zeroRoot_ideal

theorem repeatedRoot_vanishingIdeal_guard_open [CharZero K] :
    MvPolynomial.vanishingIdeal K
        {p ∈ repeatedRootLocus (K := K) | MvPolynomial.eval p guard ≠ 0} =
      MvPolynomial.vanishingIdeal K (repeatedRootLocus (K := K)) :=
  vanishingIdeal_guard_open repeatedRoot_vanishingIdeal_isPrime guard_notMem_repeatedRoot_ideal

/-- The guard is nonzero in the zero-root coordinate ring. -/
theorem guard_zeroRoot_quotient_ne_zero [CharZero K] :
    Ideal.Quotient.mk (MvPolynomial.vanishingIdeal K (zeroRootLocus (K := K))) guard ≠ 0 :=
  fun h => guard_notMem_zeroRoot_ideal (Ideal.Quotient.eq_zero_iff_mem.mp h)

/-- The guard is nonzero in the repeated-root coordinate ring. -/
theorem guard_repeatedRoot_quotient_ne_zero [CharZero K] :
    Ideal.Quotient.mk (MvPolynomial.vanishingIdeal K (repeatedRootLocus (K := K))) guard ≠ 0 :=
  fun h => guard_notMem_repeatedRoot_ideal (Ideal.Quotient.eq_zero_iff_mem.mp h)

theorem guard_zeroRoot_fraction_ne_zero [CharZero K] :
    let I := MvPolynomial.vanishingIdeal K (zeroRootLocus (K := K))
    algebraMap _ (FractionRing (CoefficientRing K ⧸ I)) (Ideal.Quotient.mk I guard) ≠ 0 := by
  dsimp only
  exact fun h => guard_zeroRoot_quotient_ne_zero
    ((IsFractionRing.to_map_eq_zero_iff).mp h)

theorem guard_repeatedRoot_fraction_ne_zero [CharZero K] :
    let I := MvPolynomial.vanishingIdeal K (repeatedRootLocus (K := K))
    algebraMap _ (FractionRing (CoefficientRing K ⧸ I)) (Ideal.Quotient.mk I guard) ≠ 0 := by
  dsimp only
  exact fun h => guard_repeatedRoot_quotient_ne_zero
    ((IsFractionRing.to_map_eq_zero_iff).mp h)

/-- The coefficients of the native spectrum on the trace-aligned chart. -/
def traceAlignedCoefficients (ket bra : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (k : ℂ) : Coefficients ℂ :=
  let d := (ket 0).det
  let db := (bra 0).det
  let e := (ket 1).det
  let eb := (bra 1).det
  let U := d * db
  let a := d + db - 2 * (U + e * eb) - k ^ 2
  let b := U - e * eb
  let c := b ^ 2 + k ^ 2 * (d + eb) * (db + e)
  ![a, b, c]

theorem traceAligned_charpoly_eq
    (ket bra : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) (k : ℂ)
    (hket0 : (ket 0).trace = 1) (hket1 : (ket 1).trace = 0)
    (hbra0 : (bra 0).trace = 1) (hbra1 : (bra 1).trace = 0)
    (hket01 : (ket 0 * ket 1).trace = k) (hbra01 : (bra 0 * bra 1).trace = k) :
    (ket 0 ⊗ₖ bra 0 + ket 1 ⊗ₖ bra 1).charpoly =
      transferPolynomial (traceAlignedCoefficients ket bra k) := by
  simpa [transferPolynomial, traceAlignedCoefficients, quartic] using
    PeriodicMPSUniformTransferSpectrum.ketFirst_charpoly_trace_aligned
      ket bra k hket0 hket1 hbra0 hbra1 hket01 hbra01

theorem traceAligned_charpoly_loci
    (ket bra : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) (k : ℂ)
    (hket0 : (ket 0).trace = 1) (hket1 : (ket 1).trace = 0)
    (hbra0 : (bra 0).trace = 1) (hbra1 : (bra 1).trace = 0)
    (hket01 : (ket 0 * ket 1).trace = k) (hbra01 : (bra 0 * bra 1).trace = k) :
    let T := ket 0 ⊗ₖ bra 0 + ket 1 ⊗ₖ bra 1
    let p := traceAlignedCoefficients ket bra k
    (T.charpoly.IsRoot 0 ↔ p 2 = 0) ∧
    ((∃ x : ℂ, 1 < T.charpoly.rootMultiplicity x) ↔ MvPolynomial.eval p discriminant = 0) := by
  dsimp only
  rw [traceAligned_charpoly_eq ket bra k hket0 hket1 hbra0 hbra1 hket01 hbra01]
  refine ⟨mem_zeroRootLocus_iff _, ?_⟩
  change _ ∈ repeatedRootLocus ↔ _
  rw [repeatedRootLocus_eq_zeroLocus, MvPolynomial.zeroLocus_span]
  simp [MvPolynomial.aeval_eq_eval]

/-- The exact transfer polynomial of the checked literal rational cores. -/
theorem rationalWitness_charpoly :
    PeriodicMPSCommonSpectralJets.baseTransfer.charpoly =
      transferPolynomial (commonCoefficients : Coefficients ℚ) := by
  rw [PeriodicMPSCommonSpectralJets.baseTransfer_charpoly]
  norm_num [transferPolynomial, commonCoefficients, quartic, map_ofNat]
  ring

theorem rationalWitness_double_root :
    PeriodicMPSCommonSpectralJets.baseTransfer.charpoly.rootMultiplicity (-1) = 2 := by
  rw [PeriodicMPSCommonSpectralJets.baseTransfer_charpoly]
  have h : (X * (X - 3) : ℚ[X]).rootMultiplicity (-1) = 0 := by
    apply Polynomial.rootMultiplicity_eq_zero
    norm_num [Polynomial.IsRoot]
  have hne : (X * (X - 3) : ℚ[X]) ≠ 0 := by
    intro hz
    have hv := congrArg (Polynomial.eval (-1 : ℚ)) hz
    norm_num at hv
  have hfactor : (X + 1 : ℚ[X]) = X - C (-1 : ℚ) := by simp
  rw [hfactor, Polynomial.rootMultiplicity_mul_X_sub_C_pow hne, h, zero_add]

/-- The rational transfer witness separates the guard on both coefficient loci
at every suffix length used in the all-length rank argument. -/
theorem rationalWitness_common_loci_and_minor {m : ℕ} (hm : 5 ≤ m) :
    PeriodicMPSCommonSpectralJets.baseTransfer.charpoly.IsRoot 0 ∧
    1 < PeriodicMPSCommonSpectralJets.baseTransfer.charpoly.rootMultiplicity (-1) ∧
    MvPolynomial.eval (commonCoefficients : Coefficients ℚ) guard ≠ 0 ∧
    (PeriodicMPSCommonSpectralJets.literalJacobian m).det ≠ 0 := by
  rw [rationalWitness_charpoly]
  exact ⟨(commonCoefficients_spec (K := ℚ)).1, (commonCoefficients_spec (K := ℚ)).2.1,
    by
      rw [(commonCoefficients_spec (K := ℚ)).2.2]
      norm_num,
    PeriodicMPSCommonSpectralDeterminant.literalJacobian_det_ne_zero hm⟩

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformSpecialSpectralBases
