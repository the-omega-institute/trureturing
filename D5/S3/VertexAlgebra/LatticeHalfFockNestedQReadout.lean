/- GID: D5/S3/VertexAlgebra/LatticeHalfFockNestedQReadout
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockNestedQReadout
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual nested Q readouts and finite signed collision Taylor balance. -/

import D5.S3.VertexAlgebra.LatticeHalfFockClearedTaylorReadout

/-! Complete intermediate-field cutoffs precede expansion of the inner
ordered halves. The original source and acted-on tensor carriers stay distinct.
Classical local-field calculus: Matsuo--Nagatomo; twisted lattice setting:
Bakalov--Kac, math/0402315. Hahn operations: mathlib, Apache 2.0. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockNestedQReadout
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockClearedTaylorReadout
open UniformGradedLocalCorrelator
open SupportedFieldWords.OrderedWords SupportedFieldWords.OrderedDistribution
open CollisionRationalExpansions.OrderedRationalExpansion
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open scoped BigOperators VertexOperator
noncomputable section

section NestedReadout
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
open StateFieldResidueReconstruction

/-- Finite complete residue extraction. The right bound uses the complete
first field on the actual input; it does not bound its ordered halves. -/
def finiteQReadout (s r : ℤ) (K : ℕ) (A B : VertexOperator ℂ V)
    (x : V) (n : ℤ) (forward backward : ℤ → ℤ → ℂ) : ℂ :=
  ∑ ell ∈ Finset.range ((K : ℤ) - r).toNat,
    Ring.choose (-(s : ℂ) / 2) ell *
      ((∑ u ∈ Finset.range
          (-((HahnModule.of ℂ).symm (B x)).order - (n - ell)).toNat,
        BinomialKernelDelta.chooseSign (r + ell) u *
          forward (r + ell - u) (n - ell + u)) -
       epsilon (r + ell) *
        ∑ u ∈ Finset.range (-((HahnModule.of ℂ).symm (A x)).order).toNat,
          BinomialKernelDelta.chooseSign (r + ell) u * backward (r + n - u) u)

/-- Residue extraction over the supported mode fibers. Each complete inner
residue is formed before it enters an outer residue. -/
def supportedQReadout (s r : ℤ) (K : ℕ) (n : ℤ)
    (forward backward : ℤ → ℤ → ℂ) : ℂ :=
  ∑ ell ∈ Finset.range ((K : ℤ) - r).toNat,
    Ring.choose (-(s : ℂ) / 2) ell *
      ((∑ᶠ u : ℕ, BinomialKernelDelta.chooseSign (r + ell) u *
          forward (r + ell - u) (n - ell + u)) -
       epsilon (r + ell) *
        ∑ᶠ u : ℕ, BinomialKernelDelta.chooseSign (r + ell) u *
          backward (r + n - u) u)

/-- Finiteness is asserted for each complete residue fiber, rather than for
the individual words obtained by expanding an intermediate field. -/
def QReadoutSupported (r : ℤ) (K : ℕ) (n : ℤ)
    (forward backward : ℤ → ℤ → ℂ) : Prop :=
  ∀ ell ∈ Finset.range ((K : ℤ) - r).toNat,
    Function.HasFiniteSupport (fun u : ℕ =>
      BinomialKernelDelta.chooseSign (r + ell) u *
        forward (r + ell - u) (n - ell + u)) ∧
    Function.HasFiniteSupport (fun u : ℕ =>
      BinomialKernelDelta.chooseSign (r + ell) u * backward (r + n - u) u)

private theorem actual_q_support (r : ℤ) (K : ℕ)
    (A B : VertexOperator ℂ V) (x : V) (n : ℤ) (phi : V →ₗ[ℂ] ℂ) :
    QReadoutSupported r K n
      (fun m k => phi ((A[[m]]) ((B[[k]]) x)))
      (fun m k => phi ((B[[m]]) ((A[[k]]) x))) := by
  intro ell hell
  constructor
  · apply (Finset.range
      (-((HahnModule.of ℂ).symm (B x)).order - (n - ell)).toNat).finite_toSet.subset
    intro u hu
    apply Finset.mem_range.mpr
    by_contra outside
    have hz : (B[[n - ell + u]]) x = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      omega
    exact hu (by simp [hz])
  · apply (Finset.range (-((HahnModule.of ℂ).symm (A x)).order).toNat).finite_toSet.subset
    intro u hu
    apply Finset.mem_range.mpr
    by_contra outside
    have hz : (A[[(u : ℤ)]]) x = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      omega
    exact hu (by simp [hz])

private theorem supportedQReadout_eq (s r : ℤ) (K : ℕ)
    (A B : VertexOperator ℂ V) (x : V) (n : ℤ) (phi : V →ₗ[ℂ] ℂ) :
    phi (((qField s r K A B)[[n]]) x) = supportedQReadout s r K n
      (fun m k => phi ((A[[m]]) ((B[[k]]) x)))
      (fun m k => phi ((B[[m]]) ((A[[k]]) x))) := by
  rw [D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport.qField_mode, map_sum]
  apply Finset.sum_congr rfl
  intro ell hell
  rw [map_smul]
  congr 1
  unfold fieldResidueCoefficient fieldResidueLeft fieldResidueRight
  rw [map_sub, map_smul,
    map_finsum phi ((fieldResidue (r + ell) A B).left_finite (n - ell) x),
    map_finsum phi ((fieldResidue (r + ell) A B).right_finite (n - ell) x)]
  simp only [map_smul, smul_eq_mul, BinomialKernelDelta.chooseSign, integerBinomial,
    show r + (ell : ℤ) + (n - ell) = r + n by omega]

/-- The complete ordinary outer residue at fractional offset ell. The two
ordered contributions are combined before any outer support assertion. -/
def completeOuterResidue (r n : ℤ) (f g : ℤ → ℤ → ℂ) (ell : ℕ) : ℂ :=
  (∑ᶠ u : ℕ, BinomialKernelDelta.chooseSign (r + ell) u *
    f (r + ell - u) (n - ell + u)) -
  epsilon (r + ell) * ∑ᶠ u : ℕ,
    BinomialKernelDelta.chooseSign (r + ell) u * g (r + n - u) u

/-- The fractional series is summed only after forming each complete residue. -/
def completeOuterQReadout (s r n : ℤ) (f g : ℤ → ℤ → ℂ) : ℂ :=
  ∑ᶠ ell : ℕ, Ring.choose (-(s : ℂ) / 2) ell * completeOuterResidue r n f g ell

/-- A locality order bounds the support of the complete residue, and every
larger fractional cutoff computes its unrestricted, finitely supported sum. -/
def OuterQCompletion (s r n : ℤ) (H : ℕ) (f g : ℤ → ℤ → ℂ) : Prop :=
  Function.support (completeOuterResidue r n f g) ⊆
    (Finset.range ((H : ℤ) - r).toNat : Set ℕ) ∧
  ∀ H' : ℕ, H ≤ H' →
    supportedQReadout s r H' n f g = completeOuterQReadout s r n f g

private theorem qField_high (s r : ℤ) (A B : VertexOperator ℂ V) (H H' : ℕ)
    (locality : (FieldNormalProductLocality.deltaEnd ^ H)
      (FieldNormalProductLocality.commutator A B) = 0)
    (high : (H : ℤ) ≤ r) : qField s r H' A B = 0 := by
  classical
  unfold qField
  apply Finset.sum_eq_zero
  intro ell member
  rw [ordinaryResidue_tail A B H locality (r + ell) (by omega)]
  suffices modeShift (ell : ℤ) (0 : VertexOperator ℂ V) = 0 by simp [this]
  apply HVertexOperator.coeff_inj
  funext e
  apply LinearMap.ext
  intro x
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff]
  rfl

private theorem completeOuterResidue_single (s r n : ℤ)
    (f g : ℤ → ℤ → ℂ) (ell : ℕ) (nonnegative : 0 ≤ r + ell) :
    completeOuterResidue r n f g ell =
      supportedQReadout s (r + ell) ((r + ell).toNat + 1) (n - ell) f g := by
  have cutoff : (((r + ell).toNat + 1 : ℕ) : ℤ) - (r + ell) = 1 := by omega
  simp only [supportedQReadout, cutoff, Int.toNat_one, Finset.sum_range_one,
    Ring.choose_zero_right, one_mul]
  unfold completeOuterResidue
  simp only [Nat.cast_zero, add_zero, sub_zero,
    show r + (ell : ℤ) + (n - ell) = r + n by omega]

private theorem completeOuterQReadout_of_support (s r n : ℤ) (H : ℕ)
    (f g : ℤ → ℤ → ℂ)
    (support : Function.support (completeOuterResidue r n f g) ⊆
      (Finset.range ((H : ℤ) - r).toNat : Set ℕ)) :
    OuterQCompletion s r n H f g := by
  classical
  refine ⟨support, ?_⟩
  intro H' larger
  unfold completeOuterQReadout
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range ((H' : ℤ) - r).toNat) (by
    intro ell nonzero
    have original : ell ∈ Finset.range ((H : ℤ) - r).toNat :=
      support (Function.mem_support.mpr (fun zero => nonzero (by simp [zero])))
    apply Finset.mem_range.mpr
    have bound := Finset.mem_range.mp original
    omega)]
  rfl

private theorem completeOuterQReadout_of_locality (s r n : ℤ) (H : ℕ)
    (A B : VertexOperator ℂ V) (x : V) (phi : V →ₗ[ℂ] ℂ)
    (f g : ℤ → ℤ → ℂ)
    (locality : (FieldNormalProductLocality.deltaEnd ^ H)
      (FieldNormalProductLocality.commutator A B) = 0)
    (matched : ∀ ell : ℕ, (H : ℤ) ≤ r + ell →
      supportedQReadout s (r + ell) ((r + ell).toNat + 1) (n - ell) f g =
        phi (((qField s (r + ell) ((r + ell).toNat + 1) A B)[[n - ell]]) x)) :
    OuterQCompletion s r n H f g := by
  apply completeOuterQReadout_of_support
  intro ell nonzero
  apply Finset.mem_range.mpr
  by_contra outside
  have high : (H : ℤ) ≤ r + ell := by omega
  apply nonzero
  rw [completeOuterResidue_single s r n f g ell (by omega), matched ell high,
    qField_high s (r + ell) A B H _ locality high]
  simp

private theorem supportedQReadout_congr (s r : ℤ) (K : ℕ) (n : ℤ)
    (f g f' g' : ℤ → ℤ → ℂ)
    (hf : ∀ m k, m + k = r + n → f m k = f' m k)
    (hg : ∀ m k, m + k = r + n → g m k = g' m k) :
    supportedQReadout s r K n f g = supportedQReadout s r K n f' g' := by
  unfold supportedQReadout
  apply Finset.sum_congr rfl
  intro ell hell
  congr 2
  · apply finsum_congr
    intro u
    rw [hf _ _ (by omega)]
  · congr 1
    apply finsum_congr
    intro u
    rw [hg _ _ (by omega)]

private theorem QReadoutSupported_congr (r : ℤ) (K : ℕ) (n : ℤ)
    (f g f' g' : ℤ → ℤ → ℂ)
    (hf : ∀ m k, m + k = r + n → f m k = f' m k)
    (hg : ∀ m k, m + k = r + n → g m k = g' m k) :
    QReadoutSupported r K n f g ↔ QReadoutSupported r K n f' g' := by
  unfold QReadoutSupported
  have forward (ell : ℕ) :
      (fun u : ℕ => BinomialKernelDelta.chooseSign (r + ell) u *
        f (r + ell - u) (n - ell + u)) =
      (fun u : ℕ => BinomialKernelDelta.chooseSign (r + ell) u *
        f' (r + ell - u) (n - ell + u)) := by
    funext u
    rw [hf _ _ (by omega)]
  have backward (ell : ℕ) :
      (fun u : ℕ => BinomialKernelDelta.chooseSign (r + ell) u * g (r + n - u) u) =
      (fun u : ℕ => BinomialKernelDelta.chooseSign (r + ell) u * g' (r + n - u) u) := by
    funext u
    rw [hg _ _ (by omega)]
  simp only [forward, backward]

private theorem finiteQReadout_eq (s r : ℤ) (K : ℕ)
    (A B : VertexOperator ℂ V) (x : V) (n : ℤ) (phi : V →ₗ[ℂ] ℂ) :
    phi (((qField s r K A B)[[n]]) x) = finiteQReadout s r K A B x n
      (fun m k => phi ((A[[m]]) ((B[[k]]) x)))
      (fun m k => phi ((B[[m]]) ((A[[k]]) x))) := by
  classical
  rw [D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport.qField_mode, map_sum]
  apply Finset.sum_congr rfl
  intro ell hell
  rw [map_smul]
  congr 1
  unfold fieldResidueCoefficient fieldResidueLeft fieldResidueRight
  have left := (fieldResidue (r + ell) A B).left_finite (n - ell) x
  have right := (fieldResidue (r + ell) A B).right_finite (n - ell) x
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range
    (-((HahnModule.of ℂ).symm (B x)).order - (n - ell)).toNat) (by
      intro u hu
      apply Finset.mem_range.mpr
      by_contra outside
      have hz : (B[[n - ell + u]]) x = 0 := by
        apply VertexOperator.ncoeff_eq_zero_of_lt_order
        omega
      exact hu (by simp [hz]))]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range
    (-((HahnModule.of ℂ).symm (A x)).order).toNat) (by
      intro u hu
      apply Finset.mem_range.mpr
      by_contra outside
      have hz : (A[[(u : ℤ)]]) x = 0 := by
        apply VertexOperator.ncoeff_eq_zero_of_lt_order
        omega
      exact hu (by simp [hz]))]
  simp only [map_sub, map_sum, map_smul, smul_eq_mul]
  simp only [BinomialKernelDelta.chooseSign, integerBinomial,
    show r + (ell : ℤ) + (n - ell) = r + n by omega]

private theorem finiteQReadout_congr (s r : ℤ) (K : ℕ)
    (A B : VertexOperator ℂ V) (x : V) (n : ℤ)
    (f g f' g' : ℤ → ℤ → ℂ)
    (hf : ∀ m k, m + k = r + n → f m k = f' m k)
    (hg : ∀ m k, m + k = r + n → g m k = g' m k) :
    finiteQReadout s r K A B x n f g = finiteQReadout s r K A B x n f' g' := by
  unfold finiteQReadout
  apply Finset.sum_congr rfl
  intro ell hell
  congr 2
  · apply Finset.sum_congr rfl
    intro u hu
    rw [hf _ _ (by omega)]
  · congr 1
    apply Finset.sum_congr rfl
    intro u hu
    rw [hg _ _ (by omega)]

/-- The six labelled orders, from 012 through 210 in lexicographic order. -/
def triplePermutation (order : Fin 6) : Equiv.Perm (Fin 3) :=
  ![Equiv.refl _, Equiv.swap 1 2, Equiv.swap 0 1,
    Equiv.ofBijective ![1, 2, 0] (by decide),
    Equiv.ofBijective ![2, 0, 1] (by decide), Equiv.swap 0 2] order

private def tripleScalar (A B C : VertexOperator ℂ V) (x : V)
    (phi : V →ₗ[ℂ] ℂ) (order : Fin 6) (modes : Exponent 3) : ℂ :=
  phi (coefficientDistribution ![A, B, C] x 1
    (List.ofFn (triplePermutation order)) (fun j => -modes j - 1))

/-- Left nesting, retaining the two inner chambers inside each finite outer
range. Every inner range is recomputed on its actual intermediate vector. -/
def nestedLeftReadout (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (A B C : VertexOperator ℂ V) (x : V) (R : Fin 6 → Exponent 3 → ℂ) : ℂ :=
  finiteQReadout outerLift r H (qField innerLift d K A B) C x n
    (fun k l => finiteQReadout innerLift d K A B ((C[[l]]) x) k
      (fun m p => R 0 ![m, p, l]) (fun m p => R 2 ![p, m, l]))
    (fun k l => finiteQReadout innerLift d K A B x l
      (fun m p => R 4 ![m, p, k]) (fun m p => R 5 ![p, m, k]))

/-- Right nesting with the complete inner field supplying the outer left
cutoff, and the actual first-field input supplying the outer right cutoff. -/
def nestedRightReadout (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (A B C : VertexOperator ℂ V) (x : V) (R : Fin 6 → Exponent 3 → ℂ) : ℂ :=
  finiteQReadout outerLift r H A (qField innerLift d K B C) x n
    (fun k l => finiteQReadout innerLift d K B C x l
      (fun m p => R 0 ![k, m, p]) (fun m p => R 1 ![k, p, m]))
    (fun k l => finiteQReadout innerLift d K B C ((A[[l]]) x) k
      (fun m p => R 3 ![l, m, p]) (fun m p => R 5 ![l, p, m]))

/-- The left nesting has no chosen intermediate mode bounds. The complete
inner differences remain inside the supported outer fibers. -/
def supportedNestedLeftReadout (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (R : Fin 6 → Exponent 3 → ℂ) : ℂ :=
  supportedQReadout outerLift r H n
    (fun k l => supportedQReadout innerLift d K k
      (fun m p => R 0 ![m, p, l]) (fun m p => R 2 ![p, m, l]))
    (fun k l => supportedQReadout innerLift d K l
      (fun m p => R 4 ![m, p, k]) (fun m p => R 5 ![p, m, k]))

/-- The right nesting retains both complete inner differences before taking
the outer supported residue. -/
def supportedNestedRightReadout (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (R : Fin 6 → Exponent 3 → ℂ) : ℂ :=
  supportedQReadout outerLift r H n
    (fun k l => supportedQReadout innerLift d K l
      (fun m p => R 0 ![k, m, p]) (fun m p => R 1 ![k, p, m]))
    (fun k l => supportedQReadout innerLift d K k
      (fun m p => R 3 ![l, m, p]) (fun m p => R 5 ![l, p, m]))

/-- Support of the complete outer fibers in the left nesting. -/
def NestedLeftSupported (innerLift d r n : ℤ) (K H : ℕ)
    (R : Fin 6 → Exponent 3 → ℂ) : Prop :=
  QReadoutSupported r H n
    (fun k l => supportedQReadout innerLift d K k
      (fun m p => R 0 ![m, p, l]) (fun m p => R 2 ![p, m, l]))
    (fun k l => supportedQReadout innerLift d K l
      (fun m p => R 4 ![m, p, k]) (fun m p => R 5 ![p, m, k])) ∧
  ∀ k l : ℤ, k + l = r + n →
    QReadoutSupported d K k (fun m p => R 0 ![m, p, l]) (fun m p => R 2 ![p, m, l]) ∧
    QReadoutSupported d K l (fun m p => R 4 ![m, p, k]) (fun m p => R 5 ![p, m, k])

/-- Support of the complete outer fibers in the right nesting. -/
def NestedRightSupported (innerLift d r n : ℤ) (K H : ℕ)
    (R : Fin 6 → Exponent 3 → ℂ) : Prop :=
  QReadoutSupported r H n
    (fun k l => supportedQReadout innerLift d K l
      (fun m p => R 0 ![k, m, p]) (fun m p => R 1 ![k, p, m]))
    (fun k l => supportedQReadout innerLift d K k
      (fun m p => R 3 ![l, m, p]) (fun m p => R 5 ![l, p, m])) ∧
  ∀ k l : ℤ, k + l = r + n →
    QReadoutSupported d K l (fun m p => R 0 ![k, m, p]) (fun m p => R 1 ![k, p, m]) ∧
    QReadoutSupported d K k (fun m p => R 3 ![l, m, p]) (fun m p => R 5 ![l, p, m])

open CollisionLaurentKernels.LaurentCollision
open OrderedCollisionCoordinates.ContextualLaurentKernel
open CollisionRationalExpansions.HahnFiberResidue
open CollisionRationalExpansions.FullOrderSpectatorPole

/-- An adjacent fractional residue in a ternary word, with the spectator on
the right. Both complete orders are extracted in their own Hahn carrier. -/
def leftPairFiberQ (s d : ℤ) (K : ℕ) (k l : ℤ)
    (F G : HahnSeries (Indices 3) ℂ) : ℂ :=
  ∑ ell ∈ Finset.range ((K : ℤ) - d).toNat,
    Ring.choose (-(s : ℂ) / 2) ell *
      ((pullFiber (firstEmbedding 0 1 (-1))
        (contextPair ℂ 0 1 (kernelZX ℂ (d + ell)) * F)).coeff
          (exponents 2 ![-k + ell - 1, -l - 1]) -
       (residue 1 1 (contextPair ℂ 0 1 (kernelXZ ℂ (d + ell)) * G)).coeff
          (exponents 2 ![-k + ell - 1, -l - 1]))

/-- The adjacent fractional residue with the spectator on the left. -/
def rightPairFiberQ (s d : ℤ) (K : ℕ) (k l : ℤ)
    (F G : HahnSeries (Indices 3) ℂ) : ℂ :=
  ∑ ell ∈ Finset.range ((K : ℤ) - d).toNat,
    Ring.choose (-(s : ℂ) / 2) ell *
      ((pullFiber (firstEmbedding 1 0 (-1))
        (contextPair ℂ 1 0 (kernelZX ℂ (d + ell)) * F)).coeff
          (exponents 2 ![-l - 1, -k + ell - 1]) -
       (residue 2 0 (contextPair ℂ 1 0 (kernelXZ ℂ (d + ell)) * G)).coeff
          (exponents 2 ![-l - 1, -k + ell - 1]))

private theorem leftPairFiberQ_eq (s d : ℤ) (K : ℕ) (k l : ℤ)
    (F G : HahnSeries (Indices 3) ℂ) :
    leftPairFiberQ s d K k l F G = supportedQReadout s d K k
      (fun m p => F.coeff (exponents 3 ![-m - 1, -p - 1, -l - 1]))
      (fun m p => G.coeff (exponents 3 ![-m - 1, -p - 1, -l - 1])) := by
  unfold leftPairFiberQ supportedQReadout
  apply Finset.sum_congr rfl
  intro ell hell
  congr 2
  · change (contextPair ℂ 0 1 (kernelZX ℂ (d + ell)) * F).coeff _ = _
    rw [(contextual_kernel_extraction ℂ 0 1 (d + ell) F _).2]
    apply finsum_congr
    intro u
    congr 1
    congr 1
    have kernelIndex : pairIndex 0 1 (toLex ((u : ℤ), d + ell - u)) =
        (exponentAddEquiv 3) ![d + ell - u, (u : ℤ), 0] := by
      have base : (0 : Indices 0) = () := by
        change (0 : Unit) = ()
        exact Subsingleton.elim _ _
      change toLex ((0 : ℤ), toLex ((u : ℤ), toLex (d + ell - u, (0 : Indices 0)))) =
        toLex ((0 : ℤ), toLex ((u : ℤ), toLex (d + ell - u, ())))
      rw [base]
      rfl
    rw [kernelIndex]
    change (exponentAddEquiv 3) ![-1, -k + ell - 1, -l - 1] - (exponentAddEquiv 3) ![d + ell - u, (u : ℤ), 0] =
      (exponentAddEquiv 3) ![-(d + ell - u) - 1, -(k - ell + u) - 1, -l - 1]
    rw [← map_sub]
    congr 1
    funext j
    fin_cases j <;> simp <;> omega
  · have constant : contextPair ℂ 0 1
        (HahnSeries.C (HahnSeries.C (epsilon (d + ell)))) =
        HahnSeries.C (epsilon (d + ell)) := by
      simp only [StateFieldResidueReconstruction.epsilon, map_zpow₀, map_neg, map_one]
    change (contextPair ℂ 0 1 (kernelXZ ℂ (d + ell)) * G).coeff _ = _
    rw [D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport.reverse_kernel,
      map_mul, constant, mul_assoc, HahnSeries.C_apply,
      HahnSeries.coeff_single_zero_mul,
      (contextual_kernel_extraction ℂ 0 1 (d + ell) G _).2]
    congr 1
    apply finsum_congr
    intro u
    congr 1
    congr 1
    have kernelIndex : pairIndex 0 1 (toLex ((u : ℤ), d + ell - u)) =
        (exponentAddEquiv 3) ![d + ell - u, (u : ℤ), 0] := by
      have base : (0 : Indices 0) = () := by
        change (0 : Unit) = ()
        exact Subsingleton.elim _ _
      change toLex ((0 : ℤ), toLex ((u : ℤ), toLex (d + ell - u, (0 : Indices 0)))) =
        toLex ((0 : ℤ), toLex ((u : ℤ), toLex (d + ell - u, ())))
      rw [base]
      rfl
    rw [kernelIndex]
    change (exponentAddEquiv 3) ![-k + ell - 1, -1, -l - 1] - (exponentAddEquiv 3) ![d + ell - u, (u : ℤ), 0] =
      (exponentAddEquiv 3) ![-(d + k - u) - 1, -(u : ℤ) - 1, -l - 1]
    rw [← map_sub]
    congr 1
    funext j
    fin_cases j <;> simp <;> omega

private theorem rightPairFiberQ_eq (s d : ℤ) (K : ℕ) (k l : ℤ)
    (F G : HahnSeries (Indices 3) ℂ) :
    rightPairFiberQ s d K k l F G = supportedQReadout s d K k
      (fun m p => F.coeff (exponents 3 ![-l - 1, -m - 1, -p - 1]))
      (fun m p => G.coeff (exponents 3 ![-l - 1, -m - 1, -p - 1])) := by
  unfold rightPairFiberQ supportedQReadout
  apply Finset.sum_congr rfl
  intro ell hell
  congr 2
  · change (contextPair ℂ 1 0 (kernelZX ℂ (d + ell)) * F).coeff _ = _
    rw [(contextual_kernel_extraction ℂ 1 0 (d + ell) F _).2]
    apply finsum_congr
    intro u
    congr 1
    congr 1
    have kernelIndex : pairIndex 1 0 (toLex ((u : ℤ), d + ell - u)) =
        (exponentAddEquiv 3) ![0, d + ell - u, (u : ℤ)] := by
      have base : (0 : Indices 0) = () := by
        change (0 : Unit) = ()
        exact Subsingleton.elim _ _
      change toLex ((u : ℤ), toLex (d + ell - u, toLex ((0 : ℤ), (0 : Indices 0)))) =
        toLex ((u : ℤ), toLex (d + ell - u, toLex ((0 : ℤ), ())))
      rw [base]
      rfl
    rw [kernelIndex]
    change (exponentAddEquiv 3) ![-l - 1, -1, -k + ell - 1] - (exponentAddEquiv 3) ![0, d + ell - u, (u : ℤ)] =
      (exponentAddEquiv 3) ![-l - 1, -(d + ell - u) - 1, -(k - ell + u) - 1]
    rw [← map_sub]
    congr 1
    funext j
    fin_cases j <;> simp <;> omega
  · have constant : contextPair ℂ 1 0
        (HahnSeries.C (HahnSeries.C (epsilon (d + ell)))) =
        HahnSeries.C (epsilon (d + ell)) := by
      simp only [StateFieldResidueReconstruction.epsilon, map_zpow₀, map_neg, map_one]
    change (contextPair ℂ 1 0 (kernelXZ ℂ (d + ell)) * G).coeff _ = _
    rw [D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport.reverse_kernel,
      map_mul, constant, mul_assoc, HahnSeries.C_apply,
      HahnSeries.coeff_single_zero_mul,
      (contextual_kernel_extraction ℂ 1 0 (d + ell) G _).2]
    congr 1
    apply finsum_congr
    intro u
    congr 1
    congr 1
    have kernelIndex : pairIndex 1 0 (toLex ((u : ℤ), d + ell - u)) =
        (exponentAddEquiv 3) ![0, d + ell - u, (u : ℤ)] := by
      have base : (0 : Indices 0) = () := by
        change (0 : Unit) = ()
        exact Subsingleton.elim _ _
      change toLex ((u : ℤ), toLex (d + ell - u, toLex ((0 : ℤ), (0 : Indices 0)))) =
        toLex ((u : ℤ), toLex (d + ell - u, toLex ((0 : ℤ), ())))
      rw [base]
      rfl
    rw [kernelIndex]
    change (exponentAddEquiv 3) ![-l - 1, -k + ell - 1, -1] - (exponentAddEquiv 3) ![0, d + ell - u, (u : ℤ)] =
      (exponentAddEquiv 3) ![-l - 1, -(d + k - u) - 1, -(u : ℤ) - 1]
    rw [← map_sub]
    congr 1
    funext j
    fin_cases j <;> simp <;> omega

/-- Scalar readouts from six genuinely supported, globally labelled carriers. -/
def hahnTripleScalar (W : Fin 6 → HahnSeries (Indices 3) ℂ)
    (order : Fin 6) (modes : Exponent 3) : ℂ :=
  (W order).coeff (orderExponents 3 (triplePermutation order) (fun j => -modes j - 1))

/-- Left nested supported fibers. The complete inner difference is kept
inside each of the two outer residue fibers. -/
def nestedLeftFiberReadout (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (W : Fin 6 → HahnSeries (Indices 3) ℂ) : ℂ :=
  supportedQReadout outerLift r H n
    (fun k l => leftPairFiberQ innerLift d K k l (W 0) (W 2))
    (fun k l => rightPairFiberQ innerLift d K l k (W 4) (W 5))

/-- Right nested supported fibers, with the actual left and right spectator
positions retained in the respective complete orders. -/
def nestedRightFiberReadout (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (W : Fin 6 → HahnSeries (Indices 3) ℂ) : ℂ :=
  supportedQReadout outerLift r H n
    (fun k l => rightPairFiberQ innerLift d K l k (W 0) (W 1))
    (fun k l => leftPairFiberQ innerLift d K k l (W 3) (W 5))

private theorem nestedLeftFiberReadout_eq (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (W : Fin 6 → HahnSeries (Indices 3) ℂ) :
    nestedLeftFiberReadout outerLift innerLift d r n K H W =
      supportedNestedLeftReadout outerLift innerLift d r n K H (hahnTripleScalar W) := by
  unfold nestedLeftFiberReadout supportedNestedLeftReadout
  apply supportedQReadout_congr
  · intro k l hkl
    rw [leftPairFiberQ_eq]
    rfl
  · intro k l hkl
    rw [rightPairFiberQ_eq]
    rfl

private theorem nestedRightFiberReadout_eq (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (W : Fin 6 → HahnSeries (Indices 3) ℂ) :
    nestedRightFiberReadout outerLift innerLift d r n K H W =
      supportedNestedRightReadout outerLift innerLift d r n K H (hahnTripleScalar W) := by
  unfold nestedRightFiberReadout supportedNestedRightReadout
  apply supportedQReadout_congr
  · intro k l hkl
    rw [rightPairFiberQ_eq]
    rfl
  · intro k l hkl
    rw [leftPairFiberQ_eq]
    rfl


private theorem supportedNestedLeftReadout_congr (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (R S : Fin 6 → Exponent 3 → ℂ)
    (same : ∀ order modes, (∑ j, modes j) = d + r + n → R order modes = S order modes) :
    supportedNestedLeftReadout outerLift innerLift d r n K H R =
      supportedNestedLeftReadout outerLift innerLift d r n K H S := by
  unfold supportedNestedLeftReadout
  apply supportedQReadout_congr <;> intro k l hkl <;> apply supportedQReadout_congr <;>
    intro m p hmp <;> apply same <;> simp [Fin.sum_univ_three] <;> omega

private theorem supportedNestedRightReadout_congr (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (R S : Fin 6 → Exponent 3 → ℂ)
    (same : ∀ order modes, (∑ j, modes j) = d + r + n → R order modes = S order modes) :
    supportedNestedRightReadout outerLift innerLift d r n K H R =
      supportedNestedRightReadout outerLift innerLift d r n K H S := by
  unfold supportedNestedRightReadout
  apply supportedQReadout_congr <;> intro k l hkl <;> apply supportedQReadout_congr <;>
    intro m p hmp <;> apply same <;> simp [Fin.sum_univ_three] <;> omega

private theorem supportedNestedLeftReadout_eq (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (A B C : VertexOperator ℂ V) (x : V) (phi : V →ₗ[ℂ] ℂ) :
    phi (((qField outerLift r H (qField innerLift d K A B) C)[[n]]) x) =
      supportedNestedLeftReadout outerLift innerLift d r n K H (tripleScalar A B C x phi) := by
  rw [supportedQReadout_eq]
  unfold supportedNestedLeftReadout
  apply supportedQReadout_congr
  · intro k l hkl
    rw [supportedQReadout_eq]
    congr 1 <;> funext m p <;>
      simp [tripleScalar, triplePermutation, coefficientDistribution, word,
        Module.End.mul_apply, Equiv.swap_apply_def]
  · intro k l hkl
    change (phi.comp (C[[k]])) (((qField innerLift d K A B)[[l]]) x) = _
    rw [supportedQReadout_eq]
    congr 1 <;> funext m p <;>
      simp [tripleScalar, triplePermutation, coefficientDistribution, word,
        Module.End.mul_apply, LinearMap.comp_apply, Equiv.swap_apply_def]

private theorem supportedNestedRightReadout_eq (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (A B C : VertexOperator ℂ V) (x : V) (phi : V →ₗ[ℂ] ℂ) :
    phi (((qField outerLift r H A (qField innerLift d K B C))[[n]]) x) =
      supportedNestedRightReadout outerLift innerLift d r n K H (tripleScalar A B C x phi) := by
  rw [supportedQReadout_eq]
  unfold supportedNestedRightReadout
  apply supportedQReadout_congr
  · intro k l hkl
    change (phi.comp (A[[k]])) (((qField innerLift d K B C)[[l]]) x) = _
    rw [supportedQReadout_eq]
    congr 1 <;> funext m p <;>
      simp [tripleScalar, triplePermutation, coefficientDistribution, word,
        Module.End.mul_apply, LinearMap.comp_apply, Equiv.swap_apply_def]
  · intro k l hkl
    rw [supportedQReadout_eq]
    congr 1 <;> funext m p <;>
      simp [tripleScalar, triplePermutation, coefficientDistribution, word,
        Module.End.mul_apply, Equiv.swap_apply_def]

private theorem NestedLeftSupported_congr (innerLift d r n : ℤ) (K H : ℕ)
    (R S : Fin 6 → Exponent 3 → ℂ)
    (same : ∀ order modes, (∑ j, modes j) = d + r + n → R order modes = S order modes) :
    NestedLeftSupported innerLift d r n K H R ↔ NestedLeftSupported innerLift d r n K H S := by
  unfold NestedLeftSupported
  apply and_congr
  · apply QReadoutSupported_congr <;> intro k l hkl <;> apply supportedQReadout_congr <;>
      intro m p hmp <;> apply same <;> simp [Fin.sum_univ_three] <;> omega
  · apply forall_congr'
    intro k
    apply forall_congr'
    intro l
    apply imp_congr_right
    intro hkl
    apply and_congr <;> apply QReadoutSupported_congr <;>
      intro m p hmp <;> apply same <;> simp [Fin.sum_univ_three] <;> omega

private theorem NestedRightSupported_congr (innerLift d r n : ℤ) (K H : ℕ)
    (R S : Fin 6 → Exponent 3 → ℂ)
    (same : ∀ order modes, (∑ j, modes j) = d + r + n → R order modes = S order modes) :
    NestedRightSupported innerLift d r n K H R ↔ NestedRightSupported innerLift d r n K H S := by
  unfold NestedRightSupported
  apply and_congr
  · apply QReadoutSupported_congr <;> intro k l hkl <;> apply supportedQReadout_congr <;>
      intro m p hmp <;> apply same <;> simp [Fin.sum_univ_three] <;> omega
  · apply forall_congr'
    intro k
    apply forall_congr'
    intro l
    apply imp_congr_right
    intro hkl
    apply and_congr <;> apply QReadoutSupported_congr <;>
      intro m p hmp <;> apply same <;> simp [Fin.sum_univ_three] <;> omega

private theorem actual_nested_left_support (innerLift d r n : ℤ) (K H : ℕ)
    (A B C : VertexOperator ℂ V) (x : V) (phi : V →ₗ[ℂ] ℂ) :
    NestedLeftSupported innerLift d r n K H (tripleScalar A B C x phi) := by
  have forward (k l : ℤ) :
      phi (((qField innerLift d K A B)[[k]]) ((C[[l]]) x)) =
        supportedQReadout innerLift d K k
          (fun m p => tripleScalar A B C x phi 0 ![m, p, l])
          (fun m p => tripleScalar A B C x phi 2 ![p, m, l]) := by
    rw [supportedQReadout_eq]
    congr 1 <;> funext m p <;>
      simp [tripleScalar, triplePermutation, coefficientDistribution, word,
        Module.End.mul_apply, Equiv.swap_apply_def]
  have backward (k l : ℤ) :
      phi ((C[[k]]) (((qField innerLift d K A B)[[l]]) x)) =
        supportedQReadout innerLift d K l
          (fun m p => tripleScalar A B C x phi 4 ![m, p, k])
          (fun m p => tripleScalar A B C x phi 5 ![p, m, k]) := by
    change (phi.comp (C[[k]])) (((qField innerLift d K A B)[[l]]) x) = _
    rw [supportedQReadout_eq]
    congr 1 <;> funext m p <;>
      simp [tripleScalar, triplePermutation, coefficientDistribution, word,
        Module.End.mul_apply, LinearMap.comp_apply, Equiv.swap_apply_def]
  constructor
  · exact (QReadoutSupported_congr r H n _ _ _ _
      (fun k l _ => forward k l) (fun k l _ => backward k l)).mp
        (actual_q_support r H (qField innerLift d K A B) C x n phi)
  · intro k l hkl
    constructor
    · simpa [tripleScalar, triplePermutation, coefficientDistribution, word,
        Module.End.mul_apply, Equiv.swap_apply_def] using
        actual_q_support d K A B ((C[[l]]) x) k phi
    · simpa [tripleScalar, triplePermutation, coefficientDistribution, word,
        Module.End.mul_apply, LinearMap.comp_apply, Equiv.swap_apply_def] using
        actual_q_support d K A B x l (phi.comp (C[[k]]))

private theorem actual_nested_right_support (innerLift d r n : ℤ) (K H : ℕ)
    (A B C : VertexOperator ℂ V) (x : V) (phi : V →ₗ[ℂ] ℂ) :
    NestedRightSupported innerLift d r n K H (tripleScalar A B C x phi) := by
  have forward (k l : ℤ) :
      phi ((A[[k]]) (((qField innerLift d K B C)[[l]]) x)) =
        supportedQReadout innerLift d K l
          (fun m p => tripleScalar A B C x phi 0 ![k, m, p])
          (fun m p => tripleScalar A B C x phi 1 ![k, p, m]) := by
    change (phi.comp (A[[k]])) (((qField innerLift d K B C)[[l]]) x) = _
    rw [supportedQReadout_eq]
    congr 1 <;> funext m p <;>
      simp [tripleScalar, triplePermutation, coefficientDistribution, word,
        Module.End.mul_apply, LinearMap.comp_apply, Equiv.swap_apply_def]
  have backward (k l : ℤ) :
      phi (((qField innerLift d K B C)[[k]]) ((A[[l]]) x)) =
        supportedQReadout innerLift d K k
          (fun m p => tripleScalar A B C x phi 3 ![l, m, p])
          (fun m p => tripleScalar A B C x phi 5 ![l, p, m]) := by
    rw [supportedQReadout_eq]
    congr 1 <;> funext m p <;>
      simp [tripleScalar, triplePermutation, coefficientDistribution, word,
        Module.End.mul_apply, Equiv.swap_apply_def]
  constructor
  · exact (QReadoutSupported_congr r H n _ _ _ _
      (fun k l _ => forward k l) (fun k l _ => backward k l)).mp
        (actual_q_support r H A (qField innerLift d K B C) x n phi)
  · intro k l hkl
    constructor
    · simpa [tripleScalar, triplePermutation, coefficientDistribution, word,
        Module.End.mul_apply, LinearMap.comp_apply, Equiv.swap_apply_def] using
        actual_q_support d K B C x l (phi.comp (A[[k]]))
    · simpa [tripleScalar, triplePermutation, coefficientDistribution, word,
        Module.End.mul_apply, Equiv.swap_apply_def] using
        actual_q_support d K B C ((A[[l]]) x) k phi

private theorem nestedLeftReadout_eq (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (A B C : VertexOperator ℂ V) (x : V) (phi : V →ₗ[ℂ] ℂ) :
    phi (((qField outerLift r H (qField innerLift d K A B) C)[[n]]) x) =
      nestedLeftReadout outerLift innerLift d r n K H A B C x (tripleScalar A B C x phi) := by
  rw [finiteQReadout_eq]
  unfold nestedLeftReadout
  apply finiteQReadout_congr
  · intro k l hkl
    rw [finiteQReadout_eq]
    congr 1 <;> funext m p <;>
      simp [tripleScalar, triplePermutation, coefficientDistribution, word,
        Module.End.mul_apply, Equiv.swap_apply_def]
  · intro k l hkl
    change (phi.comp (C[[k]])) (((qField innerLift d K A B)[[l]]) x) = _
    rw [finiteQReadout_eq]
    congr 1 <;> funext m p <;>
      simp [tripleScalar, triplePermutation, coefficientDistribution, word,
        Module.End.mul_apply, LinearMap.comp_apply, Equiv.swap_apply_def]

private theorem nestedRightReadout_eq (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (A B C : VertexOperator ℂ V) (x : V) (phi : V →ₗ[ℂ] ℂ) :
    phi (((qField outerLift r H A (qField innerLift d K B C))[[n]]) x) =
      nestedRightReadout outerLift innerLift d r n K H A B C x (tripleScalar A B C x phi) := by
  rw [finiteQReadout_eq]
  unfold nestedRightReadout
  apply finiteQReadout_congr
  · intro k l hkl
    change (phi.comp (A[[k]])) (((qField innerLift d K B C)[[l]]) x) = _
    rw [finiteQReadout_eq]
    congr 1 <;> funext m p <;>
      simp [tripleScalar, triplePermutation, coefficientDistribution, word,
        Module.End.mul_apply, LinearMap.comp_apply, Equiv.swap_apply_def]
  · intro k l hkl
    rw [finiteQReadout_eq]
    congr 1 <;> funext m p <;>
      simp [tripleScalar, triplePermutation, coefficientDistribution, word,
        Module.End.mul_apply, Equiv.swap_apply_def]

private theorem nestedLeftReadout_congr (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (A B C : VertexOperator ℂ V) (x : V) (R S : Fin 6 → Exponent 3 → ℂ)
    (same : ∀ order modes, (∑ j, modes j) = d + r + n → R order modes = S order modes) :
    nestedLeftReadout outerLift innerLift d r n K H A B C x R =
      nestedLeftReadout outerLift innerLift d r n K H A B C x S := by
  unfold nestedLeftReadout
  apply finiteQReadout_congr <;> intro k l hkl <;> apply finiteQReadout_congr <;>
    intro m p hmp <;> apply same <;> simp [Fin.sum_univ_three] <;> omega

private theorem nestedRightReadout_congr (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (A B C : VertexOperator ℂ V) (x : V) (R S : Fin 6 → Exponent 3 → ℂ)
    (same : ∀ order modes, (∑ j, modes j) = d + r + n → R order modes = S order modes) :
    nestedRightReadout outerLift innerLift d r n K H A B C x R =
      nestedRightReadout outerLift innerLift d r n K H A B C x S := by
  unfold nestedRightReadout
  apply finiteQReadout_congr <;> intro k l hkl <;> apply finiteQReadout_congr <;>
    intro m p hmp <;> apply same <;> simp [Fin.sum_univ_three] <;> omega

end NestedReadout

/-- The rational readout retains the original global labels, including when
the word is read in a different supported order. -/
def rationalTripleReadout (D : LatticeData) (a b : Carrier D) (K : ℕ)
    (P : LabelledPolynomial ℂ 3) (order : Fin 6) (modes : Exponent 3) : ℂ :=
  (orderedRationalFor ℂ 3 (triplePermutation order)
    (algebraMap _ (CommonRational ℂ 3) P /
      algebraMap _ (CommonRational ℂ 3)
        (weightedClearingPolynomial (threeOrders D a b K)))).coeff
    (orderExponents 3 (triplePermutation order) (fun j => -modes j - 1))

/-- Exchange the current and first-source labels without changing the
numerator, its clearing factors, or the six supported orders. -/
def swapCurrentSourceReadout (R : Fin 6 → Exponent 3 → ℂ)
    (order : Fin 6) (modes : Exponent 3) : ℂ :=
  R (![2, 3, 0, 1, 5, 4] order) ![modes 1, modes 0, modes 2]

/-- The six supported Hahn expansions of the unchanged common rational. -/
def rationalTripleCarriers (D : LatticeData) (a b : Carrier D) (K : ℕ)
    (P : LabelledPolynomial ℂ 3) (order : Fin 6) : HahnSeries (Indices 3) ℂ :=
  orderedRationalFor ℂ 3 (triplePermutation order)
    (algebraMap _ (CommonRational ℂ 3) P /
      algebraMap _ (CommonRational ℂ 3)
        (weightedClearingPolynomial (threeOrders D a b K)))

/-- Relabel the current and first source while retaining the actual word
positions of every supported coefficient. -/
def swapCurrentSourceCarriers (W : Fin 6 → HahnSeries (Indices 3) ℂ)
    (order : Fin 6) : HahnSeries (Indices 3) ℂ :=
  W (![2, 3, 0, 1, 5, 4] order)

private theorem hahnTripleScalar_swap (W : Fin 6 → HahnSeries (Indices 3) ℂ) :
    hahnTripleScalar (swapCurrentSourceCarriers W) =
      swapCurrentSourceReadout (hahnTripleScalar W) := by
  funext order modes
  fin_cases order <;>
    simp [hahnTripleScalar, swapCurrentSourceCarriers, swapCurrentSourceReadout,
      triplePermutation, orderExponents, labelPermutation, Equiv.swap_apply_def] <;>
    congr 1 <;> congr 1 <;> funext j <;> fin_cases j <;>
    simp [Equiv.swap_apply_def]

private theorem tripleScalar_swap {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B C : VertexOperator ℂ V) (x : V) (phi : V →ₗ[ℂ] ℂ) :
    tripleScalar B A C x phi = swapCurrentSourceReadout (tripleScalar A B C x phi) := by
  funext order modes
  fin_cases order <;>
    simp [tripleScalar, swapCurrentSourceReadout, triplePermutation,
      coefficientDistribution, word, Module.End.mul_apply, Equiv.swap_apply_def]

/- proof_shape: actual_nested_ordered_readouts: content
   admission_basis: escape-witness
   escape_witness: finiteQReadout_eq uses the actual complete intermediate
   field order before expanding either inner chamber. The two nested
   extraction lemmas retain all four ordered words. Fixed total mode degree
   then identifies every summand with the same actual Laurent slice in its
   own supported permutation. No local Taylor substitution is assumed. -/
/-- The three genuinely nested Q coefficients are read from one and the same
actual ternary Laurent numerator, for all signed indices and all outer cutoffs.
This is ordered extraction, before the collision-coordinate Taylor identity. -/
theorem actual_nested_ordered_readouts (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (a b : Carrier D) :
    ∃ K : ℕ, ∀ (gamma delta d r n : ℤ) (x : ActualTensor D hu)
      (phi : ActualTensor D hu →ₗ[ℂ] ℂ),
      ∃ P : LabelledPolynomial ℂ 3,
        (∀ e : Exponent 3, P.coeff e =
          if totalExponent e =
              (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
          then phi (actualNumerator D hu i a b gamma delta K x e) else 0) ∧
        ∀ (H₁ H₂ H₃ : ℕ) (j : ℤ),
          phi (((qField (gamma + 1) r H₁
            (targetSlice D hu (neutralMode D i d a) (gamma + 1))
            (targetSlice D hu b delta))[[n]]) x) =
            nestedLeftReadout (gamma + 1) 1 d r n (vectorFrequencyBound D a + 1) H₁
              (targetCurrent D hu i) (targetSlice D hu a gamma) (targetSlice D hu b delta)
              x (rationalTripleReadout D a b K P) ∧
          phi (((qField 1 (d - j) H₂ (targetCurrent D hu i)
            (qField gamma (r + j) K (targetSlice D hu a gamma)
              (targetSlice D hu b delta)))[[n]]) x) =
            nestedRightReadout 1 gamma (r + j) (d - j) n K H₂
              (targetCurrent D hu i) (targetSlice D hu a gamma) (targetSlice D hu b delta)
              x (rationalTripleReadout D a b K P) ∧
          phi (((qField gamma (d + r - j) H₃ (targetSlice D hu a gamma)
            (targetSlice D hu (neutralMode D i j b) (delta + 1)))[[n]]) x) =
            nestedRightReadout gamma 1 j (d + r - j) n (vectorFrequencyBound D b + 1) H₃
              (targetSlice D hu a gamma) (targetCurrent D hu i) (targetSlice D hu b delta)
              x (swapCurrentSourceReadout (rationalTripleReadout D a b K P)) := by
  obtain ⟨K, carriers⟩ := actual_finite_laurent_carriers D hu i a b
  refine ⟨K, ?_⟩
  intro gamma delta d r n x phi
  let total := (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
  obtain ⟨P, coefficients, words⟩ := carriers gamma delta x phi total
  refine ⟨P, coefficients, ?_⟩
  let J := targetCurrent D hu i
  let A := targetSlice D hu a gamma
  let B := targetSlice D hu b delta
  have same (order : Fin 6) (modes : Exponent 3)
      (degree : (∑ k, modes k) = d + r + n) :
      tripleScalar J A B x phi order modes = rationalTripleReadout D a b K P order modes := by
    have index : totalExponent (fun k => -modes k - 1) =
        total - ∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ) := by
      simp only [totalExponent, Fin.sum_univ_three] at degree ⊢
      dsimp [total]
      omega
    have readout := words (triplePermutation order) (fun k => -modes k - 1)
    rw [if_pos index] at readout
    exact readout.symm
  intro H₁ H₂ H₃ j
  refine ⟨?_, ?_, ?_⟩
  · rw [D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport.current_q D hu i a gamma d, nestedLeftReadout_eq]
    exact nestedLeftReadout_congr _ _ _ _ _ _ _ J A B x _ _ same
  · rw [nestedRightReadout_eq]
    apply nestedRightReadout_congr
    intro order modes degree
    apply same
    omega
  · rw [D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport.current_q D hu i b delta j, nestedRightReadout_eq, tripleScalar_swap]
    apply nestedRightReadout_congr
    intro order modes degree
    apply same
    simp [Fin.sum_univ_three] at degree ⊢
    omega


open CollisionLaurentKernels.LaurentCollision
open OrderedCollisionCoordinates.ContextualLaurentKernel
open CollisionRationalExpansions.HahnFiberResidue
open CollisionRationalExpansions.FullOrderSpectatorPole

private def currentSourceTau (reverse : Bool) :
    Fin 2 ≃ LabelledRationalClearing.GlobalRationalCurry.Remaining (0 : Fin 3) :=
  if reverse then (Equiv.swap 0 1).trans (finSuccAboveEquiv (0 : Fin 3))
  else finSuccAboveEquiv (0 : Fin 3)

/-- The complete current/source local residue, with the spectator retained
on its actual side of the pair. All diagonal weights are signed. -/
def currentSourceLocalQ (reverse : Bool) (s d : ℤ) (K : ℕ) (k l : ℤ)
    (R : CommonRational ℂ 3) : ℂ :=
  ∑ ell ∈ Finset.range ((K : ℤ) - d).toNat,
    Ring.choose (-(s : ℂ) / 2) ell *
      (if reverse then
        ((OrderedCollisionCoordinates.LocalResidueCurrying.fusedLocalSeries ℂ 2 0
          (0 : Fin 3) ⟨1, by decide⟩ (currentSourceTau true)
          (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (0 : Fin 3)
            ⟨1, by decide⟩ ^ (d + ell) * R)).coeff (-1)).coeff
          (exponents 2 ![-l - 1, -k + ell - 1])
      else
        ((OrderedCollisionCoordinates.LocalResidueCurrying.fusedLocalSeries ℂ 1 1
          (0 : Fin 3) ⟨1, by decide⟩ (currentSourceTau false)
          (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (0 : Fin 3)
            ⟨1, by decide⟩ ^ (d + ell) * R)).coeff (-1)).coeff
          (exponents 2 ![-k + ell - 1, -l - 1]))

private theorem weighted_local_fiber (pre post : ℕ)
    (z : Fin ((pre + 2) + post))
    (tau : Fin ((pre + 1) + post) ≃ LabelledRationalClearing.GlobalRationalCurry.Remaining z)
    (x : LabelledRationalClearing.GlobalRationalCurry.Remaining z)
    (hx : tau (OrderedCollisionResidues.AdjacentLabelledCoordinates.boundarySlot pre post) = x)
    (P : LabelledPolynomial ℂ ((pre + 2) + post))
    (orders : Fin ((pre + 2) + post) × Fin ((pre + 2) + post) → ℕ)
    (r : ℤ) (g : Indices ((pre + 1) + post)) :
    let R := algebraMap _ (CommonRational ℂ ((pre + 2) + post)) P /
      algebraMap _ (CommonRational ℂ ((pre + 2) + post))
        (∏ p ∈ LabelledRationalClearing.PairDifferenceLocalization.labelledPairs ((pre + 2) + post),
          LabelledRationalClearing.PairDifferenceLocalization.pairPolynomial ℂ p.1 p.2 ^ orders p)
    (pullFiber (firstEmbedding pre post (-1))
      (contextPair ℂ pre post (kernelZX ℂ r) *
        OrderedCollisionCoordinates.AdjacentFullOrders.firstRational ℂ pre post z tau R)).coeff g -
    (residue (pre + 1) post
      (contextPair ℂ pre post (kernelXZ ℂ r) *
        OrderedCollisionCoordinates.AdjacentFullOrders.secondRational ℂ pre post z tau R)).coeff g =
    ((OrderedCollisionCoordinates.LocalResidueCurrying.fusedLocalSeries ℂ (pre + 1) post z x tau
      (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ z x ^ r * R)).coeff (-1)).coeff g := by
  dsimp only
  have equality := RationalCollision.LaurentNumerator.weighted_laurent_collision
    ℂ pre post z tau x hx P orders r
  have first : ∀ R : CommonRational ℂ ((pre + 2) + post),
      OrderedCollisionCoordinates.AdjacentFullOrders.firstRational ℂ pre post z tau
        (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ z x ^ r * R) =
      contextPair ℂ pre post (kernelZX ℂ r) *
        OrderedCollisionCoordinates.AdjacentFullOrders.firstRational ℂ pre post z tau R := by
    intro R
    simp only [LabelledRationalClearing.WeightedActualQ.globalDiagonal, map_mul, map_zpow₀,
      OrderedCollisionResidues.LabelledDiagonalResidue.first_diagonal ℂ pre post z tau x hx,
      iotaZX_diagonal, kernelZX_zpow]
  have second : ∀ R : CommonRational ℂ ((pre + 2) + post),
      OrderedCollisionCoordinates.AdjacentFullOrders.secondRational ℂ pre post z tau
        (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ z x ^ r * R) =
      contextPair ℂ pre post (kernelXZ ℂ r) *
        OrderedCollisionCoordinates.AdjacentFullOrders.secondRational ℂ pre post z tau R := by
    intro R
    simp only [LabelledRationalClearing.WeightedActualQ.globalDiagonal, map_mul, map_zpow₀,
      OrderedCollisionResidues.LabelledDiagonalResidue.second_diagonal ℂ pre post z tau x hx,
      iotaXZ_diagonal, kernelXZ_zpow]
  dsimp only at equality
  rw [first, second] at equality
  exact congrArg (fun F : HahnSeries (Indices ((pre + 1) + post)) ℂ => F.coeff g) equality.symm

private theorem currentSourceLocalQ_eq (D : LatticeData) (a b : Carrier D) (K : ℕ)
    (P : LabelledPolynomial ℂ 3) (s d k l : ℤ) :
    let W := rationalTripleCarriers D a b K P
    let R := algebraMap _ (CommonRational ℂ 3) P /
      algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))
    leftPairFiberQ s d (vectorFrequencyBound D a + 1) k l (W 0) (W 2) =
      currentSourceLocalQ false s d (vectorFrequencyBound D a + 1) k l R ∧
    rightPairFiberQ s d (vectorFrequencyBound D a + 1) k l (W 4) (W 5) =
      currentSourceLocalQ true s d (vectorFrequencyBound D a + 1) k l R := by
  dsimp only
  have f₀ : SupportedWordRationalCollision.ActualOrderedCoordinates.firstOrder
      0 1 (0 : Fin 3) (currentSourceTau false) = triplePermutation 0 := by
    ext j; fin_cases j <;> rfl
  have g₀ : SupportedWordRationalCollision.ActualOrderedCoordinates.secondOrder
      0 1 (0 : Fin 3) (currentSourceTau false) = triplePermutation 2 := by
    ext j; fin_cases j <;> rfl
  have f₁ : SupportedWordRationalCollision.ActualOrderedCoordinates.firstOrder
      1 0 (0 : Fin 3) (currentSourceTau true) = triplePermutation 4 := by
    ext j; fin_cases j <;> rfl
  have g₁ : SupportedWordRationalCollision.ActualOrderedCoordinates.secondOrder
      1 0 (0 : Fin 3) (currentSourceTau true) = triplePermutation 5 := by
    ext j; fin_cases j <;> rfl
  constructor
  · unfold leftPairFiberQ currentSourceLocalQ
    simp only [Bool.false_eq_true, ite_false]
    apply Finset.sum_congr rfl
    intro ell hell
    congr 1
    have eq := weighted_local_fiber 0 1 (0 : Fin 3) (currentSourceTau false)
      ⟨1, by decide⟩ (by rfl) P (threeOrders D a b K) (d + ell)
      (exponents 2 ![-k + ell - 1, -l - 1])
    rw [← SupportedWordRationalCollision.ActualOrderedCoordinates.firstOrder_rational,
      ← SupportedWordRationalCollision.ActualOrderedCoordinates.secondOrder_rational,
      f₀, g₀] at eq
    exact eq
  · unfold rightPairFiberQ currentSourceLocalQ
    simp only [Bool.true_eq, ite_true]
    apply Finset.sum_congr rfl
    intro ell hell
    congr 1
    have eq := weighted_local_fiber 1 0 (0 : Fin 3) (currentSourceTau true)
      ⟨1, by decide⟩ (by rfl) P (threeOrders D a b K) (d + ell)
      (exponents 2 ![-l - 1, -k + ell - 1])
    rw [← SupportedWordRationalCollision.ActualOrderedCoordinates.firstOrder_rational,
      ← SupportedWordRationalCollision.ActualOrderedCoordinates.secondOrder_rational,
      f₁, g₁] at eq
    exact eq

/-- The current/source pair is collided locally inside each supported outer
fiber; its two spectator positions retain their respective complete orders. -/
def nestedLeftLocalReadout (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (R : CommonRational ℂ 3) : ℂ :=
  supportedQReadout outerLift r H n
    (fun k l => currentSourceLocalQ false innerLift d K k l R)
    (fun k l => currentSourceLocalQ true innerLift d K l k R)

private theorem nestedLeftLocalReadout_eq (D : LatticeData) (a b : Carrier D) (K : ℕ)
    (P : LabelledPolynomial ℂ 3) (outerLift innerLift d r n : ℤ) (H : ℕ) :
    nestedLeftFiberReadout outerLift innerLift d r n (vectorFrequencyBound D a + 1) H
      (rationalTripleCarriers D a b K P) =
    nestedLeftLocalReadout outerLift innerLift d r n (vectorFrequencyBound D a + 1) H
      (algebraMap _ (CommonRational ℂ 3) P /
        algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))) := by
  unfold nestedLeftFiberReadout nestedLeftLocalReadout
  apply supportedQReadout_congr
  · intro k l _
    exact (currentSourceLocalQ_eq D a b K P innerLift d k l).1
  · intro k l _
    exact (currentSourceLocalQ_eq D a b K P innerLift d l k).2

private def lastSourceTau (z : Fin 2) (spectatorLeft : Bool) :
    Fin 2 ≃ LabelledRationalClearing.GlobalRationalCurry.Remaining z.castSucc :=
  if spectatorLeft then finSuccAboveEquiv z.castSucc
  else (Equiv.swap 0 1).trans (finSuccAboveEquiv z.castSucc)

/-- A complete inner collision with the second source, retaining the actual
spectator side and the original current/source labels. -/
def lastSourceLocalQ (z : Fin 2) (spectatorLeft : Bool) (s d : ℤ) (K : ℕ) (k l : ℤ)
    (R : CommonRational ℂ 3) : ℂ :=
  let x : LabelledRationalClearing.GlobalRationalCurry.Remaining z.castSucc :=
    ⟨2, by fin_cases z <;> decide⟩
  ∑ ell ∈ Finset.range ((K : ℤ) - d).toNat,
    Ring.choose (-(s : ℂ) / 2) ell *
      (if spectatorLeft then
        ((OrderedCollisionCoordinates.LocalResidueCurrying.fusedLocalSeries ℂ 2 0
          z.castSucc x (lastSourceTau z true)
          (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ z.castSucc x ^
            (d + ell) * R)).coeff (-1)).coeff
          (exponents 2 ![-l - 1, -k + ell - 1])
      else
        ((OrderedCollisionCoordinates.LocalResidueCurrying.fusedLocalSeries ℂ 1 1
          z.castSucc x (lastSourceTau z false)
          (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ z.castSucc x ^
            (d + ell) * R)).coeff (-1)).coeff
          (exponents 2 ![-k + ell - 1, -l - 1]))

private theorem sourceSourceLocalQ_eq (D : LatticeData) (a b : Carrier D) (K I : ℕ)
    (P : LabelledPolynomial ℂ 3) (s d k l : ℤ) :
    let W := rationalTripleCarriers D a b K P
    let R := algebraMap _ (CommonRational ℂ 3) P /
      algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))
    rightPairFiberQ s d I k l (W 0) (W 1) =
      lastSourceLocalQ 1 true s d I k l R ∧
    leftPairFiberQ s d I k l (W 3) (W 5) =
      lastSourceLocalQ 1 false s d I k l R := by
  dsimp only
  have f_left : SupportedWordRationalCollision.ActualOrderedCoordinates.firstOrder
      1 0 (1 : Fin 3) (lastSourceTau 1 true) = triplePermutation 0 := by
    ext j; fin_cases j <;> rfl
  have g_left : SupportedWordRationalCollision.ActualOrderedCoordinates.secondOrder
      1 0 (1 : Fin 3) (lastSourceTau 1 true) = triplePermutation 1 := by
    ext j; fin_cases j <;> rfl
  have f_right : SupportedWordRationalCollision.ActualOrderedCoordinates.firstOrder
      0 1 (1 : Fin 3) (lastSourceTau 1 false) = triplePermutation 3 := by
    ext j; fin_cases j <;> rfl
  have g_right : SupportedWordRationalCollision.ActualOrderedCoordinates.secondOrder
      0 1 (1 : Fin 3) (lastSourceTau 1 false) = triplePermutation 5 := by
    ext j; fin_cases j <;> rfl
  constructor
  · unfold rightPairFiberQ lastSourceLocalQ
    simp only [Bool.true_eq, Bool.false_eq_true, ite_true, ite_false]
    apply Finset.sum_congr rfl
    intro ell hell
    congr 1
    have eq := weighted_local_fiber 1 0 (1 : Fin 3) (lastSourceTau 1 true)
      ⟨2, by decide⟩ (by rfl) P (threeOrders D a b K) (d + ell)
      (exponents 2 ![-l - 1, -k + ell - 1])
    rw [← SupportedWordRationalCollision.ActualOrderedCoordinates.firstOrder_rational,
      ← SupportedWordRationalCollision.ActualOrderedCoordinates.secondOrder_rational,
      f_left, g_left] at eq
    exact eq
  · unfold leftPairFiberQ lastSourceLocalQ
    simp only [Bool.true_eq, Bool.false_eq_true, ite_true, ite_false]
    apply Finset.sum_congr rfl
    intro ell hell
    congr 1
    have eq := weighted_local_fiber 0 1 (1 : Fin 3) (lastSourceTau 1 false)
      ⟨2, by decide⟩ (by rfl) P (threeOrders D a b K) (d + ell)
      (exponents 2 ![-k + ell - 1, -l - 1])
    rw [← SupportedWordRationalCollision.ActualOrderedCoordinates.firstOrder_rational,
      ← SupportedWordRationalCollision.ActualOrderedCoordinates.secondOrder_rational,
      f_right, g_right] at eq
    exact eq

private theorem currentSecondSourceLocalQ_eq (D : LatticeData) (a b : Carrier D) (K I : ℕ)
    (P : LabelledPolynomial ℂ 3) (s d k l : ℤ) :
    let W := swapCurrentSourceCarriers (rationalTripleCarriers D a b K P)
    let R := algebraMap _ (CommonRational ℂ 3) P /
      algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))
    rightPairFiberQ s d I k l (W 0) (W 1) =
      lastSourceLocalQ 0 true s d I k l R ∧
    leftPairFiberQ s d I k l (W 3) (W 5) =
      lastSourceLocalQ 0 false s d I k l R := by
  dsimp only
  have f_left : SupportedWordRationalCollision.ActualOrderedCoordinates.firstOrder
      1 0 (0 : Fin 3) (lastSourceTau 0 true) = triplePermutation 2 := by
    ext j; fin_cases j <;> rfl
  have g_left : SupportedWordRationalCollision.ActualOrderedCoordinates.secondOrder
      1 0 (0 : Fin 3) (lastSourceTau 0 true) = triplePermutation 3 := by
    ext j; fin_cases j <;> rfl
  have f_right : SupportedWordRationalCollision.ActualOrderedCoordinates.firstOrder
      0 1 (0 : Fin 3) (lastSourceTau 0 false) = triplePermutation 1 := by
    ext j; fin_cases j <;> rfl
  have g_right : SupportedWordRationalCollision.ActualOrderedCoordinates.secondOrder
      0 1 (0 : Fin 3) (lastSourceTau 0 false) = triplePermutation 4 := by
    ext j; fin_cases j <;> rfl
  constructor
  · unfold rightPairFiberQ lastSourceLocalQ
    simp only [Bool.true_eq, Bool.false_eq_true, ite_true, ite_false]
    apply Finset.sum_congr rfl
    intro ell hell
    congr 1
    have eq := weighted_local_fiber 1 0 (0 : Fin 3) (lastSourceTau 0 true)
      ⟨2, by decide⟩ (by rfl) P (threeOrders D a b K) (d + ell)
      (exponents 2 ![-l - 1, -k + ell - 1])
    rw [← SupportedWordRationalCollision.ActualOrderedCoordinates.firstOrder_rational,
      ← SupportedWordRationalCollision.ActualOrderedCoordinates.secondOrder_rational,
      f_left, g_left] at eq
    exact eq
  · unfold leftPairFiberQ lastSourceLocalQ
    simp only [Bool.true_eq, Bool.false_eq_true, ite_true, ite_false]
    apply Finset.sum_congr rfl
    intro ell hell
    congr 1
    have eq := weighted_local_fiber 0 1 (0 : Fin 3) (lastSourceTau 0 false)
      ⟨2, by decide⟩ (by rfl) P (threeOrders D a b K) (d + ell)
      (exponents 2 ![-k + ell - 1, -l - 1])
    rw [← SupportedWordRationalCollision.ActualOrderedCoordinates.firstOrder_rational,
      ← SupportedWordRationalCollision.ActualOrderedCoordinates.secondOrder_rational,
      f_right, g_right] at eq
    exact eq

/-- A supported outer Q readout whose complete inner collision is local.
The eliminated label distinguishes A/B from J/B, without relabelling the numerator. -/
def nestedRightLocalReadout (z : Fin 2) (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (R : CommonRational ℂ 3) : ℂ :=
  supportedQReadout outerLift r H n
    (fun k l => lastSourceLocalQ z true innerLift d K l k R)
    (fun k l => lastSourceLocalQ z false innerLift d K k l R)

private theorem nestedRightLocalReadout_sourceSource (D : LatticeData) (a b : Carrier D) (K I : ℕ)
    (P : LabelledPolynomial ℂ 3) (outerLift innerLift d r n : ℤ) (H : ℕ) :
    nestedRightFiberReadout outerLift innerLift d r n I H
      (rationalTripleCarriers D a b K P) =
    nestedRightLocalReadout 1 outerLift innerLift d r n I H
      (algebraMap _ (CommonRational ℂ 3) P /
        algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))) := by
  unfold nestedRightFiberReadout nestedRightLocalReadout
  apply supportedQReadout_congr
  · intro k l _
    exact (sourceSourceLocalQ_eq D a b K I P innerLift d l k).1
  · intro k l _
    exact (sourceSourceLocalQ_eq D a b K I P innerLift d k l).2

private theorem nestedRightLocalReadout_currentSecondSource (D : LatticeData) (a b : Carrier D) (K I : ℕ)
    (P : LabelledPolynomial ℂ 3) (outerLift innerLift d r n : ℤ) (H : ℕ) :
    nestedRightFiberReadout outerLift innerLift d r n I H
      (swapCurrentSourceCarriers (rationalTripleCarriers D a b K P)) =
    nestedRightLocalReadout 0 outerLift innerLift d r n I H
      (algebraMap _ (CommonRational ℂ 3) P /
        algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))) := by
  unfold nestedRightFiberReadout nestedRightLocalReadout
  apply supportedQReadout_congr
  · intro k l _
    exact (currentSecondSourceLocalQ_eq D a b K I P innerLift d l k).1
  · intro k l _
    exact (currentSecondSourceLocalQ_eq D a b K I P innerLift d k l).2

/- proof_shape: actual_supported_nested_extraction: content
   admission_basis: escape-witness
   escape_witness: complete intermediate-field support bounds the outer fibers
   after cancellation; actual rightmost-vector support bounds every inner
   fiber. The common actual Laurent slice transports these bounds and all
   three complete extractions without retaining chosen mode cutoffs. -/
/-- The actual common numerator has supported nested residue fibers. All
three complete Q products are extracted without intermediate mode cutoffs;
outer support bounds the complete inner difference, with both orders intact. -/
theorem actual_supported_nested_extraction (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (a b : Carrier D) :
    ∃ K : ℕ, ∀ (gamma delta d r n : ℤ) (x : ActualTensor D hu)
      (phi : ActualTensor D hu →ₗ[ℂ] ℂ),
      ∃ P : LabelledPolynomial ℂ 3,
        (∀ e : Exponent 3, P.coeff e =
          if totalExponent e =
              (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
          then phi (actualNumerator D hu i a b gamma delta K x e) else 0) ∧
        ∀ (H₁ H₂ H₃ : ℕ) (j : ℤ),
          NestedLeftSupported 1 d r n (vectorFrequencyBound D a + 1) H₁
            (rationalTripleReadout D a b K P) ∧
          NestedRightSupported gamma (r + j) (d - j) n K H₂
            (rationalTripleReadout D a b K P) ∧
          NestedRightSupported 1 j (d + r - j) n (vectorFrequencyBound D b + 1) H₃
            (swapCurrentSourceReadout (rationalTripleReadout D a b K P)) ∧
          phi (((qField (gamma + 1) r H₁
            (targetSlice D hu (neutralMode D i d a) (gamma + 1))
            (targetSlice D hu b delta))[[n]]) x) =
            supportedNestedLeftReadout (gamma + 1) 1 d r n
              (vectorFrequencyBound D a + 1) H₁ (rationalTripleReadout D a b K P) ∧
          phi (((qField 1 (d - j) H₂ (targetCurrent D hu i)
            (qField gamma (r + j) K (targetSlice D hu a gamma)
              (targetSlice D hu b delta)))[[n]]) x) =
            supportedNestedRightReadout 1 gamma (r + j) (d - j) n K H₂
              (rationalTripleReadout D a b K P) ∧
          phi (((qField gamma (d + r - j) H₃ (targetSlice D hu a gamma)
            (targetSlice D hu (neutralMode D i j b) (delta + 1)))[[n]]) x) =
            supportedNestedRightReadout gamma 1 j (d + r - j) n
              (vectorFrequencyBound D b + 1) H₃
              (swapCurrentSourceReadout (rationalTripleReadout D a b K P)) ∧
          phi (((qField (gamma + 1) r H₁
            (targetSlice D hu (neutralMode D i d a) (gamma + 1))
            (targetSlice D hu b delta))[[n]]) x) =
            nestedLeftFiberReadout (gamma + 1) 1 d r n
              (vectorFrequencyBound D a + 1) H₁ (rationalTripleCarriers D a b K P) ∧
          phi (((qField 1 (d - j) H₂ (targetCurrent D hu i)
            (qField gamma (r + j) K (targetSlice D hu a gamma)
              (targetSlice D hu b delta)))[[n]]) x) =
            nestedRightFiberReadout 1 gamma (r + j) (d - j) n K H₂
              (rationalTripleCarriers D a b K P) ∧
          phi (((qField gamma (d + r - j) H₃ (targetSlice D hu a gamma)
            (targetSlice D hu (neutralMode D i j b) (delta + 1)))[[n]]) x) =
            nestedRightFiberReadout gamma 1 j (d + r - j) n
              (vectorFrequencyBound D b + 1) H₃
              (swapCurrentSourceCarriers (rationalTripleCarriers D a b K P)) ∧
          phi (((qField (gamma + 1) r H₁
            (targetSlice D hu (neutralMode D i d a) (gamma + 1))
            (targetSlice D hu b delta))[[n]]) x) =
            nestedLeftLocalReadout (gamma + 1) 1 d r n
              (vectorFrequencyBound D a + 1) H₁
              (algebraMap _ (CommonRational ℂ 3) P /
                algebraMap _ (CommonRational ℂ 3)
                  (weightedClearingPolynomial (threeOrders D a b K))) ∧
          phi (((qField 1 (d - j) H₂ (targetCurrent D hu i)
            (qField gamma (r + j) K (targetSlice D hu a gamma)
              (targetSlice D hu b delta)))[[n]]) x) =
            nestedRightLocalReadout 1 1 gamma (r + j) (d - j) n K H₂
              (algebraMap _ (CommonRational ℂ 3) P /
                algebraMap _ (CommonRational ℂ 3)
                  (weightedClearingPolynomial (threeOrders D a b K))) ∧
          phi (((qField gamma (d + r - j) H₃ (targetSlice D hu a gamma)
            (targetSlice D hu (neutralMode D i j b) (delta + 1)))[[n]]) x) =
            nestedRightLocalReadout 0 gamma 1 j (d + r - j) n
              (vectorFrequencyBound D b + 1) H₃
              (algebraMap _ (CommonRational ℂ 3) P /
                algebraMap _ (CommonRational ℂ 3)
                  (weightedClearingPolynomial (threeOrders D a b K))) := by
  obtain ⟨K, carriers⟩ := actual_finite_laurent_carriers D hu i a b
  refine ⟨K, ?_⟩
  intro gamma delta d r n x phi
  let total := (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
  obtain ⟨P, coefficients, words⟩ := carriers gamma delta x phi total
  refine ⟨P, coefficients, ?_⟩
  let J := targetCurrent D hu i
  let A := targetSlice D hu a gamma
  let B := targetSlice D hu b delta
  have same (order : Fin 6) (modes : Exponent 3)
      (degree : (∑ k, modes k) = d + r + n) :
      tripleScalar J A B x phi order modes = rationalTripleReadout D a b K P order modes := by
    have index : totalExponent (fun k => -modes k - 1) =
        total - ∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ) := by
      simp only [totalExponent, Fin.sum_univ_three] at degree ⊢
      dsimp [total]
      omega
    have readout := words (triplePermutation order) (fun k => -modes k - 1)
    rw [if_pos index] at readout
    exact readout.symm
  have swapped (j : ℤ) (order : Fin 6) (modes : Exponent 3)
      (degree : (∑ k, modes k) = j + (d + r - j) + n) :
      tripleScalar A J B x phi order modes =
        swapCurrentSourceReadout (rationalTripleReadout D a b K P) order modes := by
    rw [tripleScalar_swap]
    apply same
    simp [Fin.sum_univ_three] at degree ⊢
    omega
  intro H₁ H₂ H₃ j
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (NestedLeftSupported_congr 1 d r n _ H₁ _ _ same).mp
      (actual_nested_left_support 1 d r n _ H₁ J A B x phi)
  · exact (NestedRightSupported_congr gamma (r + j) (d - j) n K H₂ _ _
      (fun order modes degree => same order modes (by omega))).mp
      (actual_nested_right_support gamma (r + j) (d - j) n K H₂ J A B x phi)
  · exact (NestedRightSupported_congr 1 j (d + r - j) n _ H₃ _ _ (swapped j)).mp
      (actual_nested_right_support 1 j (d + r - j) n _ H₃ A J B x phi)
  · rw [D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport.current_q D hu i a gamma d,
      supportedNestedLeftReadout_eq]
    exact supportedNestedLeftReadout_congr _ _ _ _ _ _ _ _ _ same
  · rw [supportedNestedRightReadout_eq]
    exact supportedNestedRightReadout_congr _ _ _ _ _ _ _ _ _
      (fun order modes degree => same order modes (by omega))
  · rw [D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport.current_q D hu i b delta j,
      supportedNestedRightReadout_eq]
    exact supportedNestedRightReadout_congr _ _ _ _ _ _ _ _ _ (swapped j)

  · rw [D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport.current_q D hu i a gamma d,
      supportedNestedLeftReadout_eq, nestedLeftFiberReadout_eq]
    exact supportedNestedLeftReadout_congr _ _ _ _ _ _ _ _ _ same
  · rw [supportedNestedRightReadout_eq, nestedRightFiberReadout_eq]
    exact supportedNestedRightReadout_congr _ _ _ _ _ _ _ _ _
      (fun order modes degree => same order modes (by omega))
  · rw [D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport.current_q D hu i b delta j,
      supportedNestedRightReadout_eq, nestedRightFiberReadout_eq, hahnTripleScalar_swap]
    exact supportedNestedRightReadout_congr _ _ _ _ _ _ _ _ _ (swapped j)

  · rw [← nestedLeftLocalReadout_eq D a b K P (gamma + 1) 1 d r n H₁,
      D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport.current_q D hu i a gamma d,
      supportedNestedLeftReadout_eq, nestedLeftFiberReadout_eq]
    exact supportedNestedLeftReadout_congr _ _ _ _ _ _ _ _ _ same

  · rw [← nestedRightLocalReadout_sourceSource D a b K K P 1 gamma (r + j) (d - j) n H₂,
      supportedNestedRightReadout_eq, nestedRightFiberReadout_eq]
    exact supportedNestedRightReadout_congr _ _ _ _ _ _ _ _ _
      (fun order modes degree => same order modes (by omega))
  · rw [← nestedRightLocalReadout_currentSecondSource D a b K
      (vectorFrequencyBound D b + 1) P gamma 1 j (d + r - j) n H₃,
      D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport.current_q D hu i b delta j,
      supportedNestedRightReadout_eq, nestedRightFiberReadout_eq, hahnTripleScalar_swap]
    exact supportedNestedRightReadout_congr _ _ _ _ _ _ _ _ _ (swapped j)

/- proof_shape: actual_nested_outer_completion: content
   admission_basis: escape-witness
   escape_witness: The actual intermediate-field locality annihilates the
   COMPLETE two-order residue for every sufficiently large outer offset.
   A degree-preserving shift of the actual supported supplier identifies each
   such residue before any expansion into numerator monomials. -/
/-- Complete outer mode support and cutoff padding for all three actual local
nested residues, on the same actual homogeneous numerator and common K. -/
theorem actual_nested_outer_completion (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (a b : Carrier D) :
    ∃ K : ℕ, ∀ (gamma delta d r n : ℤ) (x : ActualTensor D hu)
      (phi : ActualTensor D hu →ₗ[ℂ] ℂ),
      ∃ P : LabelledPolynomial ℂ 3,
        (∀ e : Exponent 3, P.coeff e =
          if totalExponent e =
              (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
          then phi (actualNumerator D hu i a b gamma delta K x e) else 0) ∧
        (∀ (H₁ H₂ H₃ : ℕ) (j : ℤ),
          NestedLeftSupported 1 d r n (vectorFrequencyBound D a + 1) H₁
            (rationalTripleReadout D a b K P) ∧
          NestedRightSupported gamma (r + j) (d - j) n K H₂
            (rationalTripleReadout D a b K P) ∧
          NestedRightSupported 1 j (d + r - j) n (vectorFrequencyBound D b + 1) H₃
            (swapCurrentSourceReadout (rationalTripleReadout D a b K P)) ∧
          phi (((qField (gamma + 1) r H₁
            (targetSlice D hu (neutralMode D i d a) (gamma + 1))
            (targetSlice D hu b delta))[[n]]) x) =
            supportedNestedLeftReadout (gamma + 1) 1 d r n
              (vectorFrequencyBound D a + 1) H₁ (rationalTripleReadout D a b K P) ∧
          phi (((qField 1 (d - j) H₂ (targetCurrent D hu i)
            (qField gamma (r + j) K (targetSlice D hu a gamma)
              (targetSlice D hu b delta)))[[n]]) x) =
            supportedNestedRightReadout 1 gamma (r + j) (d - j) n K H₂
              (rationalTripleReadout D a b K P) ∧
          phi (((qField gamma (d + r - j) H₃ (targetSlice D hu a gamma)
            (targetSlice D hu (neutralMode D i j b) (delta + 1)))[[n]]) x) =
            supportedNestedRightReadout gamma 1 j (d + r - j) n
              (vectorFrequencyBound D b + 1) H₃
              (swapCurrentSourceReadout (rationalTripleReadout D a b K P)) ∧
          phi (((qField (gamma + 1) r H₁
            (targetSlice D hu (neutralMode D i d a) (gamma + 1))
            (targetSlice D hu b delta))[[n]]) x) =
            nestedLeftFiberReadout (gamma + 1) 1 d r n
              (vectorFrequencyBound D a + 1) H₁ (rationalTripleCarriers D a b K P) ∧
          phi (((qField 1 (d - j) H₂ (targetCurrent D hu i)
            (qField gamma (r + j) K (targetSlice D hu a gamma)
              (targetSlice D hu b delta)))[[n]]) x) =
            nestedRightFiberReadout 1 gamma (r + j) (d - j) n K H₂
              (rationalTripleCarriers D a b K P) ∧
          phi (((qField gamma (d + r - j) H₃ (targetSlice D hu a gamma)
            (targetSlice D hu (neutralMode D i j b) (delta + 1)))[[n]]) x) =
            nestedRightFiberReadout gamma 1 j (d + r - j) n
              (vectorFrequencyBound D b + 1) H₃
              (swapCurrentSourceCarriers (rationalTripleCarriers D a b K P)) ∧
          phi (((qField (gamma + 1) r H₁
            (targetSlice D hu (neutralMode D i d a) (gamma + 1))
            (targetSlice D hu b delta))[[n]]) x) =
            nestedLeftLocalReadout (gamma + 1) 1 d r n
              (vectorFrequencyBound D a + 1) H₁
              (algebraMap _ (CommonRational ℂ 3) P /
                algebraMap _ (CommonRational ℂ 3)
                  (weightedClearingPolynomial (threeOrders D a b K))) ∧
          phi (((qField 1 (d - j) H₂ (targetCurrent D hu i)
            (qField gamma (r + j) K (targetSlice D hu a gamma)
              (targetSlice D hu b delta)))[[n]]) x) =
            nestedRightLocalReadout 1 1 gamma (r + j) (d - j) n K H₂
              (algebraMap _ (CommonRational ℂ 3) P /
                algebraMap _ (CommonRational ℂ 3)
                  (weightedClearingPolynomial (threeOrders D a b K))) ∧
          phi (((qField gamma (d + r - j) H₃ (targetSlice D hu a gamma)
            (targetSlice D hu (neutralMode D i j b) (delta + 1)))[[n]]) x) =
            nestedRightLocalReadout 0 gamma 1 j (d + r - j) n
              (vectorFrequencyBound D b + 1) H₃
              (algebraMap _ (CommonRational ℂ 3) P /
                algebraMap _ (CommonRational ℂ 3)
                  (weightedClearingPolynomial (threeOrders D a b K)))) ∧
        let R := algebraMap _ (CommonRational ℂ 3) P /
          algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))
        ∀ (H₁ H₂ H₃ : ℕ) (j : ℤ),
          ((FieldNormalProductLocality.deltaEnd ^ H₁)
            (FieldNormalProductLocality.commutator
              (targetSlice D hu (neutralMode D i d a) (gamma + 1))
              (targetSlice D hu b delta)) = 0 →
            OuterQCompletion (gamma + 1) r n H₁
              (fun k l => currentSourceLocalQ false 1 d (vectorFrequencyBound D a + 1) k l R)
              (fun k l => currentSourceLocalQ true 1 d (vectorFrequencyBound D a + 1) l k R)) ∧
          ((FieldNormalProductLocality.deltaEnd ^ H₂)
            (FieldNormalProductLocality.commutator (targetCurrent D hu i)
              (qField gamma (r + j) K (targetSlice D hu a gamma)
                (targetSlice D hu b delta))) = 0 →
            OuterQCompletion 1 (d - j) n H₂
              (fun k l => lastSourceLocalQ 1 true gamma (r + j) K l k R)
              (fun k l => lastSourceLocalQ 1 false gamma (r + j) K k l R)) ∧
          ((FieldNormalProductLocality.deltaEnd ^ H₃)
            (FieldNormalProductLocality.commutator (targetSlice D hu a gamma)
              (targetSlice D hu (neutralMode D i j b) (delta + 1))) = 0 →
            OuterQCompletion gamma (d + r - j) n H₃
              (fun k l => lastSourceLocalQ 0 true 1 j (vectorFrequencyBound D b + 1) l k R)
              (fun k l => lastSourceLocalQ 0 false 1 j (vectorFrequencyBound D b + 1) k l R)) := by
  classical
  obtain ⟨K, actual⟩ := actual_supported_nested_extraction D hu i a b
  refine ⟨K, ?_⟩
  intro gamma delta d r n x phi
  obtain ⟨P, coefficients, readouts⟩ := actual gamma delta d r n x phi
  refine ⟨P, coefficients, readouts, ?_⟩
  dsimp only
  intro H₁ H₂ H₃ j
  have identify (d' r' n' : ℤ) (degree : d' + r' + n' = d + r + n)
      (P' : LabelledPolynomial ℂ 3)
      (coefficients' : ∀ e : Exponent 3, P'.coeff e =
        if totalExponent e =
            (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d' - r' - n' - 3
        then phi (actualNumerator D hu i a b gamma delta K x e) else 0) : P' = P := by
    apply AddMonoidAlgebra.coeff_injective
    ext e
    rw [coefficients', coefficients,
      show (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d' - r' - n' - 3 =
        (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3 by omega]
  refine ⟨?_, ?_, ?_⟩
  · intro locality
    apply completeOuterQReadout_of_locality (gamma + 1) r n H₁
      (targetSlice D hu (neutralMode D i d a) (gamma + 1))
      (targetSlice D hu b delta) x phi _ _ locality
    intro ell high
    obtain ⟨P', coefficients', readouts⟩ := actual gamma delta d (r + ell) (n - ell) x phi
    have identical := identify d (r + ell) (n - ell) (by omega) P' coefficients'
    subst P'
    exact (readouts ((r + ell).toNat + 1) 0 0 0).2.2.2.2.2.2.2.2.2.1.symm
  · intro locality
    apply completeOuterQReadout_of_locality 1 (d - j) n H₂
      (targetCurrent D hu i)
      (qField gamma (r + j) K (targetSlice D hu a gamma) (targetSlice D hu b delta))
      x phi _ _ locality
    intro ell high
    obtain ⟨P', coefficients', readouts⟩ := actual gamma delta (d + ell) r (n - ell) x phi
    have identical := identify (d + ell) r (n - ell) (by omega) P' coefficients'
    subst P'
    have equation := (readouts 0 ((d - j + ell).toNat + 1) 0 j).2.2.2.2.2.2.2.2.2.2.1.symm
    simpa only [show d + (ell : ℤ) - j = d - j + ell by omega,
      nestedRightLocalReadout] using equation
  · intro locality
    apply completeOuterQReadout_of_locality gamma (d + r - j) n H₃
      (targetSlice D hu a gamma)
      (targetSlice D hu (neutralMode D i j b) (delta + 1)) x phi _ _ locality
    intro ell high
    obtain ⟨P', coefficients', readouts⟩ := actual gamma delta (d + ell) r (n - ell) x phi
    have identical := identify (d + ell) r (n - ell) (by omega) P' coefficients'
    subst P'
    have equation := (readouts 0 0 ((d + r - j + ell).toNat + 1) j).2.2.2.2.2.2.2.2.2.2.2.symm
    simpa only [show d + (ell : ℤ) + r - j = d + r - j + ell by omega,
      nestedRightLocalReadout] using equation

section CollisionTaylor
open CollisionLaurentKernels.LaurentCollision
open CollisionLaurentKernels.RationalFusedResidue
open CollisionLaurentKernels.SeparatedResidue
open CollisionLaurentKernels.PolynomialCollision
open CollisionRationalExpansions.RationalCoefficientCollision
open CollisionRationalExpansions.SpectatorPole
open CollisionRationalExpansions.PartialFractionCollision

/-- Coefficients of the common fractional collision numerator, before division
by the three pairwise poles. Integer numerator powers are unrestricted. -/
def collisionTaylor (P : LabelledPolynomial ℂ 3) (gamma : ℤ) (u v : ℕ) : ℂ :=
  Finsupp.linearCombination ℂ (fun e : Exponent 3 =>
    Ring.choose ((e 0 : ℂ) - 1 / 2) u *
      Ring.choose ((e 1 : ℂ) - (gamma : ℂ) / 2) v) P.coeff

/-- The same numerator in the left-associated coordinates h=y-v, t=v-z.
The shift by u is the power of z+t remaining after the first extraction. -/
def associatedTaylor (P : LabelledPolynomial ℂ 3) (gamma : ℤ) (u v : ℕ) : ℂ :=
  Finsupp.linearCombination ℂ (fun e : Exponent 3 =>
    Ring.choose ((e 0 : ℂ) - 1 / 2) u *
      Ring.choose ((e 0 : ℂ) + (e 1 : ℂ) - (u : ℂ) - ((gamma : ℂ) + 1) / 2) v)
    P.coeff

private theorem fractional_coordinate_cocycle (a b : ℂ) (u v : ℕ) :
    Ring.choose a u * Ring.choose (a + b - u) v =
      ∑ j ∈ Finset.range (v + 1),
        ((u + j).choose u : ℂ) * Ring.choose a (u + j) * Ring.choose b (v - j) := by
  have vandermonde := Ring.add_choose_eq (R := ℂ)
    (r := a - u) (s := b) v (Commute.all _ _)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at vandermonde
  rw [show a + b - (u : ℂ) = (a - u) + b by ring, vandermonde, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have product := Ring.choose_smul_choose a (n := u + j) (k := u) (by omega)
  rw [nsmul_eq_mul, Nat.add_sub_cancel_left] at product
  rw [product]
  ring

theorem associatedTaylor_cocycle (P : LabelledPolynomial ℂ 3)
    (gamma : ℤ) (u v : ℕ) :
    associatedTaylor P gamma u v =
      ∑ j ∈ Finset.range (v + 1),
        ((u + j).choose u : ℂ) * collisionTaylor P gamma (u + j) (v - j) := by
  classical
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => simp [associatedTaylor, collisionTaylor]
  | add P Q hP hQ =>
    simp only [associatedTaylor, collisionTaylor, AddMonoidAlgebra.coeff_add,
      map_add, mul_add, Finset.sum_add_distrib] at hP hQ ⊢
    rw [hP, hQ]
  | single e c =>
    simp only [associatedTaylor, collisionTaylor, AddMonoidAlgebra.coeff_single,
      Finsupp.linearCombination_single, smul_eq_mul]
    have cocycle := fractional_coordinate_cocycle
      ((e 0 : ℂ) - 1 / 2) ((e 1 : ℂ) - (gamma : ℂ) / 2) u v
    have exponent : (e 0 : ℂ) - 1 / 2 + ((e 1 : ℂ) - (gamma : ℂ) / 2) - u =
        (e 0 : ℂ) + (e 1 : ℂ) - u - ((gamma : ℂ) + 1) / 2 := by ring
    rw [exponent] at cocycle
    rw [cocycle, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

def fusedResidueWeight (A k : ℤ) : ℂ :=
  if k < 0 then ((Ring.choose A (-k - 1).toNat : ℤ) : ℂ) else 0

def orderedResidueWeight (k B : ℤ) : ℂ :=
  if B < 0 then BinomialKernelDelta.chooseSign k (-B - 1).toNat else 0

private theorem signed_residue_balance (A B k : ℤ) (total : A + B + k = -2) :
    fusedResidueWeight A k = orderedResidueWeight k B -
      StateFieldResidueReconstruction.epsilon k * orderedResidueWeight k A := by
  by_cases negative : k < 0
  · let m := (-k - 1).toNat
    have kform : k = -(m : ℤ) - 1 := by dsimp [m]; omega
    have h := LatticeHalfFockClearedTaylorReadout.signed_kernel_choose m A
    have bform : B = (m : ℤ) - A - 1 := by omega
    simpa only [fusedResidueWeight, orderedResidueWeight, if_pos negative,
      kform, if_pos (show -(m : ℤ) - 1 < 0 by omega), bform, show -((m : ℤ) - A - 1) - 1 = A - m by omega,
      show (m : ℤ) - A - 1 < 0 ↔ 0 ≤ A - m by omega,
      show A < 0 ↔ 0 ≤ -A - 1 by omega,
      show -(-(m : ℤ) - 1) - 1 = m by omega, Int.toNat_natCast] using h.symm
  · obtain ⟨degree, kform⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k by omega)
    subst k
    have chooseNat (j : ℕ) : BinomialKernelDelta.chooseSign (degree : ℤ) j =
        (-1 : ℂ) ^ j * (degree.choose j : ℂ) := by
      simp [BinomialKernelDelta.chooseSign, Ring.choose_natCast]
    unfold fusedResidueWeight orderedResidueWeight
    rw [if_neg (by omega)]
    by_cases hA : A < 0
    · by_cases hB : B < 0
      · rw [if_pos hA, if_pos hB, chooseNat, chooseNat]
        let a := (-A - 1).toNat
        let b := (-B - 1).toNat
        have split : degree = a + b := by dsimp [a, b]; omega
        have symmetry : degree.choose b = degree.choose a := by
          rw [split, Nat.choose_symm_add]
        have sign : StateFieldResidueReconstruction.epsilon (degree : ℤ) *
            (-1 : ℂ) ^ a = (-1 : ℂ) ^ b := by
          rw [StateFieldResidueReconstruction.epsilon, zpow_natCast, split,
            pow_add]
          have square : (-1 : ℂ) ^ a * (-1 : ℂ) ^ a = 1 := by
            rw [← mul_pow]; norm_num
          calc
            _ = ((-1 : ℂ) ^ a * (-1 : ℂ) ^ a) * (-1 : ℂ) ^ b := by ring
            _ = _ := by rw [square, one_mul]
        change 0 = (-1 : ℂ) ^ b * (degree.choose b : ℂ) -
          StateFieldResidueReconstruction.epsilon (degree : ℤ) *
            ((-1 : ℂ) ^ a * (degree.choose a : ℂ))
        rw [symmetry, ← mul_assoc, sign, sub_self]
      · rw [if_pos hA, if_neg hB, chooseNat,
          Nat.choose_eq_zero_of_lt (show degree < (-A - 1).toNat by omega)]
        simp
    · rw [if_neg hA]
      by_cases hB : B < 0
      · rw [if_pos hB, chooseNat,
          Nat.choose_eq_zero_of_lt (show degree < (-B - 1).toNat by omega)]
        simp
      · simp [if_neg hB]

private theorem finite_collision_balance (P : LabelledPolynomial ℂ 3)
    (gamma d r : ℤ) (L M N degree : ℕ)
    (antidiagonal : (degree : ℤ) = L + M + N - d - r - 2) :
    (∑ u ∈ Finset.range (degree + 1), collisionTaylor P gamma u (degree - u) *
      fusedResidueWeight ((u : ℤ) - M) (d - L)) =
    (∑ u ∈ Finset.range (degree + 1), collisionTaylor P gamma u (degree - u) *
      orderedResidueWeight (d - L) ((degree - u : ℕ) + r - N)) -
    StateFieldResidueReconstruction.epsilon (d - L) *
      ∑ u ∈ Finset.range (degree + 1), collisionTaylor P gamma u (degree - u) *
        orderedResidueWeight (d - L) ((u : ℤ) - M) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  have bound : u ≤ degree := by simpa using Finset.mem_range.mp hu
  have total : ((u : ℤ) - M) + ((degree - u : ℕ) + r - N) + (d - L) = -2 := by
    rw [Int.natCast_sub bound]
    omega
  rw [signed_residue_balance _ _ _ total]
  ring

private theorem compatible_coefficient_mul (h : RatFunc ℂ)
    (R : CollisionLaurentKernels.LaurentCollision.Rational ℂ)
    (compatible : CollisionRationalExpansions.PartialFractionCollision.Compatible ℂ R) :
    CollisionRationalExpansions.PartialFractionCollision.Compatible ℂ
      (CollisionRationalExpansions.RationalCoefficientCollision.rationalX ℂ h * R) := by
  simp only [Compatible, map_mul, rationalX_ZX, rationalX_XZ, rationalX_fused,
    residue_outerSeries_mul, resXZ_inner_scalar] at *
  rw [← mul_sub, compatible]

private theorem compatible_sub
    (R S : CollisionLaurentKernels.LaurentCollision.Rational ℂ)
    (hR : CollisionRationalExpansions.PartialFractionCollision.Compatible ℂ R)
    (hS : CollisionRationalExpansions.PartialFractionCollision.Compatible ℂ S) :
    CollisionRationalExpansions.PartialFractionCollision.Compatible ℂ (R - S) := by
  unfold Compatible at *
  have subZX (F G : ZX ℂ) : resZ_ZX ℂ (F - G) = resZ_ZX ℂ F - resZ_ZX ℂ G := by
    ext n
    simp [resZ_ZX, HahnSeries.map_coeff]
  simp only [map_sub, subZX, resZ_XZ, HahnSeries.coeff_sub] at *
  linear_combination hR - hS

private theorem nonnegative_diagonal_collision (degree : ℕ) (B : ℤ) :
    CollisionRationalExpansions.PartialFractionCollision.Compatible ℂ
      (CollisionLaurentKernels.LaurentCollision.z ℂ ^ B *
        CollisionLaurentKernels.LaurentCollision.diagonal ℂ ^ degree) := by
  induction degree generalizing B with
  | zero =>
    have law := separated_rational_collision ℂ (RatFunc.X ^ B) 1
    dsimp only at law
    rw [← fused_residue_commutes] at law
    simpa only [Compatible, pow_zero, mul_one, map_one, one_mul, map_zpow₀,
      LatticeHalfFockLeftCurrentTransport.rational_z] using law.symm
  | succ degree ih =>
    have nz : z ℂ ≠ 0 := by
      unfold z
      simpa only [map_zero] using
        (IsFractionRing.injective (Bivariate ℂ) (Rational ℂ)).ne Polynomial.X_ne_zero
    have form : z ℂ ^ B * diagonal ℂ ^ (degree + 1) =
        z ℂ ^ (B + 1) * diagonal ℂ ^ degree -
          rationalX ℂ RatFunc.X * (z ℂ ^ B * diagonal ℂ ^ degree) := by
      rw [zpow_add₀ nz, zpow_one, pow_succ,
        LatticeHalfFockLeftCurrentTransport.rational_x]
      unfold diagonal
      ring
    rw [form]
    exact compatible_sub _ _ (ih (B + 1)) (compatible_coefficient_mul _ _ (ih B))

private theorem signed_laurent_collision (B k : ℤ) :
    CollisionRationalExpansions.PartialFractionCollision.Compatible ℂ
      (CollisionLaurentKernels.LaurentCollision.z ℂ ^ B *
        CollisionLaurentKernels.LaurentCollision.diagonal ℂ ^ k) := by
  by_cases hk : 0 ≤ k
  · obtain ⟨degree, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    simpa only [zpow_natCast] using nonnegative_diagonal_collision degree B
  · by_cases hB : 0 ≤ B
    · obtain ⟨degree, rfl⟩ := Int.eq_ofNat_of_zero_le hB
      simpa only [Compatible, zpow_natCast, zpow_zero, one_mul, Nat.cast_zero, sub_zero] using
        laurent_monomial_collision ℂ 0 degree 0 k
    · let p := (-B).toNat
      let q := (-k).toNat
      have Bform : B = -(p : ℤ) := by dsimp [p]; omega
      have kform : k = -(q : ℤ) := by dsimp [q]; omega
      have law := (negative_laurent_collision p q).2
      rw [← fused_residue_commutes] at law
      simpa only [Compatible, Bform, kform] using law.symm

/-- The rational two-residue chart of the actual Taylor antidiagonal. A
negative antidiagonal gives the empty sum. The remaining z power is -n-1
for the degree slice used by actual_nested_ordered_readouts. -/
def collisionChart (P : LabelledPolynomial ℂ 3) (gamma d r : ℤ) (L M N : ℕ) :
    CollisionLaurentKernels.LaurentCollision.Rational ℂ :=
  let degree : ℤ := L + M + N - d - r - 2
  ∑ u ∈ Finset.range (degree + 1).toNat,
    CollisionRationalExpansions.RationalCoefficientCollision.rationalX ℂ
      ((algebraMap ℂ (RatFunc ℂ) (collisionTaylor P gamma u (degree - u).toNat)) *
        RatFunc.X ^ ((degree - u).toNat + r - N)) *
      (CollisionLaurentKernels.LaurentCollision.z ℂ ^ ((u : ℤ) - M) *
        CollisionLaurentKernels.LaurentCollision.diagonal ℂ ^ (d - L))

private theorem collisionChart_balance (P : LabelledPolynomial ℂ 3)
    (gamma d r : ℤ) (L M N : ℕ) :
    CollisionRationalExpansions.PartialFractionCollision.Compatible ℂ
      (collisionChart P gamma d r L M N) := by
  unfold collisionChart
  apply compatible_sum
  intro u hu
  exact compatible_coefficient_mul _ _ (signed_laurent_collision _ _)

/-- The same actual Laurent numerator obeys the finite fractional coordinate
cocycle and the signed two-residue collision balance. These are chart
identities; identification with the complete nested Q coefficients is separate. -/
theorem actual_collision_taylor_balance (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (a b : Carrier D) :
    ∃ K : ℕ, ∀ (gamma delta d r n : ℤ) (x : ActualTensor D hu)
      (phi : ActualTensor D hu →ₗ[ℂ] ℂ),
      ∃ P : LabelledPolynomial ℂ 3,
        (∀ e : Exponent 3, P.coeff e =
          if totalExponent e =
              (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
          then phi (actualNumerator D hu i a b gamma delta K x e) else 0) ∧
        (∀ (H₁ H₂ H₃ : ℕ) (j : ℤ),
          phi (((qField (gamma + 1) r H₁
            (targetSlice D hu (neutralMode D i d a) (gamma + 1))
            (targetSlice D hu b delta))[[n]]) x) =
            nestedLeftReadout (gamma + 1) 1 d r n (vectorFrequencyBound D a + 1) H₁
              (targetCurrent D hu i) (targetSlice D hu a gamma) (targetSlice D hu b delta)
              x (rationalTripleReadout D a b K P) ∧
          phi (((qField 1 (d - j) H₂ (targetCurrent D hu i)
            (qField gamma (r + j) K (targetSlice D hu a gamma)
              (targetSlice D hu b delta)))[[n]]) x) =
            nestedRightReadout 1 gamma (r + j) (d - j) n K H₂
              (targetCurrent D hu i) (targetSlice D hu a gamma) (targetSlice D hu b delta)
              x (rationalTripleReadout D a b K P) ∧
          phi (((qField gamma (d + r - j) H₃ (targetSlice D hu a gamma)
            (targetSlice D hu (neutralMode D i j b) (delta + 1)))[[n]]) x) =
            nestedRightReadout gamma 1 j (d + r - j) n (vectorFrequencyBound D b + 1) H₃
              (targetSlice D hu a gamma) (targetCurrent D hu i) (targetSlice D hu b delta)
              x (swapCurrentSourceReadout (rationalTripleReadout D a b K P))) ∧
        (∀ u v : ℕ, associatedTaylor P gamma u v =
          ∑ j ∈ Finset.range (v + 1),
            ((u + j).choose u : ℂ) * collisionTaylor P gamma (u + j) (v - j)) ∧
        (let R := collisionChart P gamma d r
          (vectorFrequencyBound D a + 1) (vectorFrequencyBound D b + 1) K
         resZ_XZ ℂ (iotaFused ℂ R) =
           resZ_ZX ℂ (iotaZX ℂ R) - resZ_XZ ℂ (iotaXZ ℂ R)) ∧
        ∀ degree : ℕ,
          (degree : ℤ) = (vectorFrequencyBound D a + 1 : ℕ) +
            (vectorFrequencyBound D b + 1 : ℕ) + K - d - r - 2 →
          (∑ u ∈ Finset.range (degree + 1), collisionTaylor P gamma u (degree - u) *
            fusedResidueWeight ((u : ℤ) - (vectorFrequencyBound D b + 1 : ℕ))
              (d - (vectorFrequencyBound D a + 1 : ℕ))) =
          (∑ u ∈ Finset.range (degree + 1), collisionTaylor P gamma u (degree - u) *
            orderedResidueWeight (d - (vectorFrequencyBound D a + 1 : ℕ))
              ((degree - u : ℕ) + r - K)) -
          StateFieldResidueReconstruction.epsilon (d - (vectorFrequencyBound D a + 1 : ℕ)) *
            ∑ u ∈ Finset.range (degree + 1), collisionTaylor P gamma u (degree - u) *
              orderedResidueWeight (d - (vectorFrequencyBound D a + 1 : ℕ))
                ((u : ℤ) - (vectorFrequencyBound D b + 1 : ℕ)) := by
  obtain ⟨K, actual⟩ := actual_nested_ordered_readouts D hu i a b
  refine ⟨K, ?_⟩
  intro gamma delta d r n x phi
  obtain ⟨P, coefficients, readouts⟩ := actual gamma delta d r n x phi
  refine ⟨P, coefficients, readouts, associatedTaylor_cocycle P gamma, ?_, ?_⟩
  · exact (collisionChart_balance P gamma d r _ _ _).symm
  · intro degree antidiagonal
    exact finite_collision_balance P gamma d r _ _ _ degree antidiagonal

/-- Exact remaining identification with the complete nested Q products.
This proposition is unproved; it is not a hypothesis of a delivered theorem.
The numerator is fixed by its actual coefficient equation. Outer locality
orders apply to complete fields, independently for each intermediate Q. -/
def sameNumeratorCollisionBridge (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (a b : Carrier D) (K : ℕ) (gamma delta d r : ℤ) : Prop :=
  let J := targetCurrent D hu i
  let A := targetSlice D hu a gamma
  let B := targetSlice D hu b delta
  let Ad := targetSlice D hu (neutralMode D i d a) (gamma + 1)
  let Bj := fun j : ℕ => targetSlice D hu (neutralMode D i j b) (delta + 1)
  let L := vectorFrequencyBound D a + 1
  let M := vectorFrequencyBound D b + 1
  let degree : ℤ := L + M + K - d - r - 2
  ∀ (n : ℤ) (x : ActualTensor D hu) (phi : ActualTensor D hu →ₗ[ℂ] ℂ)
    (P : LabelledPolynomial ℂ 3),
    (∀ e : Exponent 3, P.coeff e =
      if totalExponent e =
          (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
      then phi (actualNumerator D hu i a b gamma delta K x e) else 0) →
    ∀ (H₁ : ℕ) (H₂ H₃ : ℕ → ℕ),
      (FieldNormalProductLocality.deltaEnd ^ H₁)
        (FieldNormalProductLocality.commutator Ad B) = 0 →
      (∀ j ∈ Finset.range ((K : ℤ) - r).toNat,
        (FieldNormalProductLocality.deltaEnd ^ H₂ j)
          (FieldNormalProductLocality.commutator J (qField gamma (r + j) K A B)) = 0) →
      (∀ j ∈ Finset.range M,
        (FieldNormalProductLocality.deltaEnd ^ H₃ j)
          (FieldNormalProductLocality.commutator A (Bj j)) = 0) →
      phi (((qField (gamma + 1) r H₁ Ad B)[[n]]) x) =
        (∑ u ∈ Finset.range (degree + 1).toNat,
          collisionTaylor P gamma u (degree - u).toNat *
            fusedResidueWeight ((u : ℤ) - M) (d - L)) ∧
      (∑ j ∈ Finset.range ((K : ℤ) - r).toNat,
        BinomialKernelDelta.chooseSign d j *
          phi (((qField 1 (d - j) (H₂ j) J (qField gamma (r + j) K A B))[[n]]) x)) =
        (∑ u ∈ Finset.range (degree + 1).toNat,
          collisionTaylor P gamma u (degree - u).toNat *
            orderedResidueWeight (d - L) (degree - u + r - K)) ∧
      StateFieldResidueReconstruction.epsilon d *
        (∑ j ∈ Finset.range M, BinomialKernelDelta.chooseSign d j *
          phi (((qField gamma (d + r - j) (H₃ j) A (Bj j))[[n]]) x)) =
        StateFieldResidueReconstruction.epsilon (d - L) *
          ∑ u ∈ Finset.range (degree + 1).toNat,
            collisionTaylor P gamma u (degree - u).toNat *
              orderedResidueWeight (d - L) ((u : ℤ) - M)

end CollisionTaylor


end
end D5.S3.VertexAlgebra.LatticeHalfFockNestedQReadout
