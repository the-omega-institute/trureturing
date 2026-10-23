/- GID: D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSliceQuotient/SupportedReadouts
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSliceQuotient/SupportedReadouts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Supported complete residues and nested two-branch readouts. -/
import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSliceQuotient.ActualLaurentCarriers

/-! Supported complete residues and nested two-branch readouts.
The finite-slice, two-branch extraction and signed-collision proofs retain their
original research substance at e7115cf0e88dde8f45861e42cd51d8a39473c0fe.
Classical local-field calculus: Matsuo--Nagatomo; twisted lattice setting:
Bakalov--Kac, math/0402315. No literature novelty or final Taylor bridge is claimed.
Hahn/Laurent kernels: mathlib, Apache 2.0 (Aaron Anderson, María Inés de
Frutos-Fernández, Filippo A. E. Nuccio); partial fractions: Kevin Buzzard,
Sidharth Hariharan, Aaron Liu. Actual field composition: Scott Carnahan,
vertexAlg 4453e34ec390e82a0c789c731ada8f9a6e86bdea, Apache 2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockNestedQReadout
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockClearedTaylorReadout
open NestedResidues.ContextualKernelExtraction
open UniformGradedLocalCorrelator
open LatticeHalfFockChargedCollision.WeightedLocalCorrelator
open SupportedFieldWords.OrderedWords SupportedFieldWords.OrderedDistribution
open CollisionRationalExpansions.OrderedRationalExpansion
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open scoped BigOperators VertexOperator
noncomputable section

section NestedReadout
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
open StateFieldResidueReconstruction
def supportedQReadout (s r : ℤ) (K : ℕ) (n : ℤ)
    (forward backward : ℤ → ℤ → ℂ) : ℂ :=
  ∑ ell ∈ Finset.range ((K : ℤ) - r).toNat,
    Ring.choose (-(s : ℂ) / 2) ell *
      ((∑ᶠ u : ℕ, BinomialKernelDelta.chooseSign (r + ell) u *
          forward (r + ell - u) (n - ell + u)) -
       epsilon (r + ell) *
        ∑ᶠ u : ℕ, BinomialKernelDelta.chooseSign (r + ell) u *
          backward (r + n - u) u)

theorem supportedQReadout_eq (s r : ℤ) (K : ℕ)
    (A B : VertexOperator ℂ V) (x : V) (n : ℤ) (phi : V →ₗ[ℂ] ℂ) :
    phi (((qField s r K A B)[[n]]) x) = supportedQReadout s r K n
      (fun m k => phi ((A[[m]]) ((B[[k]]) x)))
      (fun m k => phi ((B[[m]]) ((A[[k]]) x))) := by
  rw [qField, LatticeHalfFockGroundRightCurrentTransport.Calculus.Q_mode, map_sum]
  apply Finset.sum_congr rfl
  intro ell hell
  rw [map_smul, ← LatticeHalfFockChargedResidue.physicalResidueCoefficient_eq_R]
  congr 1
  unfold LatticeHalfFockChargedResidue.physicalResidueCoefficient
    LatticeHalfFockChargedResidue.physicalResidueLeft
    LatticeHalfFockChargedResidue.physicalResidueRight
  rw [map_sub, map_smul,
    map_finsum phi (LatticeHalfFockChargedResidue.physicalResidueLeft_finite A B (r + ell) (n - ell) x),
    map_finsum phi (LatticeHalfFockChargedResidue.physicalResidueRight_finite A B (r + ell) (n - ell) x)]
  simp only [map_smul, smul_eq_mul, BinomialKernelDelta.chooseSign,
    LatticeHalfFockChargedResidue.physicalResidueWeight, integerBinomial,
    StateFieldResidueReconstruction.epsilon,
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
  unfold qField LatticeHalfFockGroundRightCurrentTransport.Calculus.Q
  apply Finset.sum_eq_zero
  intro ell member
  have valid := LatticeHalfFockGroundRightCurrentTransport.Calculus.valid_of_locality A B H locality
  rw [valid (r + ell) (by omega)]
  suffices LatticeHalfFockGroundRightCurrentTransport.Calculus.Z (ell : ℤ)
      (0 : VertexOperator ℂ V) = 0 by simp [this]
  apply HVertexOperator.coeff_inj
  funext e
  apply LinearMap.ext
  intro x
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff]
  rw [LatticeHalfFockGroundRightCurrentTransport.Calculus.Z, VertexOperator.ncoeff_of_coeff]
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

theorem completeOuterQReadout_of_locality (s r n : ℤ) (H : ℕ)
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

theorem supportedQReadout_congr (s r : ℤ) (K : ℕ) (n : ℤ)
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

open CollisionLaurentKernels.LaurentCollision
open OrderedCollisionCoordinates.ContextualLaurentKernel
theorem reverse_kernel (r : ℤ) :
    kernelXZ ℂ r = (HahnSeries.C (HahnSeries.C (StateFieldResidueReconstruction.epsilon r))) * kernelZX ℂ r := by
  unfold kernelXZ kernelZX StateFieldResidueReconstruction.epsilon
  rw [neg_eq_neg_one_mul, mul_zpow, map_mul]
  simp only [map_zpow₀, map_neg, map_one]
  ring


def triplePermutation (order : Fin 6) : Equiv.Perm (Fin 3) :=
  ![Equiv.refl _, Equiv.swap 1 2, Equiv.swap 0 1,
    Equiv.ofBijective ![1, 2, 0] (by decide),
    Equiv.ofBijective ![2, 0, 1] (by decide), Equiv.swap 0 2] order

def tripleScalar (A B C : VertexOperator ℂ V) (x : V)
    (phi : V →ₗ[ℂ] ℂ) (order : Fin 6) (modes : Exponent 3) : ℂ :=
  phi (coefficientDistribution ![A, B, C] x 1
    (List.ofFn (triplePermutation order)) (fun j => -modes j - 1))
private def supportedNestedLeftReadout (outerLift innerLift d r n : ℤ) (K H : ℕ)
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
open CollisionLaurentKernels.LaurentCollision
open OrderedCollisionCoordinates.ContextualLaurentKernel
open CollisionRationalExpansions.HahnFiberResidue
open CollisionRationalExpansions.FullOrderSpectatorPole
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
    rw [reverse_kernel,
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
    rw [reverse_kernel,
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

theorem nestedLeftFiberReadout_eq (outerLift innerLift d r n : ℤ) (K H : ℕ)
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

theorem nestedRightFiberReadout_eq (outerLift innerLift d r n : ℤ) (K H : ℕ)
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


theorem supportedNestedLeftReadout_congr (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (R S : Fin 6 → Exponent 3 → ℂ)
    (same : ∀ order modes, (∑ j, modes j) = d + r + n → R order modes = S order modes) :
    supportedNestedLeftReadout outerLift innerLift d r n K H R =
      supportedNestedLeftReadout outerLift innerLift d r n K H S := by
  unfold supportedNestedLeftReadout
  apply supportedQReadout_congr <;> intro k l hkl <;> apply supportedQReadout_congr <;>
    intro m p hmp <;> apply same <;> simp [Fin.sum_univ_three] <;> omega

theorem supportedNestedRightReadout_congr (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (R S : Fin 6 → Exponent 3 → ℂ)
    (same : ∀ order modes, (∑ j, modes j) = d + r + n → R order modes = S order modes) :
    supportedNestedRightReadout outerLift innerLift d r n K H R =
      supportedNestedRightReadout outerLift innerLift d r n K H S := by
  unfold supportedNestedRightReadout
  apply supportedQReadout_congr <;> intro k l hkl <;> apply supportedQReadout_congr <;>
    intro m p hmp <;> apply same <;> simp [Fin.sum_univ_three] <;> omega

theorem supportedNestedLeftReadout_eq (outerLift innerLift d r n : ℤ) (K H : ℕ)
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

theorem supportedNestedRightReadout_eq (outerLift innerLift d r n : ℤ) (K H : ℕ)
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

end NestedReadout

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

theorem hahnTripleScalar_swap (W : Fin 6 → HahnSeries (Indices 3) ℂ) :
    hahnTripleScalar (swapCurrentSourceCarriers W) =
      swapCurrentSourceReadout (hahnTripleScalar W) := by
  funext order modes
  fin_cases order <;>
    simp [hahnTripleScalar, swapCurrentSourceCarriers, swapCurrentSourceReadout,
      triplePermutation, orderExponents, labelPermutation, Equiv.swap_apply_def] <;>
    congr 1 <;> congr 1 <;> funext j <;> fin_cases j <;>
    simp [Equiv.swap_apply_def]

theorem tripleScalar_swap {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B C : VertexOperator ℂ V) (x : V) (phi : V →ₗ[ℂ] ℂ) :
    tripleScalar B A C x phi = swapCurrentSourceReadout (tripleScalar A B C x phi) := by
  funext order modes
  fin_cases order <;>
    simp [tripleScalar, swapCurrentSourceReadout, triplePermutation,
      coefficientDistribution, word, Module.End.mul_apply, Equiv.swap_apply_def]

end
end D5.S3.VertexAlgebra.LatticeHalfFockNestedQReadout
