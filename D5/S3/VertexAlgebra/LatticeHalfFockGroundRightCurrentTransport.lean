/- GID: D5/S3/VertexAlgebra/LatticeHalfFockGroundRightCurrentTransport
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockGroundRightCurrentTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native ground-first finite current transport. -/

import D5.S3.VertexAlgebra.LatticeHalfFockCurrentWard
import D5.S3.VertexAlgebra.LatticeHalfFockPhysicalRescaling

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality
open LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField
open LatticeHalfFockCorrectedField
open LatticeHalfFockPhysicalRescaling
open LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents
open scoped BigOperators TensorProduct

noncomputable section

namespace D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport

universe u

/- The two projected components are retained as an honest source vector.  A
   Bool is used only to name the two signs; no component is discarded. -/
def projectedGround (D : LatticeData) (alpha : Charge D) (epsilon : Bool) : Carrier D :=
  (2 : ℂ)⁻¹ •
    (Finsupp.single alpha (1 : Oscillator D) +
      (if epsilon then -(1 : ℂ) else (1 : ℂ)) •
        Finsupp.single (-alpha) (1 : Oscillator D))

theorem projectedGround_positive_neutral
    (D : LatticeData) (i : Fin D.rank) (alpha : Charge D) (epsilon : Bool)
    (m : ℕ) (hm : 0 < m) :
    neutralMode D i (m : ℤ) (projectedGround D alpha epsilon) = 0 := by
  have hzero (beta : Charge D) :
      neutralPolynomialMode D i beta (m : ℤ) (1 : Oscillator D) = 0 := by
    apply neutralPolynomialMode_vanish D i beta (1 : Oscillator D) (m : ℤ)
    simp [polynomialFrequencyBound, hm]
  simp only [projectedGround, map_smul, map_add, neutralMode_single]
  rw [hzero alpha, hzero (-alpha)]
  simp

/- The actual physical slice keeps the original source carrier and the actual
   tensor carrier separate. -/
def slice (D : LatticeData) (hu : IsUnit D.G.det)
    (u : Carrier D) (lift mode : ℤ) : Module.End ℂ (ActualTensor D hu) :=
  (correctedField D hu u).coeff (-2 * mode - lift - 2)

def current (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (mode : ℤ) : Module.End ℂ (ActualTensor D hu) :=
  LatticeHalfFock.tensorCurrent D (ActualGround D hu) i mode

/- The Ward theorem becomes a genuine simple-pole commutator on either
   projected ground component.  The source zero mode is retained in the
   output; no division by its charge is used. -/
theorem projectedGround_current_ward
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (alpha : Charge D) (epsilon : Bool) (q lift mode : ℤ) (x : ActualTensor D hu) :
    (current D hu i q) (slice D hu (projectedGround D alpha epsilon) lift mode x) -
        (slice D hu (projectedGround D alpha epsilon) lift mode)
          (current D hu i q x) =
      (slice D hu (neutralMode D i 0 (projectedGround D alpha epsilon)) (lift + 1)
        (q + mode) x) := by
  simp only [slice, current]
  have hward := correctedField_current_ward D hu i
    (projectedGround D alpha epsilon) q (-2 * mode - lift - 2) x
  have hbound : 0 < vectorFrequencyBound D (projectedGround D alpha epsilon) + 1 := by
    omega
  rw [hward]
  rw [Finset.sum_eq_single 0]
  · simp only [Ring.choose_zero_right, one_smul]
    congr 2
    congr 1
    ring_nf
  · intro b hb hne
    have hbpos : 0 < b := Nat.pos_of_ne_zero hne
    rw [projectedGround_positive_neutral D i alpha epsilon b hbpos]
    simp
  · intro hnot
    exact (hnot (Finset.mem_range.mpr hbound)).elim

/- The ordered finite residue coefficient used below.  The two ordered
   summands remain visible in this definition; they are not replaced by an
   endomorphism-valued support assertion. -/
def residueWeight (r : ℤ) (j : ℕ) : ℂ :=
  (-1 : ℂ) ^ j * Ring.choose (r : ℂ) j

def groundCellWeight (gamma r d : ℤ) (ell v j k : ℕ) : ℂ :=
  Ring.choose (-(gamma : ℂ) / 2) ell * Ring.choose (-1 / 2 : ℂ) v *
    residueWeight (r + (ell : ℤ)) j *
    residueWeight (d + (v : ℤ)) k

def groundLeftCell {M : Type*} [AddCommGroup M] [Module ℂ M]
    (A B J : ℤ → Module.End ℂ M) (r d n : ℤ)
    (gamma : ℤ) (ell v j k : ℕ) : Module.End ℂ M :=
  let R := r + (ell : ℤ)
  let E := d + (v : ℤ)
  let w := groundCellWeight gamma r d ell v j k
  w • (
    -((-1 : ℂ) ^ E) •
      (A (R - (j : ℤ)) * B (n - (ell : ℤ) + (j : ℤ) + E - (k : ℤ)) * J (k : ℤ)) -
    ((-1 : ℂ) ^ R) •
      (J (E - (k : ℤ)) * B (n + R - (j : ℤ) - (v : ℤ) + (k : ℤ)) * A (j : ℤ)) +
    (A (R - (j : ℤ)) * J (E - (k : ℤ)) *
      B (n - (ell : ℤ) - (v : ℤ) + (j : ℤ) + (k : ℤ)) -
      J (E - (k : ℤ)) * A (R - (j : ℤ)) *
        B (n - (ell : ℤ) - (v : ℤ) + (j : ℤ) + (k : ℤ))) +
    ((-1 : ℂ) ^ R * (-1 : ℂ) ^ E) •
      (B (n + R + E - (j : ℤ) - (k : ℤ)) * J (k : ℤ) * A (j : ℤ) -
        B (n + R + E - (j : ℤ) - (k : ℤ)) * A (j : ℤ) * J (k : ℤ)))

def groundRightCell {M : Type*} [AddCommGroup M] [Module ℂ M]
    (A B J : ℤ → Module.End ℂ M) (r d n : ℤ)
    (gamma : ℤ) (ell v j k : ℕ) : Module.End ℂ M :=
  let R := r + (ell : ℤ)
  let E := d + (v : ℤ)
  let w := groundCellWeight gamma r d ell v j k
  w • (
    -((-1 : ℂ) ^ E) •
      (A (R - (j : ℤ)) * B (n - (ell : ℤ) + (j : ℤ) + E - (k : ℤ)) * J (k : ℤ)) -
    ((-1 : ℂ) ^ R) •
      (J (E - (k : ℤ)) * B (n + R - (j : ℤ) - (v : ℤ) + (k : ℤ)) * A (j : ℤ)))

def groundCorrectionCell {M : Type*} [AddCommGroup M] [Module ℂ M]
    (A₀ B : ℤ → Module.End ℂ M) (r d n : ℤ)
    (gamma : ℤ) (ell v j k : ℕ) : Module.End ℂ M :=
  let R := r + (ell : ℤ)
  let E := d + (v : ℤ)
  let w := groundCellWeight gamma r d ell v j k
  w • (A₀ (R + E - (j : ℤ) - (k : ℤ)) *
      B (n - (ell : ℤ) - (v : ℤ) + (j : ℤ) + (k : ℤ)) -
    ((-1 : ℂ) ^ R * (-1 : ℂ) ^ E) •
      (B (n + R + E - (j : ℤ) - (k : ℤ)) * A₀ ((j : ℤ) + (k : ℤ))))

def groundFiniteLeft {M : Type*} [AddCommGroup M] [Module ℂ M]
    (A B J : ℤ → Module.End ℂ M) (r d n gamma : ℤ)
    (outer inner : ℕ) : Module.End ℂ M :=
  ∑ ell ∈ Finset.range outer, ∑ v ∈ Finset.range outer,
    ∑ j ∈ Finset.range inner, ∑ k ∈ Finset.range inner,
      groundLeftCell A B J r d n gamma ell v j k

def groundFiniteRight {M : Type*} [AddCommGroup M] [Module ℂ M]
    (A B J : ℤ → Module.End ℂ M) (r d n gamma : ℤ)
    (outer inner : ℕ) : Module.End ℂ M :=
  ∑ ell ∈ Finset.range outer, ∑ v ∈ Finset.range outer,
    ∑ j ∈ Finset.range inner, ∑ k ∈ Finset.range inner,
      groundRightCell A B J r d n gamma ell v j k

def groundFiniteCorrection {M : Type*} [AddCommGroup M] [Module ℂ M]
    (A₀ B : ℤ → Module.End ℂ M) (r d n gamma : ℤ)
    (outer inner : ℕ) : Module.End ℂ M :=
  ∑ ell ∈ Finset.range outer, ∑ v ∈ Finset.range outer,
    ∑ j ∈ Finset.range inner, ∑ k ∈ Finset.range inner,
      groundCorrectionCell A₀ B r d n gamma ell v j k

/- One cell is the actual operator cancellation.  Its proof uses only the
   Ward commutator and the integer signed mode arithmetic. -/
theorem ground_cell_cancellation
    {M : Type*} [AddCommGroup M] [Module ℂ M]
    (A A₀ B J : ℤ → Module.End ℂ M) (r d n gamma : ℤ)
    (ell v j k : ℕ)
    (ward : ∀ z t : ℤ, J z * A t - A t * J z = A₀ (z + t)) :
    groundLeftCell A B J r d n gamma ell v j k =
      groundRightCell A B J r d n gamma ell v j k -
        groundCorrectionCell A₀ B r d n gamma ell v j k := by
  dsimp [groundLeftCell, groundRightCell, groundCorrectionCell,
    groundCellWeight, residueWeight]
  have h₁ := ward (d + (v : ℤ) - (k : ℤ)) (r + (ell : ℤ) - (j : ℤ))
  have h₂ := ward (k : ℤ) (j : ℤ)
  have hleft :
      A (r + (ell : ℤ) - (j : ℤ)) * J (d + (v : ℤ) - (k : ℤ)) *
          B (n - (ell : ℤ) - (v : ℤ) + (j : ℤ) + (k : ℤ)) -
        J (d + (v : ℤ) - (k : ℤ)) * A (r + (ell : ℤ) - (j : ℤ)) *
          B (n - (ell : ℤ) - (v : ℤ) + (j : ℤ) + (k : ℤ)) =
      -(A₀ (r + (ell : ℤ) + (d + (v : ℤ)) - (j : ℤ) - (k : ℤ)) *
          B (n - (ell : ℤ) - (v : ℤ) + (j : ℤ) + (k : ℤ))) := by
    calc
      _ = -((J (d + (v : ℤ) - (k : ℤ)) *
          A (r + (ell : ℤ) - (j : ℤ)) -
          A (r + (ell : ℤ) - (j : ℤ)) *
            J (d + (v : ℤ) - (k : ℤ))) *
          B (n - (ell : ℤ) - (v : ℤ) + (j : ℤ) + (k : ℤ))) := by noncomm_ring
      _ = -(A₀ (r + (ell : ℤ) + (d + (v : ℤ)) - (j : ℤ) - (k : ℤ)) *
          B (n - (ell : ℤ) - (v : ℤ) + (j : ℤ) + (k : ℤ))) := by
        rw [h₁]
        congr 1
        congr 1
        ring
  have hright :
      B (n + (r + (ell : ℤ)) + (d + (v : ℤ)) - (j : ℤ) - (k : ℤ)) * J (k : ℤ) * A (j : ℤ) -
        B (n + (r + (ell : ℤ)) + (d + (v : ℤ)) - (j : ℤ) - (k : ℤ)) *
          A (j : ℤ) * J (k : ℤ) =
      B (n + (r + (ell : ℤ)) + (d + (v : ℤ)) - (j : ℤ) - (k : ℤ)) *
        A₀ ((j : ℤ) + (k : ℤ)) := by
    calc
      _ = B (n + (r + (ell : ℤ)) + (d + (v : ℤ)) - (j : ℤ) - (k : ℤ)) *
          (J (k : ℤ) * A (j : ℤ) - A (j : ℤ) * J (k : ℤ)) := by noncomm_ring
      _ = B (n + (r + (ell : ℤ)) + (d + (v : ℤ)) - (j : ℤ) - (k : ℤ)) *
          A₀ ((j : ℤ) + (k : ℤ)) := by
        rw [h₂]
        congr 1
        congr 1
        ring
  rw [hleft, hright]
  module

/- Summing the proved cells is the finite ground-first normal-product
   interchange.  `outer` and `inner` are explicit finite cutoffs; no tail or
   full-current law is hidden in the statement. -/
theorem ground_finite_right_transport
    {M : Type u} [AddCommGroup M] [Module ℂ M]
    (A A₀ B J : ℤ → Module.End ℂ M) (r d n gamma : ℤ)
    (outer inner : ℕ)
    (ward : ∀ z t : ℤ, J z * A t - A t * J z = A₀ (z + t)) :
    groundFiniteLeft A B J r d n gamma outer inner =
      groundFiniteRight A B J r d n gamma outer inner -
        groundFiniteCorrection A₀ B r d n gamma outer inner := by
  simp only [groundFiniteLeft, groundFiniteRight, groundFiniteCorrection]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ell hell
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  exact ground_cell_cancellation A A₀ B J r d n gamma ell v j k ward

/- Concrete native consumer: instantiate the cancellation with the original
   corrected field on `Carrier D`, its actual tensor current, and the two
   projected ground components. -/
theorem projectedGround_finite_right_transport
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (alpha : Charge D) (epsilon : Bool) (b : Carrier D)
    (r d n gamma delta : ℤ) (outer inner : ℕ) :
    groundFiniteLeft
        (fun mode => slice D hu (projectedGround D alpha epsilon) gamma mode)
        (fun mode => slice D hu b delta mode)
        (fun mode => current D hu i mode)
        r d n gamma outer inner =
      groundFiniteRight
        (fun mode => slice D hu (projectedGround D alpha epsilon) gamma mode)
        (fun mode => slice D hu b delta mode)
        (fun mode => current D hu i mode)
        r d n gamma outer inner -
      groundFiniteCorrection
        (fun mode => slice D hu
          (neutralMode D i 0 (projectedGround D alpha epsilon)) (gamma + 1) mode)
        (fun mode => slice D hu b delta mode)
        r d n gamma outer inner := by
  apply ground_finite_right_transport
  intro z t
  apply LinearMap.ext
  intro x
  exact projectedGround_current_ward D hu i alpha epsilon z gamma t x

end D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport

end
