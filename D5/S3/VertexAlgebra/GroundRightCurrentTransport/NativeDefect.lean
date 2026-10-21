/- GID: D5/S3/VertexAlgebra/GroundRightCurrentTransport/NativeDefect
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/GroundRightCurrentTransport/NativeDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original-source ground-current defects and negative-word propagation. -/

import D5.S3.VertexAlgebra.GroundRightCurrentTransport.Interchange
import D5.S3.VertexAlgebra.LatticeActualStateFieldCalculus
import D5.S3.VertexAlgebra.LatticeHalfFockAllStatePhysicalLocality

/-! Complete supported residue calculus for the native ground-current consumer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct VertexOperator
open D5.S3.VertexAlgebra

namespace D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport

universe u

open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField LatticeHalfFockCorrectedField
open LatticeHalfFockPhysicalRescaling LatticeFiniteNegativeGeneration LatticeSugawaraCurrents

local macro "ext_modes" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.ext_modes))
local macro "R_mode" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.R_mode))
local macro "Z_mode" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.Z_mode))
local macro "Q_mode" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.Q_mode))
local macro "Q_cutoff" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.Q_cutoff))
local macro "valid_of_locality" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.valid_of_locality))
local macro "Q_left_valid" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Interchange 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.Q_left_valid))
local macro "Q_right_valid" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Interchange 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.Q_right_valid))
local macro "Q_interchange" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Interchange 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.Q_interchange))
local macro "R_sub" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Interchange 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.R_sub))
local macro "Q_sub" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Interchange 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.Q_sub))
local macro "Q_zero" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Interchange 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.Q_zero))


open scoped VertexOperator
open Calculus

private def nativeSlice (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Carrier D) (gamma : ℤ) : VertexOperator ℂ (ActualTensor D hu) :=
  physicalSlice D hu (correctedField D hu a) gamma

private theorem nativeSlice_mode (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Carrier D) (gamma n : ℤ) :
    (nativeSlice D hu a gamma)[[n]] = slice D hu a gamma n :=
  physicalSlice_mode D hu (correctedField D hu a) gamma n

private theorem native_valid_exists (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Carrier D) (gamma delta : ℤ) :
    ∃ K : ℕ, ∀ shift : ℤ,
      Valid (Z (-shift) (nativeSlice D hu a gamma)) (nativeSlice D hu b delta) K := by
  obtain ⟨K, locality⟩ :=
    LatticeHalfFockAllStatePhysicalLocality.correctedField_physical_locality D hu a b
  refine ⟨K, fun shift => valid_of_locality _ _ K ?_⟩
  funext p q
  apply LinearMap.ext
  intro x
  rw [FieldDeltaBinomial.delta_binomial]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply,
    FieldNormalProductLocality.commutator, LinearMap.sub_apply,
    Module.End.mul_apply, Z_mode, sub_neg_eq_add, nativeSlice_mode, slice]
  have h := locality (-2*(p+shift)-gamma-2) (-2*q-delta-2) x
  convert h using 1
  apply Finset.sum_congr rfl
  intro j hj
  have within : j ≤ K := by simpa using Finset.mem_range.mp hj
  rw [Int.natCast_sub within]
  rw [show -2*(p+(K:ℤ)-j+shift)-gamma-2 = -2*(p+shift)-gamma-2-2*((K:ℤ)-j) by ring,
    show -2*(q+(j:ℤ))-delta-2 = -2*q-delta-2-2*j by ring]

private def nativeCutoff (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Carrier D) (gamma delta : ℤ) : ℕ :=
  Classical.choose (native_valid_exists D hu a b gamma delta)

private theorem native_valid (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Carrier D) (gamma delta : ℤ) :
    Valid (nativeSlice D hu a gamma) (nativeSlice D hu b delta)
      (nativeCutoff D hu a b gamma delta) := by
  have h := Classical.choose_spec (native_valid_exists D hu a b gamma delta) 0
  have z0 : Z 0 (nativeSlice D hu a gamma) = nativeSlice D hu a gamma := by
    apply ext_modes
    intro n
    simp only [Z_mode, sub_zero]
  simpa only [nativeCutoff, neg_zero, z0] using h

/-- The complete-cutoff inverse residue product of two original-source slices. -/
def nativeProduct (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Carrier D) (gamma delta r : ℤ) : VertexOperator ℂ (ActualTensor D hu) :=
  Q (nativeSlice D hu a gamma) (nativeSlice D hu b delta) gamma r
    (nativeCutoff D hu a b gamma delta)

/-- Difference from the original source iterate, on the actual tensor carrier. -/
def defect (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Carrier D) (gamma delta r : ℤ) : VertexOperator ℂ (ActualTensor D hu) :=
  nativeSlice D hu (LatticeAllStateReconstruction.mu D a r b) (gamma+delta) -
    nativeProduct D hu a b gamma delta r

private def nativeCurrent (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank) :
    VertexOperator ℂ (ActualTensor D hu) := physicalJet D hu (i,0)

private theorem nativeCurrent_mode (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (n : ℤ) :
    (nativeCurrent D hu i)[[n]] = current D hu i n := by
  rw [nativeCurrent, physicalJet_mode]
  simp [jetCurrent, jetScalar, current]

private theorem native_current_residue (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (b : Carrier D) (delta r n : ℤ) (x : ActualTensor D hu) :
    ((R (nativeCurrent D hu i) (nativeSlice D hu b delta) r)[[n]]) x =
      currentResidue D hu i (correctedField D hu b) delta r n x := by
  simp only [R_mode, nativeCurrent_mode, nativeSlice_mode, slice, current,
    currentResidue, residueWeight]
  rw [add_comm n r]

private theorem native_current_valid (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (b : Carrier D) (delta : ℤ) :
    Valid (nativeCurrent D hu i) (nativeSlice D hu b delta)
      (vectorFrequencyBound D b + 1) := by
  intro r hr
  obtain ⟨s, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ r by omega)
  apply ext_modes
  intro n
  apply LinearMap.ext
  intro x
  rw [native_current_residue]
  exact correctedField_positive_current_residue_tail D hu i b delta n s x (by omega)

local macro "currentInverse" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds.inverse_all))

private theorem native_current_inverse (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (b : Carrier D) (delta r : ℤ) :
    nativeSlice D hu (neutralMode D i r b) (delta+1) =
      Q (nativeCurrent D hu i) (nativeSlice D hu b delta) 1 r
        (vectorFrequencyBound D b + 1) := by
  apply ext_modes
  intro n
  apply LinearMap.ext
  intro x
  rw [nativeSlice_mode, Q_mode]
  simp only [slice, native_current_residue]
  rw [show -2*n-(delta+1)-2 = -2*n-delta-3 by omega]
  have h := currentInverse D hu i b delta r n x
    ((vectorFrequencyBound D b + 1 : ℤ)-r).toNat (by omega)
  simpa only [Int.cast_one, neg_div, Nat.cast_add, Nat.cast_one] using h

private theorem nativeSlice_sub (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Carrier D) (s : ℤ) :
    nativeSlice D hu (a-b) s = nativeSlice D hu a s - nativeSlice D hu b s := by
  apply ext_modes
  intro n
  apply LinearMap.ext
  intro x
  simp only [nativeSlice_mode, slice, map_sub, Pi.sub_apply, LinearMap.sub_apply]

local macro "sourceCurrent" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds.source_current))

private theorem source_ground_commutator (D : LatticeData) (i : Fin D.rank)
    (alpha : Charge D) (epsilon : Bool) (b : Carrier D) (d r : ℤ) :
    LatticeAllStateReconstruction.mu D (projectedGround D alpha epsilon) r
        (neutralMode D i d b) =
      neutralMode D i d
        (LatticeAllStateReconstruction.mu D (projectedGround D alpha epsilon) r b) -
      LatticeAllStateReconstruction.mu D
        (neutralMode D i 0 (projectedGround D alpha epsilon)) (r+d) b := by
  let a := projectedGround D alpha epsilon
  let h := neutralMode D i (-1) (LatticeAllStateField.vacuum D)
  have currentMode (z : ℤ) : (LatticeAllStateField.Y D h)[[z]] = neutralMode D i z := by
    apply LinearMap.ext
    intro c
    exact sourceCurrent D i z c
  have law := LatticeActualStateFieldCalculus.mode_commutator D h a d r
  rw [currentMode] at law
  have collapse : (∑ᶠ j : ℕ,
      LatticeActualStateFieldCalculus.commutatorTerm D h a d r j) =
      (LatticeAllStateField.Y D (neutralMode D i 0 a))[[r+d]] := by
    rw [finsum_eq_single _ 0]
    · simp only [LatticeActualStateFieldCalculus.commutatorTerm, h, sourceCurrent,
        StateFieldResidueReconstruction.integerBinomial, Ring.choose_zero_right,
        Int.cast_one, one_smul, Nat.cast_zero, sub_zero, add_comm d r]
    · intro j hj
      simp only [LatticeActualStateFieldCalculus.commutatorTerm, h, sourceCurrent,
        projectedGround_positive_neutral D i alpha epsilon j (Nat.pos_of_ne_zero hj),
        a, map_zero, Pi.zero_apply, smul_zero]
  rw [collapse] at law
  have result := congrArg (fun L : Module.End ℂ (Carrier D) => L b) law
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at result
  change neutralMode D i d (LatticeAllStateReconstruction.mu D a r b) -
      LatticeAllStateReconstruction.mu D a r (neutralMode D i d b) =
    LatticeAllStateReconstruction.mu D (neutralMode D i 0 a) (r+d) b at result
  have eq := sub_eq_iff_eq_add.mp result
  calc
    _ = neutralMode D i d (LatticeAllStateReconstruction.mu D a r b) -
        LatticeAllStateReconstruction.mu D (neutralMode D i 0 a) (r+d) b := by
      rw [eq]
      abel

private theorem native_ground_ward (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (alpha : Charge D) (epsilon : Bool) (gamma : ℤ) :
    ∀ z t : ℤ,
      (nativeCurrent D hu i)[[z]] * (nativeSlice D hu (projectedGround D alpha epsilon) gamma)[[t]] -
        (nativeSlice D hu (projectedGround D alpha epsilon) gamma)[[t]] *
          (nativeCurrent D hu i)[[z]] =
      (nativeSlice D hu (neutralMode D i 0 (projectedGround D alpha epsilon))
        (gamma+1))[[z+t]] := by
  intro z t
  simp only [nativeCurrent_mode, nativeSlice_mode]
  apply LinearMap.ext
  intro x
  exact projectedGround_current_ward D hu i alpha epsilon z gamma t x

private theorem native_product_growth (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (alpha : Charge D) (epsilon : Bool) (b : Carrier D)
    (gamma delta r d : ℤ) :
    nativeProduct D hu (projectedGround D alpha epsilon) (neutralMode D i d b)
        gamma (delta+1) r =
      Q (nativeCurrent D hu i)
        (nativeProduct D hu (projectedGround D alpha epsilon) b gamma delta r) 1 d
        (max (vectorFrequencyBound D b + 1)
          (((nativeCutoff D hu (neutralMode D i 0 (projectedGround D alpha epsilon))
            b (gamma+1) delta : ℕ) : ℤ)-r).toNat) -
      nativeProduct D hu (neutralMode D i 0 (projectedGround D alpha epsilon))
        b (gamma+1) delta (r+d) := by
  let a := projectedGround D alpha epsilon
  let a0 := neutralMode D i 0 a
  let A := nativeSlice D hu a gamma
  let A0 := nativeSlice D hu a0 (gamma+1)
  let B := nativeSlice D hu b delta
  let J := nativeCurrent D hu i
  let KAB := nativeCutoff D hu a b gamma delta
  let K0 := nativeCutoff D hu a0 b (gamma+1) delta
  let KJB := vectorFrequencyBound D b + 1
  let KN := nativeCutoff D hu a (neutralMode D i d b) gamma (delta+1)
  have ward := native_ground_ward D hu i alpha epsilon gamma
  have hAB := native_valid D hu a b gamma delta
  have h0 := native_valid D hu a0 b (gamma+1) delta
  have hJB := native_current_valid D hu i b delta
  have hN := native_valid D hu a (neutralMode D i d b) gamma (delta+1)
  rw [native_current_inverse] at hN
  have hleft := Q_left_valid A A0 J B d KAB KJB K0 hAB h0 ward
  have law := Q_interchange A A0 J B gamma r d KAB KJB K0 hAB hJB h0 ward
  change Q A (nativeSlice D hu (neutralMode D i d b) (delta+1)) gamma r KN = _
  rw [native_current_inverse]
  rw [Q_cutoff A (Q J B 1 d KJB) gamma r KN
    (max KAB ((K0 : ℤ)-d).toNat) hN hleft]
  exact law

private theorem defect_current_valid_exists (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (alpha : Charge D) (epsilon : Bool) (b : Carrier D)
    (gamma delta r : ℤ) :
    ∃ K : ℕ, Valid (nativeCurrent D hu i)
      (defect D hu (projectedGround D alpha epsilon) b gamma delta r) K := by
  let a := projectedGround D alpha epsilon
  let a0 := neutralMode D i 0 a
  let U := LatticeAllStateReconstruction.mu D a r b
  let K0 := nativeCutoff D hu a0 b (gamma+1) delta
  let KP := max (vectorFrequencyBound D b + 1) ((K0 : ℤ)-r).toNat
  let KU := vectorFrequencyBound D U + 1
  let K := max KU KP
  have hU := native_current_valid D hu i U (gamma+delta)
  have hP := Q_right_valid (nativeSlice D hu a gamma) (nativeSlice D hu a0 (gamma+1))
    (nativeCurrent D hu i) (nativeSlice D hu b delta) r gamma
    (nativeCutoff D hu a b gamma delta) (vectorFrequencyBound D b + 1) K0
    (native_current_valid D hu i b delta) (native_valid D hu a0 b (gamma+1) delta)
    (native_ground_ward D hu i alpha epsilon gamma)
  change Valid (nativeCurrent D hu i) (nativeProduct D hu a b gamma delta r) KP at hP
  refine ⟨K, ?_⟩
  intro d hd
  change R (nativeCurrent D hu i)
    (nativeSlice D hu U (gamma+delta) - nativeProduct D hu a b gamma delta r) d = 0
  rw [R_sub, hU d (by dsimp [K, KU] at hd; omega),
    hP d (by dsimp [K, KP] at hd; omega), sub_zero]

/-- The current inverse product on the actual original-source defect field.
    Its cutoff is certified for this changed field, including its source iterate. -/
def currentDefectProduct (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (alpha : Charge D) (epsilon : Bool) (b : Carrier D)
    (gamma delta r d : ℤ) : VertexOperator ℂ (ActualTensor D hu) :=
  Q (nativeCurrent D hu i)
    (defect D hu (projectedGround D alpha epsilon) b gamma delta r) 1 d
      (Classical.choose (defect_current_valid_exists D hu i alpha epsilon b gamma delta r))

/- proof_shape: projectedGround_defect_transport: content
   admission_basis: escape-witness
   escape_witness: The finite eight-composition cancellation and half-binomial
   convolution connect original-source Jacobi with native actual-input inverse
   products, including the zero-mode correction and freshly certified cutoffs.
   Literature status: classical twisted-lattice calculus; no novelty claim. -/
/-- Native ground-first current transport of the actual original-source defect.
    No compatibility or transport law is a premise; every signed insertion survives. -/
theorem projectedGround_defect_transport (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (alpha : Charge D) (epsilon : Bool) (b : Carrier D)
    (gamma delta r d : ℤ) :
    defect D hu (projectedGround D alpha epsilon) (neutralMode D i d b)
        gamma (delta+1) r =
      currentDefectProduct D hu i alpha epsilon b gamma delta r d -
        defect D hu (neutralMode D i 0 (projectedGround D alpha epsilon))
          b (gamma+1) delta (r+d) := by
  let a := projectedGround D alpha epsilon
  let a0 := neutralMode D i 0 a
  let U := LatticeAllStateReconstruction.mu D a r b
  let P := nativeProduct D hu a b gamma delta r
  let J := nativeCurrent D hu i
  let K0 := nativeCutoff D hu a0 b (gamma+1) delta
  let KP := max (vectorFrequencyBound D b + 1) ((K0 : ℤ)-r).toNat
  let KU := vectorFrequencyBound D U + 1
  let K := max KU KP
  have hU := native_current_valid D hu i U (gamma+delta)
  have hP := Q_right_valid (nativeSlice D hu a gamma) (nativeSlice D hu a0 (gamma+1))
    J (nativeSlice D hu b delta) r gamma (nativeCutoff D hu a b gamma delta)
    (vectorFrequencyBound D b + 1) K0 (native_current_valid D hu i b delta)
    (native_valid D hu a0 b (gamma+1) delta)
    (native_ground_ward D hu i alpha epsilon gamma)
  change Valid J P KP at hP
  have hUK : Valid J (nativeSlice D hu U (gamma+delta)) K :=
    fun z hz => hU z (by dsimp [K, KU] at hz; omega)
  have hPK : Valid J P K := fun z hz => hP z (by dsimp [K] at hz; omega)
  have hEK : Valid J (defect D hu a b gamma delta r) K := by
    intro z hz
    change R J (nativeSlice D hu U (gamma+delta)-P) z = 0
    rw [R_sub, hUK z hz, hPK z hz, sub_zero]
  have action : currentDefectProduct D hu i alpha epsilon b gamma delta r d =
      Q J (nativeSlice D hu U (gamma+delta)) 1 d KU - Q J P 1 d KP := by
    unfold currentDefectProduct
    rw [Q_cutoff J (defect D hu a b gamma delta r) 1 d _ K
      (Classical.choose_spec (defect_current_valid_exists D hu i alpha epsilon b gamma delta r)) hEK]
    change Q J (nativeSlice D hu U (gamma+delta)-P) 1 d K = _
    rw [Q_sub, ← Q_cutoff J (nativeSlice D hu U (gamma+delta)) 1 d KU K hU hUK,
      ← Q_cutoff J P 1 d KP K hP hPK]
  rw [action]
  unfold defect
  rw [source_ground_commutator D i alpha epsilon b d r, nativeSlice_sub,
    show gamma+(delta+1) = (gamma+delta)+1 by omega,
    native_current_inverse, native_product_growth D hu i alpha epsilon b gamma delta r d]
  have lifts : nativeSlice D hu
      (LatticeAllStateReconstruction.mu D a0 (r+d) b) (gamma+delta+1) =
      nativeSlice D hu (LatticeAllStateReconstruction.mu D a0 (r+d) b)
        ((gamma+1)+delta) := by rw [show gamma+delta+1 = (gamma+1)+delta by omega]
  rw [lifts]
  change (_-_) - (_-_) = (_-_) - (_-_)
  abel

end D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport
