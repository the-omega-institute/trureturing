/- GID: D5/S3/VertexAlgebra/GroundRightCurrentTransport/Propagation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/GroundRightCurrentTransport/Propagation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original-source all-signed compatibility propagated by native negative currents. -/
import D5.S3.VertexAlgebra.GroundRightCurrentTransport.NativeDefect
import D5.S3.VertexAlgebra.GroundRightCurrentTransport.Compatibility

/-! Original-source coefficient compatibility and its negative-current consumer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
open scoped BigOperators VertexOperator
open D5.S3.VertexAlgebra
namespace D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockCorrectedField LatticeHalfFockPhysicalRescaling
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents Calculus

local macro "nativeSlice" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.NativeDefect 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.nativeSlice))
local macro "nativeSlice_mode" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.NativeDefect 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.nativeSlice_mode))
local macro "nativeCutoff" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.NativeDefect 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.nativeCutoff))
local macro "native_valid" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.NativeDefect 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.native_valid))
local macro "nativeCurrent" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.NativeDefect 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.nativeCurrent))
local macro "ext_modes" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.ext_modes))
local macro "high" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.high))
local macro "upper" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.upper))
local macro "inverse_of_full" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Compatibility 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.inverse_of_full))
local macro "Q_zero" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Interchange 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.Q_zero))

/-- The full three-supported original-source coefficient identity. All signed
    indices and both physical lifts are universally quantified. -/
def OriginalCompatible (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Carrier D) (gamma delta : ℤ) : Prop :=
  fullLaw (physicalSlice D hu (correctedField D hu a) gamma)
    (physicalSlice D hu (correctedField D hu b) delta)
    (fun r => physicalSlice D hu (correctedField D hu (LatticeAllStateReconstruction.mu D a r b))
      (gamma+delta)) gamma

private theorem source_tail (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Carrier D) (s : ℤ) : ∃ K : ℕ, ∀ r : ℤ, (K : ℤ) ≤ r →
      nativeSlice D hu (LatticeAllStateReconstruction.mu D a r b) s = 0 := by
  refine ⟨upper (LatticeAllStateField.Y D a) b, ?_⟩
  intro r hr
  have hz := high (LatticeAllStateField.Y D a) b r hr
  change LatticeAllStateReconstruction.mu D a r b = 0 at hz
  rw [hz]
  apply ext_modes
  intro n
  apply LinearMap.ext
  intro x
  simp only [nativeSlice_mode, slice, map_zero, Pi.zero_apply]

theorem compatible_defect (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Carrier D) (gamma delta : ℤ)
    (law : OriginalCompatible D hu a b gamma delta) (r : ℤ) :
    defect D hu a b gamma delta r = 0 := by
  obtain ⟨KU, tail⟩ := source_tail D hu a b (gamma+delta)
  exact sub_eq_zero.mpr (inverse_of_full (nativeSlice D hu a gamma)
    (nativeSlice D hu b delta)
    (fun t => nativeSlice D hu (LatticeAllStateReconstruction.mu D a t b) (gamma+delta))
    gamma KU (nativeCutoff D hu a b gamma delta) tail
    (native_valid D hu a b gamma delta) law r)

theorem defect_compatible (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Carrier D) (gamma delta : ℤ)
    (zero : ∀ r : ℤ, defect D hu a b gamma delta r = 0) :
    OriginalCompatible D hu a b gamma delta := by
  obtain ⟨KU, tail⟩ := source_tail D hu a b (gamma+delta)
  exact recover_full (nativeSlice D hu a gamma) (nativeSlice D hu b delta)
    (fun t => nativeSlice D hu (LatticeAllStateReconstruction.mu D a t b) (gamma+delta))
    gamma KU (nativeCutoff D hu a b gamma delta) tail
    (Classical.choose_spec (native_valid_exists D hu a b gamma delta))
    (native_valid D hu a b gamma delta) (fun r => sub_eq_zero.mp (zero r))

theorem compatible_smul_left (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Carrier D) (gamma delta : ℤ) (c : ℂ)
    (law : OriginalCompatible D hu a b gamma delta) :
    OriginalCompatible D hu (c • a) b gamma delta := by
  change fullLaw (nativeSlice D hu a gamma) (nativeSlice D hu b delta)
    (fun t => nativeSlice D hu (LatticeAllStateReconstruction.mu D a t b)
      (gamma+delta)) gamma at law
  change fullLaw (nativeSlice D hu (c • a) gamma) (nativeSlice D hu b delta)
    (fun t => nativeSlice D hu (LatticeAllStateReconstruction.mu D (c • a) t b)
      (gamma+delta)) gamma
  intro p q r x
  have left (j : ℕ) :
      leftTerm (fun t => nativeSlice D hu (LatticeAllStateReconstruction.mu D (c • a) t b)
        (gamma+delta)) gamma p q r x j =
      c • leftTerm (fun t => nativeSlice D hu (LatticeAllStateReconstruction.mu D a t b)
        (gamma+delta)) gamma p q r x j := by
    simp only [leftTerm, nativeSlice_mode, slice, LatticeAllStateReconstruction.mu,
      map_smul, Pi.smul_apply, LinearMap.smul_apply]
    rw [smul_comm]
  have first (j : ℕ) :
      firstTerm (nativeSlice D hu (c • a) gamma) (nativeSlice D hu b delta) p q r x j =
      c • firstTerm (nativeSlice D hu a gamma) (nativeSlice D hu b delta) p q r x j := by
    simp only [firstTerm, nativeSlice_mode, slice, map_smul, Pi.smul_apply, LinearMap.smul_apply]
    rw [smul_comm]
  have second (j : ℕ) :
      secondTerm (nativeSlice D hu (c • a) gamma) (nativeSlice D hu b delta) p q r x j =
      c • secondTerm (nativeSlice D hu a gamma) (nativeSlice D hu b delta) p q r x j := by
    simp only [secondTerm, nativeSlice_mode, slice, map_smul, Pi.smul_apply, LinearMap.smul_apply]
    module
  have leftEq := funext left
  have firstEq := funext first
  have secondEq := funext second
  rw [leftEq, firstEq, secondEq]
  obtain ⟨hl, hf, hs, h⟩ := law p q r x
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Pi.smul_def'] using hl.smul_right (fun _ : ℕ => c)
  · simpa only [Pi.smul_def'] using hf.smul_right (fun _ : ℕ => c)
  · simpa only [Pi.smul_def'] using hs.smul_right (fun _ : ℕ => c)
  rw [← smul_finsum, ← smul_finsum, ← smul_finsum, h, smul_sub]

theorem ground_zero_mode (D : LatticeData) (i : Fin D.rank)
    (alpha : Charge D) (epsilon : Bool) :
    neutralMode D i 0 (projectedGround D alpha epsilon) =
      (bilinear D (unitCharge D i) alpha : ℂ) • projectedGround D alpha (!epsilon) := by
  have sector (beta : Charge D) :
      neutralMode D i 0 (Finsupp.single beta (1 : Oscillator D)) =
        (bilinear D (unitCharge D i) beta : ℂ) •
          Finsupp.single beta (1 : Oscillator D) := by
    simp [neutralMode_single, neutralPolynomialMode]
  simp only [projectedGround, map_smul, map_add, sector,
    bilinear_neg_right, Int.cast_neg]
  cases epsilon <;> simp only [Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ite_false, ite_true] <;> module

/- proof_shape: projectedGround_negative_current_step: content;
   projectedGround_right_word: content
   admission_basis: escape-witness
   escape_witness: Two-sided finite inversion recovers all signed coefficient
   laws from zero native defects, and actual source h0 swaps the projected
   ground signs. This consumes unconditional defect transport to propagate
   along unbounded negative right-source words. The exact ground-pair base
   is an explicit hypothesis, not an established compatibility law.
   Literature status: classical twisted-lattice calculus; no novelty claim. -/
/-- Negative-current propagation of the full original-source law. The premises
    are the smaller right source at both projected ground signs and every lift;
    no transport or target module law is assumed. -/
theorem projectedGround_negative_current_step (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (m : ℕ) (hm : 0 < m) (alpha : Charge D) (b : Carrier D)
    (smaller : ∀ epsilon : Bool, ∀ gamma delta : ℤ,
      OriginalCompatible D hu (projectedGround D alpha epsilon) b gamma delta)
    (epsilon : Bool) (gamma delta : ℤ) :
    OriginalCompatible D hu (projectedGround D alpha epsilon)
      (neutralMode D i (-(m : ℤ)) b) gamma delta := by
  apply defect_compatible
  intro r
  have zero := compatible_defect D hu (projectedGround D alpha epsilon) b gamma (delta-1)
    (smaller epsilon gamma (delta-1)) r
  have zero0 := compatible_defect D hu
    (neutralMode D i 0 (projectedGround D alpha epsilon)) b (gamma+1) (delta-1)
    (by
      rw [ground_zero_mode]
      exact compatible_smul_left D hu _ b (gamma+1) (delta-1) _
        (smaller (!epsilon) (gamma+1) (delta-1))) (r-(m:ℤ))
  have transport := projectedGround_defect_transport D hu i alpha epsilon b
    gamma (delta-1) r (-(m:ℤ))
  rw [show delta-1+1 = delta by omega] at transport
  rw [transport]
  unfold currentDefectProduct
  simp only [zero, Q_zero, show r+ -(m:ℤ) = r-(m:ℤ) by omega, zero0, sub_zero]

/-- A word of actual negative source-current insertions, without a target vacuum. -/
def rightCurrentWord (D : LatticeData) : List (Index D) → Carrier D → Carrier D
  | [], b => b
  | j :: w, b => neutralMode D j.1 (-((j.2+1 : ℕ) : ℤ)) (rightCurrentWord D w b)

/-- Full signed compatibility along any negative right-source word. This assumes
    only the exact all-charge, both-sign ground-pair base displayed below. -/
theorem projectedGround_right_word (D : LatticeData) (hu : IsUnit D.G.det)
    (groundPair : ∀ alpha beta : Charge D, ∀ epsilon eta : Bool, ∀ gamma delta : ℤ,
      OriginalCompatible D hu (projectedGround D alpha epsilon)
        (projectedGround D beta eta) gamma delta)
    (word : List (Index D)) (alpha beta : Charge D) (epsilon eta : Bool)
    (gamma delta : ℤ) :
    OriginalCompatible D hu (projectedGround D alpha epsilon)
      (rightCurrentWord D word (projectedGround D beta eta)) gamma delta := by
  induction word generalizing epsilon gamma delta with
  | nil => exact groundPair alpha beta epsilon eta gamma delta
  | cons j w ih =>
    exact projectedGround_negative_current_step D hu j.1 (j.2+1) (by omega) alpha
      (rightCurrentWord D w (projectedGround D beta eta)) ih epsilon gamma delta

end D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport
