/- GID: D5/S3/VertexAlgebra/GroundRightCurrentTransport/SectorPropagation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/GroundRightCurrentTransport/SectorPropagation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete arbitrary-second-source GroundFirst from compatible ground pairs. -/
import D5.S3.VertexAlgebra.GroundRightCurrentTransport.SourceGeneration
import D5.S3.VertexAlgebra.LatticeHalfFockCorrectedMonodromy

/-! The only compatibility premise is the explicitly matching ground-pair family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
open scoped BigOperators VertexOperator
namespace D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeInvolution
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockPhysicalRescaling Calculus

local macro "Q_zero" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Interchange 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.Q_zero))

private theorem parity_step (s : ℤ) : (-1 : ℂ) ^ (s+1) = -((-1 : ℂ) ^ s) := by
  rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  simp

private theorem parity_back (s : ℤ) : (-1 : ℂ) ^ (s-1) = -((-1 : ℂ) ^ s) := by
  have h := parity_step (s-1)
  rw [show s-1+1 = s by omega] at h
  rw [h, neg_neg]

private theorem parity_square (s : ℤ) : (-1 : ℂ) ^ s * (-1 : ℂ) ^ s = 1 := by
  rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← two_mul]
  exact (even_two_mul s).neg_one_zpow

private theorem parity_slice (s n : ℤ) : (-1 : ℂ) ^ (-2*n-s-2) = (-1 : ℂ) ^ s := by
  rw [show -2*n-s-2 = s+2*(-n-s-1) by ring,
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    (even_two_mul (-n-s-1)).neg_one_zpow, mul_one]

/-- Exactly the parity-compatible charged ground pairs, for every signed lift.
This premise is supplied by the ground-pair residue problem. -/
def SectorGroundPair (D : LatticeData) (hu : IsUnit D.G.det) : Prop :=
  ∀ alpha beta : Charge D, ∀ epsilon eta : Bool, ∀ gamma delta : ℤ,
    sectorSign epsilon = (-1 : ℂ) ^ gamma →
    sectorSign eta = (-1 : ℂ) ^ delta →
    OriginalCompatible D hu (projectedGround D alpha epsilon)
      (projectedGround D beta eta) gamma delta

private theorem compatible_zero_right (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Carrier D) (gamma delta : ℤ) : OriginalCompatible D hu a 0 gamma delta := by
  intro p q r x
  have left :
      leftTerm (fun t => physicalSlice D hu
        (correctedField D hu (LatticeAllStateReconstruction.mu D a t 0))
          (gamma + delta)) gamma p q r x = (fun _ => 0) := by
    funext j
    simp [leftTerm, physicalSlice_mode, LatticeAllStateReconstruction.mu]
  have first :
      firstTerm (physicalSlice D hu (correctedField D hu a) gamma)
        (physicalSlice D hu (correctedField D hu 0) delta) p q r x = (fun _ => 0) := by
    funext j
    simp [firstTerm, physicalSlice_mode]
  have second :
      secondTerm (physicalSlice D hu (correctedField D hu a) gamma)
        (physicalSlice D hu (correctedField D hu 0) delta) p q r x = (fun _ => 0) := by
    funext j
    simp [secondTerm, physicalSlice_mode]
  rw [left, first, second]
  simp [Function.HasFiniteSupport]

private theorem compatible_add_right (D : LatticeData) (hu : IsUnit D.G.det)
    (a b c : Carrier D) (gamma delta : ℤ)
    (hb : OriginalCompatible D hu a b gamma delta)
    (hc : OriginalCompatible D hu a c gamma delta) :
    OriginalCompatible D hu a (b+c) gamma delta := by
  intro p q r x
  have left (j : ℕ) :
      leftTerm (fun t => physicalSlice D hu
        (correctedField D hu (LatticeAllStateReconstruction.mu D a t (b+c)))
          (gamma + delta)) gamma p q r x j =
      leftTerm (fun t => physicalSlice D hu
        (correctedField D hu (LatticeAllStateReconstruction.mu D a t b))
          (gamma + delta)) gamma p q r x j +
      leftTerm (fun t => physicalSlice D hu
        (correctedField D hu (LatticeAllStateReconstruction.mu D a t c))
          (gamma + delta)) gamma p q r x j := by
    simp only [leftTerm, physicalSlice_mode, LatticeAllStateReconstruction.mu,
      map_add, Pi.add_apply, LinearMap.add_apply, smul_add]
  have first (j : ℕ) :
      firstTerm (physicalSlice D hu (correctedField D hu a) gamma)
        (physicalSlice D hu (correctedField D hu (b+c)) delta) p q r x j =
      firstTerm (physicalSlice D hu (correctedField D hu a) gamma)
        (physicalSlice D hu (correctedField D hu b) delta) p q r x j +
      firstTerm (physicalSlice D hu (correctedField D hu a) gamma)
        (physicalSlice D hu (correctedField D hu c) delta) p q r x j := by
    simp only [firstTerm, physicalSlice_mode, map_add, Pi.add_apply,
      LinearMap.add_apply, smul_add]
  have second (j : ℕ) :
      secondTerm (physicalSlice D hu (correctedField D hu a) gamma)
        (physicalSlice D hu (correctedField D hu (b+c)) delta) p q r x j =
      secondTerm (physicalSlice D hu (correctedField D hu a) gamma)
        (physicalSlice D hu (correctedField D hu b) delta) p q r x j +
      secondTerm (physicalSlice D hu (correctedField D hu a) gamma)
        (physicalSlice D hu (correctedField D hu c) delta) p q r x j := by
    simp only [secondTerm, physicalSlice_mode, map_add, Pi.add_apply,
      LinearMap.add_apply, smul_add]
  rw [funext left, funext first, funext second]
  obtain ⟨bl, bf, bs, be⟩ := hb p q r x
  obtain ⟨cl, cf, cs, ce⟩ := hc p q r x
  refine ⟨bl.add cl, bf.add cf, bs.add cs, ?_⟩
  rw [finsum_add_distrib bl cl, finsum_add_distrib bf cf, finsum_add_distrib bs cs,
    be, ce]
  abel

private theorem compatible_smul_right (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Carrier D) (gamma delta : ℤ) (c : ℂ)
    (hb : OriginalCompatible D hu a b gamma delta) :
    OriginalCompatible D hu a (c • b) gamma delta := by
  intro p q r x
  have left (j : ℕ) :
      leftTerm (fun t => physicalSlice D hu
        (correctedField D hu (LatticeAllStateReconstruction.mu D a t (c • b)))
          (gamma + delta)) gamma p q r x j = c •
      leftTerm (fun t => physicalSlice D hu
        (correctedField D hu (LatticeAllStateReconstruction.mu D a t b))
          (gamma + delta)) gamma p q r x j := by
    simp only [leftTerm, physicalSlice_mode, LatticeAllStateReconstruction.mu,
      map_smul, Pi.smul_apply, LinearMap.smul_apply]
    rw [smul_comm]
  have first (j : ℕ) :
      firstTerm (physicalSlice D hu (correctedField D hu a) gamma)
        (physicalSlice D hu (correctedField D hu (c • b)) delta) p q r x j = c •
      firstTerm (physicalSlice D hu (correctedField D hu a) gamma)
        (physicalSlice D hu (correctedField D hu b) delta) p q r x j := by
    simp only [firstTerm, physicalSlice_mode, map_smul, Pi.smul_apply, LinearMap.smul_apply]
    rw [smul_comm]
  have second (j : ℕ) :
      secondTerm (physicalSlice D hu (correctedField D hu a) gamma)
        (physicalSlice D hu (correctedField D hu (c • b)) delta) p q r x j = c •
      secondTerm (physicalSlice D hu (correctedField D hu a) gamma)
        (physicalSlice D hu (correctedField D hu b) delta) p q r x j := by
    simp only [secondTerm, physicalSlice_mode, map_smul, Pi.smul_apply, LinearMap.smul_apply]
    module
  rw [funext left, funext first, funext second]
  obtain ⟨hl, hf, hs, h⟩ := hb p q r x
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Pi.smul_def'] using hl.smul_right (fun _ : ℕ => c)
  · simpa only [Pi.smul_def'] using hf.smul_right (fun _ : ℕ => c)
  · simpa only [Pi.smul_def'] using hs.smul_right (fun _ : ℕ => c)
  rw [← smul_finsum, ← smul_finsum, ← smul_finsum, h, smul_sub]

private def compatibleRight (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Carrier D) (gamma delta : ℤ) : Submodule ℂ (Carrier D) where
  carrier := {b | OriginalCompatible D hu a b gamma delta}
  zero_mem' := compatible_zero_right D hu a gamma delta
  add_mem' := fun hb hc => compatible_add_right D hu a _ _ gamma delta hb hc
  smul_mem' := fun c _ hb => compatible_smul_right D hu a _ gamma delta c hb

/- proof_shape: sector_ground_right_word: content;
   physicalSlice_sectorProject: content; mu_sectorProject: content;
   projectedGround_arbitrary_second: content
   admission_basis: escape-witness
   escape_witness: The restricted induction transports opposite first signs
   and signed lifts gamma+1, delta-1 without an all-lifts base. Actual source
   bilinearity preserves all three finite supports under independent finite
   expansions. Corrected-field and original-mu theta covariance remove the
   second projection at its physical lift and at the sum lift. Together these
   give the full arbitrary-second-source law from exactly matching ground pairs.
   Literature status: classical twisted-lattice calculus; no novelty claim. -/
/-- Restricted word invariant: both projected signs and both integer lifts
stay linked. In the correction term h0 uses gamma+1 and delta-1. -/
theorem sector_ground_right_word (D : LatticeData) (hu : IsUnit D.G.det)
    (groundPair : SectorGroundPair D hu) (word : List (Index D))
    (alpha beta : Charge D) (epsilon eta : Bool) (gamma delta : ℤ)
    (hgamma : sectorSign epsilon = (-1 : ℂ) ^ gamma)
    (hdelta : sectorSign (wordParity word eta) = (-1 : ℂ) ^ delta) :
    OriginalCompatible D hu (projectedGround D alpha epsilon)
      (rightCurrentWord D word (projectedGround D beta eta)) gamma delta := by
  induction word generalizing epsilon gamma delta with
  | nil => exact groundPair alpha beta epsilon eta gamma delta hgamma hdelta
  | cons j w ih =>
    have tailParity : sectorSign (wordParity w eta) = (-1 : ℂ) ^ (delta-1) := by
      have flip : wordParity (j :: w) eta = !(wordParity w eta) := by
        simpa only [wordParity] using wordParity_not D w eta
      rw [flip, sectorSign_not] at hdelta
      rw [parity_back, ← hdelta, neg_neg]
    have flipped : sectorSign (!epsilon) = (-1 : ℂ) ^ (gamma+1) := by
      rw [sectorSign_not, hgamma, parity_step]
    apply defect_compatible
    intro r
    have zero := compatible_defect D hu (projectedGround D alpha epsilon)
      (rightCurrentWord D w (projectedGround D beta eta)) gamma (delta-1)
      (ih epsilon gamma (delta-1) hgamma tailParity) r
    have zero0 := compatible_defect D hu
      (neutralMode D j.1 0 (projectedGround D alpha epsilon))
      (rightCurrentWord D w (projectedGround D beta eta)) (gamma+1) (delta-1)
      (by
        rw [ground_zero_mode]
        exact compatible_smul_left D hu _ _ (gamma+1) (delta-1) _
          (ih (!epsilon) (gamma+1) (delta-1) flipped tailParity))
      (r-((j.2+1 : ℕ) : ℤ))
    have transport := projectedGround_defect_transport D hu j.1 alpha epsilon
      (rightCurrentWord D w (projectedGround D beta eta)) gamma (delta-1) r
      (-((j.2+1 : ℕ) : ℤ))
    rw [show delta-1+1 = delta by omega] at transport
    change defect D hu _ (neutralMode D j.1 _ _) gamma delta r = 0
    rw [transport]
    unfold currentDefectProduct
    simp only [zero, Q_zero, show r + -((j.2+1 : ℕ) : ℤ) =
      r-((j.2+1 : ℕ) : ℤ) by omega, zero0, sub_zero]

private theorem wordParity_twice (D : LatticeData) (w : List (Index D)) (epsilon : Bool) :
    wordParity w (wordParity w epsilon) = epsilon := by
  induction w generalizing epsilon with
  | nil => rfl
  | cons j w ih =>
    simp only [wordParity, wordParity_not, Bool.not_not]
    exact ih epsilon

/-- Actual coefficient projection on the physical lift. No restriction is
placed on the inhomogeneous actual target vector. -/
theorem physicalSlice_sectorProject (D : LatticeData) (hu : IsUnit D.G.det)
    (b : Carrier D) (eta : Bool) (delta : ℤ)
    (hdelta : sectorSign eta = (-1 : ℂ) ^ delta) :
    physicalSlice D hu (correctedField D hu (sectorProject D eta b)) delta =
      physicalSlice D hu (correctedField D hu b) delta := by
  apply HVertexOperator.coeff_inj
  funext e
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff,
    physicalSlice_mode, physicalSlice_mode]
  change (correctedField D hu ((2 : ℂ)⁻¹ • (b + sectorSign eta • theta D b))).coeff _ = _
  simp only [map_smul, map_add, Pi.smul_apply, Pi.add_apply,
    correctedField_theta, hdelta, parity_slice, smul_smul]
  rw [parity_square]
  module

/-- Theta covariance of the original ordinary source iterate transports the
selected right projection to the sum lift, including its signed carry. -/
theorem mu_sectorProject (D : LatticeData) (a b : Carrier D) (r gamma delta : ℤ)
    (epsilon eta zeta : Bool)
    (ha : theta D a = sectorSign epsilon • a)
    (hgamma : sectorSign epsilon = (-1 : ℂ) ^ gamma)
    (hdelta : sectorSign eta = (-1 : ℂ) ^ delta)
    (hsum : sectorSign zeta = (-1 : ℂ) ^ (gamma + delta)) :
    sectorProject D zeta (LatticeAllStateReconstruction.mu D a r b) =
      LatticeAllStateReconstruction.mu D a r (sectorProject D eta b) := by
  have cov : theta D (LatticeAllStateReconstruction.mu D a r b) =
      sectorSign epsilon • LatticeAllStateReconstruction.mu D a r (theta D b) := by
    rw [LatticeAllStateReconstruction.mu, stateField_theta, ha]
    simp only [LatticeAllStateReconstruction.mu, map_smul, Pi.smul_apply, LinearMap.smul_apply]
  change (2 : ℂ)⁻¹ • (LatticeAllStateReconstruction.mu D a r b +
    sectorSign zeta • theta D (LatticeAllStateReconstruction.mu D a r b)) = _
  rw [cov]
  change _ = ((LatticeAllStateField.Y D a)[[r]])
    ((2 : ℂ)⁻¹ • (b + sectorSign eta • theta D b))
  simp only [map_smul, map_add, LatticeAllStateReconstruction.mu, smul_smul]
  have sign : sectorSign zeta * sectorSign epsilon = sectorSign eta := by
    rw [hsum, hgamma, hdelta, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    calc
      _ = ((-1 : ℂ) ^ gamma * (-1 : ℂ) ^ gamma) * (-1 : ℂ) ^ delta := by ring
      _ = _ := by rw [parity_square, one_mul]
  rw [sign]

private def liftSector (delta : ℤ) : Bool := if Even delta then false else true

private theorem liftSector_sign (delta : ℤ) :
    sectorSign (liftSector delta) = (-1 : ℂ) ^ delta := by
  rw [neg_one_zpow_eq_ite]
  by_cases h : Even delta <;> simp [liftSector, h, sectorSign]

/-- Complete GroundFirst extension. The ground-pair residue identity remains
exactly SectorGroundPair; no all-lifts or all-source law is assumed. -/
theorem projectedGround_arbitrary_second (D : LatticeData) (hu : IsUnit D.G.det)
    (groundPair : SectorGroundPair D hu) (alpha : Charge D) (epsilon : Bool)
    (gamma delta : ℤ) (b : Carrier D)
    (hgamma : sectorSign epsilon = (-1 : ℂ) ^ gamma) :
    OriginalCompatible D hu (projectedGround D alpha epsilon) b gamma delta := by
  classical
  let eta := liftSector delta
  have hdelta : sectorSign eta = (-1 : ℂ) ^ delta := liftSector_sign delta
  let a := projectedGround D alpha epsilon
  have projected : OriginalCompatible D hu a (sectorProject D eta b) gamma delta := by
    rw [theta_source_expansion]
    apply (compatibleRight D hu a gamma delta).sum_mem
    intro beta hbeta
    apply (compatibleRight D hu a gamma delta).sum_mem
    intro e he
    apply (compatibleRight D hu a gamma delta).smul_mem
    exact sector_ground_right_word D hu groundPair (LatticeAllStateField.occurrences D e)
      alpha beta epsilon (wordParity (LatticeAllStateField.occurrences D e) eta)
      gamma delta hgamma (by rw [wordParity_twice]; exact hdelta)
  have fields := physicalSlice_sectorProject D hu b eta delta hdelta
  have iterates (r : ℤ) :
      physicalSlice D hu (correctedField D hu
        (LatticeAllStateReconstruction.mu D a r (sectorProject D eta b))) (gamma + delta) =
      physicalSlice D hu (correctedField D hu
        (LatticeAllStateReconstruction.mu D a r b)) (gamma + delta) := by
    rw [← mu_sectorProject D a b r gamma delta epsilon eta (liftSector (gamma + delta))
      (projectedGround_eigen D alpha epsilon) hgamma hdelta (liftSector_sign (gamma + delta))]
    exact physicalSlice_sectorProject D hu _ _ _ (liftSector_sign (gamma + delta))
  change fullLaw _ _ _ _ at projected ⊢
  simpa only [fields, iterates] using projected

end D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport
