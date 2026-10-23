/- GID: D5/S3/VertexAlgebra/GroundRightCurrentTransport/FirstSourceCompatibility
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/GroundRightCurrentTransport/FirstSourceCompatibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Matching-sector compatibility for an arbitrary first source. -/

import D5.S3.VertexAlgebra.GroundRightCurrentTransport.NegativeWordExtension
import D5.S3.VertexAlgebra.ChargedResidue.SourceToQ

/-! The source expansion is consumed without changing the original product or
    target carrier.  Every summand is handled at its own initial signed lift;
    the current-word induction then returns it to the requested lift. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
open scoped BigOperators VertexOperator
namespace D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport
open LatticeGeneratingFieldLocality LatticeAllStateReconstruction
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockPhysicalRescaling LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeHalfFockLeftCurrentTransport

private theorem compatible_zero_left (D : LatticeData) (hu : IsUnit D.G.det)
    (b : Carrier D) (gamma delta : ℤ) :
    OriginalCompatible D hu 0 b gamma delta := by
  intro p q r x
  have left :
      Calculus.leftTerm (fun t => physicalSlice D hu
        (correctedField D hu (LatticeAllStateReconstruction.mu D 0 t b))
        (gamma + delta))
        gamma p q r x = (fun _ => 0) := by
    funext j
    simp [Calculus.leftTerm, physicalSlice_mode,
      LatticeAllStateReconstruction.mu]
  have first :
      Calculus.firstTerm (physicalSlice D hu (correctedField D hu 0) gamma)
        (physicalSlice D hu (correctedField D hu b) delta) p q r x = (fun _ => 0) := by
    funext j
    simp [Calculus.firstTerm, physicalSlice_mode]
  have second :
      Calculus.secondTerm (physicalSlice D hu (correctedField D hu 0) gamma)
        (physicalSlice D hu (correctedField D hu b) delta) p q r x = (fun _ => 0) := by
    funext j
    simp [Calculus.secondTerm, physicalSlice_mode]
  rw [left, first, second]
  simp [Function.HasFiniteSupport]

theorem compatible_add_left (D : LatticeData) (hu : IsUnit D.G.det)
    (a c b : Carrier D) (gamma delta : ℤ)
    (ha : OriginalCompatible D hu a b gamma delta)
    (hc : OriginalCompatible D hu c b gamma delta) :
    OriginalCompatible D hu (a + c) b gamma delta := by
  change Calculus.fullLaw
    (physicalSlice D hu (correctedField D hu (a+c)) gamma)
    (physicalSlice D hu (correctedField D hu b) delta)
    (fun t => physicalSlice D hu
      (correctedField D hu (LatticeAllStateReconstruction.mu D (a+c) t b))
      (gamma + delta)) gamma at ⊢
  change Calculus.fullLaw
    (physicalSlice D hu (correctedField D hu a) gamma)
    (physicalSlice D hu (correctedField D hu b) delta)
    (fun t => physicalSlice D hu
      (correctedField D hu (LatticeAllStateReconstruction.mu D a t b))
      (gamma + delta)) gamma at ha
  change Calculus.fullLaw
    (physicalSlice D hu (correctedField D hu c) gamma)
    (physicalSlice D hu (correctedField D hu b) delta)
    (fun t => physicalSlice D hu
      (correctedField D hu (LatticeAllStateReconstruction.mu D c t b))
      (gamma + delta)) gamma at hc
  intro p q r x
  have left (j : ℕ) :
      Calculus.leftTerm (fun t => physicalSlice D hu
        (correctedField D hu (LatticeAllStateReconstruction.mu D (a+c) t b))
        (gamma + delta))
        gamma p q r x j =
      Calculus.leftTerm (fun t => physicalSlice D hu
        (correctedField D hu (LatticeAllStateReconstruction.mu D a t b))
        (gamma + delta))
        gamma p q r x j +
      Calculus.leftTerm (fun t => physicalSlice D hu
        (correctedField D hu (LatticeAllStateReconstruction.mu D c t b))
        (gamma + delta))
        gamma p q r x j := by
    simp only [Calculus.leftTerm, physicalSlice_mode,
      LatticeAllStateReconstruction.mu, map_add, Pi.add_apply,
      LinearMap.add_apply, smul_add]
  have first (j : ℕ) :
      Calculus.firstTerm
        (physicalSlice D hu (correctedField D hu (a+c)) gamma)
        (physicalSlice D hu (correctedField D hu b) delta) p q r x j =
      Calculus.firstTerm (physicalSlice D hu (correctedField D hu a) gamma)
        (physicalSlice D hu (correctedField D hu b) delta) p q r x j +
      Calculus.firstTerm (physicalSlice D hu (correctedField D hu c) gamma)
        (physicalSlice D hu (correctedField D hu b) delta) p q r x j := by
    simp only [Calculus.firstTerm, physicalSlice_mode, map_add,
      Pi.add_apply, LinearMap.add_apply, add_smul, smul_add]
  have second (j : ℕ) :
      Calculus.secondTerm
        (physicalSlice D hu (correctedField D hu (a+c)) gamma)
        (physicalSlice D hu (correctedField D hu b) delta) p q r x j =
      Calculus.secondTerm (physicalSlice D hu (correctedField D hu a) gamma)
        (physicalSlice D hu (correctedField D hu b) delta) p q r x j +
      Calculus.secondTerm (physicalSlice D hu (correctedField D hu c) gamma)
        (physicalSlice D hu (correctedField D hu b) delta) p q r x j := by
    simp only [Calculus.secondTerm, physicalSlice_mode, map_add,
      Pi.add_apply, LinearMap.add_apply, add_smul, smul_add]
  have leftEq :
      Calculus.leftTerm (fun t => physicalSlice D hu
        (correctedField D hu (LatticeAllStateReconstruction.mu D (a+c) t b))
        (gamma + delta)) gamma p q r x =
      Calculus.leftTerm (fun t => physicalSlice D hu
        (correctedField D hu (LatticeAllStateReconstruction.mu D a t b))
        (gamma + delta)) gamma p q r x +
      Calculus.leftTerm (fun t => physicalSlice D hu
        (correctedField D hu (LatticeAllStateReconstruction.mu D c t b))
        (gamma + delta)) gamma p q r x := funext left
  have firstEq :
      Calculus.firstTerm (physicalSlice D hu (correctedField D hu (a+c)) gamma)
        (physicalSlice D hu (correctedField D hu b) delta) p q r x =
      Calculus.firstTerm (physicalSlice D hu (correctedField D hu a) gamma)
        (physicalSlice D hu (correctedField D hu b) delta) p q r x +
      Calculus.firstTerm (physicalSlice D hu (correctedField D hu c) gamma)
        (physicalSlice D hu (correctedField D hu b) delta) p q r x := funext first
  have secondEq :
      Calculus.secondTerm (physicalSlice D hu (correctedField D hu (a+c)) gamma)
        (physicalSlice D hu (correctedField D hu b) delta) p q r x =
      Calculus.secondTerm (physicalSlice D hu (correctedField D hu a) gamma)
        (physicalSlice D hu (correctedField D hu b) delta) p q r x +
      Calculus.secondTerm (physicalSlice D hu (correctedField D hu c) gamma)
        (physicalSlice D hu (correctedField D hu b) delta) p q r x := funext second
  rw [leftEq, firstEq, secondEq]
  simp only [Pi.add_apply]
  obtain ⟨hal, haf, has, hae⟩ := ha p q r x
  obtain ⟨hcl, hcf, hcs, hce⟩ := hc p q r x
  refine ⟨hal.add hcl, haf.add hcf, has.add hcs, ?_⟩
  rw [finsum_add_distrib hal hcl, finsum_add_distrib haf hcf,
    finsum_add_distrib has hcs, hae, hce]
  abel

private def compatibleLeft (D : LatticeData) (hu : IsUnit D.G.det)
    (b : Carrier D) (gamma delta : ℤ) : Submodule ℂ (Carrier D) where
  carrier := {a | OriginalCompatible D hu a b gamma delta}
  zero_mem' := compatible_zero_left D hu b gamma delta
  add_mem' := fun ha hc => compatible_add_left D hu _ _ b gamma delta ha hc
  smul_mem' := fun c _ ha => compatible_smul_left D hu _ b gamma delta c ha

local macro "parity_square" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.SectorPropagation 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.parity_square))

private theorem wordParity_sign (D : LatticeData) (word : List (Index D))
    (epsilon : Bool) :
    sectorSign (wordParity word epsilon) =
      sectorSign epsilon * (-1 : ℂ) ^ (word.length : ℤ) := by
  induction word generalizing epsilon with
  | nil => simp [wordParity]
  | cons j w ih =>
      calc
        sectorSign (wordParity (j :: w) epsilon) =
            sectorSign (wordParity w (!epsilon)) := rfl
        _ = sectorSign (!epsilon) * (-1 : ℂ) ^ (w.length : ℤ) := ih (!epsilon)
        _ = sectorSign epsilon * (-1 : ℂ) *
            (-1 : ℂ) ^ (w.length : ℤ) := by
              rw [sectorSign_not]
              ring
        _ = sectorSign epsilon *
            (-1 : ℂ) ^ ((w.length : ℤ) + 1) := by
              rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
              norm_num
        _ = sectorSign epsilon * (-1 : ℂ) ^ ((j :: w).length : ℤ) := by
              simp only [List.length_cons, Nat.cast_add, Nat.cast_one]

/-! The requested matching-sector first-source law.  The only base input is
    the existing charged ground-pair supplier; all arbitrary source states are
    reconstructed from their actual finite current-word expansion. -/
theorem sectorProject_first_source_compatibility
    (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Carrier D) (epsilon : Bool) (s t : ℤ)
    (hs : sectorSign epsilon = (-1 : ℂ) ^ s) :
    OriginalCompatible D hu (sectorProject D epsilon a) b s t := by
  classical
  rw [theta_source_expansion]
  apply (compatibleLeft D hu b s t).sum_mem
  intro alpha hα
  apply (compatibleLeft D hu b s t).sum_mem
  intro e he
  apply (compatibleLeft D hu b s t).smul_mem
  let word := LatticeAllStateField.occurrences D e
  let n : ℤ := (word.length : ℤ)
  have hword : sectorSign (wordParity word epsilon) = (-1 : ℂ) ^ (s - n) := by
    have hprod :
        (-1 : ℂ) ^ (s - n) * (-1 : ℂ) ^ n = (-1 : ℂ) ^ s := by
      rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
      congr 1
      dsimp [n]
      ring
    calc
      sectorSign (wordParity word epsilon) =
          sectorSign epsilon * (-1 : ℂ) ^ n := wordParity_sign D word epsilon
      _ = (-1 : ℂ) ^ s * (-1 : ℂ) ^ n := by rw [hs]
      _ = ((-1 : ℂ) ^ (s - n) * (-1 : ℂ) ^ n) * (-1 : ℂ) ^ n := by
        rw [hprod]
      _ = (-1 : ℂ) ^ (s - n) := by
        rw [mul_assoc, parity_square, mul_one]
  have law := projectedGround_left_current_word D hu
    (LatticeHalfFockChargedResidue.charged_sector_ground_pair D hu)
    word alpha (wordParity word epsilon) (s - n) hword b t
  change OriginalCompatible D hu
    (rightCurrentWord D word (projectedGround D alpha (wordParity word epsilon))) b s t
  simpa only [word, n, sub_add_cancel] using law

end D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport
