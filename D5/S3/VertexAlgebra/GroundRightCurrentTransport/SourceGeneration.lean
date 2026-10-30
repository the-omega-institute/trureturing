/- GID: D5/S3/VertexAlgebra/GroundRightCurrentTransport/SourceGeneration
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/GroundRightCurrentTransport/SourceGeneration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite theta eigensource expansion by actual neutral negative currents. -/
import D5.S3.VertexAlgebra.GroundRightCurrentTransport.Propagation
import D5.S3.VertexAlgebra.LatticeInvolution

/-! Oscillator generation uses all charged grounds, without a form positivity hypothesis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
open scoped BigOperators VertexOperator
namespace D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeInvolution MvPolynomial

/-- The two source reflection eigenvalues. -/
def sectorSign (epsilon : Bool) : ℂ := if epsilon then -1 else 1

@[simp] theorem sectorSign_not (epsilon : Bool) :
    sectorSign (!epsilon) = -sectorSign epsilon := by cases epsilon <;> norm_num [sectorSign]

@[simp] theorem sectorSign_square (epsilon : Bool) :
    sectorSign epsilon * sectorSign epsilon = 1 := by cases epsilon <;> norm_num [sectorSign]

/-- Projection on the original charge-polynomial carrier. -/
def sectorProject (D : LatticeData) (epsilon : Bool) : Module.End ℂ (Carrier D) :=
  (2 : ℂ)⁻¹ • (LinearMap.id + sectorSign epsilon • thetaLinear D)

private theorem sectorProject_apply (D : LatticeData) (epsilon : Bool) (b : Carrier D) :
    sectorProject D epsilon b = (2 : ℂ)⁻¹ • (b + sectorSign epsilon • theta D b) := rfl

/-- A current reverses the theta sector of its source. -/
def wordParity {D : LatticeData} : List (Index D) → Bool → Bool
  | [], epsilon => epsilon
  | _ :: w, epsilon => wordParity w (!epsilon)

@[simp] theorem wordParity_not (D : LatticeData) (w : List (Index D))
    (epsilon : Bool) : wordParity w (!epsilon) = !(wordParity w epsilon) := by
  induction w generalizing epsilon with
  | nil => rfl
  | cons j w ih => simpa only [wordParity, Bool.not_not] using ih (!epsilon)

private theorem project_ground (D : LatticeData) (alpha : Charge D) (epsilon : Bool) :
    sectorProject D epsilon (Finsupp.single alpha (1 : Oscillator D)) =
      projectedGround D alpha epsilon := by
  simp only [sectorProject_apply, show theta D (Finsupp.single alpha (1 : Oscillator D)) =
    Finsupp.single (-alpha) (1 : Oscillator D) by
      change thetaLinear D _ = _
      simp only [theta_single, map_one] ]
  rfl

private theorem project_current (D : LatticeData) (epsilon : Bool)
    (i : Fin D.rank) (m : ℤ) (b : Carrier D) :
    sectorProject D epsilon (neutralMode D i m b) =
      neutralMode D i m (sectorProject D (!epsilon) b) := by
  simp only [sectorProject_apply, theta_neutralMode, sectorSign_not,
    map_smul, map_add, smul_neg, neg_smul, map_neg]

private theorem word_single (D : LatticeData) (alpha : Charge D)
    (w : List (Index D)) :
    rightCurrentWord D w (Finsupp.single alpha (1 : Oscillator D)) =
      Finsupp.single alpha ((w.map (fun j => (X j : Oscillator D))).prod) := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    rw [rightCurrentWord, ih]
    simp only [neutralMode, Finsupp.lsum_single, LinearMap.comp_apply,
      Finsupp.lsingle_apply, neutralPolynomialMode,
      show -((j.2+1 : ℕ) : ℤ) < 0 by omega, ↓reduceIte,
      LinearMap.mulLeft_apply, List.map_cons, List.prod_cons]
    rw [show (- -((j.2+1 : ℕ) : ℤ)-1).toNat = j.2 by omega]

private theorem project_word (D : LatticeData) (alpha : Charge D)
    (w : List (Index D)) (epsilon : Bool) :
    sectorProject D epsilon
        (rightCurrentWord D w (Finsupp.single alpha (1 : Oscillator D))) =
      rightCurrentWord D w (projectedGround D alpha (wordParity w epsilon)) := by
  induction w generalizing epsilon with
  | nil => exact project_ground D alpha epsilon
  | cons j w ih =>
    rw [rightCurrentWord, project_current, ih]
    rfl

/- proof_shape: theta_source_expansion: content;
   sectorSign_not, sectorSign_square, wordParity_not, sectorProject_eigen,
   projectedGround_eigen: consumed-helper; rightCurrentWord_eigen: content
   admission_basis: escape-witness
   escape_witness: The native negative-mode formula generates each oscillator
   monomial in its original charge fiber. Linear projection through arbitrarily
   long words reverses the ground sign once per letter and gives independent
   finite charge and polynomial supports. SectorPropagation consumes this
   expansion, its sign identities and projected-ground eigenvalue to extend
   the exact compatible ground-pair family to arbitrary second sources.
   Literature status: classical lattice involution calculus; no novelty claim. -/
/-- Every projected source has a finite negative-current expansion. The charge
and oscillator supports are the independent supports of the actual input. -/
theorem theta_source_expansion (D : LatticeData) (b : Carrier D) (epsilon : Bool) :
    sectorProject D epsilon b =
      ∑ alpha ∈ b.support, ∑ e ∈ (b alpha).support,
        (b alpha).coeff e • rightCurrentWord D (occurrences D e)
          (projectedGround D alpha (wordParity (occurrences D e) epsilon)) := by
  classical
  have expand (alpha : Charge D) (p : Oscillator D) :
      sectorProject D epsilon (Finsupp.single alpha p) =
        ∑ e ∈ p.support, p.coeff e • rightCurrentWord D (occurrences D e)
          (projectedGround D alpha (wordParity (occurrences D e) epsilon)) := by
    conv_lhs => rw [p.as_sum]
    rw [Finsupp.single_finsetSum, map_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [show monomial e (p.coeff e) = p.coeff e • monomial e 1 by
      rw [← (monomial e).map_smul]; simp only [smul_eq_mul, mul_one],
      ← Finsupp.smul_single, map_smul]
    rw [← occurrences_product, ← word_single, project_word]
  conv_lhs => rw [← Finsupp.sum_single b]
  simp only [Finsupp.sum, map_sum, expand]

/-- The projected source really has the declared theta eigenvalue, even when
that projected component vanishes. -/
theorem sectorProject_eigen (D : LatticeData) (epsilon : Bool) (b : Carrier D) :
    theta D (sectorProject D epsilon b) = sectorSign epsilon • sectorProject D epsilon b := by
  have invol : theta D (theta D b) = b := theta_involutive D b
  simp only [sectorProject_apply, map_smul, map_add, invol]
  have hs := sectorSign_square epsilon
  calc
    _ = (2 : ℂ)⁻¹ • (theta D b + sectorSign epsilon • b) := rfl
    _ = (2 : ℂ)⁻¹ • (sectorSign epsilon • b +
        (sectorSign epsilon * sectorSign epsilon) • theta D b) := by rw [hs, one_smul, add_comm]
    _ = _ := by module

/-- Exact eigenvalue of the charged ground source. -/
theorem projectedGround_eigen (D : LatticeData) (alpha : Charge D) (epsilon : Bool) :
    theta D (projectedGround D alpha epsilon) =
      sectorSign epsilon • projectedGround D alpha epsilon := by
  rw [← project_ground]
  exact sectorProject_eigen D epsilon _

/-- Word length flips the ground sector once for every actual current. -/
theorem rightCurrentWord_eigen (D : LatticeData) (w : List (Index D))
    (alpha : Charge D) (epsilon : Bool) :
    theta D (rightCurrentWord D w (projectedGround D alpha epsilon)) =
      sectorSign (wordParity w epsilon) •
        rightCurrentWord D w (projectedGround D alpha epsilon) := by
  induction w with
  | nil => exact projectedGround_eigen D alpha epsilon
  | cons j w ih =>
    rw [rightCurrentWord, theta_neutralMode, ih, map_smul]
    simp only [wordParity, wordParity_not, sectorSign_not, neg_smul]

end D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport
