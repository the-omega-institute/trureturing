/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTopDetection
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTopDetection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Top coefficients separate lawful mixed fields on the actual twisted parities. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddSourceRestriction
import D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockEvenFixedModeIrreducibility
import D5.S3.VertexAlgebra.Lattice.FixedGradedDuality
import D5.S3.VertexAlgebra.SourceBPZ.ThetaReflectionAction
import D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
import D5.S3.VertexAlgebra.LatticeHalfFockCorrectedConformal
import D5.S3.VertexAlgebra.LatticeActualLZeroGrading

/-!
Abe, *Fusion rules for the free bosonic orbifold vertex operator algebra*,
arXiv:math/9907120v1, Proposition 2.10, p. 8. The r = 0 residue moves a
fixed mode across each mixed coefficient. The target step uses the span
of coefficient differences and the native fixed-mode irreducibility.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner

open LatticeGeneratingFieldLocality LatticeInvolution LatticePositiveEnergy
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockGradedTrace LatticeHalfFockParityT HalfFock.LatticeHalfFockParityField
open StateFieldResidueReconstruction (integerBinomial)
open ActualLeechHyperbolic (leechData leech_spec)
open LatticeTwistedGroundRealization (Half)
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open private theta_omega_fixed from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner

noncomputable section

variable {D : LatticeData} {hu : IsUnit D.G.det} {s : Bool}

abbrev fixedAction (t : Bool) (a : FixedCarrier D) (p : ℤ) :
    Module.End ℂ (Twisted D hu t) :=
  (fixedParitySlice D hu (paritySign t) a)[[p]]

private theorem fixedAction_val (t : Bool) (a : FixedCarrier D) (p : ℤ)
    (v : Twisted D hu t) :
    (fixedAction t a p v).val = (correctedField D hu a.val).coeff (-2*p-2) v.val := by
  change (correctedField D hu a.val).coeff (2*(-p-1)) v.val = _
  rw [show 2*(-p-1) = -2*p-2 by omega]

private theorem zeroBinomial (i : ℕ) (hi : i ≠ 0) : integerBinomial 0 i = 0 := by
  simp [integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]

private theorem zeroSignedFinsum {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : ℕ → V) :
    (∑ᶠ i : ℕ, (((-1 : ℂ)^i) * integerBinomial 0 i) • f i) = f 0 := by
  rw [finsum_eq_single _ 0]
  · simp [integerBinomial]
  · intro i hi
    simp only [zeroBinomial i hi, mul_zero, zero_smul]

/-- The finite r = 0 commutator on the two actual twisted parities.
The index of each mixed coefficient is its physical mode minus 1/2. -/
theorem mixed_commutator (F : LawfulMixedField D hu s) (a : FixedCarrier D)
    (b : OddCarrier D) (v : Twisted D hu s) (p q : ℤ) :
    let term := fun i : ℕ => integerBinomial p i •
      F.coeff (p+q-i) (oddMode D a i b) v
    Function.HasFiniteSupport term ∧
      (∑ᶠ i, term i) =
        fixedAction (!s) a p (F.coeff q b v) - F.coeff q b (fixedAction s a p v) := by
  have law := F.borcherds a b v p q 0
  unfold mixedBorcherds at law
  dsimp only at law ⊢
  refine ⟨by simpa only [zero_add] using law.1, ?_⟩
  have h := law.2.2.2
  let first (i : ℕ) := fixedAction (!s) a (p+0-i) (F.coeff (q+i) b v)
  let second (i : ℕ) := StateFieldResidueReconstruction.epsilon 0 •
    F.coeff (q+0-i) b (fixedAction s a (p+i) v)
  change (∑ᶠ i : ℕ, integerBinomial p i • F.coeff (p+q-i) (oddMode D a (0+i) b) v) =
    (∑ᶠ i : ℕ, (((-1 : ℂ)^i) * integerBinomial 0 i) • first i) -
    (∑ᶠ i : ℕ, (((-1 : ℂ)^i) * integerBinomial 0 i) • second i) at h
  rw [zeroSignedFinsum first, zeroSignedFinsum second] at h
  simpa only [first, second, StateFieldResidueReconstruction.epsilon, zpow_zero,
    one_smul, Nat.cast_zero, add_zero, zero_add, sub_zero] using h

private theorem sub_sub_exchange {V : Type*} [AddCommGroup V] (a b c d : V) :
    (a - b) - (c - d) = (a - c) - (b - d) := by abel

private theorem difference_commutator (F G : LawfulMixedField D hu s)
    (a : FixedCarrier D) (b : OddCarrier D) (v : Twisted D hu s) (p q : ℤ) :
    let d := fun (n : ℤ) (c : OddCarrier D) (x : Twisted D hu s) =>
      F.coeff n c x - G.coeff n c x
    let term := fun i : ℕ => integerBinomial p i • d (p+q-i) (oddMode D a i b) v
    Function.HasFiniteSupport term ∧
      (∑ᶠ i, term i) =
        fixedAction (!s) a p (d q b v) - d q b (fixedAction s a p v) := by
  let f (i : ℕ) := integerBinomial p i • F.coeff (p+q-i) (oddMode D a i b) v
  let g (i : ℕ) := integerBinomial p i • G.coeff (p+q-i) (oddMode D a i b) v
  obtain ⟨hf, hF⟩ := mixed_commutator F a b v p q
  obtain ⟨hg, hG⟩ := mixed_commutator G a b v p q
  have hterm :
      (fun i : ℕ => integerBinomial p i •
        (F.coeff (p+q-i) (oddMode D a i b) v - G.coeff (p+q-i) (oddMode D a i b) v)) =
      fun i => f i - g i := by
    funext i
    exact smul_sub (integerBinomial p i)
      (F.coeff (p+q-i) (oddMode D a i b) v) (G.coeff (p+q-i) (oddMode D a i b) v)
  change Function.HasFiniteSupport (fun i : ℕ => integerBinomial p i •
    (F.coeff (p+q-i) (oddMode D a i b) v - G.coeff (p+q-i) (oddMode D a i b) v)) ∧ _
  rw [hterm]
  have hf' : Function.HasFiniteSupport f := hf
  have hg' : Function.HasFiniteSupport g := hg
  refine ⟨(hf'.union hg').subset ?_, ?_⟩
  · intro i hi
    by_contra hn
    apply hi
    have hz : i ∉ Function.support f ∧ i ∉ Function.support g := by
      simpa only [Set.mem_union, not_or] using hn
    change f i - g i = 0
    rw [Function.notMem_support.mp hz.1, Function.notMem_support.mp hz.2]
    exact sub_self (0 : Twisted D hu (!s))
  · change (∑ᶠ i, (f i - g i)) =
      fixedAction (!s) a p (F.coeff q b v - G.coeff q b v) -
        (F.coeff q b (fixedAction s a p v) - G.coeff q b (fixedAction s a p v))
    change (∑ᶠ i, f i) = _ at hF
    change (∑ᶠ i, g i) = _ at hG
    rw [@finsum_sub_distrib ℕ (Twisted D hu (!s)) _ f g hf' hg', hF, hG,
      map_sub (fixedAction (!s) a p) (F.coeff q b v) (G.coeff q b v)]
    exact sub_sub_exchange
      (fixedAction (!s) a p (F.coeff q b v)) (F.coeff q b (fixedAction s a p v))
      (fixedAction (!s) a p (G.coeff q b v)) (G.coeff q b (fixedAction s a p v))

private theorem twisted_mode_irreducible (hrank : 2 ≤ D.rank)
    (S : Submodule ℂ (Twisted D hu s))
    (stable : ∀ (a : FixedCarrier D) (p : ℤ) (v : Twisted D hu s),
      v ∈ S → fixedAction s a p v ∈ S) : S = ⊥ ∨ S = ⊤ := by
  cases s with
  | false =>
    exact HalfFock.LatticeHalfFockEvenFixedModeIrreducibility.fixedParitySlice_even_irreducible
      D hu S stable
  | true =>
    exact HalfFock.LatticeHalfFockOddFixedModeIrreducibility.fixedParitySlice_odd_irreducible
      D hu hrank S stable

/-- The doubled oscillator energy of the lowest grade for each twisted parity. -/
abbrev twistedTopGrade (t : Bool) : ℕ := if t then 1 else 0

/-- The actual lowest-grade submodule of the indicated twisted parity. -/
abbrev twistedTop (D : LatticeData) (hu : IsUnit D.G.det) (t : Bool) :
    Submodule ℂ (Twisted D hu t) :=
  (actualGrade D hu (twistedTopGrade t)).comap (paritySpace D hu (paritySign t)).subtype

private def ambientGradeReadout (D : LatticeData) (hu : IsUnit D.G.det) (N : ℕ) :
    Module.End ℂ (ActualTensor D hu) := by
  classical
  let B := actualAmbientBasis D hu
  let indices : Set (OddMonomial D × Half (groundRank D hu)) := {i | oddWeight D i.1 = N}
  let restrict := Finsupp.restrictDom ℂ ℂ indices
  let filter := (Finsupp.supported ℂ ℂ indices).subtype.comp restrict
  exact B.repr.symm.toLinearMap.comp (filter.comp B.repr.toLinearMap)

/-- Projection to the target's actual lowest-grade coordinates in its ambient tensor. -/
def twistedTopReadout (D : LatticeData) (hu : IsUnit D.G.det) (t : Bool) :
    Twisted D hu t →ₗ[ℂ] ActualTensor D hu :=
  (ambientGradeReadout D hu (twistedTopGrade t)).comp (paritySpace D hu (paritySign t)).subtype

private theorem ambientGradeReadout_coord (N : ℕ) (x : ActualTensor D hu)
    (i : OddMonomial D × Half (groundRank D hu)) :
    (actualAmbientBasis D hu).repr (ambientGradeReadout D hu N x) i =
      if oddWeight D i.1 = N then (actualAmbientBasis D hu).repr x i else 0 := by
  classical
  simp [ambientGradeReadout, Finsupp.filter_apply]

private theorem signedGrade_coord_zero (M : ℤ) (x : ActualTensor D hu)
    (hx : actualTensorL0 D hu x = ((D.rank : ℂ) / 16 + (M : ℂ) / 2) • x)
    (i : OddMonomial D × Half (groundRank D hu)) (hi : (oddWeight D i.1 : ℤ) ≠ M) :
    (actualAmbientBasis D hu).repr x i = 0 := by
  have h := congrArg (fun w => (actualAmbientBasis D hu).repr w i) hx
  rw [actualTensorL0_repr] at h
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at h
  by_contra hn
  have hscalar := mul_right_cancel₀ hn h
  have hcast : (oddWeight D i.1 : ℂ) = (M : ℂ) := by
    linear_combination 2 * hscalar
  exact hi (by exact_mod_cast hcast)

private theorem ambientGradeReadout_zero_of_signedGrade_ne (N : ℕ) (M : ℤ)
    (x : ActualTensor D hu)
    (hx : actualTensorL0 D hu x = ((D.rank : ℂ) / 16 + (M : ℂ) / 2) • x)
    (hne : (N : ℤ) ≠ M) :
    ambientGradeReadout D hu N x = 0 := by
  apply (actualAmbientBasis D hu).repr.injective
  ext i
  rw [ambientGradeReadout_coord, map_zero, Finsupp.zero_apply]
  split_ifs with hi
  · exact signedGrade_coord_zero M x hx i (by simpa only [hi] using hne)
  · rfl

private theorem ambientGradeReadout_self (N : ℕ) (x : ActualTensor D hu)
    (hx : x ∈ actualGrade D hu N) : ambientGradeReadout D hu N x = x := by
  classical
  apply (actualAmbientBasis D hu).repr.injective
  ext i
  rw [ambientGradeReadout_coord]
  split_ifs with hi
  · rfl
  · symm
    by_contra hn
    exact hi ((actual_grade_mem_iff_repr_support D hu N x).mp hx i
      (Finsupp.mem_support_iff.mpr hn))

private theorem lowering_kills_top (a : FixedCarrier D) (h p : ℤ)
    (ha : a.val ∈ grade D h) (hlower : h - 1 < p) (v : Twisted D hu s)
    (hv : v ∈ twistedTop D hu s) : fixedAction s a p v = 0 := by
  have hv' : actualTensorL0 D hu v.val =
      ((D.rank : ℂ) / 16 + ((twistedTopGrade s : ℕ) : ℂ) / 2) • v.val := by
    simpa only [twistedTop, Submodule.mem_comap, actualGrade, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero,
      Submodule.subtype_apply] using hv
  let N : ℤ := (twistedTopGrade s : ℤ) + (-2*p-2) + 2*h
  have he := HalfFock.ActualEnergyCovariance.correctedField_signed_output D hu h
    (twistedTopGrade s : ℤ) (-2*p-2) a.val ha v.val
    (by simpa only [Int.cast_natCast] using hv')
  have hn : N < 0 := by
    have htop : (twistedTopGrade s : ℤ) ≤ 1 := by cases s <;> decide
    dsimp only [N]
    omega
  let x := (correctedField D hu a.val).coeff (-2*p-2) v.val
  have hx : x = 0 := by
    apply (actualAmbientBasis D hu).repr.injective
    apply Finsupp.ext
    intro i
    rw [map_zero, Finsupp.zero_apply]
    have hn' : Int.ofNat (oddWeight D i.1) ≠ N := ne_of_gt (lt_of_lt_of_le hn (Int.natCast_nonneg _))
    exact signedGrade_coord_zero N x he i hn'
  apply Subtype.ext
  exact (fixedAction_val s a p v).trans hx

private theorem topReadout_raising_zero (a : FixedCarrier D) (h p : ℤ)
    (ha : a.val ∈ grade D h) (hraise : p < h - 1) (v : Twisted D hu s) :
    twistedTopReadout D hu s (fixedAction s a p v) = 0 := by
  let A := (correctedField D hu a.val).coeff (-2*p-2)
  have hzero : (ambientGradeReadout D hu (twistedTopGrade s)).comp A = 0 := by
    apply (actualAmbientBasis D hu).ext
    intro i
    change ambientGradeReadout D hu (twistedTopGrade s) (A (actualAmbientBasis D hu i)) = 0
    have he := HalfFock.ActualEnergyCovariance.correctedField_signed_output D hu h
      (oddWeight D i.1 : ℤ) (-2*p-2) a.val ha (actualAmbientBasis D hu i)
      (by simpa only [Int.cast_natCast] using actual_basis_eigenvalue D hu i.1 i.2)
    apply ambientGradeReadout_zero_of_signedGrade_ne _ _ _ he
    cases s <;> simp [twistedTopGrade] <;> omega
  change ambientGradeReadout D hu (twistedTopGrade s) (fixedAction s a p v).val = 0
  rw [fixedAction_val]
  exact LinearMap.congr_fun hzero v.val

private theorem fixedAction_equal_degree_top (a : FixedCarrier D) (h p : ℤ)
    (ha : a.val ∈ grade D h) (hp : p = h - 1) (v : Twisted D hu s)
    (hv : v ∈ twistedTop D hu s) : fixedAction s a p v ∈ twistedTop D hu s := by
  have hv' : actualTensorL0 D hu v.val =
      ((D.rank : ℂ) / 16 + ((twistedTopGrade s : ℕ) : ℂ) / 2) • v.val := by
    simpa only [twistedTop, Submodule.mem_comap, actualGrade, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero,
      Submodule.subtype_apply] using hv
  have he := HalfFock.ActualEnergyCovariance.correctedField_signed_output D hu h
    (twistedTopGrade s : ℤ) (-2*p-2) a.val ha v.val
    (by simpa only [Int.cast_natCast] using hv')
  have hd : (twistedTopGrade s : ℤ) + (-2*p-2) + 2*h = (twistedTopGrade s : ℤ) := by omega
  simp only [twistedTop, Submodule.mem_comap, actualGrade, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero,
    Submodule.subtype_apply, fixedAction_val]
  simpa only [hd, Int.cast_natCast] using he

private theorem theta_gradeProjection (n : ℤ) (x : Carrier D) :
    theta D (gradeProjection D n x) = gradeProjection D n (theta D x) := by
  simpa only [SourceBPZ.ThetaReflectionAction.thetaRep_apply_one] using
    SourceBPZ.ThetaReflectionAction.thetaRep_gradeProjection_commute D n x

private theorem topReadout_agrees_on_homogeneous_fixedMode_top (F G : LawfulMixedField D hu s)
    (hTop : ∀ (n : ℤ) (b : OddCarrier D) (v : Twisted D hu s), v ∈ twistedTop D hu s →
      twistedTopReadout D hu (!s) (F.coeff n b v) =
        twistedTopReadout D hu (!s) (G.coeff n b v))
    (a : FixedCarrier D) (p q h : ℤ) (ha : a.val ∈ grade D h)
    (b : OddCarrier D) (v : Twisted D hu s) (hv : v ∈ twistedTop D hu s) :
    twistedTopReadout D hu (!s) (F.coeff q b (fixedAction s a p v)) =
      twistedTopReadout D hu (!s) (G.coeff q b (fixedAction s a p v)) := by
  classical
  let P := twistedTopReadout D hu (!s)
  rcases lt_trichotomy p (h - 1) with hr | he | hl
  · obtain ⟨hfin, comm⟩ := difference_commutator F G a b v p q
    have hseed (n : ℤ) (u : OddCarrier D) :
        P (F.coeff n u v) = P (G.coeff n u v) := hTop n u v hv
    have hraise (w : Twisted D hu (!s)) : P (fixedAction (!s) a p w) = 0 :=
      topReadout_raising_zero a h p ha hr w
    let d (n : ℤ) (u : OddCarrier D) (w : Twisted D hu s) :=
      F.coeff n u w - G.coeff n u w
    let term (i : ℕ) := integerBinomial p i • d (p+q-i) (oddMode D a i b) v
    have h := congrArg P comm
    change P (∑ᶠ i, term i) =
      P (fixedAction (!s) a p (d q b v) - d q b (fixedAction s a p v)) at h
    rw [map_finsum P (show Function.HasFiniteSupport term from hfin),
      map_sub P, hraise, zero_sub] at h
    have hzero (i : ℕ) : P (term i) = 0 := by
      change P (integerBinomial p i •
        (F.coeff (p+q-i) (oddMode D a i b) v - G.coeff (p+q-i) (oddMode D a i b) v)) = 0
      rw [map_smul P, map_sub P, hseed, sub_self, smul_zero]
    simp only [hzero, finsum_zero] at h
    change 0 = -P (F.coeff q b (fixedAction s a p v) -
      G.coeff q b (fixedAction s a p v)) at h
    rw [map_sub P] at h
    exact sub_eq_zero.mp (neg_eq_zero.mp h.symm)
  · exact hTop q b _ (fixedAction_equal_degree_top a h p ha he v hv)
  · simp only [lowering_kills_top a h p ha hl v hv, map_zero]

private def fixedActionAt (p : ℤ) (v : Twisted D hu s) :
    FixedCarrier D →ₗ[ℂ] Twisted D hu s := by
  let coeffAt := LatticeHalfFockFockNormalField.coefficientAt D hu (-2*p-2) v.val
  let fixedCoeff := (coeffAt.comp (correctedField D hu)).comp (fixedSpace D).subtype
  refine fixedCoeff.codRestrict (paritySpace D hu (paritySign s)) fun c => ?_
  change (correctedField D hu c.val).coeff (-2*p-2) v.val ∈ paritySpace D hu (paritySign s)
  rw [← fixedAction_val s c p v]
  exact (fixedAction s c p v).property

private theorem fixedActionAt_apply (p : ℤ) (v : Twisted D hu s) (a : FixedCarrier D) :
    fixedActionAt p v a = fixedAction s a p v :=
  Subtype.ext (fixedAction_val s a p v).symm

/-- Agreement on the input top propagates to each fixed-mode descendant of
an input top vector. The source and the mixed index range over all coefficients. -/
theorem topReadout_agrees_on_fixedMode_top (F G : LawfulMixedField D hu s)
    (hTop : ∀ (n : ℤ) (b : OddCarrier D) (v : Twisted D hu s), v ∈ twistedTop D hu s →
      twistedTopReadout D hu (!s) (F.coeff n b v) =
        twistedTopReadout D hu (!s) (G.coeff n b v))
    (a : FixedCarrier D) (p q : ℤ) (b : OddCarrier D) (v : Twisted D hu s)
    (hv : v ∈ twistedTop D hu s) :
    twistedTopReadout D hu (!s) (F.coeff q b (fixedAction s a p v)) =
      twistedTopReadout D hu (!s) (G.coeff q b (fixedAction s a p v)) := by
  classical
  let P := twistedTopReadout D hu (!s)
  let A := fixedActionAt p v
  let EF := P.comp ((F.coeff q b).comp A)
  let EG := P.comp ((G.coeff q b).comp A)
  let grades := stateEnergies D a.val
  let part (n : ℤ) : FixedCarrier D :=
    (FixedGradedDuality.fixedGradeProjection D theta_gradeProjection n a).val
  have hsum : (∑ n ∈ grades, part n) = a :=
    FixedGradedDuality.fixedGradeProjection_sum D theta_gradeProjection a
  have hpart (n : ℤ) : EF (part n) = EG (part n) := by
    change P (F.coeff q b (A (part n))) = P (G.coeff q b (A (part n)))
    rw [fixedActionAt_apply p v (part n)]
    exact topReadout_agrees_on_homogeneous_fixedMode_top F G hTop (part n) p q n
      (FixedGradedDuality.fixedGradeProjection D theta_gradeProjection n a).property b v hv
  have he : EF a = EG a := calc
    EF a = EF (∑ n ∈ grades, part n) := congrArg EF hsum.symm
    _ = ∑ n ∈ grades, EF (part n) := map_sum EF part grades
    _ = ∑ n ∈ grades, EG (part n) := Finset.sum_congr rfl fun n _ => hpart n
    _ = EG (∑ n ∈ grades, part n) := (map_sum EG part grades).symm
    _ = EG a := congrArg EG hsum
  exact (congrArg (fun x => P (F.coeff q b x)) (fixedActionAt_apply p v a).symm).trans
    (he.trans (congrArg (fun x => P (G.coeff q b x)) (fixedActionAt_apply p v a)))

private theorem fixedAction_borcherds (a b : FixedCarrier D) (v : Twisted D hu s)
    (p q r : ℤ) :
    let left := fun i : ℕ => integerBinomial p i •
      fixedAction s (fixedMode D a (r+i) b) (p+q-i) v
    let first := fun i : ℕ => (((-1 : ℂ)^i)*integerBinomial r i) •
      fixedAction s a (p+r-i) (fixedAction s b (q+i) v)
    let second := fun i : ℕ => (((-1 : ℂ)^i)*integerBinomial r i) •
      (StateFieldResidueReconstruction.epsilon r • fixedAction s b (q+r-i) (fixedAction s a (p+i) v))
    Function.HasFiniteSupport left ∧
      (∑ᶠ i, left i) = (∑ᶠ i, first i) - (∑ᶠ i, second i) := by
  have eigen : theta D a.val = (-1 : ℂ) ^ (0 : ℤ) • a.val := by
    simpa only [zpow_zero, one_smul] using (mem_fixedSpace D a.val).mp a.property
  have native := LatticeHalfFockGroundRightCurrentTransport.first_eigen_arbitrary_second
    D hu a.val 0 eigen b.val 0
  unfold LatticeHalfFockGroundRightCurrentTransport.OriginalCompatible
    LatticeHalfFockGroundRightCurrentTransport.Calculus.fullLaw at native
  have h := native p q r v.val
  unfold LatticeHalfFockGroundRightCurrentTransport.Calculus.leftTerm
    LatticeHalfFockGroundRightCurrentTransport.Calculus.firstTerm
    LatticeHalfFockGroundRightCurrentTransport.Calculus.secondTerm
    LatticeHalfFockGroundRightCurrentTransport.residueWeight at h
  have binom (n : ℤ) (i : ℕ) : integerBinomial n i = Ring.choose (n : ℂ) i :=
    Ring.map_choose (Int.castRingHom ℂ) n i
  simp only [LatticeHalfFockPhysicalRescaling.physicalSlice_mode,
    Int.cast_zero, zero_div, add_zero, sub_zero, ← binom] at h
  let incl : Twisted D hu s →ₗ[ℂ] ActualTensor D hu :=
    (paritySpace D hu (paritySign s)).subtype
  have injective : Function.Injective incl := Subtype.val_injective
  have incl_apply (w : Twisted D hu s) : incl w = w.val := rfl
  have finite_lift (f : ℕ → Twisted D hu s)
      (hf : Function.HasFiniteSupport (fun i => incl (f i))) :
      Function.HasFiniteSupport f := by
    apply hf.subset
    intro i hi hz
    exact hi (injective (hz.trans (map_zero incl).symm))
  have sum_map (f : ℕ → Twisted D hu s) :
      incl (∑ᶠ i, f i) = ∑ᶠ i, incl (f i) :=
    incl.toAddMonoidHom.map_finsum_of_injective injective f
  have fixed_val (n : ℤ) :
      (fixedMode D a n b).val = LatticeAllStateReconstruction.mu D a.val n b.val := rfl
  dsimp only
  refine ⟨finite_lift _ ?_, ?_⟩
  · simpa only [incl_apply, Submodule.coe_smul, fixedAction_val, fixed_val] using h.1
  · apply injective
    rw [map_sub incl, sum_map, sum_map, sum_map]
    simpa only [incl_apply, Submodule.coe_smul, fixedAction_val, fixed_val,
      StateFieldResidueReconstruction.epsilon] using h.2.2.2

private theorem fixedAction_tail (a : FixedCarrier D) (v : Twisted D hu s) :
    ∃ N : ℤ, ∀ n ≥ N, fixedAction s a n v = 0 := by
  let A := fixedParitySlice D hu (paritySign s) a
  let order := ((HahnModule.of ℂ).symm (A v)).order
  refine ⟨-order, fun n hn => VertexOperator.ncoeff_eq_zero_of_lt_order A n v ?_⟩
  change -n - 1 < order
  omega

private theorem twistedTop_nonzero (hrank : 2 ≤ D.rank) :
    ∃ v : Twisted D hu s, v ∈ twistedTop D hu s ∧ v ≠ 0 := by
  classical
  have indexes : ∃ d : OddMonomial D, oddWeight D d = twistedTopGrade s := by
    cases s with
    | false => exact ⟨0, by simp [oddWeight, twistedTopGrade]⟩
    | true =>
      let i : Fin D.rank := ⟨0, by omega⟩
      exact ⟨Finsupp.single (i, 0) 1,
        by simp [oddWeight, twistedTopGrade, Finsupp.weight_single,
          LatticeHalfFockChargedCoefficients.omega]⟩
  obtain ⟨d, hd⟩ := indexes
  let i : OddMonomial D × Half (groundRank D hu) := (d, 0)
  let x := actualAmbientBasis D hu i
  have hx : x ∈ actualGrade D hu (twistedTopGrade s) :=
    actualGradeVector_mem D hu _ (⟨d, hd⟩, i.2)
  have hs : x ∈ paritySpace D hu (paritySign s) := by
    have h := actualParity_on_actualGrade D hu (twistedTopGrade s) ⟨x, hx⟩
    simp only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero]
    cases s with
    | false =>
      simpa only [twistedTopGrade, paritySign, Bool.false_eq_true, ite_false, pow_zero, one_smul] using h
    | true =>
      change actualParity D hu x = ((-1 : ℂ) ^ (1 : ℕ)) • x at h
      rw [pow_one] at h
      exact h
  let v : Twisted D hu s := ⟨x, hs⟩
  refine ⟨v, hx, ?_⟩
  intro hz
  have hxz : x = 0 := congrArg (fun w : Twisted D hu s => w.val) hz
  exact (actualAmbientBasis D hu).ne_zero i hxz

private theorem fixedAction_pair_mem (S : Submodule ℂ (Twisted D hu s))
    (v : Twisted D hu s) (seed : ∀ (a : FixedCarrier D) (q : ℤ), fixedAction s a q v ∈ S)
    (a b : FixedCarrier D) (k q : ℤ) :
    fixedAction s a k (fixedAction s b q v) ∈ S := by
  classical
  obtain ⟨P, hP⟩ := fixedAction_tail a v
  obtain ⟨Q, hQ⟩ := fixedAction_tail b v
  have outer (i : ℕ) : fixedAction s a (P+i) v = 0 := hP _ (by omega)
  let product (k q : ℤ) := fixedAction s a k (fixedAction s b q v)
  have descend (d : ℕ) : ∀ q : ℤ, (Q-q).toNat = d → ∀ k : ℤ, product k q ∈ S := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro q hd k
      by_cases hq : Q ≤ q
      · dsimp only [product]
        rw [hQ q hq, map_zero]
        exact S.zero_mem
      have distance : (d : ℤ) = Q-q := by
        rw [← hd]
        exact Int.toNat_of_nonneg (by omega)
      let r : ℤ := k-P
      have hPr : P+r = k := by dsimp [r]; omega
      let left (i : ℕ) := integerBinomial P i •
        fixedAction s (fixedMode D a (r+i) b) (P+q-i) v
      let first (i : ℕ) := (((-1 : ℂ)^i)*integerBinomial r i) • product (k-i) (q+i)
      let second (i : ℕ) := (((-1 : ℂ)^i)*integerBinomial r i) •
        (StateFieldResidueReconstruction.epsilon r • fixedAction s b (q+r-i) (fixedAction s a (P+i) v))
      obtain ⟨hl, h⟩ := fixedAction_borcherds a b v P q r
      change (∑ᶠ i, left i) =
        (∑ᶠ i : ℕ, (((-1 : ℂ)^i)*integerBinomial r i) • product (P+r-i) (q+i)) -
          (∑ᶠ i, second i) at h
      have hsecond (i : ℕ) : second i = 0 := by
        simp only [second, outer, map_zero, smul_zero]
      have forward : (∑ᶠ i, left i) = ∑ᶠ i, first i := by
        simpa only [hPr, hsecond, finsum_zero, sub_zero (a := (∑ᶠ i, first i)), first] using h
      have left_mem : (∑ᶠ i, left i) ∈ S := by
        rw [finsum_eq_sum left (show Function.HasFiniteSupport left from hl)]
        apply S.sum_mem
        intro i _
        exact S.smul_mem (integerBinomial P i) (seed (fixedMode D a (r+i) b) (P+q-i))
      have hsupp : Function.support first ⊆ (↑(Finset.range (d+1)) : Set ℕ) := by
        intro i hi
        by_contra hout
        simp only [Finset.mem_coe, Finset.mem_range] at hout
        exact hi (by
          dsimp only [first, product]
          rw [hQ (q+i) (by omega), map_zero, smul_zero])
      have leading : first 0 = product k q := by simp [first, integerBinomial]
      have tail_mem : (∑ i ∈ Finset.range d, first (i+1)) ∈ S := by
        apply S.sum_mem
        intro i _
        change (((-1 : ℂ)^(i+1))*integerBinomial r (i+1)) •
          product (k-(i+1 : ℕ)) (q+(i+1 : ℕ)) ∈ S
        exact S.smul_mem _
          (ih _ (by omega : (Q - (q + ((i+1 : ℕ) : ℤ))).toNat < d) _ rfl _)
      rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_range_succ', leading] at forward
      let main := product k q
      let total := ∑ᶠ i, left i
      let tail := ∑ i ∈ Finset.range d, first (i+1)
      have recover : main = total - tail :=
        (eq_sub_iff_add_eq (a := main) (b := total) (c := tail)).mpr
          ((add_comm main tail).trans forward.symm)
      have hmem : total - tail ∈ S :=
        Submodule.sub_mem S (x := total) (y := tail) left_mem tail_mem
      exact (congrArg (fun x : Twisted D hu s => x ∈ S) recover).mpr hmem
  exact descend (Q-q).toNat q rfl k

private theorem span_top_of_single_modes {V I : Type*} [AddCommGroup V] [Module ℂ V]
    (act : I → ℤ → Module.End ℂ V) (T : Submodule ℂ V)
    (irreducible : ∀ S : Submodule ℂ V,
      (∀ a p v, v ∈ S → act a p v ∈ S) → S = ⊥ ∨ S = ⊤)
    (nonzero : ∃ v ∈ T, v ≠ 0)
    (pair : ∀ (S : Submodule ℂ V) (v : V), (∀ a p, act a p v ∈ S) →
      ∀ a b k q, act a k (act b q v) ∈ S) :
    Submodule.span ℂ ((T : Set V) ∪
      {w | ∃ a q v, v ∈ T ∧ w = act a q v}) = ⊤ := by
  let generators : Set V := (T : Set V) ∪ {w | ∃ a q v, v ∈ T ∧ w = act a q v}
  let S := Submodule.span ℂ generators
  have seed (a : I) (q : ℤ) (v : V) (hv : v ∈ T) : act a q v ∈ S :=
    Submodule.subset_span (show act a q v ∈ generators from Or.inr ⟨a, q, v, hv, rfl⟩)
  have stable (a : I) (k : ℤ) : S ≤ S.comap (act a k) := by
    apply Submodule.span_le.mpr
    intro w hw
    rcases hw with hw | ⟨b, q, v, hv, rfl⟩
    · exact seed a k w hw
    · exact pair S v (fun c n => seed c n v hv) a b k q
  rcases irreducible S (fun a k _ hv => stable a k hv) with hbot | htop
  · obtain ⟨v, hv, hne⟩ := nonzero
    have hmem : v ∈ S := Submodule.subset_span (show v ∈ generators from Or.inl hv)
    rw [hbot, Submodule.mem_bot] at hmem
    exact (hne hmem).elim
  · exact htop

/-- The native fixed modes applied once to the input top, together with
the top itself, span the carrier. Large p kills the reversed half of the
signed Jacobi identity and lets the inner mode descend from truncation. -/
theorem twistedTop_mode_span (hrank : 2 ≤ D.rank) :
    Submodule.span ℂ ((twistedTop D hu s : Set (Twisted D hu s)) ∪
      {w : Twisted D hu s | ∃ (a : FixedCarrier D) (q : ℤ) (v : Twisted D hu s),
        v ∈ twistedTop D hu s ∧ w = fixedAction s a q v}) = ⊤ := by
  have irreducible (S : Submodule ℂ (Twisted D hu s))
      (stable : ∀ (a : FixedCarrier D) (p : ℤ) (v : Twisted D hu s),
        v ∈ S → fixedAction s a p v ∈ S) : S = ⊥ ∨ S = ⊤ :=
    twisted_mode_irreducible hrank S stable
  have nonzero : ∃ v ∈ twistedTop D hu s, v ≠ 0 := twistedTop_nonzero hrank
  have pair (S : Submodule ℂ (Twisted D hu s)) (v : Twisted D hu s)
      (seed : ∀ (a : FixedCarrier D) (p : ℤ), fixedAction s a p v ∈ S)
      (a b : FixedCarrier D) (k q : ℤ) :
      fixedAction s a k (fixedAction s b q v) ∈ S :=
    fixedAction_pair_mem S v seed a b k q
  have h := @span_top_of_single_modes (Twisted D hu s) (FixedCarrier D)
    (inferInstanceAs (AddCommGroup (Twisted D hu s)))
    (inferInstanceAs (Module ℂ (Twisted D hu s)))
    (fixedAction (D := D) (hu := hu) s) (twistedTop D hu s) irreducible nonzero pair
  exact h

private theorem topReadout_agrees_all_inputs (hrank : 2 ≤ D.rank) (F G : LawfulMixedField D hu s)
    (hTop : ∀ (n : ℤ) (b : OddCarrier D) (v : Twisted D hu s), v ∈ twistedTop D hu s →
      twistedTopReadout D hu (!s) (F.coeff n b v) =
        twistedTopReadout D hu (!s) (G.coeff n b v))
    (n : ℤ) (b : OddCarrier D) (v : Twisted D hu s) :
    twistedTopReadout D hu (!s) (F.coeff n b v) =
      twistedTopReadout D hu (!s) (G.coeff n b v) := by
  let P := twistedTopReadout D hu (!s)
  let L := (P.comp (F.coeff n b)) - (P.comp (G.coeff n b))
  have hspan : Submodule.span ℂ ((twistedTop D hu s : Set (Twisted D hu s)) ∪
      {w : Twisted D hu s | ∃ (a : FixedCarrier D) (q : ℤ) (v : Twisted D hu s),
        v ∈ twistedTop D hu s ∧ w = fixedAction s a q v}) ≤ LinearMap.ker L := by
    apply Submodule.span_le.mpr
    intro w hw
    apply LinearMap.mem_ker.mpr
    apply sub_eq_zero.mpr
    rcases hw with hw | ⟨a, q, t, ht, rfl⟩
    · exact hTop n b w hw
    · exact topReadout_agrees_on_fixedMode_top F G hTop a q n b t ht
  rw [twistedTop_mode_span hrank] at hspan
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp (hspan (Submodule.mem_top (x := v))))

/-- Native top-to-top coefficient injectivity for both mixed parities.
The range of the differences is detected using a proper top projection kernel. -/
theorem eq_of_twistedTopReadout_agreement (hrank : 2 ≤ D.rank) (F G : LawfulMixedField D hu s)
    (hTop : ∀ (n : ℤ) (b : OddCarrier D) (v : Twisted D hu s), v ∈ twistedTop D hu s →
      twistedTopReadout D hu (!s) (F.coeff n b v) =
        twistedTopReadout D hu (!s) (G.coeff n b v)) :
    F = G := by
  classical
  let P := twistedTopReadout D hu (!s)
  let d (n : ℤ) (b : OddCarrier D) (v : Twisted D hu s) := F.coeff n b v - G.coeff n b v
  let generators : Set (Twisted D hu (!s)) :=
    {w | ∃ (n : ℤ) (b : OddCarrier D) (v : Twisted D hu s), w = d n b v}
  let S : Submodule ℂ (Twisted D hu (!s)) := Submodule.span ℂ generators
  have seed (n : ℤ) (b : OddCarrier D) (v : Twisted D hu s) : d n b v ∈ S := by
    have hm : d n b v ∈ generators := ⟨n, b, v, rfl⟩
    exact Submodule.subset_span hm
  have Sker : S ≤ LinearMap.ker P := by
    apply Submodule.span_le.mpr
    rintro w ⟨n, b, v, rfl⟩
    apply LinearMap.mem_ker.mpr
    change twistedTopReadout D hu (!s) (F.coeff n b v - G.coeff n b v) = 0
    rw [map_sub P (F.coeff n b v) (G.coeff n b v)]
    exact sub_eq_zero.mpr (topReadout_agrees_all_inputs hrank F G hTop n b v)
  have stable (a : FixedCarrier D) (p : ℤ) : S ≤ S.comap (fixedAction (!s) a p) := by
    apply Submodule.span_le.mpr
    rintro w ⟨q, b, v, rfl⟩
    let term := fun i : ℕ => integerBinomial p i • d (p+q-i) (oddMode D a i b) v
    obtain ⟨hfin, h⟩ := difference_commutator F G a b v p q
    have hsum : (∑ᶠ i, term i) ∈ S := by
      rw [finsum_eq_sum term (show Function.HasFiniteSupport term from hfin)]
      exact S.sum_mem (fun i _ => S.smul_mem _ (seed _ _ _))
    change fixedAction (!s) a p (d q b v) ∈ S
    have hmode : (∑ᶠ i, term i) + d q b (fixedAction s a p v) =
        fixedAction (!s) a p (d q b v) :=
      (eq_sub_iff_add_eq (a := ∑ᶠ i, term i) (b := fixedAction (!s) a p (d q b v))
        (c := d q b (fixedAction s a p v))).mp h
    rw [← hmode]
    exact S.add_mem hsum (seed _ _ _)
  have hbot : S = ⊥ := by
    rcases twisted_mode_irreducible hrank S (fun a p _ hv => stable a p hv) with hbot | htop
    · exact hbot
    · obtain ⟨w, hw, hne⟩ := twistedTop_nonzero (hu := hu) (s := !s) hrank
      have hker : P w = 0 := LinearMap.mem_ker.mp (Sker (htop.symm ▸ Submodule.mem_top))
      have hself : P w = w.val :=
        ambientGradeReadout_self (twistedTopGrade (!s)) w.val hw
      exact (hne (Subtype.ext (hself.symm.trans hker))).elim
  have hcoeff : F.coeff = G.coeff := by
    funext n
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro v
    have h := seed n b v
    rw [hbot, Submodule.mem_bot] at h
    exact sub_eq_zero.mp h
  cases F
  cases G
  cases hcoeff
  rfl

private def stress (D : LatticeData) : FixedCarrier D :=
  ⟨LatticeActualConformalState.omega D (actualInverse D),
    (mem_fixedSpace D _).mpr (theta_omega_fixed D (actualInverse D))⟩

private theorem stress_action (t : Bool) (v : Twisted D hu t) :
    (fixedAction t (stress D) 1 v).val = actualTensorL0 D hu v.val := by
  rw [fixedAction_val]
  change (correctedField D hu (LatticeActualConformalState.omega D (actualInverse D))).coeff
    (-4) v.val = actualTensorL0 D hu v.val
  rw [LatticeHalfFockCorrectedConformal.correctedField_omega D hu _
    (actualInverse_left D hu), LatticeHalfFock.tensorStressField,
    HVertexOperator.coeff_of_coeff]
  norm_num [LatticeHalfFock.stressCoeff, actualTensorL0, LatticeHalfFock.tensorL]

private theorem stress_odd_zero (hu : IsUnit D.G.det) (b : OddCarrier D) :
    oddMode D (stress D) 0 b = oddTranslation D b := by
  apply Subtype.ext
  change ((LatticeAllStateField.Y D (LatticeActualConformalState.omega D
    (actualInverse D)))[[0]]) b.val = LatticeSugawaraConformal.translation D b.val
  rw [LatticeActualConformalWard.omega_ncoeff, show (0 : ℤ) - 1 = -1 by norm_num,
    LatticeSugawaraConformal.sugawaraMode_minus_one_eq_translation D _
      (actualInverse_left D hu) (actualInverse_right D hu)]

private theorem stress_odd_one (hu : IsUnit D.G.det) (h : ℤ) (b : OddCarrier D) (hb : b.val ∈ grade D h) :
    oddMode D (stress D) 1 b = (h : ℂ) • b := by
  apply Subtype.ext
  change ((LatticeAllStateField.Y D (LatticeActualConformalState.omega D
    (actualInverse D)))[[1]]) b.val = (h : ℂ) • b.val
  rw [LatticeActualConformalWard.omega_ncoeff, sub_self]
  exact (actualL0_eigen_iff_grade D _ (actualInverse_left D hu)
    (actualInverse_right D hu) h b.val).mpr hb

private theorem mixed_commutator_one (F : LawfulMixedField D hu s) (a : FixedCarrier D)
    (b : OddCarrier D) (v : Twisted D hu s) (n : ℤ) :
    fixedAction (!s) a 1 (F.coeff n b v) - F.coeff n b (fixedAction s a 1 v) =
      F.coeff (n+1) (oddMode D a 0 b) v + F.coeff n (oddMode D a 1 b) v := by
  classical
  let term (i : ℕ) := integerBinomial 1 i • F.coeff (1+n-i) (oddMode D a i b) v
  have comm := (mixed_commutator F a b v 1 n).2
  change (∑ᶠ i, term i) = _ at comm
  have hsupp : Function.support term ⊆ (↑(Finset.range 2) : Set ℕ) := by
    intro i hi
    by_contra hout
    simp only [Finset.mem_coe, Finset.mem_range] at hout
    have hz : Ring.choose (1 : ℤ) i = 0 := by
      change Ring.choose ((1 : ℕ) : ℤ) i = 0
      simp only [Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega : 1 < i), Nat.cast_zero]
    exact hi (by simp [term, integerBinomial, hz])
  rw [← comm, finsum_eq_sum_of_support_subset _ hsupp]
  simp [Finset.sum_range_succ, term, integerBinomial, add_comm n 1]

/-- The candidate's energy covariance follows from its own p = 1 commutator
with the native stress state and its physical translation law. -/
theorem lawfulMixed_signed_grade (F : LawfulMixedField D hu s) (n h : ℤ)
    (M : ℕ) (b : OddCarrier D) (v : Twisted D hu s) (hb : b.val ∈ grade D h)
    (hv : v.val ∈ actualGrade D hu M) :
    let x := (F.coeff n b v).val
    actualTensorL0 D hu x =
      ((D.rank : ℂ) / 16 + (((M : ℤ) + 2*h - 2*n - 3 : ℤ) : ℂ) / 2) • x := by
  -- On the fixed stress mode the two actual actions are the ambient L0.
  have hvL : actualTensorL0 D hu v.val = ((D.rank : ℂ) / 16 + (M : ℂ) / 2) • v.val := by
    simpa only [actualGrade, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] using hv
  have hin : fixedAction s (stress D) 1 v =
      ((D.rank : ℂ) / 16 + (M : ℂ) / 2) • v := by
    apply Subtype.ext
    rw [stress_action, Submodule.coe_smul]
    exact hvL
  have hcomm := mixed_commutator_one F (stress D) b v n
  rw [stress_odd_zero hu, stress_odd_one hu h b hb, hin,
    F.derivative b v (n+1), show n+1-1 = n by omega] at hcomm
  simp only [map_smul, LinearMap.smul_apply] at hcomm
  have h := congrArg (fun w : Twisted D hu (!s) => w.val) hcomm
  simp only [stress_action, Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul] at h
  dsimp only
  rw [sub_eq_iff_eq_add] at h
  rw [h, ← add_smul, ← add_smul]
  congr 1
  push_cast
  ring

/-- The integer label of the physical half-integer mode that maps the input
top to the output top for a state of source weight h. -/
def twistedTopZhuIndex (s : Bool) (h : ℤ) : ℤ :=
  if s then h - 1 else h - 2

/-- All other physical modes of a homogeneous source have zero top readout. -/
theorem twistedTopReadout_eq_zero_of_ne_zhuIndex (F : LawfulMixedField D hu s) (n h : ℤ)
    (b : OddCarrier D) (v : Twisted D hu s) (hb : b.val ∈ grade D h)
    (hv : v ∈ twistedTop D hu s) (hn : n ≠ twistedTopZhuIndex s h) :
    twistedTopReadout D hu (!s) (F.coeff n b v) = 0 := by
  apply ambientGradeReadout_zero_of_signedGrade_ne _ _ _
    (lawfulMixed_signed_grade F n h (twistedTopGrade s) b v hb hv)
  cases s <;> simp [twistedTopGrade, twistedTopZhuIndex] at hn ⊢ <;> omega

/-- Agreement just at the Zhu mode of each homogeneous odd source detects
the full lawful mixed field on the actual twisted parities. -/
theorem eq_of_twistedZhuTopReadout_agreement (hrank : 2 ≤ D.rank)
    (F G : LawfulMixedField D hu s)
    (hZhu : ∀ (h : ℤ) (b : OddCarrier D) (v : Twisted D hu s),
      b.val ∈ grade D h → v ∈ twistedTop D hu s →
      twistedTopReadout D hu (!s) (F.coeff (twistedTopZhuIndex s h) b v) =
        twistedTopReadout D hu (!s) (G.coeff (twistedTopZhuIndex s h) b v)) :
    F = G := by
  classical
  apply eq_of_twistedTopReadout_agreement hrank F G
  intro n b v hv
  have hom (h : ℤ) (c : OddCarrier D) (hc : c.val ∈ grade D h) :
      twistedTopReadout D hu (!s) (F.coeff n c v) =
        twistedTopReadout D hu (!s) (G.coeff n c v) := by
    by_cases hn : n = twistedTopZhuIndex s h
    · exact hn.symm ▸ hZhu h c v hc hv
    · rw [twistedTopReadout_eq_zero_of_ne_zhuIndex F n h c v hc hv hn,
        twistedTopReadout_eq_zero_of_ne_zhuIndex G n h c v hc hv hn]
  let part (h : ℤ) : OddCarrier D := ⟨gradeProjection D h b.val, by
    change gradeProjection D h b.val ∈ eigenspace D (-1)
    rw [mem_eigenspace, theta_gradeProjection,
      (mem_eigenspace D (-1) b.val).mp b.property, map_smul]⟩
  have hsum : (∑ h ∈ stateEnergies D b.val, part h) = b := by
    apply Subtype.ext
    change (minusSpace D).subtype (∑ h ∈ stateEnergies D b.val, part h) = b.val
    rw [map_sum]
    exact sum_gradeProjections D b.val
  -- Compose with evaluation before decomposing the odd source.
  let P := twistedTopReadout D hu (!s)
  let EF := P.comp ((LinearMap.applyₗ v).comp (F.coeff n))
  let EG := P.comp ((LinearMap.applyₗ v).comp (G.coeff n))
  change EF b = EG b
  rw [← hsum]
  simp only [map_sum]
  exact Finset.sum_congr rfl (fun h _ => hom h (part h) (gradeProjection_mem D h b.val))

/-- The top coefficient map of Abe's Proposition 2.10 on the actual Leech
odd source and either of the two parity-changing twisted fields. -/
theorem leech_twistedZhuTopReadout_injective (s : Bool) :
    Function.Injective (fun F : LawfulMixedField leechData leechUnit s =>
      fun (h : ℤ) (b : {b : OddCarrier leechData // b.val ∈ grade leechData h})
          (v : twistedTop leechData leechUnit s) =>
        twistedTopReadout leechData leechUnit (!s)
          (F.coeff (twistedTopZhuIndex s h) b.val v.val)) := by
  intro F G h
  apply eq_of_twistedZhuTopReadout_agreement (by rw [leech_spec.1]; decide) F G
  intro w b v hb hv
  exact congrFun (congrFun (congrFun h w) ⟨b, hb⟩) ⟨v, hv⟩

end

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
