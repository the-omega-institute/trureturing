/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeSameParityZhuTopBalance
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeSameParityZhuTopBalance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Zhu residues of integral mixed coefficients on the actual same-parity twisted tops. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddZhuTopBalance

/-!
The integral fixed-module coefficient identities in Abe, arXiv:math/9907120v1,
§2 and §4.2, with the actual fixed actions on the two twisted legs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

open scoped BigOperators DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParity

open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeInvolution
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockGradedTrace
open HalfFock.LatticeHalfFockParityField (fixedParitySlice paritySpace)
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open StateFieldResidueReconstruction (integerBinomial)
open NativeOddTwistedIntertwiner (OddCarrier Twisted paritySign oddMode oddTranslation
  twistedTop twistedTopGrade twistedTopReadout fixedAction fixedTopZero oddZhuResidue)
open private zeroSignedFinsum stress stress_action stress_odd_zero stress_odd_one
    ambientGradeReadout_self lowering_kills_top topReadout_raising_zero
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTopDetection
open private oddPart oddPart_grade oddPart_on_odd oddResidue_finite
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddZhuTopBalance

noncomputable section

/-- Physical integral mode n has doubled-coordinate exponent -2*n-2. -/
abbrev Coefficients (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool) :=
  ℤ → OddCarrier D →ₗ[ℂ] Twisted D hu s →ₗ[ℂ] Twisted D hu s

/-- The full signed coefficient identity with the native fixed action on each leg. -/
def signedBorcherds (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (F : Coefficients D hu s)
    (a : FixedCarrier D) (b : OddCarrier D) (v : Twisted D hu s) (p q r : ℤ) : Prop :=
  let ρ := fun (t : Bool) (m : ℤ) => (fixedParitySlice D hu (paritySign t) a)[[m]]
  let left := fun i : ℕ => integerBinomial p i • F (p+q-i) (oddMode D a (r+i) b) v
  let first := fun i : ℕ => (((-1 : ℂ)^i)*integerBinomial r i) •
    ρ s (p+r-i) (F (q+i) b v)
  let second := fun i : ℕ => (((-1 : ℂ)^i)*integerBinomial r i) •
    (StateFieldResidueReconstruction.epsilon r • F (q+r-i) b (ρ s (p+i) v))
  Function.HasFiniteSupport left ∧ Function.HasFiniteSupport first ∧
    Function.HasFiniteSupport second ∧
    (∑ᶠ i, left i) = (∑ᶠ i, first i) - (∑ᶠ i, second i)

/-- Arbitrary lower-truncated mixed fields with physical translation and the full
signed Jacobi law relative to the actual fixed lattice algebra. -/
structure LawfulField (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool) where
  coeff : Coefficients D hu s
  truncation : ∀ b v, ∃ N : ℤ, ∀ n ≥ N, coeff n b v = 0
  derivative : ∀ (b : OddCarrier D) (v : Twisted D hu s) (n : ℤ),
    coeff n (oddTranslation D b) v = (-(n : ℂ)) • coeff (n-1) b v
  borcherds : ∀ a b v p q r, signedBorcherds D hu s coeff a b v p q r

variable {D : LatticeData} {hu : IsUnit D.G.det} {s : Bool}

local instance (D : LatticeData) (hu : IsUnit D.G.det) (t : Bool) :
    AddCommGroup (twistedTop D hu t) :=
  @Submodule.addCommGroup ℂ (Twisted D hu t) _ _ _ (twistedTop D hu t)

/-- Equal top energies select the physical mode h - 1. -/
def topIndex (h : ℤ) : ℤ := h - 1

theorem mixed_commutator (F : LawfulField D hu s) (a : FixedCarrier D)
    (b : OddCarrier D) (v : Twisted D hu s) (p q : ℤ) :
    let term := fun i : ℕ => integerBinomial p i •
      F.coeff (p+q-i) (oddMode D a i b) v
    Function.HasFiniteSupport term ∧
      (∑ᶠ i, term i) =
        fixedAction s a p (F.coeff q b v) - F.coeff q b (fixedAction s a p v) := by
  have law := F.borcherds a b v p q 0
  unfold signedBorcherds at law
  dsimp only at law ⊢
  refine ⟨by simpa only [zero_add] using law.1, ?_⟩
  have h := law.2.2.2
  let first (i : ℕ) := fixedAction s a (p+0-i) (F.coeff (q+i) b v)
  let second (i : ℕ) := StateFieldResidueReconstruction.epsilon 0 •
    F.coeff (q+0-i) b (fixedAction s a (p+i) v)
  change (∑ᶠ i : ℕ, integerBinomial p i • F.coeff (p+q-i) (oddMode D a (0+i) b) v) =
    (∑ᶠ i : ℕ, (((-1 : ℂ)^i) * integerBinomial 0 i) • first i) -
    (∑ᶠ i : ℕ, (((-1 : ℂ)^i) * integerBinomial 0 i) • second i) at h
  rw [zeroSignedFinsum first, zeroSignedFinsum second] at h
  simpa only [first, second, StateFieldResidueReconstruction.epsilon, zpow_zero,
    one_smul, Nat.cast_zero, add_zero, zero_add, sub_zero] using h

private theorem mixed_commutator_one (F : LawfulField D hu s) (a : FixedCarrier D)
    (b : OddCarrier D) (v : Twisted D hu s) (n : ℤ) :
    fixedAction s a 1 (F.coeff n b v) - F.coeff n b (fixedAction s a 1 v) =
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
theorem signed_grade (F : LawfulField D hu s) (n h : ℤ)
    (M : ℕ) (b : OddCarrier D) (v : Twisted D hu s) (hb : b.val ∈ grade D h)
    (hv : v.val ∈ actualGrade D hu M) :
    let x := (F.coeff n b v).val
    actualTensorL0 D hu x =
      ((D.rank : ℂ) / 16 + (((M : ℤ) + 2*h - 2*n - 2 : ℤ) : ℂ) / 2) • x := by
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
  have h := congrArg (fun w : Twisted D hu s => w.val) hcomm
  simp only [stress_action, Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul] at h
  dsimp only
  rw [sub_eq_iff_eq_add] at h
  rw [h, ← add_smul, ← add_smul]
  congr 1
  push_cast
  ring

private theorem selected_mode_mem_top (F : LawfulField D hu s) (h : ℤ)
    (b : OddCarrier D) (hb : b.val ∈ grade D h) (v : twistedTop D hu s) :
    F.coeff (topIndex h) b v.val ∈ twistedTop D hu s := by
  have he := signed_grade F (topIndex h) h
    (twistedTopGrade s) b v.val hb v.property
  have hi : (twistedTopGrade s : ℤ) + 2*h - 2*topIndex h - 2 =
      (twistedTopGrade s : ℤ) := by
    simp only [topIndex]
    omega
  simpa only [twistedTop, Submodule.mem_comap, actualGrade, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero,
    Submodule.subtype_apply, hi, Int.cast_natCast] using he

private def homogeneousTopEvaluation (F : LawfulField D hu s) (v : twistedTop D hu s)
    (h : ℤ) : grade D h →ₗ[ℂ] twistedTop D hu s :=
  LinearMap.codRestrict _ (((LinearMap.applyₗ v.val).comp (F.coeff (topIndex h))).comp
      ((oddPart D).comp (grade D h).subtype))
    (fun b => selected_mode_mem_top F h (oddPart D b.val) (oddPart_grade h b) v)

/-- The degree-wise selected coefficient, extended linearly over the actual energy direct sum. -/
def zhuTopEvaluation (F : LawfulField D hu s) (v : twistedTop D hu s) :
    OddCarrier D →ₗ[ℂ] twistedTop D hu s :=
  (DirectSum.toModule ℂ ℤ (twistedTop D hu s) (homogeneousTopEvaluation F v)).comp
    ((carrierEnergyDecomposition D).toLinearMap.comp (minusSpace D).subtype)

/-- This is the same homogeneous coefficient used by the top detector. -/
theorem zhuTopEvaluation_homogeneous (F : LawfulField D hu s) (v : twistedTop D hu s)
    (h : ℤ) (b : OddCarrier D) (hb : b.val ∈ grade D h) :
    (zhuTopEvaluation F v b).val = F.coeff (topIndex h) b v.val := by
  have he : carrierEnergyDecomposition D b.val =
      DirectSum.lof ℂ ℤ (fun n => grade D n) h ⟨b.val, hb⟩ := by
    apply (carrierEnergyDecomposition D).symm.injective
    rw [LinearEquiv.symm_apply_apply]
    change b.val = DirectSum.coeLinearMap (grade D) (DirectSum.lof ℂ ℤ (fun n => grade D n) h ⟨b.val, hb⟩)
    rw [DirectSum.coeLinearMap_lof]
  change (DirectSum.toModule ℂ ℤ (twistedTop D hu s) (homogeneousTopEvaluation F v)
    (carrierEnergyDecomposition D b.val)).val = _
  rw [he, DirectSum.toModule_lof]
  change F.coeff (topIndex h) (oddPart D b.val) v.val = _
  rw [oddPart_on_odd]

private theorem readout_on_top (t : Bool) (v : twistedTop D hu t) :
    twistedTopReadout D hu t v.val = v.val.val :=
  ambientGradeReadout_self _ _ v.property

/-- Project the signed Jacobi identity in the range where the ordered products can
contribute only their term at index zero. The sign in front of the input action
is `-ε(r)`. -/
theorem zhuTopEvaluation_residue (F : LawfulField D hu s)
    (a : FixedCarrier D) (b : OddCarrier D) (v : twistedTop D hu s)
    (d : ℕ) (h p r : ℤ) (ha : a.val ∈ grade D (d : ℤ)) (hb : b.val ∈ grade D h)
    (hp : (d : ℤ)-1 ≤ p) (hr : p+r ≤ (d : ℤ)-1) :
    zhuTopEvaluation F v (oddZhuResidue a b p r) =
      ((if p+r = (d : ℤ)-1 then fixedTopZero s a d ha (zhuTopEvaluation F v b) else 0) -
        (if p = (d : ℤ)-1 then StateFieldResidueReconstruction.epsilon r •
          zhuTopEvaluation F (fixedTopZero s a d ha v) b else 0) : twistedTop D hu s) := by
  classical
  let k := topIndex h
  let q := k+(d : ℤ)-p-r-1
  let P := twistedTopReadout D hu s
  let A := (paritySpace D hu (paritySign s)).subtype.comp (twistedTop D hu s).subtype
  let left (i : ℕ) := integerBinomial p i • F.coeff (p+q-i) (oddMode D a (r+i) b) v.val
  let first (i : ℕ) := (((-1 : ℂ)^i)*integerBinomial r i) •
    fixedAction s a (p+r-i) (F.coeff (q+i) b v.val)
  let second (i : ℕ) := (((-1 : ℂ)^i)*integerBinomial r i) •
    (StateFieldResidueReconstruction.epsilon r • F.coeff (q+r-i) b (fixedAction s a (p+i) v.val))
  have law := F.borcherds a b v.val p q r
  change Function.HasFiniteSupport left ∧ Function.HasFiniteSupport first ∧
    Function.HasFiniteSupport second ∧
      (∑ᶠ i, left i) = (∑ᶠ i, first i) - (∑ᶠ i, second i) at law
  have hj := congrArg P law.2.2.2
  change P (∑ᶠ i, left i) = P ((∑ᶠ i, first i) - (∑ᶠ i, second i)) at hj
  rw [map_sub P, map_finsum P law.1, map_finsum P law.2.1, map_finsum P law.2.2.1] at hj
  have hleft :
      A (zhuTopEvaluation F v (oddZhuResidue a b p r)) = ∑ᶠ i, P (left i) := by
    change (A.comp (zhuTopEvaluation F v)) (oddZhuResidue a b p r) = _
    rw [oddZhuResidue, map_finsum _ (oddResidue_finite a b p r)]
    congr 1
    funext i
    let w := (d : ℤ)+h-(r+i)-1
    have hg : (oddMode D a (r+i) b).val ∈ grade D w :=
      actual_mode_grade D (actualInverse D) (actualInverse_left D hu)
        (actualInverse_right D hu) (d : ℤ) h (r+i) a.val b.val ha hb
    have hi : topIndex w = p+q-i := by
      simp only [w, q, k, topIndex]
      omega
    simp only [left, map_smul, LinearMap.comp_apply]
    congr 1
    rw [show A (zhuTopEvaluation F v (oddMode D a (r+i) b)) =
        P (zhuTopEvaluation F v (oddMode D a (r+i) b)).val from (readout_on_top _ _).symm,
      zhuTopEvaluation_homogeneous F v w _ hg, hi]
  have hfirst : (∑ᶠ i, P (first i)) = A
      (if p+r = (d : ℤ)-1 then fixedTopZero s a d ha (zhuTopEvaluation F v b) else 0) := by
    rw [finsum_eq_single _ 0]
    · by_cases he : p+r = (d : ℤ)-1
      · have hq : q = k := by dsimp [q]; omega
        rw [ite_eq_left he]
        let u := zhuTopEvaluation F v b
        let weightZero := (d : ℤ) - 1
        have hfirst0 : first 0 = fixedAction s a weightZero (F.coeff k b v.val) := by
          simp only [first, Nat.cast_zero, sub_zero, add_zero, pow_zero, one_mul,
            integerBinomial, Ring.choose_zero_right, Int.cast_one, one_smul, hq, he, weightZero]
        have huval : u.val = F.coeff k b v.val := zhuTopEvaluation_homogeneous F v h b hb
        rw [hfirst0, ← huval]
        exact readout_on_top s (fixedTopZero s a d ha u)
      · rw [ite_eq_right he, map_zero]
        simp only [first, Nat.cast_zero, sub_zero, add_zero, map_smul]
        rw [topReadout_raising_zero a (d : ℤ) _ ha (by omega), smul_zero]
    · intro i hi
      simp only [first, map_smul]
      rw [topReadout_raising_zero a (d : ℤ) _ ha (by omega), smul_zero]
  have hsecond : (∑ᶠ i, P (second i)) = A
      (if p = (d : ℤ)-1 then StateFieldResidueReconstruction.epsilon r •
        zhuTopEvaluation F (fixedTopZero s a d ha v) b else 0) := by
    rw [finsum_eq_single _ 0]
    · by_cases he : p = (d : ℤ)-1
      · have hq : q+r = k := by dsimp [q]; omega
        rw [ite_eq_left he]
        let u := fixedTopZero s a d ha v
        have hsecond0 : second 0 = StateFieldResidueReconstruction.epsilon r • F.coeff k b u.val := by
          simp only [second, Nat.cast_zero, sub_zero, add_zero, pow_zero, one_mul,
            integerBinomial, Ring.choose_zero_right, Int.cast_one, one_smul, hq, he]
          rfl
        have huz : (zhuTopEvaluation F u b).val = F.coeff k b u.val :=
          zhuTopEvaluation_homogeneous F u h b hb
        rw [hsecond0, map_smul P, map_smul A, ← huz]
        exact congrArg (fun w : ActualTensor D hu => StateFieldResidueReconstruction.epsilon r • w)
          (readout_on_top s (zhuTopEvaluation F u b))
      · rw [ite_eq_right he, map_zero]
        simp only [second, Nat.cast_zero, sub_zero, add_zero]
        rw [lowering_kills_top a (d : ℤ) p ha (by omega) v.val v.property]
        simp
    · intro i hi
      simp only [second]
      rw [lowering_kills_top a (d : ℤ) (p+i) ha (by omega) v.val v.property]
      simp
  have hinj : Function.Injective A := fun _ _ e => Subtype.ext (Subtype.ext e)
  apply hinj
  rw [map_sub A, hleft, hj, hfirst, hsecond]

/-- The two star actions and the circle relation for the actual odd source.
The three choices of `(p,r)` are `(d,-1)`, `(d-1,-1)`, and `(d,-2)`. -/
theorem zhuTopEvaluation_balanced (F : LawfulField D hu s)
    (a : FixedCarrier D) (b : OddCarrier D) (v : twistedTop D hu s)
    (d : ℕ) (h : ℤ) (ha : a.val ∈ grade D (d : ℤ)) (hb : b.val ∈ grade D h) :
    zhuTopEvaluation F v (oddZhuResidue a b d (-1)) =
        fixedTopZero s a d ha (zhuTopEvaluation F v b) ∧
    zhuTopEvaluation F v (oddZhuResidue a b ((d : ℤ)-1) (-1)) =
        zhuTopEvaluation F (fixedTopZero s a d ha v) b ∧
    zhuTopEvaluation F v (oddZhuResidue a b d (-2)) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [zhuTopEvaluation_residue F a b v d h d (-1) ha hb (by omega) (by omega),
      ite_eq_left (show (d : ℤ) + (-1) = (d : ℤ) - 1 by omega),
      ite_eq_right (show (d : ℤ) ≠ (d : ℤ) - 1 by omega)]
    exact sub_zero (fixedTopZero s a d ha (zhuTopEvaluation F v b))
  · rw [zhuTopEvaluation_residue F a b v d h ((d : ℤ)-1) (-1) ha hb (by omega) (by omega),
      ite_eq_right (show (d : ℤ) - 1 + (-1) ≠ (d : ℤ) - 1 by omega), ite_eq_left rfl]
    have heps : StateFieldResidueReconstruction.epsilon (-1) = -1 := by
      norm_num [StateFieldResidueReconstruction.epsilon]
    rw [heps]
    let u := zhuTopEvaluation F (fixedTopZero s a d ha v) b
    change 0 - (-1 : ℂ) • u = u
    rw [neg_one_smul ℂ u, zero_sub (-u), neg_neg]
  · rw [zhuTopEvaluation_residue F a b v d h d (-2) ha hb (by omega) (by omega),
      ite_eq_right (show (d : ℤ) + (-2) ≠ (d : ℤ) - 1 by omega),
      ite_eq_right (show (d : ℤ) ≠ (d : ℤ) - 1 by omega)]
    exact sub_self (0 : twistedTop D hu s)

end
end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParity
