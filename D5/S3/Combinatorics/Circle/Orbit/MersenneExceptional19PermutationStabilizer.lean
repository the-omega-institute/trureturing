/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.GroupTheory.OrderOfElement]
   utility: none
   digest: Exactly 3d-1 literal zero tests force full physical exceptional19 permutation rigidity. -/
/- The sum-of-squares argument and weight separation originate in the supplied
old-layout direct-carry candidate (root SHA256
6ee1ad04e4601d55d1fb6df3be601893c470c279693554b0ed32eda99adadcb3).
The scalar bridge below instead consumes the actual selected reconstruction. -/
import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis.Reconstruction
import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.WeightSeparation

/-! # Full physical permutation rigidity from the actual selected zero tests -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Circle.MersenneExceptional19PermutationStabilizer
open scoped BigOperators
open MersenneExceptional19Stabilizer (degree base seed total place base_facts)
open MersenneExceptional19UpperBasis
  (UpperIndex selectedMask selected_literal_zero SelectedAnnihilates
    actual_selected_upper_reconstruction)
open MersenneExceptional19ZeroLattice (primitive source_eq_scale_primitive)
open private actual_weights_injective actual_weights_no_negative_pair
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.WeightSeparation

/-- Over Q the selected reconstruction is a scalar multiple of the actual
weights. Only the nonzero integer source scale is cancelled. -/
private theorem selected_scalar (r : ℕ) (X : Fin (3*degree r) → ℚ)
    (hX : SelectedAnnihilates r X) :
    ∃ c : ℚ, ∀ i, X i=c*(SourceWidth.actualSource (3*degree r) (seed r) i : ℚ) := by
  let j0 : Fin (degree r) := ⟨0,by dsimp [degree]; omega⟩
  let c : ℚ := (-3 : ℤ) • X (place 0 j0)+(2 : ℤ) • X (place 2 j0)
  let g : ℚ := ((19*((base r : ℤ)-1) : ℤ) : ℚ)
  have hgZ : (19*((base r : ℤ)-1) : ℤ)≠0 := by
    have hB : (4096 : ℤ)≤base r := by exact_mod_cast (base_facts r).1
    omega
  have hg : g≠0 := Int.cast_ne_zero.mpr hgZ
  refine ⟨c/g,?_⟩
  intro i
  have hi : X i=(primitive r i : ℚ)*c := by
    simpa only [c,j0,zsmul_eq_mul] using actual_selected_upper_reconstruction r X hX i
  have hw : (SourceWidth.actualSource (3*degree r) (seed r) i : ℚ)=
      g*(primitive r i : ℚ) := by
    rw [source_eq_scale_primitive,Int.cast_mul]
  rw [hi,hw]
  field_simp [hg]

/-- Each physical selected image sum supplies exactly one reconstruction
relation; injectivity of p justifies Finset.sum_image. -/
private theorem permuted_selected_annihilates (r : ℕ)
    (p : Equiv.Perm (Fin (3*degree r)))
    (hp : ∀ k : UpperIndex r, total r ((selectedMask r k).image p)=0) :
    SelectedAnnihilates r (fun i =>
      (SourceWidth.actualSource (3*degree r) (seed r) (p i) : ℚ)) := by
  classical
  intro k
  have hz := hp k
  unfold total at hz
  rw [Finset.sum_image] at hz
  · have hq := congrArg (fun z : ℤ => (z : ℚ)) hz
    simpa only [Int.cast_sum,Int.cast_zero] using hq
  · intro i hi j hj hij
    exact p.injective hij

private theorem selected_rigidity (r : ℕ) (p : Equiv.Perm (Fin (3*degree r)))
    (hp : ∀ k : UpperIndex r, total r ((selectedMask r k).image p)=0) : p=1 := by
  classical
  let w : Fin (3*degree r) → ℚ := fun i =>
    (SourceWidth.actualSource (3*degree r) (seed r) i : ℚ)
  obtain ⟨c,hc⟩ := selected_scalar r (fun i => w (p i))
    (permuted_selected_annihilates r p hp)
  change ∀ i, w (p i)=c*w i at hc
  let i0 : Fin (3*degree r) := ⟨0,by dsimp [degree]; omega⟩
  have hw0 : w i0≠0 := by
    intro h
    have hz : SourceWidth.actualSource (3*degree r) (seed r) i0=0 := by
      exact Int.cast_eq_zero.mp h
    apply actual_weights_no_negative_pair r i0 i0
    simp [hz]
  let S : ℚ := ∑ i : Fin (3*degree r), (w i)^2
  have hS : 0<S := by
    have hle : (w i0)^2≤S := by
      exact Finset.single_le_sum (fun i _ => sq_nonneg (w i)) (Finset.mem_univ i0)
    exact lt_of_lt_of_le (sq_pos_of_ne_zero hw0) hle
  have hperm : (∑ i : Fin (3*degree r), (w (p i))^2)=S := by
    exact Equiv.sum_comp p (fun i => (w i)^2)
  have hscale : (∑ i : Fin (3*degree r), (w (p i))^2)=c^2*S := by
    simp_rw [hc, mul_pow]
    rw [← Finset.mul_sum]
  have heq : c^2*S=1*S := by simpa using hscale.symm.trans hperm
  have hsq : c^2=1 := mul_right_cancel₀ (ne_of_gt hS) heq
  have hfactor : (c-1)*(c+1)=0 := by nlinarith only [hsq]
  rcases mul_eq_zero.mp hfactor with hplus | hminus
  · have hc1 : c=1 := by linarith
    apply Equiv.ext
    intro i
    have hw : w (p i)=w i := by simpa [hc1] using hc i
    have hi : SourceWidth.actualSource (3*degree r) (seed r) (p i)=
        SourceWidth.actualSource (3*degree r) (seed r) i := Int.cast_injective hw
    simpa only [Equiv.Perm.one_apply] using actual_weights_injective r hi
  · have hcneg : c= -1 := by linarith
    have hw : w (p i0)= -w i0 := by simpa [hcneg] using hc i0
    have hi : SourceWidth.actualSource (3*degree r) (seed r) (p i0)=
        -SourceWidth.actualSource (3*degree r) (seed r) i0 := Int.cast_injective (by simpa only [Int.cast_neg] using hw)
    exact False.elim (actual_weights_no_negative_pair r (p i0) i0 hi)

/-- For every natural r, the images of exactly 3d-1 actual selected masks
being literal integer-zero already force the full physical permutation to be
identity. No invariance or permutation of the selected family is assumed. -/
theorem actual_selected_image_zero_perm_iff (r : ℕ)
    (p : Equiv.Perm (Fin (3*(18*r+12)))) :
    (∀ k : UpperIndex r,
      (∑ i ∈ (selectedMask r k).image p,
        SourceWidth.actualSource (3*(18*r+12))
          ((2^(18*r+12)-1)*(2^((18*r+12)+1)-3)) i)=0) ↔ p=1 := by
  constructor
  · intro hp
    exact selected_rigidity r p hp
  · intro hp
    subst p
    intro k
    simpa only [Equiv.Perm.coe_one,Finset.image_id] using selected_literal_zero r k

/-- The full literal integer-zero family on the original physical labels has
trivial permutation stabilizer for all r, including r=0. -/
theorem actual_zero_family_perm_iff (r : ℕ)
    (p : Equiv.Perm (Fin (3*(18*r+12)))) :
    (∀ A : Finset (Fin (3*(18*r+12))),
      (∑ i ∈ A.image p,
        SourceWidth.actualSource (3*(18*r+12))
          ((2^(18*r+12)-1)*(2^((18*r+12)+1)-3)) i)=0 ↔
      (∑ i ∈ A,
        SourceWidth.actualSource (3*(18*r+12))
          ((2^(18*r+12)-1)*(2^((18*r+12)+1)-3)) i)=0) ↔ p=1 := by
  constructor
  · intro hp
    apply (actual_selected_image_zero_perm_iff r p).mp
    intro k
    exact (hp (selectedMask r k)).mpr (selected_literal_zero r k)
  · intro hp
    subst p
    intro A
    simp

end D5.S3.Combinatorics.Circle.MersenneExceptional19PermutationStabilizer
