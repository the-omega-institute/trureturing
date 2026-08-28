/- GID: D5/S3/Factorization/PrimePowers/CompatibleResidueJointImage
   generality: G
   mirror-B: D5/B/S3/Factorization/PrimePowers/CompatibleResidueJointImage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compatible residue images are strict exactly for noncoprime arbitrary moduli. -/

/- Library-search audit trail (2026-08-25):
   * Exact pinned-Mathlib hit `Nat.chineseRemainder'` constructs a simultaneous
     representative from equality modulo `gcd m n`; it is applied directly.
   * `ZMod.intCast_zmod_cast` identifies each chosen integer representative with
     its residue class, so both coordinates can be compared in `ZMod (gcd m n)`.
   * Current-tree `FiniteCrtJoin` handles pairwise-coprime prime powers, where the
     compatibility constraint is trivial; it does not state the noncoprime image.
   * `BoundedIntegerCrtCompleteness` concerns injectivity on `Fin N`, not the image
     of the integer readout. No current module gives this compatible-pair equality. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.PrimePowers.CompatibleResidueJointImage

/-- The integer readout in one residue factor. For modulus zero this is the identity on
integers; for modulus one it is the constant readout into the trivial factor. -/
def localResidueReadout (modulus : Nat) : Int -> ZMod modulus :=
  fun x => x

/-- The simultaneous readout into two local residue factors. -/
def jointResidueReadout (m n : Nat) : Int -> ZMod m × ZMod n :=
  fun x => (localResidueReadout m x, localResidueReadout n x)

/-- The jointly realizable pairs of local residue states. -/
def jointResidueImage (m n : Nat) : Set (ZMod m × ZMod n) :=
  Set.range (jointResidueReadout m n)

/-- The subobject cut out by agreement after both coordinates are reduced to their gcd. -/
def compatibleResiduePairs (m n : Nat) : Set (ZMod m × ZMod n) :=
  {pair |
    ((ZMod.cast pair.1 : Int) : ZMod (Nat.gcd m n)) =
      ((ZMod.cast pair.2 : Int) : ZMod (Nat.gcd m n))}

/-- Realization independence means that every freely chosen pair of local states is joint. -/
def ResidueRealizationIndependent (m n : Nat) : Prop :=
  Function.Surjective (jointResidueReadout m n)

/-- The joint image is exactly the pairs agreeing over the common gcd modulus. This holds
for arbitrary natural moduli; no positivity or primality assumption is used. -/
theorem joint_residue_image_eq_compatible_pairs (m n : Nat) :
    jointResidueImage m n = compatibleResiduePairs m n := by
  ext pair
  constructor
  · rintro ⟨x, rfl⟩
    change
      ((ZMod.cast (x : ZMod m) : Int) : ZMod (Nat.gcd m n)) =
        ((ZMod.cast (x : ZMod n) : Int) : ZMod (Nat.gcd m n))
    have hleft :
        ((ZMod.cast (x : ZMod m) : Int) : ZMod (Nat.gcd m n)) =
          (x : ZMod (Nat.gcd m n)) := by
      have hrepresentative := congrArg
        (ZMod.castHom (Nat.gcd_dvd_left m n) (ZMod (Nat.gcd m n)))
        (ZMod.intCast_zmod_cast (x : ZMod m))
      simpa only [map_intCast] using hrepresentative
    have hright :
        ((ZMod.cast (x : ZMod n) : Int) : ZMod (Nat.gcd m n)) =
          (x : ZMod (Nat.gcd m n)) := by
      have hrepresentative := congrArg
        (ZMod.castHom (Nat.gcd_dvd_right m n) (ZMod (Nat.gcd m n)))
        (ZMod.intCast_zmod_cast (x : ZMod n))
      simpa only [map_intCast] using hrepresentative
    exact hleft.trans hright.symm
  · intro hpair
    rcases eq_or_ne m 0 with rfl | hm
    · refine ⟨ZMod.cast pair.1, ?_⟩
      apply Prod.ext
      · exact ZMod.intCast_zmod_cast pair.1
      · have hcompat :
            ((ZMod.cast pair.1 : Int) : ZMod n) =
              ((ZMod.cast pair.2 : Int) : ZMod n) := by
          change
            ((ZMod.cast pair.1 : Int) : ZMod (Nat.gcd 0 n)) =
              ((ZMod.cast pair.2 : Int) : ZMod (Nat.gcd 0 n)) at hpair
          have htransport := congrArg
            (ZMod.ringEquivCongr (Nat.gcd_zero_left n)) hpair
          simpa only [map_intCast] using htransport
        exact hcompat.trans (ZMod.intCast_zmod_cast pair.2)
    · rcases eq_or_ne n 0 with rfl | hn
      · refine ⟨ZMod.cast pair.2, ?_⟩
        apply Prod.ext
        · have hcompat :
              ((ZMod.cast pair.1 : Int) : ZMod m) =
                ((ZMod.cast pair.2 : Int) : ZMod m) := by
            change
              ((ZMod.cast pair.1 : Int) : ZMod (Nat.gcd m 0)) =
                ((ZMod.cast pair.2 : Int) : ZMod (Nat.gcd m 0)) at hpair
            have htransport := congrArg
              (ZMod.ringEquivCongr (Nat.gcd_zero_right m)) hpair
            simpa only [map_intCast] using htransport
          exact hcompat.symm.trans (ZMod.intCast_zmod_cast pair.1)
        · exact ZMod.intCast_zmod_cast pair.2
      · letI : NeZero m := ⟨hm⟩
        letI : NeZero n := ⟨hn⟩
        change
          ((ZMod.cast pair.1 : Int) : ZMod (Nat.gcd m n)) =
            ((ZMod.cast pair.2 : Int) : ZMod (Nat.gcd m n)) at hpair
        have hvals :
            (pair.1.val : ZMod (Nat.gcd m n)) =
              (pair.2.val : ZMod (Nat.gcd m n)) := by
          simpa only [ZMod.cast_eq_val, Int.cast_natCast] using hpair
        have hmod : pair.1.val ≡ pair.2.val [MOD Nat.gcd m n] :=
          (ZMod.natCast_eq_natCast_iff pair.1.val pair.2.val (Nat.gcd m n)).mp hvals
        let x := Nat.chineseRemainder' hmod
        refine ⟨(x : Int), ?_⟩
        apply Prod.ext
        · change ((x : Int) : ZMod m) = pair.1
          calc
            ((x : Int) : ZMod m) = ((x : Nat) : ZMod m) := by
              rw [Int.cast_natCast]
            _ = (pair.1.val : ZMod m) :=
              (ZMod.natCast_eq_natCast_iff x pair.1.val m).mpr x.property.1
            _ = pair.1 := ZMod.natCast_zmod_val pair.1
        · change ((x : Int) : ZMod n) = pair.2
          calc
            ((x : Int) : ZMod n) = ((x : Nat) : ZMod n) := by
              rw [Int.cast_natCast]
            _ = (pair.2.val : ZMod n) :=
              (ZMod.natCast_eq_natCast_iff x pair.2.val n).mpr x.property.2
            _ = pair.2 := ZMod.natCast_zmod_val pair.2

#print axioms joint_residue_image_eq_compatible_pairs

/-- Thus the joint image lies in the direct product and is precisely the subobject selected
by the cross-factor compatibility equation. -/
theorem joint_residue_image_is_compatible_subobject (m n : Nat) :
    jointResidueImage m n ⊆ (Set.univ : Set (ZMod m × ZMod n)) ∧
      jointResidueImage m n = compatibleResiduePairs m n := by
  exact ⟨Set.subset_univ _, joint_residue_image_eq_compatible_pairs m n⟩

#print axioms joint_residue_image_is_compatible_subobject

/-- The compatible image is a strict subset of the free product exactly when the overlap
has more than one residue class. -/
theorem joint_residue_image_ssubset_product_iff (m n : Nat) :
    jointResidueImage m n ⊂ (Set.univ : Set (ZMod m × ZMod n)) ↔
      Nat.gcd m n ≠ 1 := by
  constructor
  · intro hstrict hgcd
    apply (Set.ssubset_univ_iff.mp hstrict)
    rw [joint_residue_image_eq_compatible_pairs]
    apply Set.eq_univ_of_forall
    intro pair
    letI : Subsingleton (ZMod (Nat.gcd m n)) :=
      ZMod.subsingleton_iff.mpr hgcd
    exact Subsingleton.elim _ _
  · intro hgcd
    apply Set.ssubset_univ_iff.mpr
    rw [joint_residue_image_eq_compatible_pairs]
    intro heq
    have hwitness :
        ((0, 1) : ZMod m × ZMod n) ∈ compatibleResiduePairs m n := by
      rw [heq]
      exact Set.mem_univ _
    have hn_one : n ≠ 1 := by
      intro hn
      apply hgcd
      simp [hn]
    have hone_rep : (ZMod.cast (1 : ZMod n) : Int) = 1 := by
      rcases n with _ | n
      · rfl
      · haveI : NeZero (n + 1) := ⟨by omega⟩
        rw [ZMod.cast_eq_val, ZMod.val_one'' hn_one]
        norm_num
    change
      ((ZMod.cast (0 : ZMod m) : Int) : ZMod (Nat.gcd m n)) =
        ((ZMod.cast (1 : ZMod n) : Int) : ZMod (Nat.gcd m n)) at hwitness
    have hone : (1 : ZMod (Nat.gcd m n)) = 0 := by
      rw [ZMod.cast_zero, hone_rep] at hwitness
      simpa only [Int.cast_one, Int.cast_zero] using hwitness.symm
    exact hgcd (ZMod.one_eq_zero_iff.mp hone)

#print axioms joint_residue_image_ssubset_product_iff

/-- Free combination occurs exactly for coprime moduli, including the degenerate coprime
pairs `(0, 1)` and `(1, 0)`. -/
theorem residue_realization_independent_iff_coprime (m n : Nat) :
    ResidueRealizationIndependent m n ↔ Nat.Coprime m n := by
  rw [ResidueRealizationIndependent, ← Set.range_eq_univ]
  rw [Nat.coprime_iff_gcd_eq_one]
  constructor
  · intro himage
    by_contra hgcd
    have hstrict := (joint_residue_image_ssubset_product_iff m n).mpr hgcd
    exact (Set.ssubset_univ_iff.mp hstrict) himage
  · intro hgcd
    by_contra himage
    have hstrict :
        jointResidueImage m n ⊂ (Set.univ : Set (ZMod m × ZMod n)) :=
      Set.ssubset_univ_iff.mpr himage
    exact (joint_residue_image_ssubset_product_iff m n).mp hstrict hgcd

#print axioms residue_realization_independent_iff_coprime

/-- Each modulus-two factor is individually covered, but the pair `(0, 1)` is incompatible.
This is the concrete counterexample to local factorization implying realization independence. -/
theorem local_factorization_does_not_imply_realization_independence :
    Function.Surjective (localResidueReadout 2) ∧
      Function.Surjective (localResidueReadout 2) ∧
      ¬ResidueRealizationIndependent 2 2 := by
  refine ⟨ZMod.intCast_surjective, ZMod.intCast_surjective, ?_⟩
  rw [residue_realization_independent_iff_coprime]
  norm_num

#print axioms local_factorization_does_not_imply_realization_independence

/- Degenerate audit: all local factors are inhabited, so no empty carrier is hidden. -/
example (m n : Nat) : Nonempty (ZMod m) ∧ Nonempty (ZMod n) := by
  exact ⟨inferInstance, inferInstance⟩

/- Coprime factors have no compatibility restriction, hence the image is the full product. -/
example (m n : Nat) (hcoprime : Nat.Coprime m n) :
    jointResidueImage m n = (Set.univ : Set (ZMod m × ZMod n)) := by
  exact Set.range_eq_univ.mpr ((residue_realization_independent_iff_coprime m n).mpr hcoprime)

/- Equal moduli give the diagonal constraint and are independent only for the singleton ring. -/
example (m : Nat) : ResidueRealizationIndependent m m ↔ m = 1 := by
  simp [residue_realization_independent_iff_coprime, Nat.coprime_self]

/- A singleton local factor imposes no restriction, even when the other modulus is zero. -/
example (m : Nat) : ResidueRealizationIndependent m 1 := by
  rw [residue_realization_independent_iff_coprime]
  exact Nat.coprime_one_right m

/- The zero-modulus readout is the identity `Int -> ZMod 0 = Int`. -/
example : localResidueReadout 0 = id := by
  funext x
  rfl

/- The modulus-one readout is the constant zero map into the singleton factor. -/
example : localResidueReadout 1 = fun _ => 0 := by
  funext x
  exact Subsingleton.elim _ _

/- With one zero modulus, independence holds exactly when the other factor is trivial. -/
example (n : Nat) : ResidueRealizationIndependent 0 n ↔ n = 1 := by
  simp [residue_realization_independent_iff_coprime]

/- At `(0, 0)` the joint identity readout has diagonal image in `Int × Int`, hence is strict. -/
example : ¬ResidueRealizationIndependent 0 0 := by
  rw [residue_realization_independent_iff_coprime]
  norm_num

end D5.S3.Factorization.PrimePowers.CompatibleResidueJointImage
