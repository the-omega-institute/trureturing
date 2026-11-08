/- GID: D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalSquare
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/ChangShrockToroidalSquare
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The native square degree L-1 block has eigenvalue v^(L-1)(v+q). -/

import D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalHoneycomb

/-!
admission_basis: open-problem-resolution (#28163; Proved)
escape_witness: none
direct_frozen_dependencies:
- D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalHoneycomb.Coeff
  statement_id: sha256:20465d7d4af54a92d7067d6a7e01b5f4bdf39360cc8143d1bbf24964d06bbb96
- D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalHoneycomb.Space
  statement_id: sha256:d665753ec343d17c78c4d50abae921ab7048cf1a297d42452e50944d4f6e4e55
- D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalHoneycomb.q
  statement_id: sha256:689e6df848f33061c26495c929b7fb13f9f372d7b6745a3da9e10a1ab585d1f9
- D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalHoneycomb.v
  statement_id: sha256:b72e0f66f5569b6fbb369b66e80ddebf4ce8f524acd2f2036998ecc3be6ec05b
- D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalHoneycomb.join
  statement_id: sha256:e08a52a19c5848952ad0509730c9d24146e16b1dbf46654c23808592d5edc610
- D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalHoneycomb.vertical
  statement_id: sha256:483507654614a243ef20ca72267969ac55ea266703d7bff10f48eaaba73f8db5
- D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalHoneycomb.alternatingVector
  statement_id: sha256:7ff0f4d30b86c3e718508cb98deff663f3f341688263adf3ef97c753d66ad7ae
- D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalHoneycomb.alternatingVector_ne_zero
  statement_id: sha256:860d6724b50477471b3a050811de1914667acfc28059261b1163b5296728387d
- D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalHoneycomb.join_alternating
  statement_id: sha256:584e79dab52e9beeeeacd68f0d123385a97c0984970ce67c16eaf4c609f84b4d
- D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalHoneycomb.list_prod_on_vector
  statement_id: sha256:2b40b621872f364f22ed00defd99dc238a75cd36a445a088a21a4b6a447ce937
- D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalHoneycomb.vertical_alternating
  statement_id: sha256:4f49a034aac8180ab39aab39fffd1922eeea8d7cad84e14359d1cee12bfa5e92
horizontal: proof_shape=definition; consumers=transfer,result
transfer: proof_shape=definition; consumers=result
result: proof_shape=bind-only; consumers=registered claim #28163
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalSquare

open D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalHoneycomb

noncomputable section

/-- All cyclic bonds of equation (2.34), including the seam and both width-two bonds. -/
def horizontal (L : ℕ) [NeZero L] : Module.End Coeff (Space L) :=
  (List.ofFn fun i : Fin L =>
    (1 : Module.End Coeff (Space L)) + v • join i (Fin.ofNat L (i.val + 1))).prod

/-- The native degree L-1 square transfer operator T = VH of equation (2.35). -/
def transfer (L : ℕ) [NeZero L] : Module.End Coeff (Space L) :=
  vertical L * horizontal L

/-- Every square width at least two has the source eigenvalue in the native degree L-1 block. -/
theorem result (L : ℕ) (hL : 2 ≤ L) :
    letI : NeZero L := ⟨by omega⟩
    ∃ w : Space L, w ≠ 0 ∧ transfer L w = (v ^ (L - 1) * (v + q)) • w := by
  classical
  let : NeZero L := ⟨by omega⟩
  refine ⟨alternatingVector L, alternatingVector_ne_zero, ?_⟩
  have hne (i : Fin L) : i ≠ Fin.ofNat L (i.val + 1) := by
    intro h
    have hh := congrArg Fin.val h
    change i.val = (i.val + 1) % L at hh
    by_cases hi : i.val + 1 < L
    · rw [Nat.mod_eq_of_lt hi] at hh
      omega
    · have hiL : i.val + 1 = L := by omega
      rw [hiL, Nat.mod_self] at hh
      omega
  have hh := list_prod_on_vector (List.finRange L)
    (fun i => (1 : Module.End Coeff (Space L)) + v • join i (Fin.ofNat L (i.val + 1)))
    (fun _ => (1 : Coeff)) (alternatingVector L) (by
      intro i _
      change alternatingVector L + v • join i _ (alternatingVector L) = _
      rw [join_alternating _ _ (hne i)]
      simp)
  have hH : horizontal L (alternatingVector L) = alternatingVector L := by
    simpa [← List.ofFn_eq_map, horizontal] using hh
  simpa only [transfer, Module.End.mul_apply, hH] using (vertical_alternating (L := L))

end
end D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalSquare
