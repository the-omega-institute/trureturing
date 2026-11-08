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
  letI : NeZero L := ⟨by omega⟩
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
