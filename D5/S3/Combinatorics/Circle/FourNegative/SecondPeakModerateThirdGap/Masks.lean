/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakModerateThirdGap/Masks
   digest: native U-transfer and shifted W partition at the original physical offsets. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.NativeMasks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakModerateThirdGap
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private MaskPartition native_partition partition_labels
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.NativeMasks

private def uFull (d : ℕ) : ℕ := 2^(d-1)-1
private def uRest (d u : ℕ) : ℕ := uFull d ^^^ u

private theorem u_capacity (d u : ℕ) (hd : 3 ≤ d) (hu : u=0 ∨ u=1 ∨ u=2) :
    u < 2^(d-1) := by
  have hp : 4 ≤ 2^(d-1) := by
    simpa using Nat.pow_le_pow_right (by decide : 0<2) (by omega : 2≤d-1)
  rcases hu with rfl|rfl|rfl <;> omega

private theorem uRest_eq (d u : ℕ) (hd : 3 ≤ d) (hu : u=0 ∨ u=1 ∨ u=2) :
    uRest d u = 2^(d-1)-1-u := by
  have hc := u_capacity d u hd hu
  have h := (native_partition (d-1) 0 u (by omega)).1
  have he : ((2^(d-1)-1) ^^^ u)+u=2^(d-1)-1 := by simpa using h
  dsimp [uRest,uFull]
  omega

private theorem u_native_partition (d u : ℕ) (hd : 3 ≤ d) (hu : u=0 ∨ u=1 ∨ u=2) :
    (chamberLabels (d-1) 0 (uRest d u) ++
      chamberLabels (d-1) 0 u).Perm (List.range' 0 (d-1)) := by
  have hc := u_capacity d u hd hu
  have h := native_partition (d-1) 0 u (by omega)
  have hp := partition_labels (d-1) 0 u ((2^(d-1)-1) ^^^ u) 0
    (by simpa using h.2)
  have hz (len off : ℕ) : chamberLabels len off 0=[] := by
    simp [chamberLabels,labels]
  simp only [hz,List.append_nil] at hp
  simpa only [uRest,uFull] using ((List.perm_append_comm _ _).trans hp)

/-- The length equation is a hypothesis; the physical offset is independent of it. -/
private theorem shifted_partition (b c off H : ℕ) (hcb : c < b) (hH : H < 2^c) :
    (chamberLabels (b-1) off ((2^(b-c-1))*H) ++
      chamberLabels (b-1) off ((2^(b-c-1))*(2^c-1-H)) ++
      chamberLabels (b-1) off (2^(b-c-1)-1)).Perm (List.range' off (b-1)) := by
  let s := b-c-1
  have hlen : c+s=b-1 := by dsimp [s]; omega
  have hn := native_partition c s H (by omega)
  have hf : 2^s*(2^c-1-H)+2^s*H=(2^c-1)*2^s := by
    rw [←Nat.mul_add,Nat.sub_add_cancel (by omega)]
    exact Nat.mul_comm _ _
  have hq : ((2^c-1)*2^s) ^^^ (2^s*H)=2^s*(2^c-1-H) := by
    have he := hn.1
    dsimp only at he
    omega
  have hp := partition_labels (c+s) off (2^s*H)
    (((2^c-1)*2^s) ^^^ (2^s*H)) (2^s-1) hn.2
  simpa only [hlen,hq,s] using hp

private theorem shifted_capacities (b c H : ℕ) (hcb : c < b) (hH : H < 2^c) :
    2^(b-c-1)*H < 2^(b-1) ∧
    2^(b-c-1)*(2^c-1-H) < 2^(b-1) ∧
    2^(b-c-1)-1 < 2^(b-1) := by
  have hn := (native_partition c (b-c-1) H (by omega)).2
  have hq : ((2^c-1)*2^(b-c-1)) ^^^ (2^(b-c-1)*H)=
      2^(b-c-1)*(2^c-1-H) := by
    have he := (native_partition c (b-c-1) H (by omega)).1
    have hf : 2^(b-c-1)*(2^c-1-H)+2^(b-c-1)*H=(2^c-1)*2^(b-c-1) := by
      rw [←Nat.mul_add,Nat.sub_add_cancel (by omega)]
      exact Nat.mul_comm _ _
    dsimp only at he
    omega
  have hlen : c+(b-c-1)=b-1 := by omega
  exact ⟨by simpa only [hlen] using hn.hcap,
    by simpa only [hlen,hq] using hn.qcap,
    by simpa only [hlen] using hn.lowcap⟩

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakModerateThirdGap
