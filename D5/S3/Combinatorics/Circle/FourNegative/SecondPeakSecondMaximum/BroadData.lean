/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakSecondMaximum/BroadData
   generality: I
   mirror-B: none(waiver:private-consumed-physical-certificate)
   mirror-E: none(waiver:private-consumed-physical-certificate)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Numerical windows and physical label banks for the reversed-middle certificate. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Masks
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakSecondMaximum
open SourceWidth PeriodicShortening RunFirstEarTransport
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
open private sourceMod charge nextBase nextNewBase chain_values new_base_bounds from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (size base newBase oldValue newValue negatives chainLength chainStart weightedMask packet_masses)
open private oldMass newMass from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
open private DataCertificate DataCertificate.mk finiteChecks finiteEarChecks from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Certificate
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (orderedPackets)
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (blocksWord)
open private native_masses
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native

private structure Values where
  z : ℤ
  w : ℤ
  r : ℤ
  q : ℤ
  x : ℤ
  y : ℤ
  H : ℤ
  S : ℤ
  A : ℤ
  B : ℤ
  L : ℤ
  K : ℤ
  SU : ℤ
  SV : ℤ
  SW : ℤ
  D : ℤ
  Dp : ℤ
  E : ℤ
  F : ℤ
  J : ℤ

private def values (z w r q : ℤ) : Values :=
  let x := r*w
  let y := q*x
  let H := 1+y+y*z
  let S := 1+x+x*y
  let A := 1+x*H
  let B := 1+w*S
  let L := 1+z+w*z+w*x*z
  let K := H+w*y*z
  let SU := 2*B-1
  let SV := 2*L-1-z
  let SW := 2*K-H
  let D := K-q*L
  let Dp := SW-q*SV
  let E := B+D-r*K
  let F := SU+Dp-r*SW
  let J := F-2*E
  ⟨z,w,r,q,x,y,H,S,A,B,L,K,SU,SV,SW,D,Dp,E,F,J⟩

set_option maxHeartbeats 2400000 in
private theorem broad_windows (z w r q : ℤ)
    (hz : 4 ≤ z) (hw : 4*z ≤ w) (hr : 2 ≤ r) (hq : 1 ≤ q) :
    let V := values z w r q
    0 < V.Dp ∧ V.Dp < V.D ∧ V.D < V.H ∧
    2*V.H ≤ V.K-1 ∧ 2*V.H ≤ V.SW-1 ∧ 2*V.H ≤ V.A-1 ∧
    0 < V.E ∧ 2*V.E < V.w*V.A ∧ 0 < V.F ∧
    0 < V.J ∧ V.J < V.A ∧ V.B > 3*V.A ∧ 4*V.S < V.A ∧
    0 ≤ V.D+V.S-r*V.H ∧ 2*(V.D+V.S-r*V.H) ≤ V.A-1 ∧
    0 ≤ V.Dp+2*V.S-r*V.H ∧ 2*(V.Dp+2*V.S-r*V.H) ≤ V.A-1 := by
  dsimp only
  let V := values z w r q
  let z0 : ℤ := z-4
  let w0 : ℤ := w-4*z
  let r0 : ℤ := r-2
  let q0 : ℤ := q-1
  have hz0 : 0 ≤ z0 := by dsimp [z0]; omega
  have hw0 : 0 ≤ w0 := by dsimp [w0]; omega
  have hr0 : 0 ≤ r0 := by dsimp [r0]; omega
  have hq0 : 0 ≤ q0 := by dsimp [q0]; omega
  have ez : z=z0+4 := by dsimp [z0]; omega
  have ew : w=4*(z0+4)+w0 := by dsimp [z0,w0]; omega
  have er : r=r0+2 := by dsimp [r0]; omega
  have eq : q=q0+1 := by dsimp [q0]; omega
  have hDp : 0 < V.Dp := by
    have he : V.Dp = 1 + q*((V.x-2*V.w-1)*V.z+V.x-1) := by
      dsimp [V,values]; ring
    rw [he]
    have hwpos : 0 < V.w := by dsimp [V,values]; omega
    have hzpos : 0 < V.z := by dsimp [V,values]; omega
    have hrV : 2 ≤ V.r := by dsimp [V,values]; exact hr
    have hxw : 2*V.w ≤ V.x := by
      have hh : 0 ≤ (V.r-2)*V.w :=
        mul_nonneg (by omega) hwpos.le
      dsimp [V,values] at hh ⊢
      nlinarith
    have hfirst : 0 ≤ (V.x-2*V.w)*V.z :=
      mul_nonneg (by omega) hzpos.le
    have hsecond : 0 < V.x-V.z-1 := by
      have hwz : 4*V.z ≤ V.w := by dsimp [V,values]; omega
      have hzV : 4 ≤ V.z := by dsimp [V,values]; exact hz
      nlinarith [hxw]
    rw [show (V.x-2*V.w-1)*V.z+V.x-1 =
      (V.x-2*V.w)*V.z+(V.x-V.z-1) by ring]
    have : 0 < (V.x-2*V.w-1)*V.z+V.x-1 := by
      rw [show (V.x-2*V.w-1)*V.z+V.x-1 =
        (V.x-2*V.w)*V.z+(V.x-V.z-1) by ring]
      nlinarith [hfirst, hsecond]
    have hqpos : 0 < q := by omega
    nlinarith
  have hDDp : 0 < V.D-V.Dp := by
    have he : V.D-V.Dp=q*V.w*V.z := by dsimp [V,values]; ring
    rw [he]
    dsimp [V,values]
    rw [ez,ew,eq]
    ring_nf
    positivity
  have hHD : 0 < V.H-V.D := by
    have he : V.H-V.D=q*(1+(V.w+1)*V.z) := by dsimp [V,values]; ring
    rw [he]
    dsimp [V,values]
    rw [ez,ew,eq]
    ring_nf
    positivity
  have hKcap : 0 ≤ V.K-1-2*V.H := by
    have he : V.K-1-2*V.H=V.y*((V.w-1)*V.z-1)-2 := by dsimp [V,values]; ring
    rw [he]
    dsimp [V,values]
    rw [ez,ew,er,eq]
    ring_nf
    positivity
  have hSWcap : 0 ≤ V.SW-1-2*V.H := by
    have he : V.SW-1-2*V.H =
        (V.K-1-2*V.H)+(V.K-V.H) := by dsimp [V,values]; ring
    rw [he]
    have hk : 0 ≤ V.K-V.H := by
      have he' : V.K-V.H=V.w*V.y*V.z := by dsimp [V,values]; ring
      rw [he']
      dsimp [V,values]
      rw [ez,ew,er,eq]
      ring_nf
      positivity
    omega
  have hAcap : 0 ≤ V.A-1-2*V.H := by
    have he : V.A-1-2*V.H=(V.x-2)*V.H := by dsimp [V,values]; ring
    rw [he]
    dsimp [V,values]
    rw [ez,ew,er,eq]
    ring_nf
    positivity
  have hEpos : 0 < V.E := by
    dsimp [V,values]
    rw [ez,ew,er,eq]
    ring_nf
    positivity
  have hEupper : 0 < V.w*V.A-2*V.E := by
    dsimp [V,values]
    rw [ez,ew,er,eq]
    ring_nf
    positivity
  have hFpos : 0 < V.F := by
    dsimp [V,values]
    rw [ez,ew,er,eq]
    ring_nf
    positivity
  have hJpos : 0 < V.J := by
    have he : V.J=(V.r-1)*V.H+q*(V.z+1)-1 := by dsimp [V,values]; ring
    rw [he]
    dsimp [V,values]
    rw [ez,ew,er,eq]
    ring_nf
    positivity
  have hJA : 0 < V.A-V.J := by
    have he : V.A-V.J=(V.x-V.r)*V.H+(V.H-q*(V.z+1))+2 := by
      dsimp [V,values]; ring
    rw [he]
    dsimp [V,values]
    rw [ez,ew,er,eq]
    ring_nf
    positivity
  have hB3A : 0 < V.B-3*V.A := by
    have he : V.B-3*V.A=(V.w-2)+(V.w-3)*V.x+
        (V.w-3-3*V.z)*V.x*V.y := by dsimp [V,values]; ring
    rw [he]
    dsimp [V,values]
    rw [ez,ew,er,eq]
    ring_nf
    have hwpos : 0 < (4*(z0+4)+w0-2 : ℤ) := by omega
    positivity
  have hS4A : 0 < V.A-4*V.S := by
    dsimp [V,values]
    rw [ez,ew,er,eq]
    ring_nf
    positivity
  have hXold : 0 ≤ V.D+V.S-V.r*V.H := by
    dsimp [V,values]
    rw [ez,ew,er,eq]
    ring_nf
    positivity
  have hXoldcap : 0 ≤ V.A-1-2*(V.D+V.S-V.r*V.H) := by
    dsimp [V,values]
    rw [ez,ew,er,eq]
    ring_nf
    positivity
  have hXnew : 0 ≤ V.Dp+2*V.S-V.r*V.H := by
    dsimp [V,values]
    rw [ez,ew,er,eq]
    ring_nf
    positivity
  have hXnewcap : 0 ≤ V.A-1-2*(V.Dp+2*V.S-V.r*V.H) := by
    dsimp [V,values]
    rw [ez,ew,er,eq]
    ring_nf
    positivity
  change
    0 < V.Dp ∧ V.Dp < V.D ∧ V.D < V.H ∧
    2*V.H ≤ V.K-1 ∧ 2*V.H ≤ V.SW-1 ∧ 2*V.H ≤ V.A-1 ∧
    0 < V.E ∧ 2*V.E < V.w*V.A ∧ 0 < V.F ∧
    0 < V.J ∧ V.J < V.A ∧ V.B > 3*V.A ∧ 4*V.S < V.A ∧
    0 ≤ V.D+V.S-V.r*V.H ∧ 2*(V.D+V.S-V.r*V.H) ≤ V.A-1 ∧
    0 ≤ V.Dp+2*V.S-V.r*V.H ∧ 2*(V.Dp+2*V.S-V.r*V.H) ≤ V.A-1
  exact ⟨hDp, by omega, by omega, by omega, by omega, by omega,
    hEpos, by omega, hFpos, hJpos, by omega, by omega, by omega,
    hXold, by omega, hXnew, by omega⟩

private theorem range_mass (f : ℕ→ℤ) (F : ℤ) (off len : ℕ)
    (hs : ∀ i<len, f (off+i)=2^i*F) :
    ((List.range' off len).map f).sum=((2:ℤ)^len-1)*F := by
  rw [← chamberLabels_full]
  have hpow : 0 < (2:ℕ)^len := Nat.two_pow_pos _
  have hh := chamberLabels_sum len off (2^len-1) (by omega) f F (by
    intro i hi; exact hs i hi)
  rw [hh, Nat.cast_sub (by have := Nat.two_pow_pos len; omega)]
  push_cast
  ring

private def broadBanks (a b c d u : ℕ) : Fin 4 → List ℕ :=
  let U0 := chamberLabels (d-1) 0 ((2^(d-1)-1) ^^^ u)
  let U1 := chamberLabels (d-1) 0 u
  ![List.range' (d+c+b-a) (a-1),
    List.range' (a+b+c) (d-1),
    U0,
    List.range' d (c-1) ++ List.range' (d+c) (b-a) ++
      List.range' (b+c+d) (a-d) ++ U1]

private def broadTerminals (a b c d : ℕ) : Fin 4 → ℕ :=
  ![d+c+b-1,a+b+c+d-1,d-1,d+c-1]

private def broadWord (a b c d u : ℕ) : List ℕ :=
  let P := broadBanks a b c d u
  let T := broadTerminals a b c d
  P 0 ++ [T 0] ++ P 1 ++ [T 1] ++ P 2 ++ [T 2] ++ P 3 ++ [T 3]

private theorem broadBanks_inventory (a b c d u : ℕ)
    (hc : 2 ≤ c) (hcd : c+2 ≤ d) (hda : d<a) (hab : a≤b)
    (hu : u < 2^(d-1)) :
    (broadWord a b c d u).Perm (List.range (a+b+c+d)) := by
  let U0 := chamberLabels (d-1) 0 ((2^(d-1)-1) ^^^ u)
  let U1 := chamberLabels (d-1) 0 u
  let W0 := List.range' (d+c+b-a) (a-1)
  let W1 := List.range' (d+c) (b-a)
  let X0 := List.range' (a+b+c) (d-1)
  let X1 := List.range' (b+c+d) (a-d)
  let V0 := List.range' d (c-1)
  have hsplit := chamberLabels_split (d-1) 0 (2^(d-1)-1) u
    (by intro i hi _; simp [Nat.testBit_two_pow_sub_one,hi])
  have hU : (U0 ++ U1).Perm (List.range' 0 (d-1)) := by
    simpa only [U0,U1,chamberLabels_full] using hsplit
  have join (off m n : ℕ) : List.range' off m ++ List.range' (off+m) n =
      List.range' off (m+n) := List.range'_append_1
  have hW : (W1 ++ W0).Perm (List.range' (d+c) (b-1)) := by
    dsimp [W0,W1]
    rw [show d+c+b-a=(d+c)+(b-a) by omega, join]
    simpa only [show b-a+(a-1)=b-1 by omega] using
      (List.Perm.refl (List.range' (d+c) (b-1)))
  have hX : (X1 ++ X0).Perm (List.range' (b+c+d) (a-1)) := by
    dsimp [X0,X1]
    rw [show a+b+c=(b+c+d)+(a-d) by omega, join]
    simpa only [show a-d+(d-1)=a-1 by omega] using
      (List.Perm.refl (List.range' (b+c+d) (a-1)))
  have merge (off len : ℕ) (hl : 1≤len) :
      List.range' off (len-1) ++ [off+len-1] = List.range' off len := by
    simpa only [show off+(len-1)=off+len-1 by omega,show len-1+1=len by omega]
      using (List.range'_1_concat (s:=off) (n:=len-1)).symm
  have h0 := merge 0 d (by omega)
  have h1 := merge d c (by omega)
  have h2 := merge (d+c) b (by omega)
  have h3 := merge (d+c+b) a (by omega)
  simp only [Nat.zero_add] at h0
  have h3' : List.range' (b+c+d) (a-1) ++ [a+b+c+d-1] =
      List.range' (b+c+d) a := by
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h3
  have hrange :
      ((List.range' 0 (d-1) ++ [d-1]) ++
        (V0 ++ [d+c-1]) ++
        ((List.range' (d+c) (b-1)) ++ [d+c+b-1]) ++
        ((List.range' (b+c+d) (a-1)) ++ [a+b+c+d-1])) =
        List.range (a+b+c+d) := by
    rw [h0,h1,h2]
    rw [h3']
    have j0 : List.range' 0 d ++ List.range' d c =
        List.range' 0 (d+c) := by
      simpa only [Nat.zero_add] using
        (List.range'_append_1 (s := 0) (m := d) (n := c))
    have j1 : List.range' 0 (d+c) ++ List.range' (d+c) b =
        List.range' 0 (d+c+b) := by
      simpa only [Nat.zero_add] using
        (List.range'_append_1 (s := 0) (m := d+c) (n := b))
    have j2 : List.range' 0 (d+c+b) ++ List.range' (b+c+d) a =
        List.range' 0 (a+b+c+d) := by
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        (List.range'_append_1 (s := 0) (m := d+c+b) (n := a))
    rw [j0, j1, j2]
    simp only [Nat.zero_add,←List.range_eq_range']
  have hblocks :
      (broadWord a b c d u : Multiset ℕ) =
        ↑W0 + {d+c+b-1} + ↑X0 + {a+b+c+d-1} +
        ↑U0 + {d-1} + ↑V0 + ↑W1 + ↑X1 + ↑U1 + {d+c-1} := by
    dsimp [broadWord,broadBanks,broadTerminals,W0,W1,X0,X1,V0,U0,U1]
    simp only [←Multiset.coe_add,Multiset.coe_singleton]
    ac_rfl
  apply Multiset.coe_eq_coe.mp
  rw [hblocks]
  calc
    (W0 : Multiset ℕ) + {d+c+b-1} + (X0 : Multiset ℕ) + {a+b+c+d-1} +
        (U0 : Multiset ℕ) + {d-1} + (V0 : Multiset ℕ) +
        (W1 : Multiset ℕ) + (X1 : Multiset ℕ) + (U1 : Multiset ℕ) + {d+c-1} =
      ((U0 : Multiset ℕ) + U1) + {d-1} + (V0 : Multiset ℕ) +
        ((W1 : Multiset ℕ) + W0) + {d+c+b-1} +
        ((X1 : Multiset ℕ) + X0) + {a+b+c+d-1} + {d+c-1} := by
      ac_rfl
    _ = (↑(U0 ++ U1) : Multiset ℕ) + {d-1} + ↑V0 +
        (↑(W1 ++ W0) : Multiset ℕ) + {d+c+b-1} +
        (↑(X1 ++ X0) : Multiset ℕ) + {a+b+c+d-1} + {d+c-1} := by
      simp only [←Multiset.coe_add]
    _ = ↑(List.range' 0 (d-1)) + {d-1} + ↑V0 +
        ↑(List.range' (d+c) (b-1)) + {d+c+b-1} +
        ↑(List.range' (b+c+d) (a-1)) + {a+b+c+d-1} + {d+c-1} := by
      rw [Multiset.coe_eq_coe.mpr hU,Multiset.coe_eq_coe.mpr hW,
        Multiset.coe_eq_coe.mpr hX]
    _ = ↑(List.range (a+b+c+d)) := by
      rw [←hrange]
      simp only [←Multiset.coe_add,Multiset.coe_singleton]
      ac_rfl

private theorem broadBanks_good (a b c d u : ℕ)
    (hc : 2 ≤ c) (hcd : c+2 ≤ d) (hda : d<a) (hab : a≤b)
    (hu : u < 2^(d-1)) (j : Fin 4) (i : ℕ)
    (hi : i ∈ broadBanks a b c d u j) :
    i < size a b c d ∧ i ∉ negatives a b c d := by
  have range_iff (start len : ℕ) :
      i ∈ List.range' start len ↔ start ≤ i ∧ i < start+len := by
    simp only [List.mem_range',Nat.one_mul]
    constructor
    · rintro ⟨k,hk,rfl⟩; omega
    · intro hh; exact ⟨i-start,by omega,by omega⟩
  fin_cases j <;> dsimp [broadBanks] at hi
  · have hi' : d+c+b-a ≤ i ∧ i < d+c+b-a+(a-1) := by
      simpa only [range_iff] using hi
    simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
    omega
  · have hi' : a+b+c ≤ i ∧ i < a+b+c+(d-1) := by
      simpa only [range_iff] using hi
    simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
    omega
  · obtain ⟨e,he,hbit,hval⟩ := (chamberLabels_mem _ _ _ _).mp hi
    simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
    have hei : i < d-1 := by omega
    have hi0 : i = e := by omega
    subst i
    omega
  · simp only [List.mem_append,List.mem_cons,List.mem_nil_iff,or_false,
      List.mem_singleton] at hi
    rcases hi with hi|hi
    · rcases hi with hi|hi
      · rcases hi with hi|hi
        · have hi' : d ≤ i ∧ i < d+(c-1) := by
            simpa only [range_iff] using hi
          simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
          omega
        · have hi' : d+c ≤ i ∧ i < d+c+(b-a) := by
            simpa only [range_iff] using hi
          simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
          omega
      · have hi' : b+c+d ≤ i ∧ i < b+c+d+(a-d) := by
          simpa only [range_iff] using hi
        simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
        omega
    · obtain ⟨e,he,hbit,hval⟩ := (chamberLabels_mem _ _ _ _).mp hi
      simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
      have hi0 : i = e := by omega
      subst i
      omega

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakSecondMaximum
