/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakSecondMaximum/Broad
   generality: I
   mirror-B: none(waiver:private-consumed-physical-certificate)
   mirror-E: none(waiver:private-consumed-physical-certificate)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Physical reversed-middle certificate with the actual binary U transfer.
-/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Masks
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakSecondMaximum
open SourceWidth PeriodicShortening RunFirstEarTransport
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
open private size sourceMod base newBase charge oldValue newValue negatives chainLength chainStart
  nextBase nextNewBase weightedMask packet_masses chain_values new_base_bounds
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private oldMass newMass from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
open private DataCertificate DataCertificate.mk orderedPackets finiteChecks finiteEarChecks
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Certificate
open private blocksWord from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
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

set_option maxHeartbeats 2400000 in
private theorem broad_certificate_exists (a b c d : ℕ)
    (hc : 2≤c) (hcd : c+2≤d) (hda : d<a) (hab : a≤b) :
    Nonempty (Certificate a b c d) := by
  classical
  let z : ℤ := 2^c
  let w : ℤ := 2^d
  let r : ℤ := 2^(a-d)
  let q : ℤ := 2^(b-a)
  let V := values z w r q
  have hz : 4≤z := by dsimp [z]; have := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hc; norm_num at this; omega
  have hw : 4*z≤w := by
    change 4*(2:ℤ)^c ≤ (2:ℤ)^d
    have he : (2:ℤ)^d=(2:ℤ)^c*2^(d-c) := by
      rw [← pow_add]
      congr 1
      omega
    rw [he]
    have hdc : 2≤d-c := by omega
    have : 4≤(2:ℤ)^(d-c) := by
      have hh := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hdc
      norm_num at hh ⊢
      exact hh
    have hp : 0 < (2:ℤ)^c := by positivity
    nlinarith
  have hr : 2≤r := by dsimp [r]; have := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (by omega : 1≤a-d); norm_num at this; omega
  have hq : 1≤q := by
    dsimp [q]
    have hh := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show 0≤b-a by omega)
    norm_num at hh ⊢
    exact hh
  have hwin := broad_windows z w r q hz hw hr hq
  rcases hwin with ⟨hDp,hDpD,hDH,hKcap,hSWcap,hAcap,hEpos,hEupper,hFpos,
    hJpos,hJA,hB3A,hS4A,hXold,hXoldcap,hXnew,hXnewcap⟩
  have hx : (2:ℤ)^a = r*w := by
    dsimp [r,w]
    rw [← pow_add]
    congr 1
    omega
  have hy : (2:ℤ)^b = q*r*w := by
    dsimp [q,r,w]
    rw [← pow_add,← pow_add]
    congr 1 <;> omega
  have hzpow : (2:ℤ)^c = z := by rfl
  have hwpow : (2:ℤ)^d = w := by rfl
  have hbase : base a b c d = ![V.A,V.B,V.L,V.K] := by
    funext i
    fin_cases i <;> dsimp [base,V,values]
    all_goals try simp only [Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,
      Matrix.cons_val_succ]
    all_goals try rw [hx]
    all_goals try rw [hy]
    all_goals try rw [hzpow]
    all_goals try rw [hwpow]
    all_goals ring_nf
  have hnewbase : newBase a b c d =
      ![2*V.A,V.SU,V.SV,V.SW] := by
    funext i
    fin_cases i <;> dsimp [newBase,charge,base,V,values]
    all_goals try rw [hx]
    all_goals try rw [hy]
    all_goals try rw [hzpow]
    all_goals try rw [hwpow]
    all_goals ring_nf
  let f := oldValue a b c d
  let g := newValue a b c d
  let N := sourceMod a b c d
  have hqnonneg : 0 ≤ V.E / V.A :=
    Int.ediv_nonneg hEpos.le (by dsimp [V,values]; positivity)
  let u : ℕ := (V.E / V.A).toNat
  have hu_cast : (u : ℤ) = V.E / V.A := by
    dsimp [u]
    exact Int.toNat_of_nonneg hqnonneg
  have hApos : 0 < V.A := by dsimp [V,values]; positivity
  have hrem_nonneg : 0 ≤ V.E % V.A :=
    Int.emod_nonneg _ (by exact ne_of_gt hApos)
  have hdiv : (u:ℤ)*V.A + V.E % V.A = V.E := by
    simpa [hu_cast] using Int.ediv_mul_add_emod V.E V.A
  let P := broadBanks a b c d u
  let T := broadTerminals a b c d
  let B := fun j : Fin 4 => (P j).toFinset
  let ps : List (Finset ℕ × ℕ) :=
    [(B 0,T 0),(B 1,T 1),(B 2,T 2),(B 3,T 3)]
  have hu : u < 2^(d-1) := by
    have he : 0 ≤ u := by omega
    have hltInt : 2*(u:ℤ) < w := by
      have hle : (u:ℤ)*V.A ≤ V.E := by nlinarith [hdiv,hrem_nonneg]
      have h2le : 2*((u:ℤ)*V.A) ≤ 2*V.E :=
        mul_le_mul_of_nonneg_left hle (by norm_num : (0:ℤ) ≤ 2)
      have h2le' : 2*(u:ℤ)*V.A ≤ 2*V.E := by
        simpa [mul_assoc] using h2le
      have hqprod0 : 2*(u:ℤ)*V.A < V.w*V.A := lt_of_le_of_lt h2le' hEupper
      have hqprod : 2*(u:ℤ)*V.A < w*V.A := by
        simpa [V,values] using hqprod0
      exact lt_of_mul_lt_mul_right hqprod hApos.le
    have hltNat : 2*u < (2:ℕ)^d := by
      have hltInt' : 2*(u:ℤ) < (2:ℤ)^d := by simpa [w] using hltInt
      exact_mod_cast hltInt'
    have hp : (2:ℤ)^(d-1) * 2 = w := by
      calc
        (2:ℤ)^(d-1) * 2 = (2:ℤ)^((d-1)+1) := by rw [pow_succ]
        _ = (2:ℤ)^d := by congr 1 <;> omega
        _ = w := hwpow.symm
    have hp' : (2:ℕ)^(d-1) * 2 = 2^d := by
      calc
        (2:ℕ)^(d-1) * 2 = 2^((d-1)+1) := by rw [pow_succ]
        _ = 2^d := by congr 1 <;> omega
    rw [← hp'] at hltNat
    omega
  have hp := broadBanks_inventory a b c d (u) hc hcd hda hab hu
  have hn (j : Fin 4) : (P j).Nodup := by
    have ht := hp.nodup_iff.mpr List.nodup_range
    simp only [broadWord,List.nodup_append] at ht
    fin_cases j <;> tauto
  have hperm (j : Fin 4) : (B j).toList.Perm (P j) := by
    apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) (hn j)).mpr
    intro i
    simp [B]
  have good (j : Fin 4) (i : ℕ) (hi : i ∈ B j) :
      i < size a b c d ∧ i ∉ negatives a b c d := by
    exact broadBanks_good a b c d (u) hc hcd hda hab hu j i
      (List.mem_toFinset.mp hi)
  have hm (side : Bool) (j : Fin 4) :
      (if side then newMass a b c d (B j) else oldMass a b c d (B j)) =
      ((P j).map (if side then g else f)).sum := by
    have mm := packet_masses a b c d (by omega) (by omega) (by omega) (by omega)
      (B j) (by intro i hi; exact good j i hi)
    have tosum (ff : ℕ→ℤ) : (∑ i∈B j,ff i)=((P j).map ff).sum := by
      exact List.sum_toFinset ff (hn j)
    cases side
    · exact mm.1.symm.trans (tosum f)
    · exact mm.2.symm.trans (tosum g)
  have tab := chain_values a b c d (by omega) (by omega) (by omega) (by omega)
  have hW (side : Bool) (i : ℕ) (hi : i<a-1) :
      (if side then g else f) (d+c+b-a+i) =
        (2:ℤ)^i * (if side then q*V.SV else q*V.L) := by
    cases side
    · have hh := tab.2.1 2 (b-a+i) (by simp [chainLength]; omega)
      rw [if_pos (by simp [chainLength]; omega)] at hh
      rw [show chainStart b c d 2 + (b-a+i) = d+c+b-a+i by
        simp [chainStart]; omega] at hh
      change f (d+c+b-a+i) = (2:ℤ)^(b-a+i)*base a b c d 2 at hh
      rw [hbase] at hh
      simpa [pow_add,q,mul_assoc,mul_left_comm,mul_comm] using hh
    · have hh := tab.2.2.1 2 (b-a+i) (by simp [chainLength]; omega)
      rw [if_pos (by simp [chainLength]; omega)] at hh
      rw [show chainStart b c d 2 + (b-a+i) = d+c+b-a+i by
        simp [chainStart]; omega] at hh
      change g (d+c+b-a+i) = (2:ℤ)^(b-a+i)*newBase a b c d 2 at hh
      rw [hnewbase] at hh
      simpa [pow_add,q,mul_assoc,mul_left_comm,mul_comm] using hh
  have hW1 (side : Bool) (i : ℕ) (hi : i<b-a) :
      (if side then g else f) (d+c+i) =
        (2:ℤ)^i * (if side then V.SV else V.L) := by
    cases side
    · have hh := tab.2.1 2 i (by simp [chainLength]; omega)
      rw [if_pos (by simp [chainLength]; omega)] at hh
      rw [show chainStart b c d 2 + i = d+c+i by simp [chainStart]] at hh
      change f (d+c+i) = (2:ℤ)^i*base a b c d 2 at hh
      rw [hbase] at hh
      exact hh
    · have hh := tab.2.2.1 2 i (by simp [chainLength]; omega)
      rw [if_pos (by simp [chainLength]; omega)] at hh
      rw [show chainStart b c d 2 + i = d+c+i by simp [chainStart]] at hh
      change g (d+c+i) = (2:ℤ)^i*newBase a b c d 2 at hh
      rw [hnewbase] at hh
      exact hh
  have hX (side : Bool) (i : ℕ) (hi : i<d-1) :
      (if side then g else f) (a+b+c+i) =
        (2:ℤ)^i * (if side then r*V.SW else r*V.K) := by
    cases side
    · have hh := tab.2.1 3 (a-d+i) (by simp [chainLength]; omega)
      rw [if_pos (by simp [chainLength]; omega)] at hh
      rw [show chainStart b c d 3 + (a-d+i) = a+b+c+i by
        simp [chainStart]; omega] at hh
      change f (a+b+c+i) = (2:ℤ)^(a-d+i)*base a b c d 3 at hh
      rw [hbase] at hh
      simpa [pow_add,r,mul_assoc,mul_left_comm,mul_comm] using hh
    · have hh := tab.2.2.1 3 (a-d+i) (by simp [chainLength]; omega)
      rw [if_pos (by simp [chainLength]; omega)] at hh
      rw [show chainStart b c d 3 + (a-d+i) = a+b+c+i by
        simp [chainStart]; omega] at hh
      change g (a+b+c+i) = (2:ℤ)^(a-d+i)*newBase a b c d 3 at hh
      rw [hnewbase] at hh
      simpa [pow_add,r,mul_assoc,mul_left_comm,mul_comm] using hh
  have hX1 (side : Bool) (i : ℕ) (hi : i<a-d) :
      (if side then g else f) (b+c+d+i) =
        (2:ℤ)^i * (if side then V.SW else V.K) := by
    cases side
    · have hh := tab.2.1 3 i (by simp [chainLength]; omega)
      rw [if_pos (by simp [chainLength]; omega)] at hh
      rw [show chainStart b c d 3 + i = b+c+d+i by
        simp [chainStart]; omega] at hh
      change f (b+c+d+i) = (2:ℤ)^i*base a b c d 3 at hh
      rw [hbase] at hh
      simpa only [Nat.zero_add, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead,
        Matrix.vecTail] using hh
    · have hh := tab.2.2.1 3 i (by simp [chainLength]; omega)
      rw [if_pos (by simp [chainLength]; omega)] at hh
      rw [show chainStart b c d 3 + i = b+c+d+i by
        simp [chainStart]; omega] at hh
      change g (b+c+d+i) = (2:ℤ)^i*newBase a b c d 3 at hh
      rw [hnewbase] at hh
      simpa only [Nat.zero_add, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead,
        Matrix.vecTail] using hh
  have hV (side : Bool) (i : ℕ) (hi : i<c-1) :
      (if side then g else f) (d+i) =
        (2:ℤ)^i * (if side then V.SU else V.B) := by
    cases side
    · have hh := tab.2.1 1 i (by simp [chainLength]; omega)
      rw [if_pos (by simp [chainLength]; omega)] at hh
      rw [show chainStart b c d 1 + i = d+i by simp [chainStart]] at hh
      change f (d+i) = (2:ℤ)^i*base a b c d 1 at hh
      rw [hbase] at hh
      exact hh
    · have hh := tab.2.2.1 1 i (by simp [chainLength]; omega)
      rw [if_pos (by simp [chainLength]; omega)] at hh
      rw [show chainStart b c d 1 + i = d+i by simp [chainStart]] at hh
      change g (d+i) = (2:ℤ)^i*newBase a b c d 1 at hh
      rw [hnewbase] at hh
      exact hh
  have hpowq : (2:ℤ)^(b-1) = (2:ℤ)^(a-1) * q := by
    dsimp [q]
    rw [← pow_add]
    congr 1
    omega
  have hpowr : (2:ℤ)^(a-1) = (2:ℤ)^(d-1) * r := by
    dsimp [r]
    rw [← pow_add]
    congr 1
    omega
  have hWold : ((P 0).map f).sum = ((2:ℤ)^(b-1)-q)*V.L := by
    dsimp [P,broadBanks]
    have hh := range_mass f (q*V.L) (d+c+b-a) (a-1) (by
      intro i hi
      simpa [mul_assoc,mul_left_comm,mul_comm] using hW false i hi)
    rw [hh]
    rw [hpowq]
    ring
  have hWnew : ((P 0).map g).sum = ((2:ℤ)^(b-1)-q)*V.SV := by
    dsimp [P,broadBanks]
    have hh := range_mass g (q*V.SV) (d+c+b-a) (a-1) (by
      intro i hi
      simpa [mul_assoc,mul_left_comm,mul_comm] using hW true i hi)
    rw [hh]
    rw [hpowq]
    ring
  have hXold : ((P 1).map f).sum = ((2:ℤ)^(a-1)-r)*V.K := by
    dsimp [P,broadBanks]
    have hh := range_mass f (r*V.K) (a+b+c) (d-1) (by
      intro i hi
      simpa [mul_assoc,mul_left_comm,mul_comm] using hX false i hi)
    rw [hh]
    rw [hpowr]
    ring
  have hXnew : ((P 1).map g).sum = ((2:ℤ)^(a-1)-r)*V.SW := by
    dsimp [P,broadBanks]
    have hh := range_mass g (r*V.SW) (a+b+c) (d-1) (by
      intro i hi
      simpa [mul_assoc,mul_left_comm,mul_comm] using hX true i hi)
    rw [hh]
    rw [hpowr]
    ring
  have hVold : ((List.range' d (c-1)).map f).sum =
      ((2:ℤ)^(c-1)-1)*V.B := by
    exact range_mass f V.B d (c-1) (by
      intro i hi; simpa using hV false i hi)
  have hVnew : ((List.range' d (c-1)).map g).sum =
      ((2:ℤ)^(c-1)-1)*V.SU := by
    exact range_mass g V.SU d (c-1) (by
      intro i hi; simpa using hV true i hi)
  have hW1old : ((List.range' (d+c) (b-a)).map f).sum =
      ((2:ℤ)^(b-a)-1)*V.L := by
    exact range_mass f V.L (d+c) (b-a) (by
      intro i hi; simpa using hW1 false i hi)
  have hW1new : ((List.range' (d+c) (b-a)).map g).sum =
      ((2:ℤ)^(b-a)-1)*V.SV := by
    exact range_mass g V.SV (d+c) (b-a) (by
      intro i hi; simpa using hW1 true i hi)
  have hX1old : ((List.range' (b+c+d) (a-d)).map f).sum =
      ((2:ℤ)^(a-d)-1)*V.K := by
    exact range_mass f V.K (b+c+d) (a-d) (by
      intro i hi; simpa using hX1 false i hi)
  have hX1new : ((List.range' (b+c+d) (a-d)).map g).sum =
      ((2:ℤ)^(a-d)-1)*V.SW := by
    exact range_mass g V.SW (b+c+d) (a-d) (by
      intro i hi; simpa using hX1 true i hi)
  let U0 := chamberLabels (d-1) 0 ((2^(d-1)-1) ^^^ (u))
  let U1 := chamberLabels (d-1) 0 (u)
  have hU1old : (U1.map f).sum = ((u : ℕ):ℤ)*V.A := by
    dsimp [U1]
    apply chamberLabels_sum
    · exact hu
    · intro e he
      have hh := tab.2.1 0 e (by simp [chainLength]; omega)
      rw [if_pos (by simp [chainLength]; omega)] at hh
      rw [show chainStart b c d 0 + e = e by simp [chainStart]] at hh
      change f e = (2:ℤ)^e * base a b c d 0 at hh
      rw [hbase] at hh
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead,
        Matrix.vecTail] using hh
  have hU1new : (U1.map g).sum = ((u : ℕ):ℤ)*(2*V.A) := by
    dsimp [U1]
    apply chamberLabels_sum
    · exact hu
    · intro e he
      have hh := tab.2.2.1 0 e (by simp [chainLength]; omega)
      rw [if_pos (by simp [chainLength]; omega)] at hh
      rw [show chainStart b c d 0 + e = e by simp [chainStart]] at hh
      change g e = (2:ℤ)^e * newBase a b c d 0 at hh
      rw [hnewbase] at hh
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead,
        Matrix.vecTail] using hh
  have hUfullold : ((List.range' 0 (d-1)).map f).sum =
      ((2:ℤ)^(d-1)-1)*V.A := by
    exact range_mass f V.A 0 (d-1) (by
      intro i hi
      have hh := tab.2.1 0 i (by simp [chainLength]; omega)
      rw [if_pos (by simp [chainLength]; omega)] at hh
      rw [show chainStart b c d 0 + i = i by simp [chainStart]] at hh
      change f i = (2:ℤ)^i * base a b c d 0 at hh
      rw [hbase] at hh
      simpa using hh)
  have hUfullnew : ((List.range' 0 (d-1)).map g).sum =
      ((2:ℤ)^(d-1)-1)*(2*V.A) := by
    exact range_mass g (2*V.A) 0 (d-1) (by
      intro i hi
      have hh := tab.2.2.1 0 i (by simp [chainLength]; omega)
      rw [if_pos (by simp [chainLength]; omega)] at hh
      rw [show chainStart b c d 0 + i = i by simp [chainStart]] at hh
      change g i = (2:ℤ)^i * newBase a b c d 0 at hh
      rw [hnewbase] at hh
      simpa using hh)
  have hU0old : (U0.map f).sum =
      ((2:ℤ)^(d-1)-1-(u : ℕ))*V.A := by
    have hs := chamberLabels_split (d-1) 0 (2^(d-1)-1) (u)
      (by intro e he _; simp [Nat.testBit_two_pow_sub_one,he])
    have hs' := (hs.map f).sum_eq
    rw [← chamberLabels_full (d-1) 0] at hs'
    rw [hUfullold,hU1old] at hs'
    norm_num at hs'
    push_cast at hs'
    simpa [U0] using hs'
  have hU0new : (U0.map g).sum =
      ((2:ℤ)^(d-1)-1-(u : ℕ))*(2*V.A) := by
    have hs := chamberLabels_split (d-1) 0 (2^(d-1)-1) (u)
      (by intro e he _; simp [Nat.testBit_two_pow_sub_one,he])
    have hs' := (hs.map g).sum_eq
    rw [← chamberLabels_full (d-1) 0] at hs'
    rw [hUfullnew,hU1new] at hs'
    norm_num at hs'
    push_cast at hs'
    simpa [U0] using hs'
  have mo : ((P 0).map f).sum = ((2:ℤ)^(b-1)-q)*V.L ∧
      ((P 1).map f).sum = ((2:ℤ)^(a-1)-r)*V.K ∧
      ((P 2).map f).sum = ((2:ℤ)^(d-1)-1-(u : ℕ))*V.A ∧
      ((P 3).map f).sum = ((2:ℤ)^(c-1)-1)*V.B +
        ((2:ℤ)^(b-a)-1)*V.L + ((2:ℤ)^(a-d)-1)*V.K +
        ((u : ℕ):ℤ)*V.A := by
    refine ⟨hWold,hXold,?_,?_⟩
    · dsimp [P,broadBanks,U0]
      exact hU0old
    · dsimp [P,broadBanks,U1]
      simp only [List.map_append,List.sum_append]
      rw [hVold,hW1old,hX1old,hU1old]
  have mg : ((P 0).map g).sum = ((2:ℤ)^(b-1)-q)*V.SV ∧
      ((P 1).map g).sum = ((2:ℤ)^(a-1)-r)*V.SW ∧
      ((P 2).map g).sum = ((2:ℤ)^(d-1)-1-(u : ℕ))*(2*V.A) ∧
      ((P 3).map g).sum = ((2:ℤ)^(c-1)-1)*V.SU +
        ((2:ℤ)^(b-a)-1)*V.SV + ((2:ℤ)^(a-d)-1)*V.SW +
        ((u : ℕ):ℤ)*(2*V.A) := by
    refine ⟨hWnew,hXnew,?_,?_⟩
    · dsimp [P,broadBanks,U0]
      exact hU0new
    · dsimp [P,broadBanks,U1]
      simp only [List.map_append,List.sum_append]
      rw [hVnew,hW1new,hX1new,hU1new]
  have native (j : Fin 4) := native_masses a b c d
    (by omega) (by omega) (by omega) (by omega) j
  have n0 := native 2
  have n1 := native 3
  have n2 := native 0
  have n3 := native 1
  have hcast (n : ℕ) : ((2^(n-1)-1:ℕ):ℤ)=(2:ℤ)^(n-1)-1 := by
    rw [Nat.cast_sub (by have := Nat.two_pow_pos (n-1);omega)]
    norm_cast
  simp only [chainLength,chainStart,nextBase,nextNewBase,hbase,hnewbase,hcast,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_add]
    at n0 n1 n2 n3
  have e0 : d+c+(b-1)=T 0 := by dsimp [T,broadTerminals];omega
  have e1 : d+c+b+(a-1)=T 1 := by dsimp [T,broadTerminals];omega
  have e2 : d-1=T 2 := by rfl
  have e3 : d+(c-1)=T 3 := by dsimp [T,broadTerminals];omega
  rw [e0] at n0
  rw [e1] at n1
  rw [e3] at n3
  change ((2:ℤ)^(b-1)-1)*V.L+f (T 0)=V.K-V.L ∧
    ((2:ℤ)^(b-1)-1)*V.SV+g (T 0)=V.SW-V.SV ∧
    2*f (T 0)=V.K-N ∧ 2*g (T 0)=V.SW-(2*N+1) at n0
  change ((2:ℤ)^(a-1)-1)*V.K+f (T 1)=V.A-V.K ∧
    ((2:ℤ)^(a-1)-1)*V.SW+g (T 1)=V.A-V.SW ∧
    2*f (T 1)=V.A-N ∧ 2*g (T 1)=V.A-(2*N+1) at n1
  change ((2:ℤ)^(d-1)-1)*V.A+f (T 2)=V.B-V.A ∧
    ((2:ℤ)^(d-1)-1)*(2*V.A)+g (T 2)=V.SU-(2*V.A) ∧
    2*f (T 2)=V.B-N ∧ 2*g (T 2)=V.SU-(2*N+1) at n2
  change ((2:ℤ)^(c-1)-1)*V.B+f (T 3)=V.L-V.B ∧
    ((2:ℤ)^(c-1)-1)*V.SU+g (T 3)=V.SV-V.SU ∧
    2*f (T 3)=V.L-N ∧ 2*g (T 3)=V.SV-(2*N+1) at n3
  let M := fun j : Fin 4 => oldMass a b c d (B j)
  let G := fun j : Fin 4 => newMass a b c d (B j)
  have m0 : M 0+f (T 0)=V.D := by
    rw [show M 0=((P 0).map f).sum from hm false 0,mo.1]
    have he : V.D=V.K-q*V.L := rfl
    rw [he]
    nlinarith only [n0.1]
  have m1 : M 1+f (T 1)=V.A-r*V.K := by
    rw [show M 1=((P 1).map f).sum from hm false 1,mo.2.1]
    nlinarith only [n1.1]
  have m2 : M 2+f (T 2)=V.B-V.A-(u : ℕ)*V.A := by
    rw [show M 2=((P 2).map f).sum from hm false 2,mo.2.2.1]
    nlinarith only [n2.1]
  have m3 : M 3+f (T 3)=V.L-V.B+((2:ℤ)^(b-a)-1)*V.L+
      ((2:ℤ)^(a-d)-1)*V.K+(u : ℕ)*V.A := by
    rw [show M 3=((P 3).map f).sum from hm false 3,mo.2.2.2]
    nlinarith only [n3.1]
  have g0 : G 0+g (T 0)=V.Dp := by
    rw [show G 0=((P 0).map g).sum from hm true 0,mg.1]
    have he : V.Dp=V.SW-q*V.SV := rfl
    rw [he]
    nlinarith only [n0.2.1]
  have g1 : G 1+g (T 1)=V.A-r*V.SW := by
    rw [show G 1=((P 1).map g).sum from hm true 1,mg.2.1]
    nlinarith only [n1.2.1]
  have g2 : G 2+g (T 2)=V.SU-2*V.A-
      2*(u : ℕ)*V.A := by
    rw [show G 2=((P 2).map g).sum from hm true 2,mg.2.2.1]
    nlinarith only [n2.2.1]
  have g3 : G 3+g (T 3)=V.SV-V.SU+((2:ℤ)^(b-a)-1)*V.SV+
      ((2:ℤ)^(a-d)-1)*V.SW+2*(u : ℕ)*V.A := by
    rw [show G 3=((P 3).map g).sum from hm true 3,mg.2.2.2]
    nlinarith only [n3.2.1]
  have heold : M 0+f (T 0)+M 1+f (T 1)+M 2+f (T 2) =
      V.E-(u : ℕ)*V.A := by
    have he : V.E=V.B+V.D-r*V.K := rfl
    rw [he]
    nlinarith only [m0,m1,m2]
  have henew : G 0+g (T 0)+G 1+g (T 1)+G 2+g (T 2)+V.A =
      V.F-2*(u : ℕ)*V.A := by
    have he : V.F=V.SU+V.Dp-r*V.SW := rfl
    rw [he]
    nlinarith only [g0,g1,g2]
  have zold : M 0+f (T 0)+M 1+f (T 1)+M 2+f (T 2)+M 3+f (T 3)=0 := by
    have he : V.D=V.K-q*V.L := rfl
    nlinarith only [m0,m1,m2,m3,he]
  have znew : G 0+g (T 0)+G 1+g (T 1)+G 2+g (T 2)+G 3+g (T 3)+V.A=0 := by
    have he : V.Dp=V.SW-q*V.SV := rfl
    nlinarith only [g0,g1,g2,g3,he]
  have xid : V.A-r*V.K=V.D+V.S-r*V.H := by
    dsimp [V,values]
    ring
  have xid' : V.A-r*V.SW=V.Dp+2*V.S-r*V.H := by
    dsimp [V,values]
    ring
  have hrem_lt : V.E % V.A < V.A := Int.emod_lt_of_pos _ hApos
  have hUold : 0 ≤ V.E % V.A ∧ 2*(V.E % V.A) ≤ V.B-1 := by
    have := hB3A
    omega
  have hUnew : 0 ≤ 2*(V.E % V.A)+V.J ∧
      2*(2*(V.E % V.A)+V.J) ≤ V.SU-1 := by
    have := hJA
    have := hJpos
    have := hB3A
    omega
  have heq : V.E-(u:ℤ)*V.A=V.E%V.A := by
    rw [←hu_cast]
    nlinarith [hdiv]
  have win (e S z C : ℤ) (he : 0≤e ∧ 2*e≤S-1)
      (hz : 2*z=S-(2*C+1)) : 0≤e ∧ e-z≤C := by omega
  have k0 := win V.D V.K (f (T 0)) (N/2) ⟨by omega,hKcap⟩ (by
    have hz := n0.2.2.1
    omega)
  have k1 := win (V.D+V.S-r*V.H) V.A (f (T 1)) (N/2)
      ⟨hXold,hXoldcap⟩ (by
    have hz := n1.2.2.1
    omega)
  have k2 := win (V.E-(u:ℤ)*V.A) V.B (f (T 2)) (N/2)
      (by rw [heq]; exact hUold) (by
    have hz := n2.2.2.1
    omega)
  have k0n := win V.Dp V.SW (g (T 0)) N ⟨hDp.le,by omega⟩ n0.2.2.2
  have k1n := win (V.Dp+2*V.S-r*V.H) V.A (g (T 1)) N
      ⟨hXnew,hXnewcap⟩ (by
    have hz := n1.2.2.2
    omega)
  have k2n := win (V.F-2*(u:ℤ)*V.A) V.SU (g (T 2)) N
      (by
        have he : V.F-2*(u:ℤ)*V.A = 2*(V.E%V.A)+V.J := by
          rw [←hu_cast]
          nlinarith [hdiv]
        rw [he]
        exact hUnew)
      n2.2.2.2
  have lastO : 0≤-f (T 3) ∧ -f (T 3)≤N/2 := by
    have hh := tab.1 2
    rw [hbase] at hh
    change 1 ≤ V.L ∧ V.L < N at hh
    have hz := n3.2.2.1
    change 2*f (T 3)=V.L-N at hz
    omega
  have lastN : 0≤-g (T 3) ∧ -g (T 3)≤N := by
    have hb := new_base_bounds a b c d (by omega) (by omega) (by omega) (by omega) 2
    rw [hnewbase] at hb
    change 1 ≤ V.SV ∧ V.SV < 2*N+1 at hb
    have hz := n3.2.2.2
    change 2*g (T 3)=V.SV-(2*N+1) at hz
    omega
  refine ⟨DataCertificate.mk ps ?_ ⟨1,by decide⟩ ?_ ?_ ?_ ?_⟩
  · change [T 0,T 1,T 2,T 3].Perm (negatives a b c d)
    have he : negatives a b c d=[T 2,T 3,T 0,T 1] := by
      dsimp [negatives,T,broadTerminals,size]
    rw [he]
    change ([T 0,T 1]++[T 2,T 3]).Perm ([T 2,T 3]++[T 0,T 1])
    exact List.perm_append_comm
  · intro pkt hpkt i hi
    simp only [ps,List.mem_cons,List.mem_nil_iff,or_false] at hpkt
    rcases hpkt with rfl|rfl|rfl|rfl
    all_goals exact good _ i (List.mem_toFinset.mp hi)
  · have he : (blocksWord (orderedPackets ps)).Perm (broadWord a b c d u) := by
      dsimp [ps,orderedPackets,blocksWord]
      simpa only [List.map_cons,List.map_nil,blocksWord,
        List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using
        (((((((hperm 0).append_right [T 0]).append (hperm 1)).append_right [T 1]).append
          (hperm 2)).append_right [T 2]).append (hperm 3)).append_right [T 3]
    exact Multiset.coe_eq_coe.mpr (he.trans hp)
  · change finiteChecks (oldMass a b c d) f (N/2) 0 ps
    simp only [ps,finiteChecks,zero_add]
    change 0≤M 0+f (T 0) ∧ M 0≤N/2 ∧
      0≤M 0+f (T 0)+M 1+f (T 1) ∧ M 0+f (T 0)+M 1≤N/2 ∧
      0≤M 0+f (T 0)+M 1+f (T 1)+M 2+f (T 2) ∧
      M 0+f (T 0)+M 1+f (T 1)+M 2≤N/2 ∧
      0≤M 0+f (T 0)+M 1+f (T 1)+M 2+f (T 2)+M 3+f (T 3) ∧
      M 0+f (T 0)+M 1+f (T 1)+M 2+f (T 2)+M 3≤N/2 ∧ True
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,trivial⟩ <;>
      nlinarith only [k0.1,k0.2,k1.1,k1.2,k2.1,k2.2,m0,m1,m2,heold,zold,lastO.2]
  · change finiteEarChecks (newMass a b c d) g N (base a b c d 0) 0 1 ps
    rw [hbase]
    change finiteEarChecks (newMass a b c d) g N V.A 0 1 ps
    simp only [ps,finiteEarChecks,finiteChecks,zero_add]
    change 0≤G 0+g (T 0) ∧ G 0≤N ∧
      0≤G 0+G 1+V.A+g (T 1) ∧ G 0+G 1+V.A≤N ∧
      0≤G 0+G 1+V.A+g (T 1)+G 2+g (T 2) ∧
      G 0+G 1+V.A+g (T 1)+G 2≤N ∧
      0≤G 0+G 1+V.A+g (T 1)+G 2+g (T 2)+G 3+g (T 3) ∧
      G 0+G 1+V.A+g (T 1)+G 2+g (T 2)+G 3≤N ∧ True
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,trivial⟩ <;>
      nlinarith only [k0n.1,k0n.2,k1n.1,k1n.2,k2n.1,k2n.2,g0,g1,g2,henew,znew,lastN.2]
end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakSecondMaximum
