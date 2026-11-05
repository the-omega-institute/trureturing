/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Physical
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Physical
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Original a2 near-b construction: Physical and its physical source consumer. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.Exhaustion
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.SourceCertificate

set_option autoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
open D5.S3.Combinatorics.Circle.FourNegative
open SourceWidth PeriodicShortening RunFirstEarTransport
open private base newBase charge sourceMod oldValue newValue from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source (size)
open private rowBase rowHeads rowSeams literalCut source_certificate
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.SourceCertificate
open private word banks banks_inventory
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.Banks
open private actual_nat_joint_iff
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint

private theorem source_bases (b c d p q h : ℕ)
    (hc : (2:ℤ)^c=4*(q:ℤ)) (hd : (2:ℤ)^d=4*(p:ℤ)*q)
    (hb : (2:ℤ)^b=8*(h:ℤ)*p*q) :
    base 2 b c d=![A p q h,B p q h,L p q,K p q h] ∧
    newBase 2 b c d=![2*A p q h,SU p q h,SV p q,SW p q h] := by
  have hbase : base 2 b c d=![A p q h,B p q h,L p q,K p q h] := by
    funext r
    fin_cases r <;> dsimp [base]
    all_goals simp only [hc,hd,hb,show (2:ℤ)^2=4 by norm_num]
    all_goals dsimp [A,B,L,K,SecondPeakHighD.A,SecondPeakHighD.B,
      SecondPeakHighD.L,SecondPeakHighD.K,SecondPeakHighD.Z,SecondPeakHighD.T,SecondPeakHighD.Y]
    all_goals ring
  refine ⟨hbase,?_⟩
  funext r
  fin_cases r <;> simp [newBase,charge,hbase,hb,hc,SU,SV,SW,
    SecondPeakHighD.SU,SecondPeakHighD.SV,SecondPeakHighD.SW]
  all_goals dsimp [A,B,L,K,SecondPeakHighD.A,SecondPeakHighD.B,
      SecondPeakHighD.L,SecondPeakHighD.K,SecondPeakHighD.Z,SecondPeakHighD.T,SecondPeakHighD.Y]
  all_goals ring

private theorem physical_windows (b c d p q h v m M : ℕ) (before : Bool)
    (hc : (2:ℤ)^c=4*(q:ℤ)) (hd : (2:ℤ)^d=4*(p:ℤ)*q)
    (hb : (2:ℤ)^b=8*(h:ℤ)*p*q) (hw : Windows p q h v m M before) :
    ∀ (side : Bool) (r : Fin 4),
      0≤rowSeams 2 b c d v m M before side r ∧
      rowSeams 2 b c d v m M before side r≤rowHeads 2 b c d side r-1 := by
  obtain ⟨hbase,hnew⟩ := source_bases b c d p q h hc hd hb
  have seam (side : Bool) (r : Fin 4) :
      rowSeams 2 b c d v m M before side r=
        if side then SecondPeakHighD.newEnds (4:ℤ) p q h v m M before r
        else SecondPeakHighD.oldEnds (4:ℤ) p q h v m M r := by
    cases side <;> fin_cases r <;>
      simp [rowSeams,rowBase,hbase,hnew,SecondPeakHighD.newEnds,SecondPeakHighD.oldEnds]
    all_goals try split_ifs
    all_goals dsimp [A,B,L,K,SU,SV,SW]
    all_goals ring
  have heads (side : Bool) (r : Fin 4) :
      rowHeads 2 b c d side r=
        if side then SecondPeakHighD.newHeads (4:ℤ) p q h r
        else SecondPeakHighD.oldHeads (4:ℤ) p q h r := by
    cases side <;> fin_cases r <;>
      simp [rowHeads,rowBase,hbase,hnew,SecondPeakHighD.newHeads,SecondPeakHighD.oldHeads,A,B,L,K,SU,SV,SW]
  intro side r
  rw [seam,heads]
  cases side
  · exact (hw r).1
  · exact (hw r).2

/-- Exact physical word: every old label once, one literal fresh insertion. -/
private theorem physical_order (b c d p q h v m M : ℕ) (before : Bool)
    (hb2 : 2≤b) (hc2 : 2≤c) (hd2 : 2≤d)
    (hc : (2:ℤ)^c=4*(q:ℤ)) (hd : (2:ℤ)^d=4*(p:ℤ)*q)
    (hb : (2:ℤ)^b=8*(h:ℤ)*p*q)
    (good : Good p q h v m M before) :
    ∃ sigma : List (Fin (2+b+c+d)), ∃ j : ℕ, j≤2+b+c+d ∧
      OriginalOrder (2+b+c+d) (1+2^2+2^(2+b)+2^(2+b+c)) sigma ∧
      OriginalOrder (2+b+c+d+1) (2*(1+2^2+2^(2+b)+2^(2+b+c)))
        (earWord (2+b+c+d) sigma j) := by
  obtain ⟨hv0,hv,hmM,hM,hsub,hw⟩ := good
  have hdhalf : (2:ℤ)^d=2*2^(d-1) := by
    conv_lhs => rw [show d=(d-1)+1 by omega,pow_succ]
    ring
  have hbhalf : (2:ℤ)^b=2*2^(b-1) := by
    conv_lhs => rw [show b=(b-1)+1 by omega,pow_succ]
    ring
  have hv' : v≤2^(d-1) := by
    have hvi : 2*(v:ℤ)≤4*(p:ℤ)*q := by exact_mod_cast hv
    have hh : (v:ℤ)≤(2:ℤ)^(d-1) := by omega
    exact_mod_cast hh
  have hM' : M<2^(b-1) := by
    have hMi : 2*(M:ℤ)<8*(h:ℤ)*p*q := by exact_mod_cast hM
    have hh : (M:ℤ)<(2:ℤ)^(b-1) := by omega
    exact_mod_cast hh
  obtain ⟨_,hold,hnew⟩ := source_certificate 2 b c d (by norm_num) hb2 hc2 hd2
    v m M before hv0 hv' hM' hsub (physical_windows b c d p q h v m M before hc hd hb hw)
  have hperm := banks_inventory 2 b c d (by norm_num) hb2 hc2 hd2 v m M hsub
  have hlen : (word 2 b c d v m M).length=2+b+c+d := by
    simpa only [List.length_range] using hperm.length_eq
  have hcut : literalCut 2 b c d v m M before≤size 2 b c d := by
    dsimp [literalCut]
    split_ifs
    · dsimp [size]; omega
    · dsimp [word] at hlen
      simp only [List.length_append,List.length_singleton] at hlen
      dsimp [size]
      omega
  exact (actual_nat_joint_iff 2 b c d (by norm_num) hb2 hc2 hd2).mpr
    ⟨word 2 b c d v m M,hperm,hold,literalCut 2 b c d v m M before,hcut,hnew⟩

/-- Original unbounded a=2, near-b domain, with no feasibility hypothesis. -/
theorem complete_original_orders (b c d : ℕ) (hc : 3≤c) (hd : c+2≤d)
    (hb : b=d+1 ∨ b=d+2) :
    ∃ sigma : List (Fin (2+b+c+d)), ∃ j : ℕ, j≤2+b+c+d ∧
      OriginalOrder (2+b+c+d) (1+2^2+2^(2+b)+2^(2+b+c)) sigma ∧
      OriginalOrder (2+b+c+d+1) (2*(1+2^2+2^(2+b)+2^(2+b+c)))
        (earWord (2+b+c+d) sigma j) := by
  let p := 2^(d-c)
  let q := 2^(c-2)
  have hce : c=2+(c-2) := by omega
  have hde : d=c+(d-c) := by omega
  have hqc : (2:ℤ)^c=4*(q:ℤ) := by
    rw [hce,pow_add]
    norm_num [q]
  have hpc : (2:ℤ)^d=4*(p:ℤ)*q := by
    rw [hde,pow_add,hqc]
    simp only [p,Nat.cast_pow,Nat.cast_ofNat]
    ring
  rcases hb with rfl|rfl
  · obtain ⟨v,m,M,before,hgood⟩ := dyadic_exists (d-c) (c-2) 1 (by omega) (by omega) (Or.inl rfl)
    apply physical_order (d+1) c d p q 1 v m M before (by omega) (by omega) (by omega) hqc hpc
    · rw [pow_succ,hpc]; norm_num; ring
    · exact hgood
  · obtain ⟨v,m,M,before,hgood⟩ := dyadic_exists (d-c) (c-2) 2 (by omega) (by omega) (Or.inr rfl)
    apply physical_order (d+2) c d p q 2 v m M before (by omega) (by omega) (by omega) hqc hpc
    · rw [show d+2=(d+1)+1 by omega,pow_succ,pow_succ,hpc]; norm_num; ring
    · exact hgood

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
