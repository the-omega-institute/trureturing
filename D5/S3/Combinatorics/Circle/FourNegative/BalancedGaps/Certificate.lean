/- GID: D5/S3/Combinatorics/Circle/FourNegative/BalancedGaps/Certificate
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/BalancedGaps/Certificate
   mirror-E: none(waiver:consumed-balanced-physical-certificate)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Complete actual-source four-packet certificates in the balanced chamber. -/
import D5.S3.Combinatorics.Circle.FourNegative.BalancedGaps.Source

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.BalancedGaps
open PacketNormalForm
open private offsets order ear correction powers bases newBases lengths modulus masses drops newDrops
  checks earChecks polynomial_endpoints
  from D5.S3.Combinatorics.Circle.FourNegative.BalancedGaps.Arithmetic
open private assigned negativeLabel packets packet_labels negative_order physical_partition
  from D5.S3.Combinatorics.Circle.FourNegative.BalancedGaps.Physical
open private assigned_masses source_doubles
  from D5.S3.Combinatorics.Circle.FourNegative.BalancedGaps.Source
open private size chainLength oldValue newValue base newBase sourceMod charge nextBase nextNewBase
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private oldMass newMass from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
open private DataCertificate DataCertificate.mk finiteChecks finiteEarChecks
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Certificate

private theorem halve_checks (mass : Finset ℕ → ℤ) (f : ℕ → ℤ) (C h : ℤ)
    (bs : List (Finset ℕ × ℕ))
    (hh : checks (2*C) (2*h) (bs.map (fun b => (2*mass b.1,2*f b.2)))) :
    finiteChecks mass f C h bs := by
  induction bs generalizing h with
  | nil => trivial
  | cons b bs ih =>
    rcases b with ⟨P,n⟩
    change 0 ≤ 2*h+2*mass P+2*f n ∧ 2*h+2*mass P ≤ 2*C ∧
      checks (2*C) (2*h+2*mass P+2*f n) (bs.map (fun b => (2*mass b.1,2*f b.2))) at hh
    refine ⟨by linarith [hh.1],by linarith [hh.2.1],ih (h+mass P+f n) ?_⟩
    convert hh.2.2 using 1 <;> ring

private theorem halve_ear_checks (mass : Finset ℕ → ℤ) (f : ℕ → ℤ) (C E h : ℤ)
    (e : ℕ) (bs : List (Finset ℕ × ℕ))
    (hh : earChecks (2*C) (2*E) (2*h) e (bs.map (fun b => (2*mass b.1,2*f b.2)))) :
    finiteEarChecks mass f C E h e bs := by
  induction bs generalizing e h with
  | nil => simp only [finiteEarChecks]
  | cons b bs ih =>
    rcases b with ⟨P,n⟩
    cases e with
    | zero =>
      change 0 ≤ 2*h+(2*mass P+2*E)+2*f n ∧ 2*h+(2*mass P+2*E) ≤ 2*C ∧
        checks (2*C) (2*h+(2*mass P+2*E)+2*f n)
          (bs.map (fun b => (2*mass b.1,2*f b.2))) at hh
      refine ⟨by linarith [hh.1],by linarith [hh.2.1],?_⟩
      apply halve_checks mass f C (h+(mass P+E)+f n) bs
      convert hh.2.2 using 1 <;> ring
    | succ e =>
      change 0 ≤ 2*h+2*mass P+2*f n ∧ 2*h+2*mass P ≤ 2*C ∧
        earChecks (2*C) (2*E) (2*h+2*mass P+2*f n) e
          (bs.map (fun b => (2*mass b.1,2*f b.2))) at hh
      refine ⟨by linarith [hh.1],by linarith [hh.2.1],ih (h+mass P+f n) e ?_⟩
      convert hh.2.2 using 1 <;> ring

private theorem balanced_certificate (s : ℕ) (hs : 2≤s) (n : Fin 16) :
    Nonempty (Certificate (s+offsets n 0) (s+offsets n 1) (s+offsets n 2) (s+offsets n 3)) := by
  let a := s+offsets n 0
  let b := s+offsets n 1
  let c := s+offsets n 2
  let d := s+offsets n 3
  have ha : 2≤a := by dsimp [a]; omega
  have hb : 2≤b := by dsimp [b]; omega
  have hc : 2≤c := by dsimp [c]; omega
  have hd : 2≤d := by dsimp [d]; omega
  let q : ℤ := 2^s
  have hq : 4≤q := by
    simpa [q] using pow_le_pow_right₀ (by decide : (1:ℤ)≤2) hs
  have hp (r : Fin 4) : powers n q r = (2:ℤ)^(s+offsets n r) := by
    dsimp [powers,q]
    rw [pow_add]; ring
  have hbase : bases n q = base a b c d := by
    funext r
    fin_cases r <;> simp only [bases,base,hp,a,b,c,d,Matrix.cons_val_zero',Matrix.cons_val_succ']
  have hnewbase : newBases n q = newBase a b c d := by
    funext r
    fin_cases r <;> simp [newBases,newBase,charge,hbase,hp,a,b,c,d]
  have hmod : modulus n q = sourceMod a b c d := by
    dsimp [modulus,sourceMod]
    rw [hp,hp,hp,hp]
  have hlength (r : Fin 4) : lengths n q r = (2:ℤ)^(chainLength a b c d r) := by
    fin_cases r <;> simpa only [lengths,chainLength,a,b,c,d,Matrix.cons_val_zero',Matrix.cons_val_succ'] using hp _
  have hm (r : Fin 4) := assigned_masses a b c d ha hb hc hd n r
  have hD := source_doubles a b c d ha hb hc hd
  have hmold (r : Fin 4) : masses n q (bases n q) r =
      2*oldMass a b c d (assigned a b c d n r) := by
    rw [masses,hlength,hbase]
    exact (hm r).1.symm
  have hmnew (r : Fin 4) : masses n q (newBases n q) r =
      2*newMass a b c d (assigned a b c d n r) := by
    rw [masses,hlength,hnewbase]
    exact (hm r).2.symm
  have hdold (r : Fin 4) : drops n q r = 2*oldValue a b c d (negativeLabel a b c d r) := by
    rw [(hD.2 r).1]
    fin_cases r <;> simp [drops,nextBase,hbase,hmod]
  have hdnew (r : Fin 4) : newDrops n q r = 2*newValue a b c d (negativeLabel a b c d r) := by
    rw [(hD.2 r).2]
    fin_cases r <;> simp [newDrops,nextNewBase,hbase,hnewbase,hmod]
  have hmapped : (order n).map (fun r => (masses n q (bases n q) r,drops n q r)) =
      (packets a b c d n).map (fun blk => (2*oldMass a b c d blk.1,2*oldValue a b c d blk.2)) := by
    simp only [packets,List.map_map,Function.comp_def,hmold,hdold]
  have hmappednew : (order n).map (fun r => (masses n q (newBases n q) r,newDrops n q r)) =
      (packets a b c d n).map (fun blk => (2*newMass a b c d blk.1,2*newValue a b c d blk.2)) := by
    simp only [packets,List.map_map,Function.comp_def,hmnew,hdnew]
  have hpoly := polynomial_endpoints n q hq
  refine ⟨DataCertificate.mk (packets a b c d n) (negative_order a b c d ha hb hc hd n)
    (ear n) (packet_labels a b c d ha hb hc hd n)
    (physical_partition a b c d ha hb hc hd n) ?_ ?_⟩
  · apply halve_checks (oldMass a b c d) (oldValue a b c d) (sourceMod a b c d/2) 0
    simp only [mul_zero]
    rw [hD.1,← hmod]
    simpa only [hmapped] using hpoly.1
  · apply halve_ear_checks (newMass a b c d) (newValue a b c d) (sourceMod a b c d)
      (base a b c d 0) 0 (ear n).val
    simpa only [mul_zero,← hmod,← hbase,hmappednew] using hpoly.2

end D5.S3.Combinatorics.Circle.FourNegative.BalancedGaps
