/- GID: D5/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Endpoint
   mirror-E: none(waiver:physical-packet-reduction)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Exact four-packet equivalence for all independent four-gap sources. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Equivalence

/-! A reduction of unrestricted physical joint orders, not a uniform allocation theorem. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
open SourceWidth PeriodicShortening RunFirstEarTransport
open private size seed sourceMod base newBase oldValue newValue negatives
  weightedMask packet_masses source_signs source_totals chain_values negatives_nodup actual_values
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private insertAt from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private strip_of_prefix from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Transport
open private DataCertificate from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Certificate
open private physical_packet_equivalence
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Equivalence
open private label lift_order marked_word
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

private def oldMass (a b c d : ℕ) (P : Finset ℕ) : ℤ :=
  ∑ r : Fin 4, base a b c d r * weightedMask b c d P r
private def newMass (a b c d : ℕ) (P : Finset ℕ) : ℤ :=
  ∑ r : Fin 4, newBase a b c d r * weightedMask b c d P r

/-- Four unordered physical packets, one negative order and one pre-negative ear slot. -/
abbrev Certificate (a b c d : ℕ) :=
  DataCertificate (size a b c d) (oldValue a b c d) (newValue a b c d)
    (sourceMod a b c d / 2) (sourceMod a b c d) (base a b c d 0)
    (negatives a b c d) (oldMass a b c d) (newMass a b c d)

private theorem actual_nat_joint_iff (a b c d : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) :
    (∃ sigma : List (Fin (a+b+c+d)), ∃ j : ℕ, j ≤ a+b+c+d ∧
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma j)) ↔
    (∃ l : List ℕ, l.Perm (List.range (size a b c d)) ∧
      InStrip (oldValue a b c d) (sourceMod a b c d / 2) 0 l ∧
      ∃ j : ℕ, j ≤ size a b c d ∧
        InStrip (newValue a b c d) (sourceMod a b c d) 0 (insertAt (size a b c d) l j)) := by
  let k := a+b+c+d
  let A := 1+2^a+2^(a+b)+2^(a+b+c)
  let N := sourceMod a b c d
  let f := oldValue a b c d
  let g := newValue a b c d
  have hmod : modulus k = N := by dsimp [k,N,size,modulus,sourceMod]; ring
  have hmod' : modulus (k+1) = 2*N+1 := by dsimp [k,N,size,modulus,sourceMod]; ring
  have hhalf : (2*N+1)/2 = N := by omega
  have hseed : (A : ℤ) = base a b c d 0 := by
    dsimp [A,seed]
    push_cast
    dsimp [base]
    ring
  have hseed' : ((2*A : ℕ) : ℤ) = 2 * base a b c d 0 := by push_cast; rw [hseed]
  have hv := actual_values a b c d
  have hfmap (xs : List (Fin k)) : xs.map (actualSource k A) = (xs.map Fin.val).map f := by
    rw [List.map_map]
    exact List.map_congr_left (fun p _ => hv.1 p)
  have hgmap (xs : List (Fin (k+1))) :
      xs.map (actualSource (k+1) (2*A)) = (xs.map Fin.val).map g := by
    rw [List.map_map]
    exact List.map_congr_left (fun p _ => hv.2 p)
  constructor
  · rintro ⟨sigma,j,hj,hold,hnew⟩
    change OriginalOrder k A sigma at hold
    change OriginalOrder (k+1) (2*A) (earWord k sigma j) at hnew
    let l := sigma.map Fin.val
    have hfr : (List.finRange k).map Fin.val = List.range k := by
      apply List.ext_getElem
      · simp
      · intro i hi hi'; simp
    have hp : l.Perm (List.range k) := (hold.1.map Fin.val).trans (List.Perm.of_eq hfr)
    have holdstrip : InStrip f (N/2) 0 l := by
      apply strip_of_prefix
      intro n
      have he : ((l.take n).map f).sum = ((sigma.take n).map (actualSource k A)).sum := by
        rw [hfmap (sigma.take n)]
        simp only [l,List.map_take]
        rfl
      rw [zero_add,he]
      simpa only [hmod,Set.mem_Icc] using hold.2.2 n
    have hearvalues : (earWord k sigma j).map Fin.val = insertAt k l j := by
      simp [earWord,insertAt,l,List.map_map,Function.comp_def,List.map_take,List.map_drop]
      rfl
    have hnewstrip : InStrip g N 0 (insertAt k l j) := by
      apply strip_of_prefix
      intro n
      have he : (((insertAt k l j).take n).map g).sum =
          (((earWord k sigma j).take n).map (actualSource (k+1) (2*A))).sum := by
        rw [hgmap ((earWord k sigma j).take n)]
        simp only [hearvalues,List.map_take]
      rw [zero_add,he]
      simpa only [hmod',hhalf,Set.mem_Icc] using hnew.2.2 n
    exact ⟨l,hp,holdstrip,j,hj,hnewstrip⟩
  · rintro ⟨l,hp,hold,j,hj,hnew⟩
    change l.Perm (List.range k) at hp
    change j ≤ k at hj
    change InStrip (fun i => centered N ((2 : ℤ)^i * base a b c d 0)) (N/2) 0 l at hold
    change InStrip (fun i => centered (2*N+1)
      ((2 : ℤ)^i * (2 * base a b c d 0))) N 0 (insertAt k l j) at hnew
    have hk : 0 < k := by dsimp [k,size]; omega
    let pre := l.take j
    let post := l.drop j
    have heword : pre ++ post = l := List.take_append_drop j l
    have hprelen : pre.length = j := by
      have hh := hp.length_eq
      simp only [List.length_range] at hh
      simp [pre,List.length_take,Nat.min_eq_left (by omega : j ≤ l.length)]
    have hp' : (pre ++ k :: post).Perm (List.range (k+1)) := by
      have hreorder : (pre ++ k :: post).Perm (l ++ [k]) := by
        rw [← heword]
        simpa [List.append_assoc] using
          (List.perm_append_singleton k post).symm.append_left pre
      exact hreorder.trans (by simpa [List.range_succ] using hp.append_right [k])
    have hold' : OriginalOrder k A (l.map (label k hk)) := by
      apply lift_order k A hk l hp
      · simpa only [hmod,hseed] using hold
      · exact ThreeNegativeEqualOuterSourceBridge.source_zero k A (by dsimp [k,size]; omega)
    have hnew' : OriginalOrder (k+1) (2*A)
        ((pre ++ k :: post).map (label (k+1) (by omega))) := by
      apply lift_order (k+1) (2*A) (by omega) (pre ++ k :: post) hp'
      · simpa only [hmod',hseed',hhalf,insertAt,pre,post] using hnew
      · exact ThreeNegativeEqualOuterSourceBridge.source_zero (k+1) (2*A)
          (by dsimp [k,size]; omega)
    refine ⟨l.map (label k hk),j,hj,hold',?_⟩
    rw [← heword]
    rw [marked_word k j hk pre post hprelen (by simpa [heword] using hp)]
    exact hnew'

/-- This characterizes joint orders; it does not assert uniform certificate existence. -/
theorem actual_four_packet_iff (a b c d : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) :
    (∃ sigma : List (Fin (a+b+c+d)), ∃ j : ℕ, j ≤ a+b+c+d ∧
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma j)) ↔ Nonempty (Certificate a b c d) := by
  have hsource := chain_values a b c d ha hb hc hd
  have hN : 0 < sourceMod a b c d := by have h := hsource.1 0; omega
  have hA : 0 < base a b c d 0 := by have h := hsource.1 0; omega
  have htotal := source_totals a b c d ha hb hc hd
  apply (actual_nat_joint_iff a b c d ha hb hc hd).trans
  apply physical_packet_equivalence (size a b c d) (oldValue a b c d) (newValue a b c d)
    (sourceMod a b c d / 2) (sourceMod a b c d) (base a b c d 0)
    (negatives a b c d) (oldMass a b c d) (newMass a b c d)
    (by omega) hN.le hA htotal.2.2 (negatives_nodup a b c d ha hb hc hd)
    (by simp [negatives])
  · intro n hn
    simp only [negatives,List.mem_cons,List.mem_nil_iff,or_false,size] at hn ⊢
    omega
  · exact source_signs a b c d ha hb hc hd
  · exact htotal.1
  · exact htotal.2.1
  · intro P hp
    exact (packet_masses a b c d ha hb hc hd P hp).1.symm
  · intro P hp
    exact (packet_masses a b c d ha hb hc hd P hp).2.symm

end D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
