/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakPlusTwoTwoU/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/ThirdPeakPlusTwoTwoU/Endpoint
   mirror-E: none(waiver:physical-dependent-source-registration-at-endpoint)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Complete original physical joint lift for gaps (a,b,d+2,d), 2<=b<a, and a+3<=d or b=2 and d=a+2. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPlusTwoTwoU.Physical
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

/-! Physical joint lift on the full original-source domains stated below.
The unrestricted Circle problem remains open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPlusTwoTwoU
open SourceWidth PeriodicShortening RunFirstEarTransport
open private base sourceMod oldValue newValue from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (size)
open private banks terminals pre post word marked
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPlusTwoTwoU.Banks
open private physical_word from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPlusTwoTwoU.Physical
open private label lift_order marked_word from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
open private zero_period_transport from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

/-- The unchanged original seed, a permutation of every original physical label,
a literal fresh ear immediately before nX, both full orders, all natural finite
repetitions and takes, and independent old/new zero totals. -/
theorem actualSource_third_peak_plus_two_two_U_joint_lift (a b d : ℕ)
    (hb : 2≤b) (hba : b<a) (hdom : a+3≤d ∨ b=2 ∧ d=a+2) :
    ∃ sigma : List (Fin (a+b+(d+2)+d)), ∃ j : ℕ,
      j<a+b+(d+2)+d ∧
      (sigma.map Fin.val)[j]?=some (a+b+(d+2)+d-1) ∧
      OriginalOrder (a+b+(d+2)+d) (1+2^a+2^(a+b)+2^(a+b+(d+2))) sigma ∧
      OriginalOrder (a+b+(d+2)+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+(d+2))))
        (earWord (a+b+(d+2)+d) sigma j) ∧
      (∀ m n : ℕ, ((((List.replicate m sigma).flatten).take n).map
        (actualSource (a+b+(d+2)+d) (1+2^a+2^(a+b)+2^(a+b+(d+2))))).sum ∈
        Set.Icc (0:ℤ) (modulus (a+b+(d+2)+d)/2)) ∧
      (∀ m n : ℕ, ((((List.replicate m (earWord (a+b+(d+2)+d) sigma j)).flatten).take n).map
        (actualSource (a+b+(d+2)+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+(d+2)))))).sum ∈
        Set.Icc (0:ℤ) (modulus (a+b+(d+2)+d))) ∧
      (∀ m : ℕ,
        (((List.replicate m sigma).flatten).map
          (actualSource (a+b+(d+2)+d) (1+2^a+2^(a+b)+2^(a+b+(d+2))))).sum=0 ∧
        (((List.replicate m (earWord (a+b+(d+2)+d) sigma j)).flatten).map
          (actualSource (a+b+(d+2)+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+(d+2)))))).sum=0) := by
  obtain ⟨u,v,hp,hold,hnew⟩ := physical_word a b d hb hba hdom
  let k:=a+b+(d+2)+d
  let seed:=1+2^a+2^(a+b)+2^(a+b+(d+2))
  let l:=word a b (d+2) d u v
  let j:=(pre a b (d+2) d u v).length
  have hk : 0<k := by dsimp [k]; omega
  change l.Perm (List.range k) at hp
  have hmod : modulus k=sourceMod a b (d+2) d := by
    dsimp [modulus,k,sourceMod]; ring
  have hmod' : modulus (k+1)=2*sourceMod a b (d+2) d+1 := by
    dsimp [modulus,k,sourceMod]; ring
  have hhalf : (2*sourceMod a b (d+2) d+1)/2=sourceMod a b (d+2) d := by omega
  have hseed : (seed:ℤ)=base a b (d+2) d 0 := by
    dsimp [seed]
    push_cast
    dsimp [base]
    ring
  have hseed' : ((2*seed:ℕ):ℤ)=2*base a b (d+2) d 0 := by push_cast; rw [hseed]
  let sigma:=l.map (label k hk)
  have hval : sigma.map Fin.val=l := by
    change (l.map (label k hk)).map Fin.val=l
    rw [List.map_map]
    have he : l.map (Fin.val ∘ label k hk)=l.map id := by
      apply List.map_congr_left
      intro i hi
      have hib : i<k := List.mem_range.mp (hp.mem_iff.mp hi)
      simp [Function.comp_def,label,Nat.mod_eq_of_lt hib]
    simpa only [List.map_id] using he
  have hlen : l.length=k := by simpa only [List.length_range] using hp.length_eq
  have hj : j<k := by
    have he : l.length=j+1+(banks a b (d+2) d u v 3).length+1 := by
      simp [l,word,post,j,List.length_append,Nat.add_assoc] <;> omega
    omega
  have getAt (P R : List ℕ) (n : ℕ) : (P++n::R)[P.length]?=some n := by
    induction P with
    | nil => rfl
    | cons i P ih => simpa using ih
  have hnX : (sigma.map Fin.val)[j]?=some (k-1) := by
    rw [hval]
    change (pre a b (d+2) d u v++
      (k-1)::(banks a b (d+2) d u v 3++[d-1]))[(pre a b (d+2) d u v).length]?=some (k-1)
    exact getAt _ _ _
  have hpnew : (marked a b (d+2) d u v).Perm (List.range (k+1)) := by
    have hm : (marked a b (d+2) d u v).Perm (l++[k]) := by
      change (pre a b (d+2) d u v++[k]++post a b (d+2) d u v).Perm
        ((pre a b (d+2) d u v++post a b (d+2) d u v)++[k])
      apply Multiset.coe_eq_coe.mp
      simp only [←Multiset.coe_add]
      ac_rfl
    exact hm.trans (by simpa only [List.range_succ] using hp.append_right [k])
  have oldOrder : OriginalOrder k seed sigma := by
    apply lift_order k seed hk l hp
    · rw [hmod,hseed]
      exact hold
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero k seed (by dsimp [k]; omega)
  have markedEq : earWord k sigma j=
      (marked a b (d+2) d u v).map (label (k+1) (by omega)) := by
    simpa only [sigma,l,word,marked,size,List.append_assoc,List.singleton_append] using
      marked_word k j hk (pre a b (d+2) d u v) (post a b (d+2) d u v) rfl hp
  have newOrder : OriginalOrder (k+1) (2*seed) (earWord k sigma j) := by
    rw [markedEq]
    apply lift_order (k+1) (2*seed) (by omega) (marked a b (d+2) d u v) hpnew
    · rw [hmod',hseed',hhalf]
      exact hnew
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero (k+1) (2*seed) (by dsimp [k]; omega)
  have eo (m : ℕ) := zero_period_transport _ _ sigma oldOrder.2.1 oldOrder.2.2 m
  have en (m : ℕ) := zero_period_transport _ _ (earWord k sigma j) newOrder.2.1 newOrder.2.2 m
  have half : modulus (k+1)/2=modulus k := by
    have hh : (2:ℤ)^(k+1)=2*(2:ℤ)^k := by rw [pow_succ]; ring
    dsimp [modulus]
    rw [hh]
    omega
  exact ⟨sigma,j,hj,hnX,oldOrder,newOrder,fun m => (eo m).2,
    fun m n => by simpa only [half] using (en m).2 n,
    fun m => ⟨(eo m).1,(en m).1⟩⟩

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPlusTwoTwoU
