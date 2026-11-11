/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualFirstTwoPlusTwo/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualFirstTwoPlusTwo/Endpoint
   mirror-E: none(waiver:physical-dependent-source-registration-at-endpoint)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Complete original physical joint lift for every 2<=a and a+2<=d with gaps (a,a,d+2,d). -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo.Physical
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

/-! Physical joint lift for every original(a,a,d+2,d) with 2 ≤ a and a+2 ≤ d.
The unrestricted Circle problem remains open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo
open SourceWidth PeriodicShortening RunFirstEarTransport
open private allocation
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo.Selection
open private physical_order
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo.Physical
open private seed sourceMod source_totals from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (size base oldValue newValue)
open private label lift_order marked_word
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
open private zero_period_transport
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint

private theorem nat_construction (a d : ℕ) (ha : 2≤a) (had : a+2≤d) :
    ∃ pre tail : List ℕ,
      (pre++(2*a+2*d+2-1)::tail).Perm (List.range (2*a+2*d+2)) ∧
      InStrip (oldValue a a (d+2) d) (sourceMod a a (d+2) d/2) 0
        (pre++(2*a+2*d+2-1)::tail) ∧
      InStrip (newValue a a (d+2) d) (sourceMod a a (d+2) d) 0
        (pre++(2*a+2*d+2)::(2*a+2*d+2-1)::tail) := by
  by_cases hl : 3≤a ∨ 7≤d
  · obtain ⟨u,v,hu,hv,hw⟩:=allocation a d ha had hl
    exact physical_order a d u v ha had hu hv hw
  · have he : a=2 := by omega
    subst a
    rcases (show d=4 ∨ d=5 ∨ d=6 by omega) with rfl|rfl|rfl
    · refine ⟨[1,2,9,10,4,11,12,5,7],[0,6,8,3],?_,?_,?_⟩
      · decide
      · norm_num [InStrip,oldValue,sourceMod,base,centered]
      · norm_num [InStrip,newValue,sourceMod,base,centered]
    · refine ⟨[0,1,2,3,11,12,13,14,5,6,7,8],[9,10,4],?_,?_,?_⟩
      · decide
      · norm_num [InStrip,oldValue,sourceMod,base,centered]
      · norm_num [InStrip,newValue,sourceMod,base,centered]
    · refine ⟨[0,1,3,4,13,14,15,16,6,7,9,11],[2,8,10,12,5],?_,?_,?_⟩
      · decide
      · norm_num [InStrip,oldValue,sourceMod,base,centered]
      · norm_num [InStrip,newValue,sourceMod,base,centered]

/-- Original physical permutation, fresh label immediately before nX, both scalar
orders, separate totals, and every natural finite repetition and take. -/
theorem actualSource_third_peak_equal_first_two_plus_two_joint_lift
    (a d : ℕ) (ha : 2≤a) (had : a+2≤d) :
    let k:=2*a+2*d+2
    let s:=1+2^a+2^(2*a)+2^(2*a+d+2)
    ∃ sigma : List (Fin k), ∃ j : ℕ,
      j<k ∧ (sigma.map Fin.val)[j]?=some (k-1) ∧
      ((earWord k sigma j).map Fin.val)[j]?=some k ∧
      ((earWord k sigma j).map Fin.val)[j+1]?=some (k-1) ∧
      OriginalOrder k s sigma ∧
      OriginalOrder (k+1) (2*s) (earWord k sigma j) ∧
      (sigma.map (fun p => actualSource (k+1) (2*s) p.castSucc)).sum=-(s:ℤ) ∧
      actualSource (k+1) (2*s) (Fin.last k)=(s:ℤ) ∧
      (∀ m n : ℕ, ((((List.replicate m sigma).flatten).take n).map
        (actualSource k s)).sum∈Set.Icc (0:ℤ) (modulus k/2)) ∧
      (∀ m n : ℕ, ((((List.replicate m (earWord k sigma j)).flatten).take n).map
        (actualSource (k+1) (2*s))).sum∈Set.Icc (0:ℤ) (modulus k)) ∧
      (∀ m : ℕ,
        (((List.replicate m sigma).flatten).map (actualSource k s)).sum=0 ∧
        (((List.replicate m (earWord k sigma j)).flatten).map
          (actualSource (k+1) (2*s))).sum=0) := by
  dsimp only
  let k:=2*a+2*d+2
  let s:=1+2^a+2^(2*a)+2^(2*a+d+2)
  let N:=sourceMod a a (d+2) d
  let AA:=base a a (d+2) d 0
  let f:=oldValue a a (d+2) d
  let g:=newValue a a (d+2) d
  have hk : 0<k := by dsimp [k]; omega
  have he : a+a+(d+2)+d=k := by dsimp [k]; omega
  have hsize : size a a (d+2) d=k := he
  have hs : seed a a (d+2)=s := by
    simp [seed,s,Nat.add_assoc,show a+a=2*a by omega,show a+a+(d+2)=2*a+d+2 by omega]
  have hseed : (s:ℤ)=AA := by
    rw [←hs]
    dsimp [seed,AA,base]
    push_cast
    simp only [pow_add]
    ring
  have hseed' : ((2*s:ℕ):ℤ)=2*AA := by push_cast; rw [hseed]
  have hmod : modulus k=N := by
    rw [←he]
    dsimp [modulus,N,sourceMod]
    simp only [pow_add]
  have hmod' : modulus (k+1)=2*N+1 := by
    dsimp [modulus] at hmod ⊢
    rw [pow_succ]
    linarith only [hmod]
  have half : modulus (k+1)/2=modulus k := by rw [hmod',hmod]; omega
  obtain ⟨pre,tail,hp,ho,hn⟩:=nat_construction a d ha had
  let l:=pre++(k-1)::tail
  let plus:=pre++k::(k-1)::tail
  change l.Perm (List.range k) at hp
  change InStrip f (N/2) 0 l at ho
  change InStrip g N 0 plus at hn
  have hlen : l.length=k := by simpa using hp.length_eq
  have hcut : pre.length<k := by dsimp [l] at hlen; simp only [List.length_append,List.length_cons] at hlen; omega
  have hpplus : plus.Perm (List.range (k+1)) := by
    have hreorder : plus.Perm (l++[k]) := by
      dsimp [plus,l]
      simpa [List.append_assoc] using
        (List.perm_append_singleton k ((k-1)::tail)).symm.append_left pre
    exact hreorder.trans (by simpa [List.range_succ] using hp.append_right [k])
  have totals:=source_totals a a (d+2) d ha ha (by omega) (by omega)
  have hzold : ((List.range k).map f).sum=0 := by simpa only [hsize] using totals.1
  have hznewold : ((List.range k).map g).sum=-AA := by simpa only [hsize] using totals.2.1
  have hfresh : g k=AA := by simpa only [hsize] using totals.2.2
  have hznew : ((List.range (k+1)).map g).sum=0 := by
    rw [List.range_succ,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,
      hznewold,hfresh]
    ring
  have oldOrder : OriginalOrder k s (l.map (label k hk)) := by
    apply lift_order k s hk l hp
    · rw [hmod,hseed]
      exact ho
    · rw [hmod,hseed]
      exact hzold
  have newOrder : OriginalOrder (k+1) (2*s) (plus.map (label (k+1) (by omega))) := by
    apply lift_order (k+1) (2*s) (by omega) plus hpplus
    · rw [half,hmod',hmod,hseed']
      exact hn
    · rw [hmod',hseed']
      exact hznew
  have marked : earWord k (l.map (label k hk)) pre.length=
      plus.map (label (k+1) (by omega)) :=
    marked_word k pre.length hk pre ((k-1)::tail) rfl hp
  let sigma:=l.map (label k hk)
  let j:=pre.length
  have oldvals : sigma.map Fin.val=l := by
    dsimp [sigma]
    rw [List.map_map]
    have hm : l.map (fun i => (label k hk i).val)=l.map id := by
      apply List.map_congr_left
      intro i hi
      have hib : i<k := List.mem_range.mp (hp.mem_iff.mp hi)
      simp [label,Nat.mod_eq_of_lt hib]
    simpa only [List.map_id,Function.comp_def] using hm
  have newvals : (earWord k sigma j).map Fin.val=plus := by
    rw [show earWord k sigma j=plus.map (label (k+1) (by omega)) from marked]
    rw [List.map_map]
    have hm : plus.map (fun i => (label (k+1) (by omega) i).val)=plus.map id := by
      apply List.map_congr_left
      intro i hi
      have hib : i<k+1 := List.mem_range.mp (hpplus.mem_iff.mp hi)
      simp [label,Nat.mod_eq_of_lt hib]
    simpa only [List.map_id,Function.comp_def] using hm
  have oldNewMap : sigma.map (fun p => actualSource (k+1) (2*s) p.castSucc)=l.map g := by
    dsimp [sigma]
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    have hib : i<k := List.mem_range.mp (hp.mem_iff.mp hi)
    simp only [Function.comp_def,actualSource,Fin.val_castSucc,label,Nat.mod_eq_of_lt hib,hmod',hseed',g,newValue,N,AA]
  have oldNewTotal : (sigma.map (fun p => actualSource (k+1) (2*s) p.castSucc)).sum=-(s:ℤ) := by
    rw [oldNewMap,(hp.map g).sum_eq,hznewold,hseed]
  have actualFresh : actualSource (k+1) (2*s) (Fin.last k)=(s:ℤ) := by
    change centered (modulus (k+1)) ((2:ℤ)^k*((2*s:ℕ):ℤ))=(s:ℤ)
    rw [hmod',hseed',hseed]
    exact hfresh
  have oldFinal : OriginalOrder k s sigma := oldOrder
  have newFinal : OriginalOrder (k+1) (2*s) (earWord k sigma j) := by rw [marked]; exact newOrder
  have eo (m : ℕ):=zero_period_transport _ _ sigma oldFinal.2.1 oldFinal.2.2 m
  have en (m : ℕ):=zero_period_transport _ _ (earWord k sigma j) newFinal.2.1 newFinal.2.2 m
  refine ⟨sigma,j,hcut,?_,?_,?_,oldFinal,newFinal,oldNewTotal,actualFresh,
    fun m => (eo m).2,fun m n => ?_,fun m => ⟨(eo m).1,(en m).1⟩⟩
  · rw [oldvals]
    simp [l,j,k]
  · rw [newvals]
    simp [plus,j,k]
  · rw [newvals]
    simp [plus,j,k]
  · simpa only [half] using (en m).2 n

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo
