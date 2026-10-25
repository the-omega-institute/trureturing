/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/AsymmetricThreeLabelCost
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/AsymmetricThreeLabelCost
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Arbitrary asymmetric three-label INITIAL phase sets have exact paid cost. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FiveLabelSeamCost

/-! # Asymmetric three-label acquisition with paid waiting -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe z

namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.AsymmetricThreeLabelCost

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S0.Tower.DBonacci.Names
open LiteralModel EndpointCells OriginalNarrowCost OriginalExecutionBridge
open WindowChargeInverse PhysicalWindowDecoder OriginalAcquiredTrace
open scoped BigOperators

private def pulse (g u : ℕ) (S : Finset ℕ) : Fin (g*u) → Bool :=
  fun i => decide (∃ t ∈ S, i.val+1=t*g)

private theorem pulse_head (g u : ℕ) (hg : 2 ≤ g) (hu : 1 ≤ u) (S : Finset ℕ)
    (support : ∀ t ∈ S, 1 ≤ t) : pulse g u S ⟨0, by nlinarith⟩ = false := by
  simp only [pulse, Fin.val_mk, Nat.zero_add, decide_eq_false_iff_not]
  rintro ⟨t,ht,eq⟩
  have := support t ht
  nlinarith

private theorem pulse_charge (g u p : ℕ) (hg : 2 ≤ g) (hu : 1 ≤ u) (hup : u < p)
    (S : Finset ℕ) (support : ∀ t ∈ S, 1 ≤ t ∧ t ≤ u)
    (j : ℕ) (hj : j < p) :
    wordIncrement (g*p-1) (-((j*g : ℕ) : ZMod (g*p-1+1))) (pulse g u S) =
      if j ∈ S then 1 else 0 := by
  have hT : g*p-1+1=g*p := by
    have : 0<g*p := by nlinarith
    omega
  have small : j*g < g*p-1+1 := by rw [hT]; nlinarith
  have hk : 3 ≤ g*p-1 := by nlinarith
  have short : g*u < g*p-1 := by nlinarith
  rw [increment_derivative _ hk _ short]
  rw [ZMod.val_natCast_of_lt small]
  have atVertex : extendedBit (pulse g u S) (j*g)=0 := by
    unfold extendedBit
    split_ifs with inside
    · simp only [bitScalar, pulse, Fin.val_mk]
      have absent : ¬∃ t ∈ S, j*g+1=t*g := by
        rintro ⟨t,ht,eq⟩
        have dv : g ∣ 1 := by
          have a : g ∣ j*g+1 := eq ▸ dvd_mul_left g t
          exact (Nat.dvd_add_iff_right (dvd_mul_left g j)).mpr a
        have := Nat.le_of_dvd (by decide : 0<1) dv
        omega
      simp [absent]
    · rfl
  rw [atVertex,zero_add]
  by_cases zero : j=0
  · subst j
    have absent : 0 ∉ S := by intro h; have := (support 0 h).1; omega
    simp [absent]
  · have jpos : 1 ≤ j := by omega
    rw [if_neg (by nlinarith : j*g ≠ 0)]
    by_cases inside : j*g-1 < g*u
    · have pos : 1 ≤ j*g := by nlinarith
      have eqs : (∃ t ∈ S, (j*g-1)+1=t*g) ↔ j ∈ S := by
        rw [Nat.sub_add_cancel pos]
        constructor
        · rintro ⟨t,ht,e⟩
          have : j=t := by nlinarith
          simpa only [this] using ht
        · intro h; exact ⟨j,h,rfl⟩
      simp [extendedBit, inside, bitScalar, pulse, eqs]
    · have absent : j ∉ S := by
        intro h
        have le := Nat.mul_le_mul_right g (support j h).2
        have pos : 1 ≤ j*g := by nlinarith
        have bound : j*g ≤ g*u := by nlinarith
        omega
      simp [extendedBit, inside, absent]

private theorem shifted_charge (g u p h r : ℕ) (hg : 2 ≤ g) (hu : 3 ≤ u)
    (hup : u < p) (hp : p=h*u+r) (hr : 1 ≤ r) (hru : r<u)
    (S : Finset ℕ) (support : ∀ t ∈ S, 1 ≤ t ∧ t ≤ u-r)
    (j : ℕ) (hj : j<p) :
    wordIncrement (g*p-1)
      (-((j*g : ℕ) : ZMod (g*p-1+1))+((h*(g*u) : ℕ) : ZMod (g*p-1+1)))
      (pulse g u (S.image (r+·))) = if j ∈ S then 1 else 0 := by
  have hh : 1 ≤ h := by
    by_contra hn
    have : h=0 := by omega
    simp_all
    omega
  have hT : g*p-1+1=g*p := by
    have : 0<g*p := by nlinarith
    omega
  have full : ((g*p : ℕ) : ZMod (g*p-1+1))=0 := by rw [← hT]; simp
  have stepNat : h*(g*u)+r*g=g*p := by rw [hp]; ring
  have step : ((h*(g*u) : ℕ) : ZMod (g*p-1+1))+((r*g : ℕ) : ZMod (g*p-1+1))=0 := by
    rw [← Nat.cast_add,stepNat,full]
  have shiftedSupport : ∀ t ∈ S.image (r+·), 1 ≤ t ∧ t ≤ u := by
    intro t ht
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
    have := support x hx
    omega
  by_cases nowrap : j+r<p
  · have phase : -((j*g : ℕ) : ZMod (g*p-1+1))+((h*(g*u) : ℕ) : ZMod (g*p-1+1)) =
        -(((j+r)*g : ℕ) : ZMod (g*p-1+1)) := by
      push_cast at step ⊢
      linear_combination step
    rw [phase,pulse_charge g u p hg (by omega) hup _ shiftedSupport _ nowrap]
    have mem : j+r ∈ S.image (r+·) ↔ j ∈ S := by
      constructor
      · rintro ht
        obtain ⟨x,hx,eq⟩ := Finset.mem_image.mp ht
        have : x=j := by omega
        simpa only [this] using hx
      · intro ht; exact Finset.mem_image.mpr ⟨j,ht,by omega⟩
    simp only [mem]
  · have low : p ≤ j+r := by omega
    have small : j+r-p<p := by omega
    have phase : -((j*g : ℕ) : ZMod (g*p-1+1))+((h*(g*u) : ℕ) : ZMod (g*p-1+1)) =
        -(((j+r-p)*g : ℕ) : ZMod (g*p-1+1)) := by
      simp only [Nat.cast_mul,Nat.cast_sub low,Nat.cast_add]
      push_cast at step full ⊢
      linear_combination step - full
    rw [phase,pulse_charge g u p hg (by omega) hup _ shiftedSupport _ small]
    have absent : j ∉ S := by
      intro ht
      have := support j ht
      have : u ≤ h*u := by nlinarith
      omega
    have shiftedAbsent : j+r-p ∉ S.image (r+·) := by
      intro ht
      obtain ⟨x,hx,eq⟩ := Finset.mem_image.mp ht
      have := support x hx
      omega
    simp [absent,shiftedAbsent]

private def words (g u h r : ℕ) (HB HC : Finset ℕ) : List (Fin (g*u) → Bool) :=
  pulse g u HC :: List.replicate (h-1) (fun _ => false) ++ [pulse g u (HB.image (r+·))]

private def label {Y : Type z} (HB HC : Finset ℕ) (A B C : Y) (j : ℕ) : Y :=
  if j ∈ HB then B else if j ∈ HC then C else A

private def decode {Y : Type z} {g u : ℕ} (A B C : Y) (v : ZMod 2)
    (archive : NarrowWindowCost.Archive (g*u)) : Y :=
  if (archive.head?).map Prod.snd = some (some (v+1)) then C
  else if ((archive.getLast?).map Prod.snd) =
    ((archive.head?).map Prod.snd).map (Option.map (·+1)) then B else A

private theorem pulse_tail_zero (g u : ℕ) (hg : 2 ≤ g) (hu : 1 ≤ u)
    (S : Finset ℕ) (support : ∀ t ∈ S, t<u) : tailAfter 0 (pulse g u S)=0 := by
  apply FiveLabelSeamCost.last_zero (g*u) (by nlinarith)
  simp only [pulse,Fin.val_mk,decide_eq_false_iff_not]
  rintro ⟨t,ht,hit⟩
  have := support t ht
  have pos : 1 ≤ g*u := by nlinarith
  rw [Nat.sub_add_cancel pos] at hit
  nlinarith

set_option maxHeartbeats 1200000 in
private theorem archive_correct {Y : Type z} (g u p h r : ℕ)
    (hg : 2 ≤ g) (hu : 3 ≤ u) (hup : u<p) (hp : p=h*u+r)
    (hr : 1 ≤ r) (hru : r<u) (HB HC : Finset ℕ) (disjoint : Disjoint HB HC)
    (boundB : ∀ t ∈ HB, 1 ≤ t ∧ t ≤ u-r)
    (boundC : ∀ t ∈ HC, 1 ≤ t ∧ t < u)
    (A B C : Y) (v : ZMod 2) (j s : ℕ) (hj : j<p) (hs : s<g*p-1) :
    decode A B C v (scriptArchive (words g u h r HB HC)
      (some ⟨v,-((j*g : ℕ) : ZMod (g*p-1+1)),s⟩)) = label HB HC A B C j := by
  have hh : 1 ≤ h := by
    by_contra hn
    have : h=0 := by omega
    simp_all
    omega
  have hk : 3 ≤ g*p-1 := by
    have : 4 ≤ g*p := by nlinarith
    omega
  have hm : 1 ≤ g*u := by nlinarith
  have short : g*u<g*p-1 := by
    have : g*u+2 ≤ g*p := by nlinarith
    omega
  let c : ZMod 2 := if j ∈ HC then 1 else 0
  let b : ZMod 2 := if j ∈ HB then 1 else 0
  have root := (short_safe_execution (g*p-1) (by omega) (g*u) hm short
    (pulse g u HC) v (-((j*g : ℕ) : ZMod (g*p-1+1))) s hs
    (Or.inr (pulse_head g u hg (by omega) HC (fun t ht => (boundC t ht).1)))).1
  rw [pulse_charge g u p hg (by omega) hup HC
    (fun t ht => ⟨(boundC t ht).1,by have := (boundC t ht).2; omega⟩) j hj,
    pulse_tail_zero g u hg (by omega) HC (fun t ht => (boundC t ht).2)] at root
  change _ = some (⟨v+c, -((j*g : ℕ) : ZMod (g*p-1+1))+(g*u : ℕ),0⟩ : LiveRecord (g*p-1)) at root
  have count : g*u+(h-1)*(g*u)=h*(g*u) := by
    have := Nat.sub_add_cancel hh
    nlinarith
  have phase : -((j*g : ℕ) : ZMod (g*p-1+1))+(g*u : ℕ)+
      (((h-1)*(g*u) : ℕ) : ZMod (g*p-1+1)) =
      -((j*g : ℕ) : ZMod (g*p-1+1))+((h*(g*u) : ℕ) : ZMod (g*p-1+1)) := by
    rw [add_assoc,← Nat.cast_add,count]
  have final := (short_safe_execution (g*p-1) (by omega) (g*u) hm short
    (pulse g u (HB.image (r+·))) (v+c)
    (-((j*g : ℕ) : ZMod (g*p-1+1))+((h*(g*u) : ℕ) : ZMod (g*p-1+1)))
    0 (by omega) (Or.inl rfl)).1
  rw [shifted_charge g u p h r hg hu hup hp hr hru HB boundB j hj] at final
  have issued : scriptArchive (words g u h r HB HC)
      (some ⟨v,-((j*g : ℕ) : ZMod (g*p-1+1)),s⟩) =
      (pulse g u HC,some (v+c)) ::
        (List.replicate (h-1) ((fun _ : Fin (g*u) => false),some (v+c)) ++
          [(pulse g u (HB.image (r+·)),some (v+c+b))]) := by
    simp only [words,List.cons_append,scriptArchive,root,endpointReading]
    rw [FiveLabelSeamCost.zero_script (g*p-1) (g*u) (by omega) hm short (h-1)]
    simp only [ite_self,phase,scriptArchive,final,endpointReading]
    rfl
  rw [issued]
  have different (x : ZMod 2) : x ≠ x+1 := by
    intro equal
    have : (0 : ZMod 2)=1 := add_left_cancel (show x+0=x+1 by simpa using equal)
    exact zero_ne_one this
  by_cases hb : j ∈ HB
  · have hc : j ∉ HC := fun hc => Finset.disjoint_left.mp disjoint hb hc
    simp [decode,List.getLast?_cons,List.getLast?_append,label,c,b,hb,hc,different]
  · by_cases hc : j ∈ HC
    · simp [decode,List.getLast?_cons,List.getLast?_append,label,c,b,hb,hc,different]
    · simp [decode,List.getLast?_cons,List.getLast?_append,label,c,b,hb,hc,different]

set_option maxHeartbeats 1800000 in
/-- The native INITIAL-label cost for arbitrary disjoint asymmetric phase sets.
The other free-value fiber and rejection label are unrestricted. Both choices of
complete-block alphabet use all actual histories, with every issued word paid.
The last natural quotient is the ceiling of p/u, since u is positive. -/
theorem original_asymmetric_three_label_cost {Y : Type z} (g u p h r : ℕ)
    (hg : 2 ≤ g) (hu : 3 ≤ u) (hup : u<p) (coprime : Nat.Coprime u p)
    (hp : p=h*u+r) (hr : 1 ≤ r) (hru : r<u)
    (HB HC : Finset ℕ) (nonemptyB : HB.Nonempty) (nonemptyC : HC.Nonempty)
    (disjoint : Disjoint HB HC)
    (boundB : ∀ j ∈ HB, 1 ≤ j ∧ j ≤ u-r)
    (boundC : ∀ j ∈ HC, 1 ≤ j ∧ j < u)
    (A B C : Y) (differentAB : A≠B) (differentAC : A≠C) (differentBC : B≠C) :
    let k := g*p-1
    let m := g*u
    let hk : 0<k := by
      have : 4 ≤ g*p := by nlinarith
      dsimp [k]; omega
    ∀ (f : Option (LiveRecord k) → Y) (v : ZMod 2) (alphabet : Bool),
    (∀ (j : Fin p) (s : ℕ), s<k →
      f (some ⟨v,-((j.val*g : ℕ) : ZMod (k+1)),s⟩) =
        if j.val ∈ HB then B else if j.val ∈ HC then C else A) →
    OriginalFiberCost k m hk alphabet f v = ((h+1 : ℕ) : ℕ∞) ∧
      h+1=(p+u-1)/u := by
  classical
  dsimp only
  intro f v alphabet target
  let k := g*p-1
  let m := g*u
  have hh : 1 ≤ h := by
    by_contra hn
    have : h=0 := by omega
    have : p=r := by simpa only [this,zero_mul,zero_add] using hp
    omega
  have period : k+1=g*p := by
    have : 0<g*p := by nlinarith
    dsimp [k]; omega
  have hk : 3 ≤ k := by
    have : 4 ≤ g*p := by nlinarith
    dsimp [k]; omega
  have hm : 1 ≤ m := by dsimp [m]; nlinarith
  have short : m<k := by
    have : g*u+2 ≤ g*p := by nlinarith
    dsimp [k,m]; omega
  have gcdEq : Nat.gcd m (k+1)=g := by
    change Nat.gcd (g*u) (k+1)=g
    rw [period,Nat.gcd_mul_left,coprime.gcd_eq_one,Nat.mul_one]
  have uEq : m/g=u := by dsimp [m]; exact Nat.mul_div_cancel_left u (by omega)
  have pEq : (k+1)/g=p := by rw [period]; exact Nat.mul_div_cancel_left p (by omega)
  have hEq : p/u=h := by
    apply Nat.div_eq_of_lt_le <;> nlinarith
  have restrict (j : Fin p) (s : ℕ) (hs : s<k) :
      f (some ⟨v,-((j.val*g : ℕ) : ZMod (k+1)),s⟩) = label HB HC A B C j.val :=
    target j s hs
  have zeroB : 0 ∉ HB := by intro mem; have := (boundB 0 mem).1; omega
  have zeroC : 0 ∉ HC := by intro mem; have := (boundC 0 mem).1; omega
  obtain ⟨b,hb⟩ := nonemptyB
  obtain ⟨c,hc⟩ := nonemptyC
  have bbound : b<u := by have := boundB b hb; omega
  have cbound : c<u := (boundC c hc).2
  have cnotB : c ∉ HB := fun mem => Finset.disjoint_left.mp disjoint mem hc
  let sample : Fin u → Y := fun j =>
    f (some ⟨v,-((j.val*g : ℕ) : ZMod (k+1)),0⟩)
  have sampled (j : Fin u) : sample j = label HB HC A B C j.val :=
    restrict ⟨j.val,lt_trans j.isLt hup⟩ 0 (by omega)
  let three : Fin 3 → Y := fun i => if i.val=0 then A else if i.val=1 then B else C
  have threeInjective : Function.Injective three := by
    intro i j equal
    fin_cases i <;> fin_cases j <;> simp_all [three]
  have rangeEq : Set.range sample=Set.range three := by
    ext y
    constructor
    · rintro ⟨j,rfl⟩
      rw [sampled]
      by_cases inB : j.val ∈ HB
      · exact ⟨1,by simp [three,label,inB]⟩
      · by_cases inC : j.val ∈ HC
        · exact ⟨2,by simp [three,label,inB,inC]⟩
        · exact ⟨0,by simp [three,label,inB,inC]⟩
    · rintro ⟨i,rfl⟩
      fin_cases i
      · exact ⟨⟨0,by omega⟩,by rw [sampled]; simp [three,label,zeroB,zeroC]⟩
      · exact ⟨⟨b,bbound⟩,by rw [sampled]; simp [three,label,hb]⟩
      · exact ⟨⟨c,cbound⟩,by rw [sampled]; simp [three,label,cnotB,hc]⟩
  have count : Nat.card (Set.range sample)=3 := by
    rw [rangeEq,Nat.card_range_of_injective threeInjective,Nat.card_fin]
  have sampleCount : Nat.card (Set.range (fun j : Fin (m/Nat.gcd m (k+1)) =>
      f (some ⟨v,-((j.val*Nat.gcd m (k+1) : ℕ) : ZMod (k+1)),0⟩)))=3 := by
    rw [gcdEq,uEq]
    exact count
  have lower := original_cost_lower k m (by omega) hm (by omega) f v alphabet
    (show 3 ≤ Nat.card (Set.range (fun j : Fin (m/Nat.gcd m (k+1)) =>
      f (some ⟨v,-((j.val*Nat.gcd m (k+1) : ℕ) : ZMod (k+1)),0⟩))) by rw [sampleCount])
  change (((((k+1)/Nat.gcd m (k+1))/(m/Nat.gcd m (k+1)))+
    Nat.clog 2 (Nat.card (Set.range (fun j : Fin (m/Nat.gcd m (k+1)) =>
      f (some ⟨v,-((j.val*Nat.gcd m (k+1) : ℕ) : ZMod (k+1)),0⟩))))-1 : ℕ) : ℕ∞) ≤ _ at lower
  rw [sampleCount,gcdEq,uEq,pEq,hEq] at lower
  have lowerBound : ((h+1 : ℕ) : ℕ∞) ≤ OriginalFiberCost k m (by omega) alphabet f v := by
    simpa only [show Nat.clog 2 3=2 from by decide,show h+2-1=h+1 by omega] using lower
  have upper : OriginalFiberFeasible k m (by omega) alphabet f v (h+1) := by
    let read : NarrowWindowCost.Archive m → Y := decode A B C v
    let π : NarrowWindowCost.Selector m Y := fun free archive =>
      match free with
      | none => .inl (f none)
      | some _ => finalSelector 0 (words g u h r HB HC) read free archive
    refine ⟨π,?_,rfl,?_⟩
    · intro free archive action _ _
      exact short_legal k m (by omega) short action
    · intro history
      dsimp only
      intro observed
      let w := history.flatMap (fun action => List.ofFn action.val)
      have outputV : NarrowWindowCost.output k (by omega) w=some v := observed
      have outputEq : NarrowWindowCost.output k (by omega) w=
          endpointReading (OriginalRecord k (by omega) w) := output_record k (by omega) w
      obtain ⟨q,record⟩ : ∃ q : LiveRecord k, OriginalRecord k (by omega) w=some q := by
        cases current : OriginalRecord k (by omega) w with
        | none => rw [outputEq,current] at outputV; contradiction
        | some q => exact ⟨q,rfl⟩
      have qValue : q.value=v := by
        rw [outputEq,record] at outputV
        exact Option.some.inj outputV
      have actual : SourceRecord k m (some q) := by
        apply ((whole_first_zero_acquisition k m (by omega) hm alphabet (fun _ => ())).1 (some q)).mpr
        refine ⟨history,?_⟩
        rw [←record_history k m (by omega) alphabet history]
        exact record
      have divides : g ∣ (-q.phase).val := by
        have dv : g ∣ q.phase.val := by simpa only [gcdEq] using actual.2
        rw [ZMod.neg_val]
        split_ifs
        · exact dvd_zero _
        · exact Nat.dvd_sub (by rw [period]; exact dvd_mul_right g p) dv
      let j : Fin p := ⟨(-q.phase).val/g,
        (Nat.div_lt_iff_lt_mul (by omega : 0<g)).mpr
          (by simpa only [Nat.mul_comm,period] using ZMod.val_lt (-q.phase))⟩
      have phase : -((j.val*g : ℕ) : ZMod (k+1))=q.phase := by
        dsimp only [j]
        rw [Nat.div_mul_cancel divides,ZMod.natCast_zmod_val,neg_neg]
      have shape : q=⟨v,-((j.val*g : ℕ) : ZMod (k+1)),q.tail⟩ := by
        cases q
        simp_all only
      have decoded : read (scriptArchive (words g u h r HB HC)
          (OriginalRecord k (by omega) w))=f (OriginalRecord k (by omega) w) := by
        rw [record,shape]
        exact (archive_correct g u p h r hg hu hup hp hr hru HB HC disjoint boundB boundC
          A B C v j.val q.tail j.isLt actual.1).trans (restrict j q.tail actual.1).symm
      have script := original_final_script k m (by omega) (words g u h r HB HC) read w (some v) []
      dsimp only at script
      have length : (words g u h r HB HC).length=h+1 := by
        simp only [words,List.length_cons,List.length_append,List.length_replicate,List.length_singleton]
        omega
      have trace := (FullPositiveWindowPrice.trace_congr π
        (finalSelector 0 (words g u h r HB HC) read) (some v) (by intro ar; rfl)
        _ _ _ _).mpr script.1
      rw [decoded] at trace
      refine ⟨h+1,le_rfl,?_⟩
      rw [execute_paid_trace k m (by omega)]
      exact ⟨_,trace,script.2.2.1.trans length,le_rfl⟩
  refine ⟨le_antisymm (iInf_le_of_le ⟨h+1,upper⟩ le_rfl) lowerBound,?_⟩
  symm
  apply Nat.div_eq_of_lt_le <;> nlinarith

#print axioms original_asymmetric_three_label_cost

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.AsymmetricThreeLabelCost
