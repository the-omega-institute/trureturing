/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FiveLabelSeamCost
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FiveLabelSeamCost
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Five original INITIAL phase labels have exact paid seam cost h plus two. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FullPositiveWindowPrice

/-! # Exact paid cost for five initial phase labels -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe z

namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FiveLabelSeamCost

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S0.Tower.DBonacci.Names
open D5.S0.Automata.TypedPartialDFAOOverBase
open LiteralModel EndpointCells OriginalNarrowCost OriginalExecutionBridge
open WindowChargeInverse PhysicalWindowDecoder OriginalAcquiredTrace
open scoped BigOperators

private def labelIndex (j : ℕ) : Fin 5 := if hj : j < 5 then ⟨j,hj⟩ else 0

private def pulse (g : ℕ) (S : Finset ℕ) : Fin (5*g) → Bool :=
  fun i => decide (∃ t ∈ S, i.val+1=t*g)

private theorem pulse_head (g : ℕ) (hg : 2 ≤ g) (S : Finset ℕ)
    (support : ∀ t ∈ S, 1 ≤ t) : pulse g S ⟨0, by omega⟩ = false := by
  simp only [pulse, Fin.val_mk, Nat.zero_add, decide_eq_false_iff_not]
  rintro ⟨t,ht,eq⟩
  have := support t ht
  nlinarith

private theorem pulse_charge (g p : ℕ) (hg : 2 ≤ g) (hp : 6 ≤ p)
    (S : Finset ℕ) (support : ∀ t ∈ S, 1 ≤ t ∧ t ≤ 5)
    (j : ℕ) (hj : j < p) :
    wordIncrement (g*p-1) (-((j*g : ℕ) : ZMod (g*p-1+1))) (pulse g S) =
      if j ∈ S then 1 else 0 := by
  have hT : g*p-1+1=g*p := by
    have pos : 0<g*p := by positivity
    exact Nat.sub_add_cancel pos
  have small : j*g < g*p-1+1 := by rw [hT]; nlinarith
  have hk : 3 ≤ g*p-1 := by nlinarith
  have short : 5*g < g*p-1 := by nlinarith
  rw [increment_derivative _ hk _ short]
  rw [ZMod.val_natCast_of_lt small]
  have atVertex : extendedBit (pulse g S) (j*g)=0 := by
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
    by_cases inside : j*g-1 < 5*g
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
        omega
      simp [extendedBit, inside, absent]

private theorem zero_script (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m)
    (short : m < k) (n : ℕ) (words : List (Fin m → Bool))
    (v : ZMod 2) (phase : ZMod (k+1)) (s : ℕ) (hs : s < k) :
    scriptArchive (List.replicate n (fun _ : Fin m => false) ++ words)
      (some ⟨v,phase,s⟩) =
    List.replicate n ((fun _ : Fin m => false),some v) ++
      scriptArchive words (some ⟨v,phase+((n*m : ℕ) : ZMod (k+1)),
        if n=0 then s else 0⟩) := by
  induction n generalizing phase s with
  | zero => simp
  | succ n ih =>
    have ex := (short_safe_execution k hk m hm short (fun _ => false)
      v phase s hs (Or.inr rfl)).1
    have tail : tailAfter 0 (fun _ : Fin m => false)=0 := by
      obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m≠0)
      apply last_false_tail
      rfl
    simp only [wordIncrement,Bool.false_eq_true,if_false,Finset.sum_const_zero,
      add_zero,tail] at ex
    simp only [List.replicate_succ,List.cons_append,scriptArchive,ex,endpointReading]
    rw [ih _ 0 (by omega)]
    simp only [ite_self]
    congr 3 <;> push_cast <;> ring

private theorem lead_safe (k m : ℕ) (hk : 3 ≤ k) (hm : 2 ≤ m) (short : m<k)
    (v : ZMod 2) (phase : ZMod (k+1)) (s : ℕ) (safe : s+1<k) :
    runBits k (fun i : Fin m => decide (i.val=0)) (some ⟨v,phase,s⟩) =
      some ⟨v+wordIncrement k phase (fun i : Fin m => decide (i.val=0)),
        phase+(m : ℕ),0⟩ := by
  obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le hm
  have size : m=n+2 := by omega
  clear hn
  subst m
  let B : Fin (n+2) → Bool := fun i => decide (i.val=0)
  have restZero : Fin.tail (Fin.tail B)=(fun _ : Fin n => false) := by
    funext i
    simp [B,Fin.tail]
  have cut : List.ofFn B=List.replicate 1 true ++ false ::
      List.ofFn (Fin.tail (Fin.tail B)) := by
    rw [List.ofFn_succ,List.ofFn_succ]
    rfl
  have ex := first_zero_block_exact k (by omega) (n+2) 1 B
    (List.ofFn (Fin.tail (Fin.tail B))) cut
    (short_legal k (n+2) (by omega) short B) v phase s (by omega)
  rw [if_pos safe] at ex
  have tail : tailAfter 0 B=0 := by
    apply last_false_tail (n+1) B 0
    simp [B,Fin.val_last]
  simpa only [tail,Nat.add_comm] using ex

private def rootBit (i : Fin 5) : ZMod 2 := if i.val=2 ∨ i.val=3 then 1 else 0
private def midBit (i : Fin 5) : ZMod 2 := if i.val=1 ∨ i.val=3 ∨ i.val=4 then 1 else 0
private def lastBit (i : Fin 5) : ZMod 2 := if i.val=4 then 1 else 0

private def expectedArchive (g h : ℕ) (v : ZMod 2) (i : Fin 5) : NarrowWindowCost.Archive (5*g) :=
  (pulse g {2,3},some (v+rootBit i)) ::
    (List.replicate (h-1) ((fun _ : Fin (5*g) => false),some (v+rootBit i)) ++
      [(pulse g {2,4,5},some (v+rootBit i+midBit i)),
       ((fun i : Fin (5*g) => decide (i.val=0)),some (v+rootBit i+midBit i+lastBit i))])

private theorem expected_injective (g h : ℕ) (v : ZMod 2) :
    Function.Injective (expectedArchive g h v) := by
  intro i j eq
  have pair := List.cons.inj eq
  have first : v+rootBit i=v+rootBit j :=
    Option.some.inj (congrArg Prod.snd pair.1)
  have root : rootBit i=rootBit j := add_left_cancel first
  have rest := pair.2
  change List.replicate (h-1) (_,some (v+rootBit i)) ++ _ =
    List.replicate (h-1) (_,some (v+rootBit j)) ++ _ at rest
  rw [root] at rest
  have two := List.append_cancel_left rest
  have mid : v+rootBit j+midBit i=v+rootBit j+midBit j :=
    Option.some.inj (congrArg Prod.snd (List.cons.inj two).1)
  have midEq : midBit i=midBit j := add_left_cancel mid
  have final := (List.cons.inj (List.cons.inj two).2).1
  have last : lastBit i=lastBit j := by
    have all := Option.some.inj (congrArg Prod.snd final)
    rw [midEq] at all
    exact add_left_cancel all
  fin_cases i <;> fin_cases j <;> simp_all [rootBit,midBit,lastBit]

private def seamWords (g h : ℕ) : List (Fin (5*g) → Bool) :=
  pulse g {2,3} ::
    (List.replicate (h-1) (fun _ => false) ++
      [pulse g {2,4,5},fun i => decide (i.val=0)])


private theorem head_charge (g p : ℕ) (hg : 2 ≤ g) (hp : 6 ≤ p)
    (j : ℕ) (hj : j<p) :
    wordIncrement (g*p-1)
      (-((j*g : ℕ) : ZMod (g*p-1+1))+((4*g : ℕ) : ZMod (g*p-1+1)))
      (fun i : Fin (5*g) => decide (i.val=0)) = if j=4 then 1 else 0 := by
  have hT : g*p-1+1=g*p := by
    have pos : 0<g*p := by positivity
    exact Nat.sub_add_cancel pos
  have small : j*g<g*p-1+1 := by rw [hT]; nlinarith
  have four : 4*g<g*p-1+1 := by rw [hT]; nlinarith
  have fourNext : 4*g+1<g*p-1+1 := by rw [hT]; nlinarith
  have zerotest : -((j*g : ℕ) : ZMod (g*p-1+1))+(4*g : ℕ)=0 ↔ j=4 := by
    constructor
    · intro eq
      have same : ((j*g : ℕ) : ZMod (g*p-1+1))=(4*g : ℕ) := by linear_combination -eq
      have natEq := (ZMod.natCast_eq_natCast_iff' (j*g) (4*g) _).mp same
      rw [Nat.mod_eq_of_lt small,Nat.mod_eq_of_lt four] at natEq
      nlinarith
    · intro eq; subst j; simp
  have lasttest : -((j*g : ℕ) : ZMod (g*p-1+1))+(4*g : ℕ) ≠ -1 := by
    intro eq
    have same : ((j*g : ℕ) : ZMod (g*p-1+1))=((4*g+1 : ℕ) : ZMod (g*p-1+1)) := by
      push_cast at eq ⊢
      linear_combination -eq
    have natEq := (ZMod.natCast_eq_natCast_iff' (j*g) (4*g+1) _).mp same
    rw [Nat.mod_eq_of_lt small,Nat.mod_eq_of_lt fourNext] at natEq
    have dv : g ∣ 1 := by
      have := dvd_mul_left g j
      rw [natEq] at this
      exact (Nat.dvd_add_iff_right (dvd_mul_left g 4)).mpr this
    have := Nat.le_of_dvd (by decide : 0<1) dv
    omega
  unfold wordIncrement
  rw [Finset.sum_eq_single (⟨0,by omega⟩ : Fin (5*g))]
  · simp only [Fin.val_mk,decide_true,ite_true,Nat.cast_zero,add_zero]
    change coefficient _ _ = _
    simp only [coefficient,zerotest,lasttest,false_or,or_false]
  · intro i _ hi
    have nz : i.val≠0 := fun eq => hi (Fin.ext eq)
    simp [nz]
  · simp

private theorem last_zero (m : ℕ) (hm : 1 ≤ m) (B : Fin m → Bool)
    (last : B ⟨m-1,by omega⟩=false) : tailAfter 0 B=0 := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m≠0)
  apply last_false_tail n B 0
  simpa only [Fin.last,Nat.succ_sub_one] using last

private theorem last_one (m : ℕ) (hm : 2 ≤ m) (B : Fin m → Bool)
    (pen : B ⟨m-2,by omega⟩=false) (last : B ⟨m-1,by omega⟩=true) :
    tailAfter 0 B=1 := by
  obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le hm
  have size : m=n+2 := by omega
  clear hn
  subst m
  apply terminal01_tail n B 0
  · simpa using pen
  · simpa using last

private theorem seam_archive (g h : ℕ) (hg : 2 ≤ g) (hh : 1 ≤ h)
    (j : Fin (5*h+1)) (v : ZMod 2) (s : ℕ) (hs : s<g*(5*h+1)-1) :
    scriptArchive (seamWords g h)
      (some ⟨v,-((j.val*g : ℕ) : ZMod (g*(5*h+1)-1+1)),s⟩) =
    expectedArchive g h v (labelIndex j.val) := by
  let p := 5*h+1
  let k := g*p-1
  let m := 5*g
  have hp : 6 ≤ p := by dsimp [p]; omega
  have period : k+1=g*p := by
    dsimp [k]
    have pos : 0<g*p := by positivity
    exact Nat.sub_add_cancel pos
  have hk : 11 ≤ k := by dsimp [k]; nlinarith
  have hm : 2 ≤ m := by dsimp [m]; omega
  have short : m<k := by dsimp [m,k]; nlinarith
  let theta : ZMod (k+1) := -((j.val*g : ℕ) : ZMod (k+1))
  have bits :
      rootBit (labelIndex j.val)=(if j.val∈({2,3} : Finset ℕ) then 1 else 0) ∧
      midBit (labelIndex j.val)=(if j.val=1 ∨ j.val=3 ∨ j.val=4 then 1 else 0) ∧
      lastBit (labelIndex j.val)=(if j.val=4 then 1 else 0) := by
    by_cases small : j.val<5
    · simp [labelIndex,small,rootBit,midBit,lastBit,eq_comm]
    · have a : j.val≠1 := by omega
      have b : j.val≠2 := by omega
      have c : j.val≠3 := by omega
      have d : j.val≠4 := by omega
      simp [labelIndex,small,rootBit,midBit,lastBit,a,b,c,d]
  have rootInc : wordIncrement k theta (pulse g {2,3})=rootBit (labelIndex j.val) := by
    rw [bits.1]
    exact pulse_charge g p hg hp {2,3} (by intro t ht; simp at ht; rcases ht with rfl|rfl <;> omega) j.val j.isLt
  have rootTail : tailAfter 0 (pulse g {2,3})=0 := by
    have endZero : pulse g {2,3} ⟨m-1,by omega⟩=false := by
      simp only [pulse,decide_eq_false_iff_not]
      rintro ⟨t,ht,eq⟩
      simp only [Finset.mem_insert,Finset.mem_singleton] at ht
      have me : m-1+1=m := by omega
      rw [me] at eq
      dsimp [m] at eq
      rcases ht with rfl|rfl <;> omega
    have me : m=(m-1)+1 := by omega
    exact last_zero m (by omega) (pulse g {2,3}) endZero
  have rootEx := (short_safe_execution k (by omega) m (by omega) short
    (pulse g {2,3}) v theta s hs
    (Or.inr (pulse_head g hg {2,3} (by intro t ht; simp at ht; rcases ht with rfl|rfl <;> omega)))).1
  rw [rootInc,rootTail] at rootEx
  let r := if j.val+1=p then 0 else j.val+1
  have hr : r<p := by dsimp [r]; split_ifs <;> have := j.isLt <;> omega
  have zeroT : ((g*p : ℕ) : ZMod (k+1))=0 := by rw [←period]; simp
  have waitPhase : theta+(m : ℕ)+(((h-1)*m : ℕ) : ZMod (k+1))=
      -((r*g : ℕ) : ZMod (k+1)) := by
    have time : m+(h-1)*m+g=g*p := by
      have wait : h-1+1=h := by omega
      have he := congrArg (fun n : ℕ => n*m) wait
      dsimp [m,p] at *
      nlinarith
    have timeCast := congrArg (fun n : ℕ => (n : ZMod (k+1))) time
    rw [zeroT] at timeCast
    dsimp only [theta,r]
    split_ifs with wrap
    · have wrapCast := congrArg (fun n : ℕ => ((n*g : ℕ) : ZMod (k+1))) wrap
      rw [Nat.mul_comm p g,zeroT] at wrapCast
      push_cast at timeCast wrapCast ⊢
      linear_combination timeCast - wrapCast
    · push_cast at timeCast ⊢
      linear_combination timeCast
  have midInc : wordIncrement k (-((r*g : ℕ) : ZMod (k+1)))
      (pulse g {2,4,5})=midBit (labelIndex j.val) := by
    rw [pulse_charge g p hg hp {2,4,5}
      (by intro t ht; simp at ht; rcases ht with rfl|rfl|rfl <;> omega) r hr,bits.2.1]
    have test : (r ∈ ({2,4,5} : Finset ℕ)) ↔ (j.val=1 ∨ j.val=3 ∨ j.val=4) := by
      simp only [Finset.mem_insert,Finset.mem_singleton]
      by_cases wrap : j.val+1=p
      · have re : r=0 := if_pos wrap
        rw [re]
        have : 5 ≤ j.val := by omega
        omega
      · have re : r=j.val+1 := if_neg wrap
        rw [re]
        omega
    simp only [test]
  have midTail : tailAfter 0 (pulse g {2,4,5})=1 := by
    have me : m=(m-2)+2 := by omega
    apply last_one m (by omega) (pulse g {2,4,5})
    · simp only [pulse,decide_eq_false_iff_not]
      rintro ⟨t,ht,eq⟩
      simp only [Finset.mem_insert,Finset.mem_singleton] at ht
      have me : m-2+1=m-1 := by omega
      rw [me] at eq
      dsimp [m] at eq
      rcases ht with rfl|rfl|rfl <;> omega
    · simp only [pulse,decide_eq_true_eq]
      refine ⟨5,by simp,?_⟩
      have me : (m-2+1)+1=m := by omega
      change m-1+1=5*g
      change m-1+1=m
      omega
  have midEx := (short_safe_execution k (by omega) m (by omega) short
    (pulse g {2,4,5}) (v+rootBit (labelIndex j.val))
    (-((r*g : ℕ) : ZMod (k+1))) 0 (by omega)
    (Or.inl rfl)).1
  rw [midInc,midTail] at midEx
  have finalPhase : -((r*g : ℕ) : ZMod (k+1))+(m : ℕ)=
      theta+((4*g : ℕ) : ZMod (k+1)) := by
    rw [←waitPhase]
    have time : m+(h-1)*m+m=g*p+4*g := by
      have wait : h-1+1=h := by omega
      have he := congrArg (fun n : ℕ => n*m) wait
      dsimp [m,p] at *
      nlinarith
    have timeCast := congrArg (fun n : ℕ => (n : ZMod (k+1))) time
    simp only [Nat.cast_add,zeroT] at timeCast
    push_cast at timeCast
    push_cast
    linear_combination timeCast
  have leadEx := lead_safe k m (by omega) hm short
    (v+rootBit (labelIndex j.val)+midBit (labelIndex j.val))
    (-((r*g : ℕ) : ZMod (k+1))+(m : ℕ)) 1 (by omega)
  rw [finalPhase,head_charge g p hg hp j.val j.isLt,←bits.2.2] at leadEx
  change scriptArchive (seamWords g h) (some ⟨v,theta,s⟩)=_
  simp only [seamWords,scriptArchive,rootEx,endpointReading]
  rw [zero_script k m (by omega) (by omega) short (h-1) _
    (v+rootBit (labelIndex j.val)) (theta+(m : ℕ)) 0 (by omega)]
  simp only [ite_self]
  rw [waitPhase]
  simp only [scriptArchive,midEx,finalPhase]
  rw [leadEx]
  rfl


set_option maxHeartbeats 1800000 in
/-- The five distinct INITIAL phase labels cost exactly h+2 paid complete blocks.
Both native alphabets and every actual initial history and legal tail are retained. -/
theorem original_five_label_seam_cost {Y : Type z} (g h : ℕ) (hg : 2 ≤ g) (hh : 1 ≤ h) :
    let p := 5*h+1
    let k := g*p-1
    let m := 5*g
    let hk : 0<k := by
      have hp : 6≤p := by dsimp [p]; omega
      have big : 12≤g*p := by nlinarith
      dsimp [k]; omega
    ∀ (labels : Fin 5 → Y), Function.Injective labels →
    ∀ (f : Option (LiveRecord k) → Y) (v : ZMod 2) (alphabet : Bool),
    (∀ (j : Fin p) (s : ℕ), s<k →
      f (some ⟨v,-((j.val*g : ℕ) : ZMod (k+1)),s⟩)=
        labels (if hj : j.val<5 then ⟨j.val,hj⟩ else 0)) →
    OriginalFiberCost k m hk alphabet f v=((h+2 : ℕ) : ℕ∞) := by
  classical
  dsimp only
  intro labels distinct f v alphabet target
  let p := 5*h+1
  let k := g*p-1
  let m := 5*g
  have hp : 6≤p := by dsimp [p]; omega
  have period : k+1=g*p := by
    dsimp [k]
    have : 0<g*p := by positivity
    omega
  have hk : 11≤k := by dsimp [k]; nlinarith
  have hm : 1 ≤ m := by dsimp [m]; omega
  have short : m<k := by dsimp [m,k]; nlinarith
  have gcdEq : Nat.gcd m (k+1)=g := by
    rw [period,show m=g*5 from by dsimp [m]; ring,Nat.gcd_mul_left]
    have inner : Nat.gcd 5 p=1 := by
      dsimp [p]
      rw [Nat.mul_comm 5 h,Nat.add_comm,Nat.gcd_add_mul_right_right]
      decide
    rw [inner,Nat.mul_one]
  have uEq : m/g=5 := by dsimp [m]; exact Nat.mul_div_cancel 5 (by omega)
  have pEq : (k+1)/g=p := by rw [period]; exact Nat.mul_div_cancel_left p (by omega)
  have hEq : p/5=h := by dsimp [p]; omega
  have restrict (j : Fin p) (s : ℕ) (hs : s<k) :
      f (some ⟨v,-((j.val*g : ℕ) : ZMod (k+1)),s⟩)=labels (labelIndex j.val) :=
    target j s hs
  have sample : (fun j : Fin 5 =>
      f (some ⟨v,-((j.val*g : ℕ) : ZMod (k+1)),0⟩))=labels := by
    funext j
    have ex := restrict ⟨j.val,by have := j.isLt; omega⟩ 0 (by omega)
    simpa only [labelIndex,dif_pos j.isLt] using ex
  have sampleCount : Nat.card (Set.range (fun j : Fin (m/Nat.gcd m (k+1)) =>
      f (some ⟨v,-((j.val*Nat.gcd m (k+1) : ℕ) : ZMod (k+1)),0⟩)))=5 := by
    rw [gcdEq,uEq]
    change Nat.card (Set.range (fun j : Fin 5 =>
      f (some ⟨v,-((j.val*g : ℕ) : ZMod (k+1)),0⟩)))=5
    have rangeEq := congrArg (fun a : Fin 5 → Y => Set.range a) sample
    rw [rangeEq,Nat.card_range_of_injective distinct,Nat.card_fin]
  have lower := original_cost_lower k m (by omega) hm (by omega) f v alphabet
    (show 3≤Nat.card (Set.range (fun j : Fin (m/Nat.gcd m (k+1)) =>
      f (some ⟨v,-((j.val*Nat.gcd m (k+1) : ℕ) : ZMod (k+1)),0⟩))) by rw [sampleCount]; omega)
  change (((((k+1)/Nat.gcd m (k+1))/(m/Nat.gcd m (k+1)))+
    Nat.clog 2 (Nat.card (Set.range (fun j : Fin (m/Nat.gcd m (k+1)) =>
      f (some ⟨v,-((j.val*Nat.gcd m (k+1) : ℕ) : ZMod (k+1)),0⟩))))-1 : ℕ) : ℕ∞) ≤ _ at lower
  rw [sampleCount,gcdEq,uEq,pEq,hEq] at lower
  have lowerBound : ((h+2 : ℕ) : ℕ∞)≤OriginalFiberCost k m (by omega) alphabet f v := by
    simpa only [show Nat.clog 2 5=3 from by decide,show h+3-1=h+2 by omega] using lower
  have upper : OriginalFiberFeasible k m (by omega) alphabet f v (h+2) := by
    let decode : NarrowWindowCost.Archive m → Y := fun archive =>
      if existsIndex : ∃ i : Fin 5, expectedArchive g h v i=archive then
        labels (Classical.choose existsIndex) else labels 0
    have decodeCorrect (i : Fin 5) : decode (expectedArchive g h v i)=labels i := by
      have ex : ∃ j : Fin 5, expectedArchive g h v j=expectedArchive g h v i := ⟨i,rfl⟩
      simp only [decode,dif_pos ex]
      congr 1
      exact expected_injective g h v (Classical.choose_spec ex)
    let pi : NarrowWindowCost.Selector m Y := fun free archive =>
      match free with
      | none => .inl (f none)
      | some _ => finalSelector 0 (seamWords g h) decode free archive
    refine ⟨pi,?_,rfl,?_⟩
    · intro free archive B _ _
      exact short_legal k m (by omega) short B
    · intro history
      dsimp only
      intro observed
      let w := history.flatMap (fun a => List.ofFn a.val)
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
      have archiveEq : scriptArchive (seamWords g h) (some q)=
          expectedArchive g h v (labelIndex j.val) := by
        rw [shape]
        exact seam_archive g h hg hh j v q.tail actual.1
      have valueEq : f (OriginalRecord k (by omega) w)=labels (labelIndex j.val) := by
        rw [record,shape]
        exact restrict j q.tail actual.1
      have script := original_final_script k m (by omega) (seamWords g h) decode
        w (some v) []
      dsimp only at script
      have length : (seamWords g h).length=h+2 := by
        simp only [seamWords,List.length_cons,List.length_append,List.length_replicate,List.length_cons,List.length_nil]
        omega
      have trace := (FullPositiveWindowPrice.trace_congr pi
        (finalSelector 0 (seamWords g h) decode) (some v) (by intro ar; rfl)
        _ _ _ _).mpr script.1
      have decoded : decode (scriptArchive (seamWords g h) (OriginalRecord k (by omega) w))=
          f (OriginalRecord k (by omega) w) := by
        calc
          _ = labels (labelIndex j.val) := by rw [record,archiveEq,decodeCorrect]
          _ = _ := valueEq.symm
      rw [decoded] at trace
      refine ⟨h+2,le_rfl,?_⟩
      rw [execute_paid_trace k m (by omega)]
      exact ⟨_,trace,script.2.2.1.trans length,le_rfl⟩
  apply le_antisymm
  · exact iInf_le_of_le ⟨h+2,upper⟩ le_rfl
  · exact lowerBound

#print axioms original_five_label_seam_cost

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FiveLabelSeamCost
