/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/RepeatedGuardrailCost
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/RepeatedGuardrailCost
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Guarded INITIAL phase labels have exact paid repeated-query cost. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalNarrowCost
import D5.S3.Observer.Budget.WorstCaseDepthInformationLowerBound
set_option autoImplicit false
open D5.S0.Tower.DBonacci.Names
open D5.S0.Tower.DBonacciGeneral.UniformBaseGap
open D5.S0.Automata.TypedPartialDFAOOverBase
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.LiteralModel
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalNarrowCost
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S3.Observer.Budget.WorstCaseDepthInformationLowerBound
open scoped BigOperators
universe z

noncomputable section
namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.RepeatedGuardrailCost

set_option maxHeartbeats 4500000 in
/-- Exact acquisition cost for arbitrary INITIAL labels supported in the repeated guardrail.
Every complete issued word is paid and every actual initial tail remains in scope. -/
theorem original_repeated_guardrail_cost {Y : Type z} (g u h rho : ℕ) (hg : 2 ≤ g) (hu : 2 ≤ u)
    (hh : 1 ≤ h) (hrho : 1 ≤ rho) (hrhou : rho < u) (hc : Nat.Coprime u rho) :
    let p := h*u+rho
    let k := g*p-1
    let m := g*u
    let hk : 0 < k := by
      have hp : 3 ≤ p := by dsimp [p]; nlinarith
      have full : 6 ≤ g*p := by nlinarith
      dsimp [k]; omega
    ∀ labels : Fin p → Y,
    let n := Nat.card (Set.range labels)
    let R := Nat.clog 2 n-1
    3 ≤ n → (∀ j : Fin p, labels j ≠ labels ⟨0, by dsimp [p]; nlinarith⟩ →
      1 ≤ j.val ∧ j.val ≤ u-R*rho) → ∀ (f : Option (LiveRecord k) → Y) (v : ZMod 2) (localAlphabet : Bool),
    (∀ (j : Fin p) (s : ℕ), s < k → f (some ⟨v,-((j.val*g : ℕ) : ZMod (k+1)),s⟩)=labels j) → OriginalFiberCost k m hk localAlphabet f v = ((R*h+1 : ℕ) : ℕ∞) := by
  classical
  dsimp only
  intro labels; intro hn support f v localAlphabet restrict; let p := h*u+rho
  let k := g*p-1
  let m := g*u
  let n := Nat.card (Set.range labels)
  let R := Nat.clog 2 n-1
  let M := u-R*rho
  have hp : 0<p := by dsimp [p]; nlinarith
  have hkl : 2 ≤ k := by
    have pLarge : 3≤p := by dsimp [p]; nlinarith
    have large : 6≤g*p := by nlinarith
    dsimp [k]; omega
  have hml : 1 ≤ m := by
    dsimp [m]
    nlinarith
  have source : n-1≤M ∧ R*rho<u ∧ M+R*rho=u ∧ 1≤R ∧ R*rho+2≤u ∧ Nat.gcd (g*u) (g*(h*u+rho))=g := by
    dsimp only [n,R,M]
    classical
    let p := h*u+rho
    have hp : 0 < p := by dsimp [p]; nlinarith
    let zero : Fin p := ⟨0,hp⟩
    let M := u-(Nat.clog 2 (Nat.card (Set.range labels))-1)*rho
    let pick : Set.range labels → Fin p := fun y =>
      if y.val=labels zero then zero else Classical.choose y.property
    have picked (y : Set.range labels) : labels (pick y)=y.val := by
      dsimp [pick]
      split_ifs with eq
      · exact eq.symm
      · exact Classical.choose_spec y.property
    have bound (y : Set.range labels) : (pick y).val ≤ M := by
      by_cases eq : y.val=labels zero
      · simp [pick,eq,zero]
      · have ne : labels (pick y) ≠ labels zero := by rwa [picked]
        exact (support (pick y) ne).2
    let ix : Set.range labels → Fin (M+1) := fun y => ⟨(pick y).val,by have := bound y; omega⟩
    have inj : Function.Injective ix := by
      intro a b same; have vals : (pick a).val=(pick b).val := congrArg (fun x : Fin (M+1) => x.val) same; have inds : pick a=pick b := Fin.ext vals
      apply Subtype.ext
      exact (picked a).symm.trans ((congrArg labels inds).trans (picked b))
    have count := Nat.card_le_card_of_injective ix inj
    rw [Nat.card_fin] at count
    have Mpos : 2 ≤ M := by omega
    have notUnderflow : (Nat.clog 2 (Nat.card (Set.range labels))-1)*rho < u := by
      apply Nat.sub_pos_iff_lt.mp
      exact lt_of_lt_of_le (by decide : 0<2) Mpos
    have gcdEq : Nat.gcd (g*u) (g*(h*u+rho))=g := by
      rw [Nat.gcd_mul_left]
      have gu : Nat.gcd u (h*u+rho)=1 := by rw [Nat.add_comm, Nat.gcd_add_mul_right_right]; exact hc.gcd_eq_one
      rw [gu, Nat.mul_one]
    have logLarge : 2 ≤ Nat.clog 2 (Nat.card (Set.range labels)) := by
      by_contra no
      have logSmall : Nat.clog 2 (Nat.card (Set.range labels)) ≤ 1 := by omega
      have countSmall : Nat.card (Set.range labels) ≤ 2 := (Nat.clog_le_iff_le_pow (by decide : 1<2)).mp logSmall
      omega
    exact ⟨by omega,notUnderflow,Nat.sub_add_cancel notUnderflow.le,by omega,by omega,gcdEq⟩
  have bridge : (∀ w : List Bool, OriginalRecord k (by omega) w = runWord (bitUpdate k) w (some ⟨0,0,0⟩)) ∧ (∀ (m : ℕ) (w : List Bool) (B : Fin m → Bool),
        OriginalRecord k (by omega) (w++List.ofFn B)= runBits k B (OriginalRecord k (by omega) w)) ∧ (∀ (m : ℕ) (a : Bool) (history : List
        (D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.EndpointCells.AllowedBlock k m a)),
        OriginalRecord k (by omega) (history.flatMap (fun B => List.ofFn B.val))= D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition.historyRecord history) ∧
      (∀ {Y : Type z} (m d : ℕ) (pi : Selector m Y) (w w' : List Bool)
        (initial : Option (ZMod 2)) (archive : Archive m),
        OriginalRecord k (by omega) w=OriginalRecord k (by omega) w' → execute k (by omega) pi d w initial archive= execute k (by omega) pi d w' initial archive)
   := by
    have shiftInteger (a : ℕ) : dbonacci k (a+k+3)+dbonacci k (a+2)=2*dbonacci k (a+k+2) := by
      have left : dbonacci k (a+k+2)=∑ i : Fin k, dbonacci k (a+i.val+2) := by simpa only [Nat.add_sub_cancel] using dbonacci_add_two_of_le k (a+k) (by omega)
      have right : dbonacci k (a+k+3)=∑ i : Fin k, dbonacci k (a+1+i.val+2) := by
        have sub : a+k+1-k=a+1 := by omega
        have fact := dbonacci_add_two_of_le k (a+k+1) (by omega)
        rw [sub] at fact
        convert fact using 1 <;> omega
      have finiteRange (a : ℕ) : (∑ i : Fin k, dbonacci k (a+i.val+2))=∑ b ∈ Finset.range k, dbonacci k (a+b+2) := by
        rw [Finset.sum_fin_eq_sum_range]
        apply Finset.sum_congr rfl
        intro i hi; simp only [Finset.mem_range.mp hi,dif_pos,Fin.val_mk]
      rw [finiteRange] at left right
      have window0 := Finset.sum_range_succ (fun b => dbonacci k (a+b+2)) k
      have window1 := Finset.sum_range_succ' (fun b => dbonacci k (a+b+2)) k
      simp only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,Nat.add_zero] at left right window0 window1 ⊢; omega
    have periodic : Function.Periodic (originalWeight k) (k+1) := by
      intro a; have modTwo := congrArg (fun n : ℕ => (n : ZMod 2)) (shiftInteger a)
      simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,CharTwo.two_eq_zero,zero_mul] at modTwo
      have equal := CharTwo.add_eq_zero.mp modTwo
      simpa only [originalWeight,show a+(k+1)+2=a+k+3 by omega] using equal
    have weight (a : ℕ) : originalWeight k a=coefficient k (a : ZMod (k+1)) := by
      let r := a%(k+1)
      have small : r < k+1 := Nat.mod_lt _ (by omega)
      have seed : originalWeight k r=if r=0 ∨ r=k then 1 else 0 := by
        by_cases last : r=k
        · rw [if_pos (Or.inr last),last]
          unfold originalWeight; rw [dbonacci_diagonal_cardinality,Nat.cast_sub (Nat.one_le_pow k 2 (by omega))]
          simp [Nat.cast_pow,CharTwo.two_eq_zero,show k≠0 by omega]
        · rw [originalWeight,dbonacci_add_two_of_lt k r (by omega),Nat.cast_pow]
          by_cases first : r=0
          · simp [first]
          · simp [first,last,CharTwo.two_eq_zero]
      have atZero : (a : ZMod (k+1))=0 ↔ r=0 := by rw [← Nat.cast_zero,ZMod.natCast_eq_natCast_iff']; simp only [Nat.zero_mod,r]
      have atEnd : (a : ZMod (k+1))=-1 ↔ r=k := by
        constructor
        · intro same
          simpa only [ZMod.val_natCast,ZMod.val_neg_one,r] using congrArg ZMod.val same
        · intro same
          apply ZMod.val_injective (k+1)
          simpa only [ZMod.val_natCast,ZMod.val_neg_one,r] using same
      rw [← periodic.map_mod_nat a,seed]; simp only [coefficient,atZero,atEnd]
    have scalar : ∀ (n a : ℕ) (B : Fin n → Bool),
        value k a (List.ofFn B)=∑ i : Fin n, if B i then originalWeight k (a+i.val) else 0 := by
      intro n; induction n with
      | zero => intro a B; simp [value]
      | succ n ih =>
        intro a B; rw [List.ofFn_succ,value,ih,Fin.sum_univ_succ]
        simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ,originalWeight,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,add_assoc]
    have valueFn (w : List Bool) : value k 0 w=wordIncrement k 0 w.get := by
      have form := scalar w.length 0 w.get
      rw [List.ofFn_get] at form; rw [form]
      unfold wordIncrement
      apply Finset.sum_congr rfl
      intro i _; simp only [Nat.zero_add,zero_add,weight]
    have tails : ∀ (w : List Bool) (q : Option (LiveRecord k)) (state : Option (Fin k)),
        q.map LiveRecord.tail=state.map Fin.val → (runWord (bitUpdate k) w q).map LiveRecord.tail=
          (state.bind (fun s => (scanner k (by omega)).evalFrom s w)).map Fin.val := by
      intro w; induction w with
      | nil => intro q state same; simpa [runWord,PartialDFA.evalFrom,runTransition] using same
      | cons b w ih =>
        intro q state same; cases q with
        | none =>
          cases state with
          | none => simpa [runWord,PartialDFA.evalFrom,runTransition,bitUpdate] using ih none none rfl
          | some s => simp at same
        | some q =>
          cases state with
          | none => simp at same
          | some s =>
            have matchTail : q.tail=s.val := Option.some.inj same
            have nextTail : (bitUpdate k b (some q)).map LiveRecord.tail= ((scanner k (by omega)).step s b).map Fin.val := by
              cases b <;> simp [bitUpdate,scanner,matchTail]
            have after := ih (bitUpdate k b (some q)) ((scanner k (by omega)).step s b) nextTail
            cases reply : (scanner k (by omega)).step s b <;>
              simpa [runWord,PartialDFA.evalFrom,runTransition,reply] using after
    have initial : ∀ w : List Bool, OriginalRecord k (by omega) w = runWord (bitUpdate k) w (some ⟨0,0,0⟩) := by
      intro w; have model := (literal_block_execution k hkl w.length w.get 0 0 0 (by omega)).1; simp only [runBits,List.ofFn_get] at model
      have matchTail := tails w (some ⟨0,0,0⟩) (some ⟨0,by omega⟩) rfl
      change (runWord (bitUpdate k) w (some ⟨0,0,0⟩)).map LiveRecord.tail= ((scanner k (by omega)).eval w).map Fin.val at matchTail
      cases safe : runAdmissible (k-1) (k-1) w.length w.get with
      | false =>
        simp only [Nat.sub_zero,safe,Bool.false_eq_true,if_false] at model; rw [model] at matchTail
        have empty : (scanner k (by omega)).eval w=none := by
          cases result : (scanner k (by omega)).eval w with
          | none => rfl
          | some s => simp [result] at matchTail
        simp only [OriginalRecord,empty,Option.map_none,model]
      | true =>
        simp only [Nat.sub_zero,safe,if_pos,zero_add] at model; rw [model] at matchTail
        obtain ⟨s,scanned,sTail⟩ := Option.map_eq_some_iff.mp matchTail.symm
        rw [OriginalRecord,scanned,Option.map_some,model,valueFn]; exact congrArg some (by cases s; cases sTail; rfl)
    have appendRun (left right : List Bool) (q : Option (LiveRecord k)) : runWord (bitUpdate k) (left++right) q=
          runWord (bitUpdate k) right (runWord (bitUpdate k) left q) := by
      induction left generalizing q with
      | nil => rfl
      | cons bit left ih => simpa only [List.cons_append,runWord] using ih (bitUpdate k bit q)
    have extend (m : ℕ) (w : List Bool) (B : Fin m → Bool) : OriginalRecord k (by omega) (w++List.ofFn B)= runBits k B (OriginalRecord k (by omega) w) := by
      rw [initial,appendRun,initial]; rfl
    have flattened (m : ℕ) (a : Bool) : ∀ (history : List
        (D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.EndpointCells.AllowedBlock k m a)) q,
        runWord (bitUpdate k) (history.flatMap (fun B => List.ofFn B.val)) q= D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition.historyRecordFrom history q := by
      intro history; induction history with
      | nil => intro q; rfl
      | cons B history ih =>
        intro q; simp only [List.flatMap_cons,appendRun,ih,
          D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition.historyRecordFrom,List.foldl_cons,runBits]
    have observed (w : List Bool) : output k (by omega) w=endpointReading (OriginalRecord k (by omega) w) := by
      unfold output OriginalRecord
      cases (scanner k (by omega)).eval w <;> rfl
    refine ⟨initial,extend,?_,?_⟩
    · intro m a history
      rw [initial,flattened]; rfl
    · intro Y m d pi
      induction d with
      | zero => intro w w' v archive same; rfl
      | succ d ih =>
        intro w w' v archive same; cases selected : pi v archive with
        | inl y => simp only [execute,selected]
        | inr B =>
          have sameNext : OriginalRecord k (by omega) (w++List.ofFn B)= OriginalRecord k (by omega) (w'++List.ofFn B) := by
            rw [extend,extend,same]
          have replies : output k (by omega) (w++List.ofFn B)= output k (by omega) (w'++List.ofFn B) := by rw [observed,observed,sameNext]
          simp only [execute,selected]; rw [replies,ih _ _ _ _ sameNext]
  have lower (b : ℕ) (feasible : OriginalFiberFeasible k m (by omega) localAlphabet f v b) : R*h+1≤b := by
    have schedule (g u h rho R : ℕ) (hg : 2≤g) (hu : 2≤u) (hh : 1≤h)
        (hrho : 1≤rho) (hR : 1≤R) (guard : R*rho+2≤u)
        (j x : ℕ) (hj : j≤u-R*rho) (hx : x<R*h*(g*u))
        (active : coefficient (g*(h*u+rho)-1)
          (-((j*g : ℕ) : ZMod (g*(h*u+rho)-1+1))+(x : ℕ)) ≠ 0) : h ∣ x/(g*u) := by
      let T := g*(h*u+rho)
      let m := g*u
      have hT : 1 ≤ T := by
        have positive : 0 < T := by dsimp [T]; positivity
        omega
      have hm : 0 < m := by dsimp [m]; positivity
      have castT : g*(h*u+rho)-1+1=T := by omega
      have jguard : j+R*rho≤u := by omega
      have jlt : j*g < T := by
        have ju : j < u := by nlinarith
        have hup : u ≤ h*u := Nat.le_mul_of_pos_left u hh
        have jp : j < h*u+rho := by omega
        have fact := Nat.mul_lt_mul_of_pos_left jp (by omega : 0<g)
        simpa only [Nat.mul_comm,T] using fact
      let N := g*(h*u+rho)-1+1
      have hN : N=T := castT
      have phase : (-((j*g : ℕ) : ZMod N)+(x : ℕ))=0 ∨
          (-((j*g : ℕ) : ZMod N)+(x : ℕ))=-1 := by
        unfold coefficient at active
        by_contra no
        exact active (if_neg no)
      have residue : ∃ e : ℕ, e≤1 ∧ (x+e)%T=j*g := by
        rcases phase with eq | eq
        · have castEq : (x : ZMod N)=((j*g : ℕ) : ZMod N) := by
            exact (neg_add_eq_zero.mp eq).symm
          have mods := (ZMod.natCast_eq_natCast_iff' x (j*g) N).mp castEq
          exact ⟨0,by omega,by simpa only [hN,Nat.add_zero,Nat.mod_eq_of_lt jlt] using mods⟩
        · have castEq : ((x+1 : ℕ) : ZMod N)=((j*g : ℕ) : ZMod N) := by
            push_cast
            have : (-((j*g : ℕ) : ZMod N)+(x : ℕ))+1=0 := by rw [eq]; simp
            push_cast at this
            linear_combination this
          have mods := (ZMod.natCast_eq_natCast_iff' (x+1) (j*g) N).mp castEq
          exact ⟨1,by omega,by simpa only [hN,Nat.mod_eq_of_lt jlt] using mods⟩
      obtain ⟨e,he,modEq⟩ := residue
      let ell := (x+e)/T
      have location : x+e=ell*T+j*g := by
        have := Nat.mod_add_div (x+e) T
        rw [modEq] at this
        simpa only [ell,Nat.mul_comm,Nat.add_comm] using this.symm
      have xBound : x+e≤R*h*m := by dsimp [m]; omega
      have ellBound : ell < R := by
        by_contra no
        have le : R*T≤ell*T := Nat.mul_le_mul_right T (by omega)
        have RT : R*T=R*h*m+R*rho*g := by dsimp [T,m]; ring
        have pos : 0<R*rho*g := by positivity
        nlinarith
      have offset : j+ell*rho < u := by
        have drop : ell*rho+rho≤R*rho := by nlinarith
        omega
      have offBound : (j+ell*rho)*g < m := by dsimp [m]; nlinarith
      have tiled : ell*T+j*g=ell*h*m+(j+ell*rho)*g := by dsimp [T,m]; ring
      have start : ell*h*m≤x := by
        by_cases offZero : j+ell*rho=0
        · have ellZero : ell=0 := by nlinarith
          simp [ellZero]
        · have offPos : 1≤j+ell*rho := by omega
          have ge : 2≤(j+ell*rho)*g := by nlinarith
          rw [tiled] at location; omega
      have finish : x < (ell*h+1)*m := by nlinarith
      have divEq : x/m=ell*h := by
        apply Nat.div_eq_of_lt_le
        · exact start
        · exact finish
      rw [divEq]; exact dvd_mul_left h ell
    have compression : ∀ {Y X : Type z} (pi : Selector m Y) (v : ZMod 2)
          (target : X → Y) (inj : Function.Injective target)
          (r : ℕ) (theta : X → ZMod (k+1)),
        (∀ (t : ℕ), t < r*h → ¬ h ∣ t → ∀ (x : X) (B : Fin m → Bool),
          wordIncrement k (theta x+((t*m : ℕ) : ZMod (k+1))) B=0) → ∀ (words : X → List Bool) (s : ℕ), s<k →
          (∀ x, OriginalRecord k (by omega) (words x)=some ⟨v,theta x,s⟩) → (∀ x, ∃ c, execute k (by omega) pi (r*h) (words x) (some v) []=some (target x,c)) →
          ∃ (q : ℕ) (protocol : AdaptiveProtocol X 2 q),
            q ≤ r ∧ Function.Injective (adaptiveTranscript protocol) := by
      classical
      intro Y X pi v target inj r theta silent words s hs records correct; let count (t b : ℕ) : ℕ := ∑ i ∈ Finset.range b, if h ∣ t+i then 1 else 0
      have countStep (t b : ℕ) : count t (b+1)= (if h ∣ t then 1 else 0)+count (t+1) b := by
        dsimp only [count]; rw [Finset.sum_range_succ']; simp only [Nat.add_zero,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
      have observed (w : List Bool) : output k (by omega) w= endpointReading (OriginalRecord k (by omega) w) := by
        unfold output OriginalRecord
        cases (scanner k (by omega)).eval w <;> rfl
      have compress : ∀ (b t : ℕ), t+b ≤ r*h → ∀ (S : Set X) (ws : X → List Bool) (z : ZMod 2) (tail : ℕ), tail<k → ∀ archive : Archive m,
          (∀ x ∈ S, OriginalRecord k (by omega) (ws x)= some ⟨z,theta x+((t*m : ℕ) : ZMod (k+1)),tail⟩) →
          (∀ x ∈ S, ∃ c, execute k (by omega) pi b (ws x) (some v) archive= some (target x,c)) → ∃ P : AdaptiveProtocol X 2 (count t b),
            ∀ x ∈ S, ∀ y ∈ S,
              adaptiveTranscript P x=adaptiveTranscript P y → target x=target y := by
        intro b; induction b with
        | zero =>
          intro t bound S ws z tail tailBound archive same success; refine ⟨.leaf,?_⟩; intro x hx y hy _; obtain ⟨cx,ex⟩ := success x hx
          obtain ⟨cy,ey⟩ := success y hy
          have equal : execute k (by omega) pi 0 (ws x) (some v) archive= execute k (by omega) pi 0 (ws y) (some v) archive := rfl
          rw [ex,ey] at equal; exact (Prod.mk.inj (Option.some.inj equal)).1
        | succ b ih =>
          intro t bound S ws z tail tailBound archive same success; cases selected : pi (some v) archive with
          | inl label =>
            refine ⟨.leaf,?_⟩
            intro x hx y hy _; obtain ⟨cx,ex⟩ := success x hx; obtain ⟨cy,ey⟩ := success y hy
            simp only [execute,selected] at ex ey; exact ((Prod.mk.inj (Option.some.inj ex)).1.symm).trans
              (Prod.mk.inj (Option.some.inj ey)).1
          | inr B =>
            let ws' : X → List Bool := fun x => ws x++List.ofFn B
            have nextRecords (x : X) (hx : x ∈ S) : OriginalRecord k (by omega) (ws' x)= if runAdmissible (k-1) (k-1-tail) m B then
                    some ⟨z+wordIncrement k (theta x+((t*m : ℕ) : ZMod (k+1))) B,
                      theta x+(((t+1)*m : ℕ) : ZMod (k+1)),tailAfter tail B⟩
                  else none := by
              dsimp only [ws']; rw [bridge.2.1,same x hx,(literal_block_execution k hkl m B z _ tail tailBound).1]
              congr 1
              push_cast
              congr 1
              ring
            by_cases safe : runAdmissible (k-1) (k-1-tail) m B=true
            · have nextTail : tailAfter tail B<k := (literal_block_execution k hkl m B z 0 tail tailBound).2 safe
              have nextRecordsSafe (x : X) (hx : x ∈ S) : OriginalRecord k (by omega) (ws' x)= some ⟨z+wordIncrement k (theta x+((t*m : ℕ) : ZMod (k+1))) B,
                      theta x+(((t+1)*m : ℕ) : ZMod (k+1)),tailAfter tail B⟩ := by
                rw [nextRecords x hx,if_pos safe]
              have advance (q : ZMod 2) (S' : Set X) (sub : S' ⊆ S)
                  (valueEq : ∀ x ∈ S', z+wordIncrement k (theta x+((t*m : ℕ) : ZMod (k+1))) B=q) : ∃ P : AdaptiveProtocol X 2 (count (t+1) b),
                    ∀ x ∈ S', ∀ y ∈ S', adaptiveTranscript P x=adaptiveTranscript P y → target x=target y := by
                apply ih (t+1) (by omega) S' ws' q (tailAfter tail B) nextTail
                  (archive++[(B,some q)])
                · intro x hx
                  rw [nextRecordsSafe x (sub hx),valueEq x hx]
                · intro x hx
                  obtain ⟨c,ex⟩ := success x (sub hx)
                  have reply : output k (by omega) (ws' x)=some q := by rw [observed,nextRecordsSafe x (sub hx),valueEq x hx]; rfl
                  simp only [execute,selected] at ex
                  change (execute k (by omega) pi b (ws' x) (some v)
                    (archive++[(B,output k (by omega) (ws' x))])).map (fun x => (x.1,x.2+1))= some (target x,c) at ex
                  rw [reply] at ex
                  obtain ⟨out,eout,eq⟩ := Option.map_eq_some_iff.mp ex
                  exact ⟨out.2,by rw [eout]; exact congrArg some (by
                    apply Prod.ext
                    · exact (Prod.mk.inj eq).1
                    · rfl)⟩
              by_cases active : h ∣ t
              · let question (x : X) : Fin 2 := ⟨(z+wordIncrement k (theta x+((t*m : ℕ) : ZMod (k+1))) B).val,
                    ZMod.val_lt _⟩
                let branch (a : Fin 2) : Set X := {x | x ∈ S ∧ question x=a}
                have branchAdvance (a : Fin 2) : ∃ P : AdaptiveProtocol X 2 (count (t+1) b),
                      ∀ x ∈ branch a, ∀ y ∈ branch a,
                        adaptiveTranscript P x=adaptiveTranscript P y → target x=target y := by
                  apply advance (a.val : ZMod 2) (branch a) (fun _ hx => hx.1)
                  intro x hx; have e := congrArg Fin.val hx.2; dsimp only [question] at e
                  apply ZMod.val_injective 2
                  rw [ZMod.val_natCast,Nat.mod_eq_of_lt a.isLt]; exact e
                let next (a : Fin 2) : AdaptiveProtocol X 2 (count (t+1) b) := Classical.choose (branchAdvance a)
                have ncount : count t (b+1)=count (t+1) b+1 := by rw [countStep,if_pos active]; omega
                rw [ncount]
                refine ⟨.query question next,?_⟩
                intro x hx y hy eq; change question x::adaptiveTranscript (next (question x)) x= question y::adaptiveTranscript (next (question y)) y at eq
                have parts := List.cons.inj eq
                have ey : y ∈ branch (question x) := ⟨hy,parts.1.symm⟩
                apply Classical.choose_spec (branchAdvance (question x)) x ⟨hx,rfl⟩ y ey
                simpa only [parts.1] using parts.2
              · have zero (x : X) : wordIncrement k (theta x+((t*m : ℕ) : ZMod (k+1))) B=0 := silent t (by omega) active x B
                have ncount : count t (b+1)=count (t+1) b := by rw [countStep,if_neg active,zero_add]
                rw [ncount]; exact advance z S (fun _ hx => hx) (fun x _ => by rw [zero x,add_zero])
            · refine ⟨.leaf,?_⟩
              intro x hx y hy _; have rx : OriginalRecord k (by omega) (ws' x)=none := by rw [nextRecords x hx,if_neg safe]
              have ry : OriginalRecord k (by omega) (ws' y)=none := by rw [nextRecords y hy,if_neg safe]
              have ox : output k (by omega) (ws' x)=none := by rw [observed,rx]; rfl
              have oy : output k (by omega) (ws' y)=none := by rw [observed,ry]; rfl
              have eq : execute k (by omega) pi (b+1) (ws x) (some v) archive= execute k (by omega) pi (b+1) (ws y) (some v) archive := by
                simp only [execute,selected]
                change (execute k (by omega) pi b (ws' x) (some v)
                  (archive++[(B,output k (by omega) (ws' x))])).map _ = (execute k (by omega) pi b (ws' y) (some v)
                  (archive++[(B,output k (by omega) (ws' y))])).map _
                rw [ox,oy,bridge.2.2.2 m b pi _ _ _ _ (rx.trans ry.symm)]
              obtain ⟨cx,ex⟩ := success x hx
              obtain ⟨cy,ey⟩ := success y hy
              rw [ex,ey] at eq; exact (Prod.mk.inj (Option.some.inj eq)).1
      obtain ⟨P,Pexact⟩ := compress (r*h) 0 (by omega) Set.univ words v s hs []
        (fun x _ => by simpa using records x) (fun x _ => correct x)
      have countBound : count 0 (r*h) ≤ r := by
        let indices := (Finset.range (r*h)).filter (fun t => h ∣ t)
        have cardEq : count 0 (r*h)=indices.card := by simp [count,indices]
        rw [cardEq]
        let quotient : {t // t ∈ indices} → Fin r := fun t =>
          ⟨t.val/h,(Nat.div_lt_iff_lt_mul (by omega : 0<h)).mpr
            (by simpa only [Nat.mul_comm] using (Finset.mem_range.mp (Finset.mem_filter.mp t.property).1))⟩
        have quotientInj : Function.Injective quotient := by
          intro a b eq; have vals : a.val/h=b.val/h := congrArg Fin.val eq; apply Subtype.ext
          have da := (Finset.mem_filter.mp a.property).2
          have db := (Finset.mem_filter.mp b.property).2
          rw [← Nat.div_mul_cancel da,← Nat.div_mul_cancel db,vals]
        have cards := Fintype.card_le_of_injective quotient quotientInj
        simpa only [Fintype.card_coe,Fintype.card_fin] using cards
      exact ⟨count 0 (r*h),P,countBound,fun x y eq => inj (Pexact x (Set.mem_univ x) y (Set.mem_univ y) eq)⟩
    change R*h+1 ≤ b
    by_contra no
    have budget : b≤R*h := by omega
    obtain ⟨pi,legal,bottom,success⟩ := feasible
    have budgetExtend : ∀ (d e : ℕ) (w : List Bool) (arc : Archive m) (y : Y) (c : ℕ),
        execute k (by omega) pi d w (some v) arc=some (y,c) → execute k (by omega) pi (d+e) w (some v) arc=some (y,c) := by
      intro d; induction d with
      | zero =>
        intro e w arc y c ex; cases selected : pi (some v) arc with
        | inl answer => cases e <;> simpa only [execute,selected,Nat.zero_add] using ex
        | inr B => simp [execute,selected] at ex
      | succ d ih =>
        intro e w arc y c ex; cases selected : pi (some v) arc with
        | inl answer => simpa only [execute,selected,Nat.succ_add] using ex
        | inr B =>
          simp only [execute,selected] at ex
          obtain ⟨out,execOut,outEq⟩ := Option.map_eq_some_iff.mp ex
          have future := ih e (w++List.ofFn B)
            (arc++[(B,output k (by omega) (w++List.ofFn B))]) out.1 out.2 execOut
          simp only [Nat.succ_add,execute,selected,future,Option.map_some,outEq]
    let zero : Fin p := ⟨0,hp⟩
    let pick : Set.range labels → Fin p := fun y =>
      if y.val=labels zero then zero else Classical.choose y.property
    have picked (y : Set.range labels) : labels (pick y)=y.val := by
      dsimp [pick]
      split_ifs with eq
      · exact eq.symm
      · exact Classical.choose_spec y.property
    have pickBound (y : Set.range labels) : (pick y).val≤M := by
      by_cases eq : y.val=labels zero
      · simp [pick,eq,zero]
      · exact (support (pick y) (by rwa [picked])).2
    let theta (y : Set.range labels) : ZMod (k+1) := -(((pick y).val*g : ℕ) : ZMod (k+1))
    have kperiod : k+1=g*p := by dsimp only [k]; exact Nat.sub_add_cancel (Nat.mul_pos (by omega) hp)
    have actual (y : Set.range labels) : ∃ history : List
        (D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.EndpointCells.AllowedBlock k m localAlphabet),
        OriginalRecord k (by omega) (history.flatMap (fun B => List.ofFn B.val))= some ⟨v,theta y,0⟩ := by
      have gcdEq : Nat.gcd m (k+1)=g := by rw [kperiod]; exact source.2.2.2.2.2
      have small : (pick y).val*g<k+1 := by
        rw [kperiod]
        have fact := Nat.mul_lt_mul_of_pos_right (pick y).isLt (by omega : 0<g)
        simpa only [Nat.mul_comm] using fact
      have divides : Nat.gcd m (k+1) ∣ (theta y).val := by
        rw [gcdEq]
        dsimp [theta]
        rw [ZMod.neg_val]
        split_ifs
        · exact dvd_zero _
        · rw [ZMod.val_natCast,Nat.mod_eq_of_lt small]
          exact Nat.dvd_sub (by rw [kperiod]; exact dvd_mul_right g p) (dvd_mul_left g (pick y).val)
      have src : D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition.SourceRecord
          k m (some ⟨v,theta y,0⟩) := ⟨by simp; omega,divides⟩
      have realization := (D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition.whole_first_zero_acquisition
        k m hkl hml localAlphabet (fun _ => ())).1
      obtain ⟨history,same⟩ := (realization _).mp src
      exact ⟨history,(bridge.2.2.1 m localAlphabet history).trans same⟩
    let history (y : Set.range labels) := Classical.choose (actual y)
    let words (y : Set.range labels) : List Bool := (history y).flatMap (fun B => List.ofFn B.val)
    have wordRecord (y : Set.range labels) : OriginalRecord k (by omega) (words y)= some ⟨v,theta y,0⟩ := Classical.choose_spec (actual y)
    have observed (w : List Bool) : output k (by omega) w=endpointReading (OriginalRecord k (by omega) w) := by
      unfold output OriginalRecord
      cases (scanner k (by omega)).eval w <;> rfl
    have wordSuccess (y : Set.range labels) : ∃ c,
        execute k (by omega) pi (R*h) (words y) (some v) []=some (y.val,c) := by
      have outputY : output k (by omega) (words y)=some v := by rw [observed,wordRecord]; rfl
      obtain ⟨c,_,ex⟩ := success (history y) outputY
      change execute k (by omega) pi b (words y) (some v) []= some (f (OriginalRecord k (by omega) (words y)),c) at ex
      have target : f (OriginalRecord k (by omega) (words y))=y.val := by rw [wordRecord,restrict (pick y) 0 (by exact lt_of_lt_of_le (by decide : 0<2) hkl),picked]
      rw [target] at ex
      have full := budgetExtend b (R*h-b) (words y) [] y.val c ex
      rw [Nat.add_sub_of_le budget] at full; exact ⟨c,full⟩
    have silent (t : ℕ) (ht : t<R*h) (inactive : ¬h ∣ t)
        (y : Set.range labels) (B : Fin m → Bool) : wordIncrement k (theta y+((t*m : ℕ) : ZMod (k+1))) B=0 := by
      unfold wordIncrement
      apply Finset.sum_eq_zero
      intro i _; split_ifs
      · have coeffZero : coefficient k (theta y+((t*m : ℕ) : ZMod (k+1))+(i.val : ℕ))=0 := by
          by_contra active
          have position : t*m+i.val<R*h*(g*u) := by
            have step : t+1≤R*h := by omega
            have fact := Nat.mul_le_mul_right m step
            change t*m+i.val<R*h*m
            exact lt_of_lt_of_le (by nlinarith only [i.isLt]) fact
          have actualActive : coefficient (g*(h*u+rho)-1)
              (-(((pick y).val*g : ℕ) : ZMod (g*(h*u+rho)-1+1))+
                ((t*m+i.val : ℕ) : ZMod (g*(h*u+rho)-1+1)))≠0 := by
            dsimp [k,p,theta] at active
            simpa only [Nat.cast_add,add_assoc] using active
          have divisibility := schedule g u h rho R hg hu hh hrho source.2.2.2.1 source.2.2.2.2.1
            (pick y).val (t*m+i.val) (pickBound y) position actualActive
          have quotient : (t*m+i.val)/m=t := by
            apply Nat.div_eq_of_lt_le
            · nlinarith
            · nlinarith [i.isLt]
          change h ∣ (t*m+i.val)/m at divisibility
          rw [quotient] at divisibility; exact inactive divisibility
        exact coeffZero
      · rfl
    obtain ⟨q,P,qBound,exactP⟩ := compression pi v Subtype.val
      Subtype.val_injective R theta silent words 0 (by omega) wordRecord wordSuccess
    letI : Fintype (Set.range labels) := Fintype.ofFinite _
    have uses : UsesReadoutFamily (id : ((Set.range labels → Fin 2) → Set.range labels → Fin 2)) P := by
      clear qBound exactP
      induction P with
      | leaf => trivial
      | query question next ih => exact ⟨⟨question,rfl⟩,ih⟩
    have cardBound := exact_identification_card_le_pow
      (id : ((Set.range labels → Fin 2) → Set.range labels → Fin 2)) (by decide : 1≤2)
      ⟨P,uses,exactP⟩
    have nBound : n≤2^R := by
      have card : n=Fintype.card (Set.range labels) := Nat.card_eq_fintype_card
      rw [card]; exact cardBound.trans (Nat.pow_le_pow_right (by decide : 0<2) qBound)
    have logBound : Nat.clog 2 n≤R := Nat.clog_le_of_le_pow nBound
    dsimp [R] at logBound
    have large : 1≤Nat.clog 2 n := by
      have positiveR := source.2.2.2.1
      dsimp only [R] at positiveR; omega
    omega
  have upper : OriginalFiberFeasible k m (by omega) localAlphabet f v (R*h+1) := by
    have queries (g u h rho R ell : ℕ) (hg : 2 ≤ g) (hu : 2 ≤ u) (hh : 1 ≤ h)
        (hrho : 1 ≤ rho) (guard : R*rho+2 ≤ u) (hell : ell ≤ R)
        (a : Fin (h*u+rho) → Bool)
        (aSupport : ∀ j, a j=true → 1≤j.val ∧ j.val≤u-R*rho) :
        let k := g*(h*u+rho)-1
        let m := g*u
        let B : Fin m → Bool := fun i => decide (∃ j : Fin (h*u+rho),
          1≤j.val ∧ j.val≤u-R*rho ∧ a j=true ∧ i.val+1=(j.val+ell*rho)*g)
        DBonacciAdmissible k m B ∧ B ⟨0,by dsimp [m]; nlinarith⟩=false ∧ ∀ (r : Fin (h*u+rho)) (v : ZMod 2) (s : ℕ), s<k → ∃ tail, tail≤1 ∧ runBits k B
            (some ⟨v,-((r.val*g : ℕ) : ZMod (k+1))+((ell*h*m : ℕ) : ZMod (k+1)),s⟩)= some ⟨v+(if a r then 1 else 0),
              -((r.val*g : ℕ) : ZMod (k+1))+(((ell*h+1)*m : ℕ) : ZMod (k+1)),tail⟩ := by
      classical
      have pulseTest (g u h rho ell j : ℕ) (hg : 2 ≤ g) (hu : 2 ≤ u) (hh : 1 ≤ h)
        (hrho : 1 ≤ rho) (hj : 1 ≤ j) (window : j+ell*rho ≤ u)
        (r : Fin (h*u+rho)) (i : Fin (g*u))
        (pulsePosition : i.val+1=(j+ell*rho)*g) :
        let k := g*(h*u+rho)-1
        let theta := -((r.val*g : ℕ) : ZMod (k+1))
        let phase := theta+((ell*h*(g*u) : ℕ) : ZMod (k+1))
        coefficient k (phase+(i.val : ℕ))=(if r.val=j then 1 else 0) := by
        let p := h*u+rho
        let T := g*p
        let k := T-1
        let N := k+1
        let m := g*u
        let x := ell*h*m+i.val
        let phase : ZMod N := -((r.val*g : ℕ) : ZMod N)+((ell*h*m : ℕ) : ZMod N)
        let phi : ZMod N := phase+(i.val : ℕ)
        have pLarge : u < p := by
          have mul : u ≤ h*u := Nat.le_mul_of_pos_left u hh
          dsimp [p]; omega
        have kLarge : 2 ≤ k := by
          have plen : 3 ≤ p := by omega
          have product : 6 ≤ T := by dsimp [T]; nlinarith
          dsimp [k]; omega
        have hN : N=T := by dsimp [N,k]; omega
        have jSmall : j*g < T := by
          have jp : j < p := by omega
          have multiplied := Nat.mul_lt_mul_of_pos_right jp (by omega : 0<g)
          simpa only [T,Nat.mul_comm] using multiplied
        have rSmall : r.val*g < T := by
          have multiplied := Nat.mul_lt_mul_of_pos_right r.isLt (by omega : 0<g)
          simpa only [T,Nat.mul_comm,p] using multiplied
        have absolutePosition : x+1=ell*T+j*g := by
          calc
            x+1 = ell*h*m+(j+ell*rho)*g := by dsimp [x]; omega
            _ = ell*T+j*g := by dsimp [m,T,p]; ring
        have turn : (T : ZMod N)=0 := by
          apply (ZMod.natCast_eq_zero_iff _ _).mpr
          rw [hN]
        have castPosition : ((x+1 : ℕ) : ZMod N)=((j*g : ℕ) : ZMod N) := by rw [absolutePosition]; simp only [Nat.cast_add,Nat.cast_mul,turn,mul_zero,zero_add]
        have phiForm : phi=-((r.val*g : ℕ) : ZMod N)+(x : ℕ) := by
          dsimp [phi,phase,x]
          push_cast
          ring
        have endTest : phi=-1 ↔ r.val=j := by
          constructor
          · intro equal
            have equalCast : ((j*g : ℕ) : ZMod N)=((r.val*g : ℕ) : ZMod N) := by
              rw [phiForm] at equal
              push_cast at castPosition equal ⊢
              linear_combination equal - castPosition
            have equalNat : j*g=r.val*g := by
              have residues := (ZMod.natCast_eq_natCast_iff' (j*g) (r.val*g) N).mp equalCast
              simpa only [hN,Nat.mod_eq_of_lt jSmall,Nat.mod_eq_of_lt rSmall] using residues
            nlinarith
          · intro equal
            rw [phiForm,equal]
            push_cast at castPosition ⊢
            linear_combination castPosition
        have noZero : phi ≠ 0 := by
          intro equal; rw [phiForm] at equal; have eqCast : (x : ZMod N)=((r.val*g : ℕ) : ZMod N) := (neg_add_eq_zero.mp equal).symm
          have modEq := (ZMod.natCast_eq_natCast_iff x (r.val*g) N).mp eqCast
          have gT : g ∣ T := by dsimp [T]; exact dvd_mul_right g p
          have gN : g ∣ N := by rw [hN]; exact gT
          have divides : g ∣ x := (modEq.dvd_iff gN).mpr (dvd_mul_left g r.val)
          have dividesNext : g ∣ x+1 := by rw [absolutePosition]; exact Nat.dvd_add (dvd_mul_of_dvd_right gT ell) (dvd_mul_left g j)
          have impossible : g ∣ 1 := by simpa only [Nat.add_sub_cancel_left] using Nat.dvd_sub dividesNext divides
          have small := Nat.le_of_dvd (by decide : 0<1) impossible
          omega
        have sampled : coefficient k phi=(if r.val=j then 1 else 0) := by
          change (if phi=0 ∨ phi=-1 then (1 : ZMod 2) else 0)=_
          simp only [noZero,false_or,endTest]
        exact sampled
      dsimp only
      let p := h*u+rho
      let k := g*p-1
      let m := g*u
      let M := u-R*rho
      let B : Fin m → Bool := fun i => decide (∃ j : Fin p,
        1≤j.val ∧ j.val≤M ∧ a j=true ∧ i.val+1=(j.val+ell*rho)*g)
      have hp : 0<p := by dsimp [p]; nlinarith
      have hm : 0< m := by dsimp [m]; nlinarith
      have hk : 2≤k := by
        have plen : 3≤p := by dsimp [p]; nlinarith
        have full : 6≤g*p := by nlinarith
        dsimp [k]; omega
      have window (j : Fin p) (hj : j.val≤M) : j.val+ell*rho≤u := by
        have rhoMul : ell*rho≤R*rho := Nat.mul_le_mul_right rho hell
        dsimp [M] at hj
        omega
      have firstZero : B ⟨0,hm⟩=false := by
        apply Bool.eq_false_iff.mpr
        intro one; obtain ⟨j,hj,_,_,position⟩ := of_decide_eq_true one; simp only [Fin.val_zero,Nat.zero_add] at position
        have sumPos : 1≤j.val+ell*rho := by omega
        nlinarith
      have divided (i : Fin m) (hi : B i=true) : g ∣ i.val+1 := by
        obtain ⟨j,_,_,_,eq⟩ := of_decide_eq_true hi
        rw [eq]; exact dvd_mul_left g (j.val+ell*rho)
      have separated (i j : Fin m) (next : j.val=i.val+1) (hi : B i=true) : B j=false := by
        apply Bool.eq_false_iff.mpr
        intro hj; have di := divided i hi; have dj := divided j hj
        rw [next] at dj
        have one : g ∣ 1 := by simpa only [Nat.add_sub_cancel_left] using Nat.dvd_sub dj di
        have small := Nat.le_of_dvd (by decide : 0<1) one
        omega
      have sparseScan : ∀ (n maxTrue fuel : ℕ), 1≤ maxTrue → ∀ word : Fin n → Bool,
          (∀ i j, j.val=i.val+1 → word i=true → word j=false) → (∀ i, i.val=0 → word i=true → 1≤fuel) → runAdmissible maxTrue fuel n word=true := by
        intro n; induction n with
        | zero => intro maxTrue fuel hmax word sep head; rfl
        | succ n ih =>
          intro maxTrue fuel hmax word sep head; have sepTail (i j : Fin n) (next : j.val=i.val+1) (hi : Fin.tail word i=true) : Fin.tail word j=false :=
            sep i.succ j.succ (by simp only [Fin.val_succ]; omega) hi
          cases hd : word 0 with
          | false =>
            have tailSafe := ih maxTrue maxTrue hmax (Fin.tail word) sepTail (fun _ _ _ => hmax)
            cases fuel <;> simpa only [runAdmissible,hd,Bool.false_eq_true,if_false] using tailSafe
          | true =>
            have fuelPos : 1≤fuel := head 0 rfl hd
            obtain ⟨fuel',eq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel≠0)
            subst fuel
            have headTail (i : Fin n) (zero : i.val=0) (hi : Fin.tail word i=true) : 1≤fuel' := by
              have no := sep 0 i.succ (by simp only [Fin.val_zero,Fin.val_succ]; omega) hd
              rw [show word i.succ=true from hi] at no
              contradiction
            have tailSafe := ih maxTrue fuel' hmax (Fin.tail word) sepTail headTail
            simpa only [runAdmissible,hd,if_true] using tailSafe
      have sparseTail : ∀ (n : ℕ) (word : Fin n → Bool) (s : ℕ), s≤1 → (∀ i j, j.val=i.val+1 → word i=true → word j=false) →
          (∀ i, i.val=0 → word i=true → s=0) → tailAfter s word≤1 := by
        intro n; induction n with
        | zero => intro word s hs sep head; exact hs
        | succ n ih =>
          intro word s hs sep head; have sepTail (i j : Fin n) (next : j.val=i.val+1) (hi : Fin.tail word i=true) : Fin.tail word j=false :=
            sep i.succ j.succ (by simp only [Fin.val_succ]; omega) hi
          cases hd : word 0 with
          | false =>
            simpa only [tailAfter,hd,Bool.false_eq_true,if_false] using ih (Fin.tail word) 0 (by omega) sepTail (by simp)
          | true =>
            have zero : s=0 := head 0 rfl hd
            have headTail (i : Fin n) (izero : i.val=0) (hi : Fin.tail word i=true) : s+1=0 := by
              have no := sep 0 i.succ (by simp only [Fin.val_zero,Fin.val_succ]; omega) hd
              rw [show word i.succ=true from hi] at no
              contradiction
            simpa only [tailAfter,hd,if_true] using ih (Fin.tail word) (s+1) (by omega) sepTail headTail
      have scanned (s : ℕ) : runAdmissible (k-1) (k-1-s) m B=true := by
        apply sparseScan m (k-1) (k-1-s) (by omega) B separated
        intro i izero hi; have eq : i=⟨0,hm⟩ := Fin.ext izero; rw [eq,firstZero] at hi
        contradiction
      have clearedTail : ∀ (n : ℕ) (hn : 0<n) (word : Fin n → Bool),
          word ⟨0,hn⟩=false → (∀ i j, j.val=i.val+1 → word i=true → word j=false) → ∀ s : ℕ, tailAfter s word≤1 := by
        intro n; cases n with
        | zero => intro hn; omega
        | succ n =>
          intro hn word first sep s; have sepTail (i j : Fin n) (next : j.val=i.val+1) (hi : Fin.tail word i=true) : Fin.tail word j=false :=
            sep i.succ j.succ (by simp only [Fin.val_succ]; omega) hi
          have head : word 0=false := first
          simpa only [tailAfter,head,Bool.false_eq_true,if_false] using
            sparseTail n (Fin.tail word) 0 (by omega) sepTail (by simp)
      have tailSmall (s : ℕ) : tailAfter s B≤1 := clearedTail m hm B firstZero separated s
      have localLegal : DBonacciAdmissible k m B := by
        obtain ⟨k',eq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
        simpa [eq,DBonacciAdmissible] using scanned 0
      refine ⟨localLegal,firstZero,?_⟩
      intro r v s hs; let phase : ZMod (k+1) := -((r.val*g : ℕ) : ZMod (k+1))+((ell*h*m : ℕ) : ZMod (k+1))
      have pulseCoeff (i : Fin m) (j : Fin p) (pos : 1≤j.val) (bound : j.val≤M)
          (position : i.val+1=(j.val+ell*rho)*g) : coefficient k (phase+(i.val : ℕ))=(if r.val=j.val then 1 else 0) :=
        pulseTest g u h rho ell j.val hg hu hh hrho pos (window j bound) r i position
      have increment : wordIncrement k phase B=(if a r then 1 else 0) := by
        unfold wordIncrement
        by_cases bit : a r=true
        · obtain ⟨rpos,rbound⟩ := aSupport r bit
          let ix : Fin m := ⟨(r.val+ell*rho)*g-1,by
            have w := window r rbound
            have full : (r.val+ell*rho)*g≤ m := by dsimp [m]; nlinarith
            have pos : 1≤(r.val+ell*rho)*g := by
              have sumPos : 0<r.val+ell*rho := by omega
              exact Nat.mul_pos sumPos (by omega)
            omega⟩
          have atIx : ix.val+1=(r.val+ell*rho)*g := by
            have pos : 1≤(r.val+ell*rho)*g := by
              have sumPos : 0<r.val+ell*rho := by omega
              exact Nat.mul_pos sumPos (by omega)
            dsimp [ix]; omega
          have on : B ix=true := by
            apply decide_eq_true
            exact ⟨r,rpos,rbound,bit,atIx⟩
          rw [Finset.sum_eq_single ix]
          · simp [on,pulseCoeff ix r rpos rbound atIx,bit]
          · intro i _ different
            by_cases one : B i=true
            · obtain ⟨j,jpos,jbound,jbit,jposition⟩ := of_decide_eq_true one
              have notSame : r.val≠j.val := by
                intro same; apply different; apply Fin.ext
                dsimp [ix]
                rw [← same] at jposition; omega
              simp [one,pulseCoeff i j jpos jbound jposition,notSame]
            · simp [one]
          · intro missing
            exact (missing (Finset.mem_univ ix)).elim
        · have allZero : ∀ i : Fin m, (if B i then coefficient k (phase+(i.val : ℕ)) else 0)=0 := by
            intro i; by_cases one : B i=true
            · obtain ⟨j,jpos,jbound,jbit,jposition⟩ := of_decide_eq_true one
              have notSame : r.val≠j.val := by
                intro same; have ij : r=j := Fin.ext same; exact bit (ij.symm ▸ jbit)
              simp [one,pulseCoeff i j jpos jbound jposition,notSame]
            · simp [one]
          rw [Finset.sum_eq_zero (fun i _ => allZero i),if_neg bit]
      have execution := (literal_block_execution k hk m B v phase s hs).1
      rw [if_pos (scanned s),increment] at execution
      refine ⟨tailAfter s B,tailSmall s,?_⟩
      have phaseShift : phase+(m : ℕ)= -((r.val*g : ℕ) : ZMod (k+1))+(((ell*h+1)*m : ℕ) : ZMod (k+1)) := by
        dsimp only [phase]
        push_cast
        ring
      rw [phaseShift] at execution; exact execution
    have archiveInjectivity {X : Type z} (h R m : ℕ) (hh : 1≤h)
        (gamma : X → Fin (R+1) → ZMod 2) (injective : Function.Injective gamma)
        (actions : ℕ → Fin m → Bool) (v : ZMod 2) :
        let L := R*h+1
        let increment (x : X) (t : ℕ) : ZMod 2 := if active : h ∣ t then if small : t/h<R+1 then gamma x ⟨t/h,small⟩ else 0 else 0
        let scalar (x : X) (t : ℕ) : ZMod 2 := v+∑ i ∈ Finset.range t, increment x i
        let archive (x : X) (t : ℕ) : Archive m := List.ofFn (fun i : Fin t => (actions i.val,some (scalar x (i.val+1))))
        Function.Injective (fun x => archive x L) := by
      classical
      dsimp only
      let L := R*h+1
      let increment (x : X) (t : ℕ) : ZMod 2 := if active : h ∣ t then if small : t/h<R+1 then gamma x ⟨t/h,small⟩ else 0 else 0
      let scalar (x : X) (t : ℕ) : ZMod 2 := v+∑ i ∈ Finset.range t, increment x i
      let archive (x : X) (t : ℕ) : Archive m := List.ofFn (fun i : Fin t => (actions i.val,some (scalar x (i.val+1))))
      have scalarStep (x : X) (t : ℕ) : scalar x (t+1)=scalar x t+increment x t := by
        dsimp only [scalar]; rw [Finset.sum_range_succ]; abel
      intro x y sameArchive; change archive x L=archive y L at sameArchive; have allEndpoints := List.ofFn_injective sameArchive
      have sameScalar (t : ℕ) (bound : t≤L) : scalar x t=scalar y t := by
        by_cases zero : t=0
        · simp [scalar,zero]
        · let i : Fin L := ⟨t-1,by omega⟩
          have same := congrArg Prod.snd (congrFun allEndpoints i)
          simp only [i,show t-1+1=t by omega] at same; exact Option.some.inj same
      apply injective
      funext ell
      let t := ell.val*h
      have active : h ∣ t := dvd_mul_left h ell.val
      have quotient : t/h=ell.val := Nat.mul_div_cancel ell.val (by omega)
      have first : t≤R*h := Nat.mul_le_mul_right h (by omega : ell.val≤R)
      have readout (x : X) : increment x t=gamma x ell := by
        dsimp only [increment]; rw [dif_pos active,dif_pos (by rw [quotient]; exact ell.isLt)]
        congr 1
        exact Fin.ext quotient
      have diff (x : X) : scalar x (t+1)-scalar x t=gamma x ell := by rw [scalarStep,readout]; abel
      rw [←diff x,←diff y,sameScalar (t+1) (by dsimp [L]; omega),sameScalar t (by dsimp [L]; omega)]
    let X := Set.range labels
    letI : Fintype X := Fintype.ofFinite _
    let A : X := ⟨labels ⟨0,hp⟩,Set.mem_range_self _⟩
    let d := R+1
    have dlog : d=Nat.clog 2 n := by
      have Rpos := source.2.2.2.1
      dsimp only [R] at Rpos
      dsimp [d,R]
      omega
    have cardCode : Fintype.card X≤Fintype.card (Fin d → ZMod 2) := by
      rw [Fintype.card_fun,Fintype.card_fin,ZMod.card,dlog]
      have cardX : n=Fintype.card X := Nat.card_eq_fintype_card
      rw [←cardX]; exact Nat.le_pow_clog (by decide : 1<2) n
    let e : X ↪ (Fin d → ZMod 2) := Classical.choice (Function.Embedding.nonempty_of_card_le cardCode)
    let gamma (x : X) (i : Fin d) : ZMod 2 := e x i-e A i
    have gammaInj : Function.Injective gamma := by
      intro x y eq; apply e.injective; funext i
      have diffs := congrFun eq i
      exact sub_left_injective diffs
    have gammaA (i : Fin d) : gamma A i=0 := sub_self _
    let lab (j : Fin p) : X := ⟨labels j,Set.mem_range_self j⟩
    let bits (ell : Fin d) (j : Fin p) : Bool := decide (gamma (lab j) ell=1)
    have bitSupport (ell : Fin d) (j : Fin p) (one : bits ell j=true) : 1≤j.val ∧ j.val≤M := by
      apply support j
      intro eq; have equal : lab j=A := Subtype.ext eq; have gammaOne : gamma (lab j) ell=1 := of_decide_eq_true one
      rw [equal,gammaA] at gammaOne; exact zero_ne_one gammaOne
    let query (ell : Fin d) : Fin m → Bool := fun i => decide (∃ j : Fin p,
      1≤j.val ∧ j.val≤M ∧ bits ell j=true ∧ i.val+1=(j.val+ell.val*rho)*g)
    have queryFact (ell : Fin d) := queries g u h rho R ell.val hg hu hh hrho
      source.2.2.2.2.1 (by dsimp [d] at ell; omega) (bits ell) (bitSupport ell)
    have binary (z : ZMod 2) : (if z=1 then (1 : ZMod 2) else 0)=z := by
      by_cases one : z=1
      · rw [if_pos one,one]
      · have notOne : z.val≠1 := by intro eq; exact one ((ZMod.val_eq_one (by decide) z).mp eq)
        have small := ZMod.val_lt z
        have zero : z=0 := (ZMod.val_eq_zero z).mp (by omega)
        simp [zero]
    let actions (t : ℕ) : Fin m → Bool := if small : t/h<d then if active : h ∣ t then query ⟨t/h,small⟩ else (fun _ => false)
      else (fun _ => false)
    let L := R*h+1
    let increment (x : X) (t : ℕ) : ZMod 2 := if active : h ∣ t then if small : t/h<d then gamma x ⟨t/h,small⟩ else 0 else 0
    let scalar (x : X) (t : ℕ) : ZMod 2 := v+∑ i ∈ Finset.range t, increment x i
    let archive (x : X) (t : ℕ) : Archive m := List.ofFn (fun i : Fin t => (actions i.val,some (scalar x (i.val+1))))
    have archiveInj : Function.Injective (fun x => archive x L) := archiveInjectivity h R m hh gamma gammaInj actions v
    let decode (arc : Archive m) : Y := if matchCode : ∃ x : X, archive x L=arc then (Classical.choose matchCode).val else A.val
    have decodeCorrect (x : X) : decode (archive x L)=x.val := by
      have existsCode : ∃ y : X, archive y L=archive x L := ⟨x,rfl⟩
      dsimp only [decode]; rw [dif_pos existsCode]
      have same : Classical.choose existsCode=x := archiveInj (Classical.choose_spec existsCode)
      rw [same]
    let pi : Selector m Y := fun y0 arc => match y0 with
      | none => .inl (f none)
      | some _ => if next : arc.length<L then .inr (actions arc.length) else .inl (decode arc)
    have allFalseLegal : DBonacciAdmissible k m (fun _ => false) := by
      obtain ⟨k',eq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
      simpa [eq,DBonacciAdmissible] using
        D5.S0.Tower.DBonacci.Values.runAdmissible_all_false (k-1) (k-1) m
    have actionLegal (t : ℕ) : DBonacciAdmissible k m (actions t) := by
      dsimp only [actions]
      split_ifs with small active
      · exact (queryFact ⟨t/h,small⟩).1
      · exact allFalseLegal
      · exact allFalseLegal
    have law : ∀ y0 arc B, pi y0 arc=.inr B → localAlphabet=true → DBonacciAdmissible k m B := by
      intro y0 arc B selected _; cases y0 with
      | none => simp only [pi,Sum.inl_ne_inr] at selected
      | some y =>
        by_cases next : arc.length<L
        · simp only [pi,dif_pos next,Sum.inr.injEq] at selected
          rw [←selected]; exact actionLegal _
        · simp only [pi,dif_neg next,Sum.inl_ne_inr] at selected
    have scalarStep (x : X) (t : ℕ) : scalar x (t+1)=scalar x t+increment x t := by
      dsimp only [scalar]; rw [Finset.sum_range_succ]; abel
    have archiveStep (x : X) (t : ℕ) : archive x (t+1)= archive x t++[(actions t,some (scalar x (t+1)))] := by
      simp only [archive,List.ofFn_succ',List.concat_eq_append,Fin.val_castSucc,Fin.val_last]
    have zeroTail : ∀ (n s : ℕ), 0<n → tailAfter s (fun _ : Fin n => false)=0 := by
      intro n; cases n with
      | zero => intro s hn; omega
      | succ n =>
        intro s _; have all : ∀ n : ℕ, tailAfter 0 (fun _ : Fin n => false)=0 := by
          intro n; induction n with
          | zero => rfl
          | succ n ih => simpa +unfoldPartialApp only [tailAfter,Bool.false_eq_true,if_false,Fin.tail] using ih
        simpa +unfoldPartialApp only [tailAfter,Bool.false_eq_true,if_false,Fin.tail] using all n
    have stepRecord (r : Fin p) (t : ℕ) (z : ZMod 2) (s : ℕ) (hs : s<k) : ∃ tail, tail<k ∧ runBits k (actions t)
          (some ⟨z,-((r.val*g : ℕ) : ZMod (k+1))+((t*m : ℕ) : ZMod (k+1)),s⟩)= some ⟨z+increment (lab r) t,
            -((r.val*g : ℕ) : ZMod (k+1))+(((t+1)*m : ℕ) : ZMod (k+1)),tail⟩ := by
      by_cases small : t/h<d
      · by_cases active : h ∣ t
        · let ell : Fin d := ⟨t/h,small⟩
          have timing : ell.val*h=t := Nat.div_mul_cancel active
          obtain ⟨tail,htail,ex⟩ := (queryFact ell).2.2 r z s hs
          have bit : (if bits ell r then (1 : ZMod 2) else 0)=gamma (lab r) ell := by simpa only [bits,decide_eq_true_eq] using binary (gamma (lab r) ell)
          change runBits k (query ell)
            (some ⟨z,-((r.val*g : ℕ) : ZMod (k+1))+((ell.val*h*m : ℕ) : ZMod (k+1)),s⟩)= some ⟨z+(if bits ell r then 1 else 0),
              -((r.val*g : ℕ) : ZMod (k+1))+(((ell.val*h+1)*m : ℕ) : ZMod (k+1)),tail⟩ at ex
          rw [timing,bit] at ex
          refine ⟨tail,by omega,?_⟩
          simpa only [actions,dif_pos small,dif_pos active,increment] using ex
        · have ex := (literal_block_execution k hkl m (fun _ => false) z
            (-((r.val*g : ℕ) : ZMod (k+1))+((t*m : ℕ) : ZMod (k+1))) s hs).1
          rw [if_pos (D5.S0.Tower.DBonacci.Values.runAdmissible_all_false _ _ _)] at ex; simp only [wordIncrement,Bool.false_eq_true,if_false,Finset.sum_const_zero,add_zero,
            zeroTail m s (by omega)] at ex
          refine ⟨0,by omega,?_⟩
          simp only [actions,dif_pos small,dif_neg active,increment,add_zero]
          convert ex using 1
          congr 2
          push_cast
          ring
      · have ex := (literal_block_execution k hkl m (fun _ => false) z
          (-((r.val*g : ℕ) : ZMod (k+1))+((t*m : ℕ) : ZMod (k+1))) s hs).1
        rw [if_pos (D5.S0.Tower.DBonacci.Values.runAdmissible_all_false _ _ _)] at ex; simp only [wordIncrement,Bool.false_eq_true,if_false,Finset.sum_const_zero,add_zero,
          zeroTail m s (by omega)] at ex
        refine ⟨0,by omega,?_⟩
        have incZero : increment (lab r) t=0 := by
          dsimp only [increment]
          split_ifs <;> rfl
        simp only [actions,dif_neg small,incZero,add_zero]
        convert ex using 1
        congr 2
        push_cast
        ring
    have observed (w : List Bool) : output k (by omega) w=endpointReading (OriginalRecord k (by omega) w) := by
      unfold output OriginalRecord
      cases (scanner k (by omega)).eval w <;> rfl
    have runProtocol (r : Fin p) : ∀ (remaining t : ℕ), t+remaining=L → ∀ (w : List Bool) (s : ℕ), s<k →
        OriginalRecord k (by omega) w= some ⟨scalar (lab r) t,-((r.val*g : ℕ) : ZMod (k+1))+((t*m : ℕ) : ZMod (k+1)),s⟩ →
        execute k (by omega) pi remaining w (some v) (archive (lab r) t)=some (labels r,remaining) := by
      intro remaining; induction remaining with
      | zero =>
        intro t time w s hs rec
        have tEq : t=L := by omega
        subst t
        have len : (archive (lab r) L).length=L := List.length_ofFn
        simp only [execute,pi,len,dif_neg (Nat.lt_irrefl L),decodeCorrect,lab]
      | succ remaining ih =>
        intro t time w s hs rec
        have tlt : t<L := by omega
        have len : (archive (lab r) t).length=t := List.length_ofFn
        have selected : pi (some v) (archive (lab r) t)=.inr (actions t) := by simp only [pi,len,dif_pos tlt]
        obtain ⟨tail,htail,ex⟩ := stepRecord r t (scalar (lab r) t) s hs
        have nextRecord : OriginalRecord k (by omega) (w++List.ofFn (actions t))= some ⟨scalar (lab r) (t+1),-((r.val*g : ℕ) : ZMod (k+1))+
              (((t+1)*m : ℕ) : ZMod (k+1)),tail⟩ := by
          rw [bridge.2.1,rec,ex,←scalarStep]
        have reply : output k (by omega) (w++List.ofFn (actions t))=some (scalar (lab r) (t+1)) := by rw [observed,nextRecord]; rfl
        have after := ih (t+1) (by omega) (w++List.ofFn (actions t)) tail htail nextRecord
        simp only [execute,selected,reply,←archiveStep,after,Option.map_some]
    refine ⟨pi,law,rfl,?_⟩
    intro history; dsimp only; intro outputV; let w := history.flatMap (fun B => List.ofFn B.val)
    have outputSame : output k (by omega) w=some v := outputV
    obtain ⟨q,rec⟩ : ∃ q : LiveRecord k, OriginalRecord k (by omega) w=some q := by
      cases current : OriginalRecord k (by omega) w with
      | none => rw [observed,current] at outputSame; contradiction
      | some q => exact ⟨q,rfl⟩
    have qValue : q.value=v := by rw [observed,rec] at outputSame; exact Option.some.inj outputSame
    have actual : D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition.SourceRecord k m (some q) := by
      have realization := (D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition.whole_first_zero_acquisition
        k m hkl hml localAlphabet (fun _ => ())).1
      apply (realization (some q)).mpr
      refine ⟨history,?_⟩
      rw [←bridge.2.2.1 m localAlphabet history]; exact rec
    have kperiod : k+1=g*p := by dsimp only [k]; exact Nat.sub_add_cancel (Nat.mul_pos (by omega) hp)
    have gcdEq : Nat.gcd m (k+1)=g := by rw [kperiod]; exact source.2.2.2.2.2
    have divides : g ∣ (-q.phase).val := by
      have gPhase : g ∣ q.phase.val := by simpa only [gcdEq] using actual.2
      rw [ZMod.neg_val]
      split_ifs
      · exact dvd_zero _
      · exact Nat.dvd_sub (by rw [kperiod]; exact dvd_mul_right g p) gPhase
    let r : Fin p := ⟨(-q.phase).val/g,
      (Nat.div_lt_iff_lt_mul (by omega : 0<g)).mpr
        (by simpa only [Nat.mul_comm,kperiod] using ZMod.val_lt (-q.phase))⟩
    have phase : -((r.val*g : ℕ) : ZMod (k+1))=q.phase := by dsimp only [r]; rw [Nat.div_mul_cancel divides,ZMod.natCast_zmod_val,neg_neg]
    have target : f (OriginalRecord k (by omega) w)=labels r := by
      rw [rec]
      have eq : q=⟨v,-((r.val*g : ℕ) : ZMod (k+1)),q.tail⟩ := by
        cases q
        simp_all only
      rw [eq]; exact restrict r q.tail actual.1
    have initial : OriginalRecord k (by omega) w= some ⟨scalar (lab r) 0,-((r.val*g : ℕ) : ZMod (k+1))+((0*m : ℕ) : ZMod (k+1)),q.tail⟩ := by
      rw [rec]; simp only [scalar,Finset.range_zero,Finset.sum_empty,add_zero,Nat.zero_mul,Nat.cast_zero,phase]
      congr 1
      cases q
      simp_all only
    have full := runProtocol r L 0 (by omega) w q.tail actual.1 initial
    refine ⟨L,le_rfl,?_⟩
    change execute k (by omega) pi L w (some v) []=some (f (OriginalRecord k (by omega) w),L)
    rw [target]
    simpa only [archive,List.ofFn_zero] using full
  change (⨅ b : {b : ℕ // OriginalFiberFeasible k m (by omega) localAlphabet f v b},
      (b.val : ℕ∞)) = ((R*h+1 : ℕ) : ℕ∞)
  apply le_antisymm
  · exact iInf_le_of_le ⟨R*h+1,upper⟩ le_rfl
  · apply le_iInf
    intro b; exact_mod_cast lower b.val b.property

#print axioms original_repeated_guardrail_cost
end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.RepeatedGuardrailCost
