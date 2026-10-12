/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalNarrowCost
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalNarrowCost
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Arbitrary initial record labels require first-window waiting and binary depth. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge
import D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.ENat.Lattice

set_option autoImplicit false
noncomputable section

namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalNarrowCost

open D5.S0.Tower.DBonacci.Names
open D5.S0.Tower.DBonacciGeneral.UniformBaseGap
open D5.S0.Automata.TypedPartialDFAOOverBase
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.LiteralModel
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.EndpointCells
open D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalExecutionBridge
open scoped BigOperators
universe z

/-- The value, phase and final tail of the same accepted literal word. -/
def OriginalRecord (k : ℕ) (hk : 0<k) (w : List Bool) : Option (LiveRecord k) :=
  ((D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.scanner k hk).eval w).map
    (fun tail => ⟨D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.value k 0 w,
      (w.length : ZMod (k+1)),tail.val⟩)
/-- One lawful selector succeeds on every actual initial history in the free-value fiber.
The initial rejection returns its label freely; each complete issued word is paid. -/
def OriginalFiberFeasible {Y : Type z} (k m : ℕ) (hk : 0<k)
    (localAlphabet : Bool) (f : Option (LiveRecord k) → Y) (v : ZMod 2) (d : ℕ) : Prop :=
  ∃ π : D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.Selector m Y,
    (∀ y₀ archive B, π y₀ archive=.inr B → localAlphabet=true → DBonacciAdmissible k m B) ∧
    π none []=.inl (f none) ∧
    ∀ history : List (AllowedBlock k m localAlphabet),
      let w := history.flatMap (fun action => List.ofFn action.val)
      D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.output k hk w=some v →
      ∃ c ≤ d, D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.execute
        k hk π d w (some v) []=some (f (OriginalRecord k hk w),c)

/-- The infimum of the finite uniform budgets, or infinity if none is feasible. -/
def OriginalFiberCost {Y : Type z} (k m : ℕ) (hk : 0<k)
    (localAlphabet : Bool) (f : Option (LiveRecord k) → Y) (v : ZMod 2) : ℕ∞ :=
  ⨅ d : {d : ℕ // OriginalFiberFeasible k m hk localAlphabet f v d}, (d.val : ℕ∞)


set_option maxHeartbeats 1500000 in
/-- A first-window wait followed by binary discrimination is necessary for any initial target.
The label image uses exactly the tail-zero indices below m/gcd(m,k+1); feasibility
still ranges over every actual history and every initial tail in the fixed-value fiber. -/
theorem original_cost_lower :
  ∀ {Y : Type z} (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m) (hshort : m < k+1)
    (f : Option (LiveRecord k) → Y) (v : ZMod 2) (localAlphabet : Bool),
  let g := Nat.gcd m (k+1)
  let u := m/g
  let p := (k+1)/g
  let h := p/u
  let q : Fin u → Option (LiveRecord k) :=
    fun j => some ⟨v,-((j.val*g : ℕ) : ZMod (k+1)),0⟩
  3 ≤ Nat.card (Set.range (fun j : Fin u => f (q j))) →
  ((h + Nat.clog 2 (Nat.card (Set.range (fun j : Fin u => f (q j)))) - 1 : ℕ) : ℕ∞)
    ≤ OriginalFiberCost k m (by omega) localAlphabet f v := by
  classical
  have nativeLower :
    ∀ {Y : Type z} (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m) (hshort : m < k+1)
      (f : Option (LiveRecord k) → Y) (v : ZMod 2) (localAlphabet : Bool),
    let g := Nat.gcd m (k+1)
    let u := m/g
    let p := (k+1)/g
    let h := p/u
    let q : Fin u → Option (LiveRecord k) := fun j => some ⟨v,-((j.val*g : ℕ) : ZMod (k+1)),0⟩
    3 ≤ Nat.card (Set.range (fun j : Fin u => f (q j))) →
    ∀ (d : ℕ) (tree : AcquisitionTree k m localAlphabet Y d),
      (∀ j : Fin u, tree.result (q j) = f (q j)) →
      h + Nat.clog 2 (Nat.card (Set.range (fun j : Fin u => f (q j)))) - 1 ≤ d := by
    classical
    have transport :
      ∀ {Y : Type z} (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m) (hshort : m < k+1)
        (f : Option (LiveRecord k) → Y) (v w : ZMod 2) (localAlphabet : Bool),
      let g := Nat.gcd m (k+1)
      let u := m/g
      let p := (k+1)/g
      let h := p/u
      let q : Fin u → Option (LiveRecord k) := fun j => some ⟨v,-((j.val*g : ℕ) : ZMod (k+1)),0⟩
      3 ≤ Nat.card (Set.range (fun j : Fin u => f (q j))) →
      ∀ (first : AllowedBlock k m localAlphabet) (S : Set (Fin u)),
        S.Nonempty →
        (∀ j ∈ S, endpointReading (runBits k first.val (q j)) = some w) →
        ∃ s : ℕ, s < k ∧
          (∀ j ∈ S, runBits k first.val (q j) =
            some ⟨w,-((j.val*g : ℕ) : ZMod (k+1))+(m : ℕ),s⟩) ∧
          (∀ actions : List (AllowedBlock k m localAlphabet), actions.length ≤ h-1 →
            ∃ tail : Option ℕ,
              (∀ j ∈ S, historyRecordFrom actions (runBits k first.val (q j)) =
                tail.map (fun s => ⟨w,-((j.val*g : ℕ) : ZMod (k+1))+
                  (((1+actions.length)*m : ℕ) : ZMod (k+1)),s⟩)) ∧
              (∀ s, tail = some s → s < k)) ∧
          (∀ (d : ℕ), d ≤ h-1 →
            ∀ tree : AcquisitionTree k m localAlphabet Y d,
            ∀ j ∈ S, ∀ j' ∈ S,
              tree.result (runBits k first.val (q j)) = tree.result (runBits k first.val (q j')) ∧
              tree.archive (runBits k first.val (q j)) = tree.archive (runBits k first.val (q j')) ∧
              ∀ entry ∈ tree.archive (runBits k first.val (q j)),
                entry.2 = some w ∨ entry.2 = none) ∧
          (∀ (r : ℕ), r ≤ h-1 → ∀ (n : ℕ) (tree : AcquisitionTree k m localAlphabet Y n),
            ∀ j ∈ S, ∀ j' ∈ S,
              (tree.archive (runBits k first.val (q j))).take r =
                (tree.archive (runBits k first.val (q j'))).take r ∧
              ∀ entry ∈ (tree.archive (runBits k first.val (q j))).take r,
                entry.2 = some w ∨ entry.2 = none) := by
      classical
      intro Y k m hk hm hshort f v w localAlphabet
      dsimp only
      let g := Nat.gcd m (k+1)
      let u := m/g
      let p := (k+1)/g
      let h := p/u
      let theta (j : Fin u) : ZMod (k+1) := -((j.val*g : ℕ) : ZMod (k+1))
      let q (j : Fin u) : Option (LiveRecord k) := some ⟨v,theta j,0⟩
      change 3 ≤ Nat.card (Set.range (fun j : Fin u => f (q j))) → _
      intro hn first S hS branch
      have hcard : Nat.card (Set.range (fun j : Fin u => f (q j))) ≤ u := by
        have fact := Nat.card_le_card_of_surjective
          (fun j : Fin u => (⟨f (q j),j,rfl⟩ : Set.range (fun j : Fin u => f (q j))))
          (by rintro ⟨y,j,rfl⟩; exact ⟨j,rfl⟩)
        rw [Nat.card_fin] at fact
        exact fact
      have hu : 3 ≤ u := hn.trans hcard
      have hg : 0 < g := Nat.gcd_pos_of_pos_left (k+1) (by omega)
      have hmu : g*u=m := Nat.mul_div_cancel' (Nat.gcd_dvd_left m (k+1))
      have hTp : g*p=k+1 := Nat.mul_div_cancel' (Nat.gcd_dvd_right m (k+1))
      have hh : h=(k+1)/m := by
        dsimp only [h]
        rw [← Nat.mul_div_mul_left p u hg,hTp,hmu]
      have hhpos : 1 ≤ h := by rw [hh]; exact Nat.div_pos (by omega) (by omega)
      have budget (n : ℕ) (hn : n ≤ h-1) : m+n*m ≤ h*m := by
        have hp : n+1 ≤ h := by omega
        calc
          m+n*m = (n+1)*m := by ring
          _ ≤ h*m := Nat.mul_le_mul_right m hp
      have hnodvd : ¬m ∣ k+1 := by
        intro hd
        have he : g=m := Nat.gcd_eq_left hd
        have : u=1 := by dsimp [u]; rw [he]; exact Nat.div_self (by omega)
        omega
      have hhm : h*m < k+1 := by
        have he := Nat.div_mul_le_self (k+1) m
        rw [← hh] at he
        have hne : h*m ≠ k+1 := by
          intro eq
          apply hnodvd
          rw [← eq]
          exact dvd_mul_left m h
        omega
      have hjg (j : Fin u) : j.val*g < m := by
        have hj := Nat.mul_lt_mul_of_pos_right j.isLt hg
        simpa [Nat.mul_comm,hmu] using hj
      have quiet (j : Fin u) (i : ℕ) (lo : m ≤ i) (hi : i < h*m) :
          coefficient k (theta j+(i : ℕ)) = 0 := by
        have hj := hjg j
        have hjle : j.val*g ≤ i := by omega
        have hdiff : 0 < i-j.val*g ∧ i-j.val*g < k := by omega
        have phase : theta j+(i : ℕ) = ((i-j.val*g : ℕ) : ZMod (k+1)) := by
          rw [Nat.cast_sub hjle]
          dsimp [theta]
          abel
        have nz : ((i-j.val*g : ℕ) : ZMod (k+1)) ≠ 0 := by
          intro eq
          have hd := (ZMod.natCast_eq_zero_iff _ _).mp eq
          have ht := Nat.le_of_dvd hdiff.1 hd
          omega
        have nm : ((i-j.val*g : ℕ) : ZMod (k+1)) ≠ -1 := by
          intro eq
          have ze : ((i-j.val*g+1 : ℕ) : ZMod (k+1)) = 0 := by
            rw [Nat.cast_add,Nat.cast_one,eq]; simp
          have hd := (ZMod.natCast_eq_zero_iff _ _).mp ze
          have ht := Nat.le_of_dvd (by omega : 0 < i-j.val*g+1) hd
          omega
        simp [coefficient,phase,nz,nm]
      have increment (t : ℕ) (lo : m ≤ t) (hi : t+m ≤ h*m)
          (B : Fin m → Bool) (j : Fin u) :
          wordIncrement k (theta j+(t : ℕ)) B = 0 := by
        unfold wordIncrement
        apply Finset.sum_eq_zero
        intro i _
        have hzero := quiet j (t+i.val) (by omega) (by omega)
        simpa only [Nat.cast_add,add_assoc] using
          (show (if B i then coefficient k (theta j+((t+i.val : ℕ) : ZMod (k+1))) else 0)=0 by
            rw [hzero]; split <;> rfl)
      have block (t s : ℕ) (hs : s < k) (lo : m ≤ t) (hi : t+m ≤ h*m)
          (B : AllowedBlock k m localAlphabet) (j : Fin u) :
          runBits k B.val (some ⟨w,theta j+(t : ℕ),s⟩) =
            if runAdmissible (k-1) (k-1-s) m B.val = true then
              some ⟨w,theta j+((t+m : ℕ) : ZMod (k+1)),tailAfter s B.val⟩ else none := by
        have exec := (literal_block_execution k hk m B.val w (theta j+(t : ℕ)) s hs).1
        rw [increment t lo hi B.val j] at exec
        simpa [Nat.cast_add,add_assoc] using exec
      have absorb (actions : List (AllowedBlock k m localAlphabet)) :
          historyRecordFrom actions (none : Option (LiveRecord k)) = none := by
        have bits (L : List Bool) : runWord (bitUpdate k) L none = none := by
          induction L with
          | nil => rfl
          | cons b L ih => simpa [runWord,bitUpdate] using ih
        induction actions with
        | nil => rfl
        | cons B actions ih => simpa [historyRecordFrom,List.foldl_cons,runBits,bits] using ih
      have literal : ∀ (actions : List (AllowedBlock k m localAlphabet)) (t s : ℕ),
          s < k → m ≤ t → t+actions.length*m ≤ h*m →
          ∃ tail : Option ℕ,
            (∀ j : Fin u, historyRecordFrom actions (some ⟨w,theta j+(t : ℕ),s⟩) =
              tail.map (fun r => ⟨w,theta j+((t+actions.length*m : ℕ) : ZMod (k+1)),r⟩)) ∧
            ∀ r, tail=some r → r<k := by
        intro actions
        induction actions with
        | nil =>
            intro t s hs lo hi
            exact ⟨some s,by simp [historyRecordFrom],by intro r hr; cases hr; exact hs⟩
        | cons B actions ih =>
            intro t s hs lo hi
            have hstep : t+m ≤ h*m := by simp only [List.length_cons] at hi; nlinarith
            by_cases safe : runAdmissible (k-1) (k-1-s) m B.val = true
            · have hs' := (literal_block_execution k hk m B.val w 0 s hs).2 safe
              obtain ⟨tail,relation,bound⟩ := ih (t+m) (tailAfter s B.val) hs' (by omega)
                (by simp only [List.length_cons] at hi; nlinarith)
              refine ⟨tail,?_,bound⟩
              intro j
              change historyRecordFrom actions (runBits k B.val (some ⟨w,theta j+(t : ℕ),s⟩)) = _
              rw [block t s hs lo hstep B j,if_pos safe,relation j]
              congr 1
              funext r
              congr 1
              simp only [List.length_cons]
              congr 1
              ring
            · refine ⟨none,?_,by simp⟩
              intro j
              change historyRecordFrom actions (runBits k B.val (some ⟨w,theta j+(t : ℕ),s⟩)) = _
              rw [block t s hs lo hstep B j,if_neg safe,absorb]
              rfl
      have treeNone : ∀ (d : ℕ) (tree : AcquisitionTree k m localAlphabet Y d),
          ∀ entry ∈ tree.archive none, entry.2=none := by
        have bits (L : List Bool) : runWord (bitUpdate k) L none=none := by
          induction L with
          | nil => rfl
          | cons b L ih => simpa [runWord,bitUpdate] using ih
        intro d tree
        induction tree with
        | stop label => simp [AcquisitionTree.archive]
        | step B next ih =>
            simpa [AcquisitionTree.archive,runBits,bits,endpointReading] using ih none
      have adaptive : ∀ (d : ℕ) (tree : AcquisitionTree k m localAlphabet Y d)
          (t s : ℕ), s<k → m≤t → t+d*m≤h*m →
          ∀ j j' : Fin u,
            tree.result (some ⟨w,theta j+(t : ℕ),s⟩) = tree.result (some ⟨w,theta j'+(t : ℕ),s⟩) ∧
            tree.archive (some ⟨w,theta j+(t : ℕ),s⟩) = tree.archive (some ⟨w,theta j'+(t : ℕ),s⟩) ∧
            ∀ entry ∈ tree.archive (some ⟨w,theta j+(t : ℕ),s⟩), entry.2=some w ∨ entry.2=none := by
        intro d tree
        induction tree with
        | stop label => intros; simp [AcquisitionTree.result,AcquisitionTree.archive]
        | @step d B next ih =>
            intro t s hs lo hi j j'
            have hstep : t+m≤h*m := by nlinarith
            by_cases safe : runAdmissible (k-1) (k-1-s) m B.val = true
            · have hs' := (literal_block_execution k hk m B.val w 0 s hs).2 safe
              have inductionResult := ih (some w) (t+m) (tailAfter s B.val) hs' (by omega)
                (by nlinarith) j j'
              simp only [AcquisitionTree.result,AcquisitionTree.archive,
                block t s hs lo hstep B j,block t s hs lo hstep B j',if_pos safe,endpointReading]
              exact ⟨inductionResult.1,congrArg (List.cons (B,some w)) inductionResult.2.1,by
                intro entry he
                rcases List.mem_cons.mp he with eq | mem
                · subst entry; exact Or.inl rfl
                · exact inductionResult.2.2 entry mem⟩
            · simp only [AcquisitionTree.result,AcquisitionTree.archive,
                block t s hs lo hstep B j,block t s hs lo hstep B j',if_neg safe,endpointReading]
              refine ⟨trivial,trivial,?_⟩
              intro entry he
              rcases List.mem_cons.mp he with eq | mem
              · subst entry; exact Or.inr rfl
              · exact Or.inr (treeNone d (next none) entry mem)
      have prefixRelation : ∀ (r n : ℕ) (tree : AcquisitionTree k m localAlphabet Y n)
          (t s : ℕ), s<k → m≤t → t+r*m≤h*m → ∀ j j' : Fin u,
          (tree.archive (some ⟨w,theta j+(t : ℕ),s⟩)).take r =
            (tree.archive (some ⟨w,theta j'+(t : ℕ),s⟩)).take r ∧
          ∀ entry ∈ (tree.archive (some ⟨w,theta j+(t : ℕ),s⟩)).take r,
            entry.2=some w ∨ entry.2=none := by
        intro r
        induction r with
        | zero => intros; simp
        | succ r ih =>
            intro n tree t s hs lo hi j j'
            cases tree with
            | stop label => simp [AcquisitionTree.archive]
            | @step n B next =>
                have hstep : t+m≤h*m := by nlinarith
                by_cases safe : runAdmissible (k-1) (k-1-s) m B.val=true
                · have hs' := (literal_block_execution k hk m B.val w 0 s hs).2 safe
                  have inductionResult := ih n (next (some w)) (t+m) (tailAfter s B.val)
                    hs' (by omega) (by nlinarith) j j'
                  simp only [AcquisitionTree.archive,block t s hs lo hstep B j,
                    block t s hs lo hstep B j',if_pos safe,endpointReading,List.take_succ_cons]
                  refine ⟨congrArg (List.cons (B,some w)) inductionResult.1,?_⟩
                  intro entry he
                  rcases List.mem_cons.mp he with eq | mem
                  · subst entry; exact Or.inl rfl
                  · exact inductionResult.2 entry mem
                · simp only [AcquisitionTree.archive,block t s hs lo hstep B j,
                    block t s hs lo hstep B j',if_neg safe,endpointReading,List.take_succ_cons]
                  refine ⟨trivial,?_⟩
                  intro entry he
                  rcases List.mem_cons.mp he with eq | mem
                  · subst entry; exact Or.inr rfl
                  · exact Or.inr (treeNone n (next none) entry (List.mem_of_mem_take mem))
      obtain ⟨j₀,hj₀⟩ := hS
      have safeFirst : runAdmissible (k-1) (k-1) m first.val = true := by
        have hb := branch j₀ hj₀
        rw [(literal_block_execution k hk m first.val v (theta j₀) 0 (by omega)).1] at hb
        by_contra hnotsafe
        simp [Nat.sub_zero,hnotsafe,endpointReading] at hb
      have hs := (literal_block_execution k hk m first.val v (theta j₀) 0 (by omega)).2
        (by simpa using safeFirst)
      have firstEq (j : Fin u) (hj : j ∈ S) :
          runBits k first.val (q j) = some ⟨w,theta j+(m : ℕ),tailAfter 0 first.val⟩ := by
        have exec := (literal_block_execution k hk m first.val v (theta j) 0 (by omega)).1
        simp only [Nat.sub_zero,safeFirst,if_pos] at exec
        have hb := branch j hj
        change endpointReading (runBits k first.val (some ⟨v,theta j,0⟩))=some w at hb
        rw [exec] at hb
        have hv : v+wordIncrement k (theta j) first.val=w := Option.some.inj hb
        simpa only [q,hv] using exec
      refine ⟨tailAfter 0 first.val,hs,firstEq,?_,?_,?_⟩
      · intro actions hlen
        obtain ⟨tail,relation,bound⟩ := literal actions m (tailAfter 0 first.val) hs le_rfl
          (budget actions.length hlen)
        refine ⟨tail,?_,bound⟩
        intro j hj
        rw [firstEq j hj,relation j]
        congr 1
        funext r
        congr 1
        congr 1
        ring
      · intro d hd tree j hj j' hj'
        change d ≤ h-1 at hd
        rw [firstEq j hj,firstEq j' hj']
        exact adaptive d tree m (tailAfter 0 first.val) hs le_rfl (budget d hd) j j'
      · intro r hr n tree j hj j' hj'
        change r ≤ h-1 at hr
        rw [firstEq j hj,firstEq j' hj']
        exact prefixRelation r n tree m (tailAfter 0 first.val) hs le_rfl (budget r hr) j j'
    intro Y k m hk hm hshort f v localAlphabet
    dsimp only
    let g := Nat.gcd m (k+1)
    let u := m/g
    let p := (k+1)/g
    let h := p/u
    let theta (j : Fin u) : ZMod (k+1) := -((j.val*g : ℕ) : ZMod (k+1))
    let q (j : Fin u) : Option (LiveRecord k) := some ⟨v,theta j,0⟩
    let labels (j : Fin u) := f (q j)
    let all : Finset (Fin u) := Finset.univ
    have rangeEq : Set.range labels = (↑(all.image labels) : Set Y) := by
      ext y
      simp [all]
    have nEq : Nat.card (Set.range labels) = (all.image labels).card := by
      rw [rangeEq]
      exact Nat.card_eq_finsetCard _
    change 3 ≤ Nat.card (Set.range labels) → _
    intro hn d tree correct
    change h + Nat.clog 2 (Nat.card (Set.range labels)) - 1 ≤ d
    have hn' : 3 ≤ (all.image labels).card := by simpa only [nEq] using hn
    have hcard : (all.image labels).card ≤ u := by
      exact Finset.card_image_le.trans_eq (by simp [all])
    have hu : 3 ≤ u := hn'.trans hcard
    have binary (a : ZMod 2) : a=0 ∨ a=1 := by
      have ha := ZMod.val_lt a
      have hv : a.val=0 ∨ a.val=1 := by omega
      rcases hv with hv | hv
      · left; exact (ZMod.val_injective 2) (by simpa using hv)
      · right; exact (ZMod.val_injective 2) (by change a.val=1; exact hv)
    have constantBound (S : Finset (Fin u)) (L : Fin u → Y) (y : Y)
        (he : ∀ j ∈ S, L j=y) : (S.image L).card ≤ 1 := by
      have sub : S.image L ⊆ {y} := by
        intro z hz
        obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
        simpa using he j hj
      simpa using Finset.card_le_card sub
    have imageCount : ∀ (d : ℕ) (tree : AcquisitionTree k m localAlphabet Y d)
        (S : Finset (Fin u)) (a : Fin u → ZMod 2) (phase : Fin u → ZMod (k+1))
        (s : ℕ), s<k →
        (S.image (fun j => tree.result (some ⟨a j,phase j,s⟩))).card ≤ 2^d := by
      intro d tree
      induction tree with
      | @stop d y =>
          intro S a phase s hs
          exact (constantBound S _ y (by intros; rfl)).trans (Nat.one_le_two_pow)
      | @step d B next ih =>
          intro S a phase s hs
          let a' := fun j => a j+wordIncrement k (phase j) B.val
          let phase' := fun j => phase j+(m : ℕ)
          let s' := tailAfter s B.val
          have exec (j : Fin u) := (literal_block_execution k hk m B.val (a j) (phase j) s hs).1
          by_cases safe : runAdmissible (k-1) (k-1-s) m B.val=true
          · have hs' : s'<k := (literal_block_execution k hk m B.val 0 0 s hs).2 safe
            let S0 := S.filter (fun j => a' j=0)
            let S1 := S.filter (fun j => a' j=1)
            have sub : S.image (fun j => (AcquisitionTree.step B next).result (some ⟨a j,phase j,s⟩)) ⊆
                (S0.image (fun j => (next (some 0)).result (some ⟨a' j,phase' j,s'⟩))) ∪
                (S1.image (fun j => (next (some 1)).result (some ⟨a' j,phase' j,s'⟩))) := by
              intro y hy
              obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hy
              rcases binary (a' j) with hv | hv
              · apply Finset.mem_union_left
                apply Finset.mem_image.mpr
                refine ⟨j,by simp [S0,hj,hv],?_⟩
                simp only [AcquisitionTree.result,exec j,if_pos safe,endpointReading]
                change (next (some 0)).result (some ⟨a' j,phase' j,s'⟩) =
                  (next (some (a' j))).result (some ⟨a' j,phase' j,s'⟩)
                rw [hv]
              · apply Finset.mem_union_right
                apply Finset.mem_image.mpr
                refine ⟨j,by simp [S1,hj,hv],?_⟩
                simp only [AcquisitionTree.result,exec j,if_pos safe,endpointReading]
                change (next (some 1)).result (some ⟨a' j,phase' j,s'⟩) =
                  (next (some (a' j))).result (some ⟨a' j,phase' j,s'⟩)
                rw [hv]
            have h0 := ih (some 0) S0 a' phase' s' hs'
            have h1 := ih (some 1) S1 a' phase' s' hs'
            have hc := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
            rw [Nat.pow_succ]
            omega
          · have hc := constantBound S
              (fun j => (AcquisitionTree.step B next).result (some ⟨a j,phase j,s⟩))
              ((next none).result none) (by
                intro j hj
                simp [AcquisitionTree.result,exec j,safe,endpointReading])
            exact hc.trans Nat.one_le_two_pow
    have delayed : ∀ (r d : ℕ) (tree : AcquisitionTree k m localAlphabet Y d)
        (S : Finset (Fin u)) (a : Fin u → ZMod 2) (phase : Fin u → ZMod (k+1))
        (s : ℕ), s<k → S.Nonempty → 2 ≤ (S.image labels).card →
        (∀ j ∈ S, tree.result (some ⟨a j,phase j,s⟩)=labels j) →
        (∀ j ∈ S, ∀ j' ∈ S,
          (tree.archive (some ⟨a j,phase j,s⟩)).take r =
          (tree.archive (some ⟨a j',phase j',s⟩)).take r) →
        r ≤ d ∧ (S.image labels).card ≤ 2^(d-r) := by
      intro r
      induction r with
      | zero =>
          intro d tree S a phase s hs hS hlabels hc hp
          refine ⟨by omega,?_⟩
          have eq : S.image labels = S.image (fun j => tree.result (some ⟨a j,phase j,s⟩)) := by
            apply Finset.image_congr
            intro j hj
            exact (hc j hj).symm
          rw [eq,Nat.sub_zero]
          exact imageCount d tree S a phase s hs
      | succ r ih =>
          intro d tree S a phase s hs hS hlabels hc hp
          cases tree with
          | stop y =>
              have small := constantBound S labels y (by intro j hj; exact (hc j hj).symm)
              omega
          | @step d B next =>
              let a' := fun j => a j+wordIncrement k (phase j) B.val
              let phase' := fun j => phase j+(m : ℕ)
              let s' := tailAfter s B.val
              have exec (j : Fin u) := (literal_block_execution k hk m B.val (a j) (phase j) s hs).1
              by_cases safe : runAdmissible (k-1) (k-1-s) m B.val=true
              · have hs' : s'<k := (literal_block_execution k hk m B.val 0 0 s hs).2 safe
                obtain ⟨j₀,hj₀⟩ := hS
                let w := a' j₀
                have hw (j : Fin u) (hj : j ∈ S) : a' j=w := by
                  have eq := hp j hj j₀ hj₀
                  simp only [AcquisitionTree.archive,exec j,exec j₀,if_pos safe,
                    endpointReading,List.take_succ_cons,List.cons.injEq] at eq
                  exact Option.some.inj (congrArg Prod.snd eq.1)
                have hc' : ∀ j ∈ S, (next (some w)).result (some ⟨a' j,phase' j,s'⟩)=labels j := by
                  intro j hj
                  have fact := hc j hj
                  simp only [AcquisitionTree.result,exec j,if_pos safe,endpointReading] at fact
                  change (next (some (a' j))).result (some ⟨a' j,phase' j,s'⟩)=labels j at fact
                  simpa only [hw j hj] using fact
                have hp' : ∀ j ∈ S, ∀ j' ∈ S,
                    ((next (some w)).archive (some ⟨a' j,phase' j,s'⟩)).take r =
                    ((next (some w)).archive (some ⟨a' j',phase' j',s'⟩)).take r := by
                  intro j hj j' hj'
                  have fact := hp j hj j' hj'
                  simp only [AcquisitionTree.archive,exec j,exec j',if_pos safe,
                    endpointReading,List.take_succ_cons,List.cons.injEq] at fact
                  change ((_,some (a' j))=(_,some (a' j'))) ∧
                    ((next (some (a' j))).archive (some ⟨a' j,phase' j,s'⟩)).take r =
                    ((next (some (a' j'))).archive (some ⟨a' j',phase' j',s'⟩)).take r at fact
                  simpa only [hw j hj,hw j' hj'] using fact.2
                have recBound := ih d (next (some w)) S a' phase' s' hs' ⟨j₀,hj₀⟩ hlabels hc' hp'
                exact ⟨by omega,by simpa only [Nat.add_sub_add_right] using recBound.2⟩
              · have small := constantBound S labels ((next none).result none) (by
                  intro j hj
                  have fact := hc j hj
                  simpa [AcquisitionTree.result,exec j,safe,endpointReading] using fact.symm)
                omega
    cases tree with
    | stop y =>
        have small := constantBound all labels y (by intro j hj; exact (correct j).symm)
        omega
    | @step d first next =>
        have exec (j : Fin u) := (literal_block_execution k hk m first.val v (theta j) 0 (by omega)).1
        have safe : runAdmissible (k-1) (k-1) m first.val=true := by
          by_contra notSafe
          have small := constantBound all labels ((next none).result none) (by
            intro j hj
            have fact := correct j
            change (AcquisitionTree.step first next).result (some ⟨v,theta j,0⟩)=labels j at fact
            simpa [AcquisitionTree.result,exec j,Nat.sub_zero,notSafe,endpointReading] using fact.symm)
          omega
        let reply (j : Fin u) := v+wordIncrement k (theta j) first.val
        let S0 := all.filter (fun j => reply j=0)
        let S1 := all.filter (fun j => reply j=1)
        have sub : all.image labels ⊆ S0.image labels ∪ S1.image labels := by
          intro y hy
          obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hy
          rcases binary (reply j) with hjv | hjv
          · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,by simp [S0,hj,hjv],rfl⟩)
          · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,by simp [S1,hj,hjv],rfl⟩)
        have total := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
        have large : ∃ (w : ZMod 2) (S : Finset (Fin u)),
            S.Nonempty ∧ (all.image labels).card ≤ 2*(S.image labels).card ∧
            2 ≤ (S.image labels).card ∧ (∀ j ∈ S, reply j=w) := by
          by_cases h01 : (S0.image labels).card ≤ (S1.image labels).card
          · have sz : 2 ≤ (S1.image labels).card := by omega
            have ne : S1.Nonempty := by
              by_contra he
              have empty : S1=∅ := Finset.not_nonempty_iff_eq_empty.mp he
              simp [empty] at sz
            exact ⟨1,S1,ne,by omega,sz,by intro j hj; exact (Finset.mem_filter.mp hj).2⟩
          · have sz : 2 ≤ (S0.image labels).card := by omega
            have ne : S0.Nonempty := by
              by_contra he
              have empty : S0=∅ := Finset.not_nonempty_iff_eq_empty.mp he
              simp [empty] at sz
            exact ⟨0,S0,ne,by omega,sz,by intro j hj; exact (Finset.mem_filter.mp hj).2⟩
        obtain ⟨w,S,hS,hlarge,htwo,hreply⟩ := large
        have branch (j : Fin u) (hj : j ∈ S) : endpointReading (runBits k first.val (q j))=some w := by
          change endpointReading (runBits k first.val (some ⟨v,theta j,0⟩))=some w
          rw [exec j]
          simpa only [Nat.sub_zero,safe,if_pos,endpointReading] using congrArg some (hreply j hj)
        obtain ⟨s,hs,firstEq,history,adaptive,transportPrefix⟩ :=
          transport k m hk hm hshort f v w localAlphabet hn first (↑S) hS branch
        have hc : ∀ j ∈ S, (next (some w)).result (some ⟨w,theta j+(m : ℕ),s⟩)=labels j := by
          intro j hj
          have fact := correct j
          change (next (endpointReading (runBits k first.val (q j)))).result (runBits k first.val (q j))=labels j at fact
          rwa [branch j hj,firstEq j hj] at fact
        have hp : ∀ j ∈ S, ∀ j' ∈ S,
            ((next (some w)).archive (some ⟨w,theta j+(m : ℕ),s⟩)).take (h-1) =
            ((next (some w)).archive (some ⟨w,theta j'+(m : ℕ),s⟩)).take (h-1) := by
          intro j hj j' hj'
          have fact := (transportPrefix (h-1) le_rfl d (next (some w)) j hj j' hj').1
          simpa only [firstEq j hj,firstEq j' hj'] using fact
        have bound := delayed (h-1) d (next (some w)) S (fun _ => w)
          (fun j => theta j+(m : ℕ)) s hs hS htwo hc hp
        have n' : Nat.clog 2 ((S.image labels).card) ≤ d-(h-1) :=
          (Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr bound.2
        have half : ((all.image labels).card+1)/2 ≤ (S.image labels).card := by omega
        have idLog := Nat.clog_of_one_lt (by decide : 1<2) (by omega : 1<(all.image labels).card)
        have logMono := Nat.clog_mono_right 2 half
        have hh : 1 ≤ h := by
          have hg : 0<g := Nat.gcd_pos_of_pos_left (k+1) (by omega)
          have hmu : g*u=m := Nat.mul_div_cancel' (Nat.gcd_dvd_left m (k+1))
          have hTp : g*p=k+1 := Nat.mul_div_cancel' (Nat.gcd_dvd_right m (k+1))
          have he : h=(k+1)/m := by
            dsimp only [h]
            rw [← Nat.mul_div_mul_left p u hg,hTp,hmu]
          rw [he]
          exact Nat.div_pos (by omega) (by omega)
        rw [nEq]
        have simplify : (all.image labels).card+2-1=(all.image labels).card+1 := by omega
        rw [simplify] at idLog
        omega
  let SelectorTree {Y : Type z} {k m : ℕ} {localAlphabet : Bool}
      (fallback : Y) (π : NarrowWindowCost.Selector m Y)
      (legal : ∀ y₀ archive B, π y₀ archive = .inr B →
        localAlphabet=true → DBonacciAdmissible k m B)
      (d : ℕ) (y₀ : Option (ZMod 2)) (archive : NarrowWindowCost.Archive m) :
      AcquisitionTree k m localAlphabet Y d :=
    Nat.rec (motive := fun n => NarrowWindowCost.Archive m →
      AcquisitionTree k m localAlphabet Y n)
      (fun archive => .stop (match π y₀ archive with
        | .inl y => y
        | .inr _ => fallback))
      (fun _ next archive => match selected : π y₀ archive with
        | .inl y => .stop y
        | .inr B => .step ⟨B,legal y₀ archive B selected⟩
          (fun reply => next (archive++[(B,reply)]))) d archive
  have selectorTreeSuccess :
    ∀ {Y : Type z} (k m : ℕ) (localAlphabet : Bool) (fallback : Y)
      (π : D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.Selector m Y)
      (legal : ∀ y₀ archive B, π y₀ archive=.inr B →
        localAlphabet=true → DBonacciAdmissible k m B)
      (d : ℕ) (q : Option (LiveRecord k)) (y₀ : Option (ZMod 2))
      (archive : D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.Archive m) (y : Y) (c : ℕ),
      NativeExecute π d q y₀ archive=some (y,c) →
        (SelectorTree fallback π legal d y₀ archive).result q=y ∧
        ((SelectorTree fallback π legal d y₀ archive).archive q).length=c := by
    classical
    intro Y k m localAlphabet fallback π legal d
    induction d with
    | zero =>
        intro q y₀ archive y c success
        cases eq : π y₀ archive with
        | inl label =>
            simp only [NativeExecute,Nat.rec_zero,Nat.rec_add_one,eq,Option.some.injEq,Prod.mk.injEq] at success
            simp [SelectorTree,Nat.rec_zero,Nat.rec_add_one,eq,AcquisitionTree.result,AcquisitionTree.archive,success.1,success.2]
        | inr B => simp [NativeExecute,Nat.rec_zero,Nat.rec_add_one,eq] at success
    | succ d ih =>
        intro q y₀ archive y c success
        cases eq : π y₀ archive with
        | inl label =>
            simp only [NativeExecute,Nat.rec_zero,Nat.rec_add_one,eq,Option.some.injEq,Prod.mk.injEq] at success
            simp only [SelectorTree,Nat.rec_zero,Nat.rec_add_one]
            split
            · rename_i label' chosen
              have same : label'=label := Sum.inl.inj (chosen.symm.trans eq)
              subst label'
              simpa only [AcquisitionTree.result,AcquisitionTree.archive,List.length_nil] using success
            · rename_i B chosen
              have impossible := chosen.symm.trans eq
              cases impossible
        | inr B =>
            simp only [NativeExecute,Nat.rec_zero,Nat.rec_add_one,eq] at success
            obtain ⟨r,hr,he⟩ := Option.map_eq_some_iff.mp success
            have nextProof := ih (runBits k B q) y₀ (archive++[(B,endpointReading (runBits k B q))]) r.1 r.2 hr
            have he' : r.1=y ∧ r.2+1=c := Prod.mk.inj he
            simp only [SelectorTree,Nat.rec_zero,Nat.rec_add_one]
            split
            · rename_i label chosen
              have impossible := chosen.symm.trans eq
              cases impossible
            · rename_i B' chosen
              have same : B'=B := Sum.inr.inj (chosen.symm.trans eq)
              subst B'
              simp only [AcquisitionTree.result,AcquisitionTree.archive,List.length_cons]
              exact ⟨nextProof.1.trans he'.1,by simpa only [SelectorTree] using congrArg (fun n => n+1) nextProof.2 |>.trans he'.2⟩
  intro Y k m hk hm hshort f v localAlphabet
  dsimp only
  let g := Nat.gcd m (k+1)
  let u := m/g
  let q : Fin u → Option (LiveRecord k) :=
    fun j => some ⟨v,-((j.val*g : ℕ) : ZMod (k+1)),0⟩
  intro hn
  have sources (j : Fin u) : SourceRecord k m (q j) := by
    have hg : 0 < g := Nat.gcd_pos_of_pos_left (k+1) (by omega)
    have hmu : g*u=m := Nat.mul_div_cancel' (Nat.gcd_dvd_left m (k+1))
    have hjg : j.val*g < k+1 := by
      have hj := Nat.mul_lt_mul_of_pos_right j.isLt hg
      have : j.val*g < m := by simpa [Nat.mul_comm,hmu] using hj
      omega
    have hval : (((j.val*g : ℕ) : ZMod (k+1))).val=j.val*g := by
      rw [ZMod.val_natCast,Nat.mod_eq_of_lt hjg]
    refine ⟨by change 0<k; omega,?_⟩
    change g ∣ (-((j.val*g : ℕ) : ZMod (k+1))).val
    rw [ZMod.neg_val]
    split_ifs
    · exact dvd_zero _
    · rw [hval]
      exact Nat.dvd_sub (Nat.gcd_dvd_right m (k+1)) (dvd_mul_left g j.val)
  apply le_iInf
  intro budget
  obtain ⟨π,legal,bottom,correct⟩ := budget.property
  let tree := SelectorTree (f none) π legal budget.val (some v) []
  have treeCorrect (j : Fin u) : tree.result (q j)=f (q j) := by
    have actual := (whole_first_zero_acquisition k m hk hm localAlphabet (fun _ => ())).1
    obtain ⟨history,realized⟩ := (actual (q j)).mp (sources j)
    let w := history.flatMap (fun action => List.ofFn action.val)
    have recordEq : OriginalRecord k (by omega) w = q j :=
      (record_history k m hk localAlphabet history).trans realized
    have observed : NarrowWindowCost.output k (by omega) w = some v := by
      rw [output_record]
      change endpointReading (OriginalRecord k (by omega) w) = some v
      rw [recordEq]
      rfl
    obtain ⟨c,hc,success⟩ := correct history observed
    rw [execute_same k m hk π budget.val w (some v) []] at success
    change NativeExecute π budget.val (OriginalRecord k (by omega) w) (some v) [] =
      some (f (OriginalRecord k (by omega) w), c) at success
    rw [recordEq] at success
    exact (selectorTreeSuccess k m localAlphabet (f none) π legal budget.val
      (q j) (some v) [] (f (q j)) c success).1
  exact_mod_cast nativeLower k m hk hm hshort f v localAlphabet hn budget.val tree treeCorrect

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalNarrowCost
