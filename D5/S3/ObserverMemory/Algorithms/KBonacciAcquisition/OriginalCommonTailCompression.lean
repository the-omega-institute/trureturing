/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalCommonTailCompression
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalCommonTailCompression
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Original selectors on a common-tail archive compress only their informative endpoints. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalNarrowCost
import D5.S3.Observer.Budget.WorstCaseDepthInformationLowerBound
set_option autoImplicit false
noncomputable section
universe z
namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalCommonTailCompression
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel OriginalNarrowCost NarrowWindowCost
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S3.Observer.Budget.WorstCaseDepthInformationLowerBound
open D5.S0.Tower.DBonacci.Names
open scoped BigOperators

/-- The number of potentially informative endpoints in this paid interval. -/
def count (h t b : ℕ) : ℕ := ∑ i ∈ Finset.range b, if h ∣ t+i then 1 else 0

/-- Every correct original selector on the same actual scalar and tail has a
binary protocol with one query per potentially informative paid endpoint.
The remembered free output and the acquired archive are independent parameters. -/
theorem compress {Y X : Type z} (k m : ℕ) (hkl : 2 ≤ k)
    (pi : Selector m Y) (free : Option (ZMod 2)) (target : X → Y)
    (theta : X → ZMod (k+1)) (h horizon : ℕ)
    (silent : ∀ t, t < horizon → ¬ h ∣ t → ∀ (x : X) (B : Fin m → Bool),
      wordIncrement k (theta x+((t*m : ℕ) : ZMod (k+1))) B=0) :
    ∀ (b t : ℕ), t+b ≤ horizon → ∀ (S : Set X) (ws : X → List Bool)
      (z : ZMod 2) (tail : ℕ), tail<k → ∀ archive : Archive m,
      (∀ x ∈ S, OriginalRecord k (by omega) (ws x)=
        some ⟨z,theta x+((t*m : ℕ) : ZMod (k+1)),tail⟩) →
      (∀ x ∈ S, ∃ c, execute k (by omega) pi b (ws x) free archive=
        some (target x,c)) → ∃ P : AdaptiveProtocol X 2 (count h t b),
        ∀ x ∈ S, ∀ y ∈ S,
          adaptiveTranscript P x=adaptiveTranscript P y → target x=target y := by
  classical
  have countStep (t b : ℕ) : count h t (b+1)=
      (if h ∣ t then 1 else 0)+count h (t+1) b := by
    dsimp only [count]
    rw [Finset.sum_range_succ']
    simp only [Nat.add_zero,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
  have observed (w : List Bool) : output k (by omega) w =
      endpointReading (OriginalRecord k (by omega) w) :=
    OriginalExecutionBridge.output_record k (by omega) w
  have appendRecord (w : List Bool) (B : Fin m → Bool) :
      OriginalRecord k (by omega) (w ++ List.ofFn B) =
      runBits k B (OriginalRecord k (by omega) w) :=
    OriginalExecutionBridge.record_append k hkl w (List.ofFn B)
  intro b; induction b with
  | zero =>
    intro t bound S ws z tail tailBound archive same success; refine ⟨.leaf,?_⟩; intro x hx y hy _; obtain ⟨cx,ex⟩ := success x hx
    obtain ⟨cy,ey⟩ := success y hy
    have equal : execute k (by omega) pi 0 (ws x) free archive= execute k (by omega) pi 0 (ws y) free archive := rfl
    rw [ex,ey] at equal; exact (Prod.mk.inj (Option.some.inj equal)).1
  | succ b ih =>
    intro t bound S ws z tail tailBound archive same success; cases selected : pi free archive with
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
        dsimp only [ws']; rw [appendRecord,same x hx,(literal_block_execution k hkl m B z _ tail tailBound).1]
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
            (valueEq : ∀ x ∈ S', z+wordIncrement k (theta x+((t*m : ℕ) : ZMod (k+1))) B=q) : ∃ P : AdaptiveProtocol X 2 (count h (t+1) b),
              ∀ x ∈ S', ∀ y ∈ S', adaptiveTranscript P x=adaptiveTranscript P y → target x=target y := by
          apply ih (t+1) (by omega) S' ws' q (tailAfter tail B) nextTail
            (archive++[(B,some q)])
          · intro x hx
            rw [nextRecordsSafe x (sub hx),valueEq x hx]
          · intro x hx
            obtain ⟨c,ex⟩ := success x (sub hx)
            have reply : output k (by omega) (ws' x)=some q := by rw [observed,nextRecordsSafe x (sub hx),valueEq x hx]; rfl
            simp only [execute,selected] at ex
            change (execute k (by omega) pi b (ws' x) free
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
          have branchAdvance (a : Fin 2) : ∃ P : AdaptiveProtocol X 2 (count h (t+1) b),
                ∀ x ∈ branch a, ∀ y ∈ branch a,
                  adaptiveTranscript P x=adaptiveTranscript P y → target x=target y := by
            apply advance (a.val : ZMod 2) (branch a) (fun _ hx => hx.1)
            intro x hx; have e := congrArg Fin.val hx.2; dsimp only [question] at e
            apply ZMod.val_injective 2
            rw [ZMod.val_natCast,Nat.mod_eq_of_lt a.isLt]; exact e
          let next (a : Fin 2) : AdaptiveProtocol X 2 (count h (t+1) b) := Classical.choose (branchAdvance a)
          have ncount : count h t (b+1)=count h (t+1) b+1 := by rw [countStep,if_pos active]; omega
          rw [ncount]
          refine ⟨.query question next,?_⟩
          intro x hx y hy eq; change question x::adaptiveTranscript (next (question x)) x= question y::adaptiveTranscript (next (question y)) y at eq
          have parts := List.cons.inj eq
          have ey : y ∈ branch (question x) := ⟨hy,parts.1.symm⟩
          apply Classical.choose_spec (branchAdvance (question x)) x ⟨hx,rfl⟩ y ey
          simpa only [parts.1] using parts.2
        · have zero (x : X) : wordIncrement k (theta x+((t*m : ℕ) : ZMod (k+1))) B=0 := silent t (by omega) active x B
          have ncount : count h t (b+1)=count h (t+1) b := by rw [countStep,if_neg active,zero_add]
          rw [ncount]; exact advance z S (fun _ hx => hx) (fun x _ => by rw [zero x,add_zero])
      · refine ⟨.leaf,?_⟩
        intro x hx y hy _; have rx : OriginalRecord k (by omega) (ws' x)=none := by rw [nextRecords x hx,if_neg safe]
        have ry : OriginalRecord k (by omega) (ws' y)=none := by rw [nextRecords y hy,if_neg safe]
        have ox : output k (by omega) (ws' x)=none := by rw [observed,rx]; rfl
        have oy : output k (by omega) (ws' y)=none := by rw [observed,ry]; rfl
        have eq : execute k (by omega) pi (b+1) (ws x) free archive= execute k (by omega) pi (b+1) (ws y) free archive := by
          simp only [execute,selected]
          change (execute k (by omega) pi b (ws' x) free
            (archive++[(B,output k (by omega) (ws' x))])).map _ = (execute k (by omega) pi b (ws' y) free
            (archive++[(B,output k (by omega) (ws' y))])).map _
          rw [ox,oy]
          rw [OriginalExecutionBridge.execute_same k m hkl,
            OriginalExecutionBridge.execute_same k m hkl]
          change (OriginalExecutionBridge.NativeExecute pi b
            (OriginalRecord k (by omega) (ws' x)) free _).map _ =
            (OriginalExecutionBridge.NativeExecute pi b
            (OriginalRecord k (by omega) (ws' y)) free _).map _
          rw [rx,ry]
        obtain ⟨cx,ex⟩ := success x hx
        obtain ⟨cy,ey⟩ := success y hy
        rw [ex,ey] at eq; exact (Prod.mk.inj (Option.some.inj eq)).1

#print axioms compress
end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalCommonTailCompression
