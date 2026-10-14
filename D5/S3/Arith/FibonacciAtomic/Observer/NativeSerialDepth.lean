/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Bounded chronological native serial reads force finite physical support and original depth. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective
import D5.S3.Arith.FibonacciAtomic.Observer.NativeHistoryCells
import D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialImage

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open NativeSerialMachine
open NativeDepthPatterns (original_prefix_locality History)
open ActualCutPartitionRecovery

/-- Agreement includes every original four-valued reply through the radius. -/
def OriginalAgree (h : Nat) (u v : Source) : Prop :=
  ∀ a : Address, a.length ≤ h → readout a u = readout a v

/-- This selector is proof-only. Its unreachable-word default does not implement
an effective consumer or assert termination of unreachable computations. -/
noncomputable def descriptor {C O : Type} (δ : C → Op C O) (c : C) (N : Nat)
    (w : List Reply) : Descriptor := by
  classical
  exact if h : ∃ (s : Trace) (b : C) (n : Nat) (a : Address),
      Replay δ c N w s (b,n,.inl a) then
    ((h.choose_spec.choose_spec).choose,
      (h.choose_spec.choose_spec).choose_spec.choose)
    else (0,[])

private theorem descriptor_eq {C O : Type} {δ : C → Op C O} {c b : C}
    {N n : Nat} {w : List Reply} {s : Trace} {a : Address}
    (p : Replay δ c N w s (b,n,.inl a)) : descriptor δ c N w = (n,a) := by
  classical
  have h : ∃ (s : Trace) (b : C) (n : Nat) (a : Address),
      Replay δ c N w s (b,n,.inl a) := ⟨s,b,n,a,p⟩
  rw [descriptor, dif_pos h]
  have hp := h.choose_spec.choose_spec.choose_spec.choose_spec
  have eq := (replay_deterministic hp p).2
  have e := congrArg (fun x : Boundary C O => (x.2.1,x.2.2)) eq
  simpa using e

theorem run_unique {C O : Type} {δ : C → Op C O}
    {c : C} {e : Nat} {r : Source} {t s : Trace} {o p : O}
    (h : Run δ c e r t o) (k : Run δ c e r s p) : t = s ∧ o = p := by
  induction h generalizing s p with
  | stop h =>
      cases k with
      | stop hq =>
          have he := Op.stop.inj (h.symm.trans hq)
          exact ⟨rfl,he⟩
      | localStep hq q =>
          cases h.symm.trans hq
      | update hq q =>
          cases h.symm.trans hq
      | read hq hz q =>
          cases h.symm.trans hq
  | localStep h run ih =>
      cases k with
      | stop hq =>
          cases h.symm.trans hq
      | localStep hq q =>
          have he := Op.localStep.inj (h.symm.trans hq)
          cases he
          obtain ⟨he,hp⟩ := ih q
          exact ⟨congrArg (List.cons _) he,hp⟩
      | update hq q =>
          cases h.symm.trans hq
      | read hq hz q =>
          cases h.symm.trans hq
  | update h run ih =>
      cases k with
      | stop hq =>
          cases h.symm.trans hq
      | localStep hq q =>
          cases h.symm.trans hq
      | update hq q =>
          have he := Op.applyRho.inj (h.symm.trans hq)
          cases he
          obtain ⟨he,hp⟩ := ih q
          exact ⟨congrArg (List.cons _) he,hp⟩
      | read hq hz q =>
          cases h.symm.trans hq
  | read h hy run ih =>
      cases k with
      | stop hq =>
          cases h.symm.trans hq
      | localStep hq q =>
          cases h.symm.trans hq
      | update hq q =>
          cases h.symm.trans hq
      | read hq hz q =>
          obtain ⟨ha,hk⟩ := Op.read.inj (h.symm.trans hq)
          cases ha
          cases hk
          have he := hy.symm.trans hz
          cases he
          obtain ⟨he,hp⟩ := ih q
          exact ⟨congrArg (List.cons _) he,hp⟩

theorem transfer {C O : Type} {δ : C → Op C O}
    {c : C} {e : Nat} {r : Source} {t : Trace} {o : O}
    (h : Run δ c e r t o) (u v : Source) (cert : r = substitution^[e] u)
    (truth : ∀ n a y, Event.read n a y ∈ t → readout a (substitution^[n] v) = y) :
    Run δ c e (substitution^[e] v) t o := by
  induction h with
  | stop h => exact Run.stop h
  | localStep h run ih =>
      exact Run.localStep h (ih cert (fun n a y hm => truth n a y (by simp [hm])))
  | @update c c' e r t o h run ih =>
      have cert' : substitution r = substitution^[e+1] u := by
        rw [cert,Function.iterate_succ_apply']
      have next := ih cert' (fun n a y hm => truth n a y (by simp [hm]))
      rw [Function.iterate_succ_apply'] at next
      exact Run.update h next
  | @read c e r a k y t o h hy run ih =>
      exact Run.read h (truth e a y (by simp))
        (ih cert (fun n a y hm => truth n a y (by simp [hm])))

/-- No source/control/address finiteness or uniform runtime is used. Finite
reply words index the actual descriptors, with epochs and repeated calls intact. -/
theorem bounded_read_support {C O : Type} (δ : C → Op C O) (c : C) (N K : Nat) :
    ∃ D : Finset Descriptor,
      ∀ (u : Source) (t : Trace) (o : O),
        Run δ c N (substitution^[N] u) t o → (answers t).length ≤ K →
        ∀ n a y, Event.read n a y ∈ t → (n,a) ∈ D := by
  classical
  let W := (List.finite_length_lt Reply K).toFinset
  refine ⟨W.image (descriptor δ c N), ?_⟩
  intro u t o run budget n a y hm
  obtain ⟨w,s,b,hw,p⟩ := (operational_replay run).2.1 n a y hm
  apply Finset.mem_image.mpr
  refine ⟨w, ?_, descriptor_eq p⟩
  simpa [W] using (show w.length < K by omega)

/-- Uniform chronological raw budget implies one finite original observation
radius and exact agreement of the entire native trace and terminal output. -/
theorem bounded_serial_original_depth {C O : Type} (δ : C → Op C O) (c : C)
    (N K : Nat) (U : Set Source) (F : Source → O)
    (correct : ∀ u ∈ U, ∃ t, Run δ c N (substitution^[N] u) t (F u) ∧
      (answers t).length ≤ K) :
    ∃ h : Nat, ∀ u ∈ U, ∀ v ∈ U, OriginalAgree h u v →
      F u = F v ∧ ∃ t, Run δ c N (substitution^[N] u) t (F u) ∧
        Run δ c N (substitution^[N] v) t (F v) := by
  classical
  obtain ⟨D,support⟩ := bounded_read_support δ c N K
  refine ⟨D.sup (fun d => d.2.length), ?_⟩
  intro u hu v hv agree
  obtain ⟨t,run,budget⟩ := correct u hu
  have trueU := (actual_register_execution δ run u rfl []).choose_spec.choose_spec.2.2.2
  have runV : Run δ c N (substitution^[N] v) t (F u) := by
    apply transfer run u v rfl
    intro n a y hm
    have ha : a.length ≤ D.sup (fun d => d.2.length) :=
      Finset.le_sup (f := fun d : Descriptor => d.2.length) (support u t (F u) run budget n a y hm)
    have eq := original_prefix_locality n a u v (fun s hs => agree s (hs.trans ha))
    exact eq.symm.trans (trueU n a y hm)
  obtain ⟨s,other,_⟩ := correct v hv
  have out := (run_unique runV other).2
  exact ⟨out,t,run,by simpa [← out] using runV⟩

/-- The exact serial clause (3) implies finite-original-depth clause (4) on the
whole actual old-row/history fiber. No ground-binding or unification premise. -/
theorem whole_row_serial_implies_depth {C : Type} (δ : C → Op C LiteralRow)
    (c : C) (P Q : CutSet) (hQ : CutPrefixFree Q) (old : LiteralRow) (H : History) (N K : Nat)
    (correct : ∀ u : NativeHistoryCells.ActualFiber P old H,
      ∃ t, Run δ c N (substitution^[N] u.val) t (canonicalRow Q u.val) ∧
        (answers t).length ≤ K) :
    ∃ h : Nat, ∀ u v : NativeHistoryCells.ActualFiber P old H,
      OriginalAgree h u.val v.val →
        canonicalRow Q u.val = canonicalRow Q v.val ∧
        ActualCutPartitionDecoder.literalRecord Q u.val =
          ActualCutPartitionDecoder.literalRecord Q v.val := by
  let U : Set Source := {u | canonicalRow P u = old ∧ NativeDepthPatterns.Consistent H u}
  obtain ⟨h,depth⟩ := bounded_serial_original_depth δ c N K U (canonicalRow Q)
    (fun u hu => correct ⟨u,hu⟩)
  refine ⟨h,fun u v same => ?_⟩
  have row := (depth u.val u.property v.val v.property same).1
  exact ⟨row,(ActualCutPartitionDecoder.canonicalRow_record_iff Q hQ u.val v.val).mp row⟩

/-- The encoded effective source-free class is included without changing its
actual register, events, epoch, terminal whole row or raw budget. -/
theorem effective_whole_row_implies_depth
    (S : NativeSerialEffective.EffectiveService LiteralRow)
    (P Q : CutSet) (hQ : CutPrefixFree Q) (old : LiteralRow) (H : History) (N K : Nat)
    (correct : ∀ u : NativeHistoryCells.ActualFiber P old H,
      ∃ t, NativeSerialEffective.ServiceRun S S.initial N (substitution^[N] u.val) t
        (canonicalRow Q u.val) ∧ (answers t).length ≤ K) :
    ∃ h : Nat, ∀ u v : NativeHistoryCells.ActualFiber P old H,
      OriginalAgree h u.val v.val →
        canonicalRow Q u.val = canonicalRow Q v.val ∧
        ActualCutPartitionDecoder.literalRecord Q u.val =
          ActualCutPartitionDecoder.literalRecord Q v.val := by
  apply whole_row_serial_implies_depth (NativeSerialEffective.compile S) S.initial P Q hQ old H N K
  intro u
  obtain ⟨t,run,budget⟩ := correct u
  exact ⟨t,NativeSerialEffective.effective_service_inclusion S run,budget⟩


/-- A whole row is encoded in preorder: a concrete/labelled hole leaf is `some`,
and a binary constructor is `none`.  No size or address bound is imposed. -/
abbrev RowWord := List (Option (Bool ⊕ Nat))

def rowWord : LiteralRow → RowWord
  | .of b => [some b]
  | .mul l r => none :: (rowWord l ++ rowWord r)

private theorem rowWord_prefix (u v : LiteralRow) (x y : RowWord)
    (h : rowWord u ++ x = rowWord v ++ y) : u = v ∧ x = y := by
  induction u generalizing v x y with
  | of b =>
      cases v with
      | of c =>
          have he : b = c ∧ x = y := by simpa [rowWord] using h
          exact ⟨congrArg FreeMagma.of he.1, he.2⟩
      | mul l r => simp [rowWord] at h
  | mul l r ihl ihr =>
      cases v with
      | of c => simp [rowWord] at h
      | mul a b =>
          have he : rowWord l ++ (rowWord r ++ x) =
              rowWord a ++ (rowWord b ++ y) := by
            simpa [rowWord, List.append_assoc] using h
          obtain ⟨hl,ht⟩ := ihl a _ _ he
          obtain ⟨hr,ht⟩ := ihr b x y ht
          exact ⟨congrArg₂ FreeMagma.mul hl hr, ht⟩

private theorem rowWord_injective : Function.Injective rowWord := by
  intro u v h
  exact (rowWord_prefix u v [] [] (by simpa using h)).1

/-- Full original-service consequence.  The shared state is arbitrary finite
retained input at its actual certified epoch, and the quantifier is the entire
native old-row/history fiber.  Output is the explicit finite whole-row word. -/
theorem original_whole_row_implies_depth_and_image
    (S : NativeSerialEffective.OriginalEffectiveService RowWord)
    (s : NativeSerialEffective.OriginalState)
    (P Q : CutSet) (hQ : CutPrefixFree Q) (old : LiteralRow) (H : History)
    (N K : Nat) (epoch : s.epoch = N)
    (hne : Nonempty (NativeHistoryCells.ActualFiber P old H))
    (correct : ∀ u : NativeHistoryCells.ActualFiber P old H,
      ∃ t, NativeSerialEffective.OriginalRun S s (substitution^[N] u.val) t
        (rowWord (canonicalRow Q u.val)) ∧ (answers t).length ≤ K) :
    (∃ h : Nat, ∀ u v : NativeHistoryCells.ActualFiber P old H,
      OriginalAgree h u.val v.val →
        canonicalRow Q u.val = canonicalRow Q v.val ∧
        ActualCutPartitionDecoder.literalRecord Q u.val =
          ActualCutPartitionDecoder.literalRecord Q v.val) ∧
    (∃ labels : Finset LiteralRow, labels.card ≤ 4^K ∧
      ∀ u : NativeHistoryCells.ActualFiber P old H, canonicalRow Q u.val ∈ labels) := by
  classical
  let U : Set Source := {u | canonicalRow P u = old ∧ NativeDepthPatterns.Consistent H u}
  let δ := NativeSerialEffective.originalNativeControl S
  let c := NativeSerialEffective.originalControl s 0
  have native : ∀ u ∈ U, ∃ t, Run δ c N (substitution^[N] u) t
      (rowWord (canonicalRow Q u)) ∧ (answers t).length ≤ K := by
    intro u hu
    obtain ⟨t,run,budget⟩ := correct ⟨u,hu⟩
    obtain ⟨nt,hn,_,hr,_⟩ := (NativeSerialEffective.original_service_simulation S run).2
    refine ⟨nt,?_,?_⟩
    · simpa only [epoch] using hn
    · simpa only [answers,hr] using budget
  constructor
  · obtain ⟨h,depth⟩ := bounded_serial_original_depth δ c N K U
      (fun u => rowWord (canonicalRow Q u)) native
    refine ⟨h, fun u v same => ?_⟩
    have row := rowWord_injective (depth u.val u.property v.val v.property same).1
    exact ⟨row,(ActualCutPartitionDecoder.canonicalRow_record_iff Q hQ u.val v.val).mp row⟩
  · obtain ⟨u⟩ := hne
    obtain ⟨words,bound,cover⟩ := NativeSerialImage.bounded_serial_output_image δ c N K U
      ⟨u.val,u.property⟩ (fun u => rowWord (canonicalRow Q u)) native
    let decode (w : RowWord) : LiteralRow :=
      if h : ∃ r, rowWord r = w then h.choose else old
    have inverse (r : LiteralRow) : decode (rowWord r) = r := by
      have h : ∃ r', rowWord r' = rowWord r := ⟨r,rfl⟩
      exact (dif_pos h).trans (rowWord_injective h.choose_spec)
    refine ⟨words.image decode, (Finset.card_image_le.trans bound), ?_⟩
    intro v
    exact Finset.mem_image.mpr ⟨_,cover v.val v.property,inverse _⟩

end D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth
