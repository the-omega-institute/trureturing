/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FullPositiveWindowPrice
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FullPositiveWindowPrice
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Actual full-positive children have attained additional adaptive and literal preset prices. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalCommonTailCompression
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe z
namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FullPositiveWindowPrice
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells OriginalNarrowCost OriginalExecutionBridge OriginalAcquiredTrace
open WindowChargeInverse WindowSeamCodes PhysicalWindowDecoder
open D5.S3.Observer.Budget.WorstCaseDepthInformationLowerBound
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S0.Tower.DBonacci.Names
open scoped BigOperators Classical

/-- An INITIAL record and current record of one original acquired source. -/
structure OperationalRequest (k m : ℕ) where
  initial : Option (LiveRecord k)
  current : Option (LiveRecord k)
  initialReading : Option (ZMod 2)
  archive : NarrowWindowCost.Archive m

/-- Exactly the whole original history fiber of this acquired child. -/
def ChildRequests (k m : ℕ) (hk : 0 < k) (alphabet : Bool)
    (free : Option (ZMod 2)) (archive : NarrowWindowCost.Archive m) :
    Set (OperationalRequest k m) :=
  {r | r.initialReading = free ∧ r.archive = archive ∧
    (r.initial, r.current) ∈ AcquiredPairs k m hk alphabet free archive}

/-- Every selected complete block belongs to the chosen original alphabet. -/
def SelectorLegal {Y : Type z} {m : ℕ} (k : ℕ) (alphabet : Bool)
    (π : NarrowWindowCost.Selector m Y) : Prop :=
  ∀ free archive B, π free archive = .inr B →
    alphabet = true → DBonacciAdmissible k m B

/-- The literal suffix uses its own paid count from the acquired offset. -/
def PresetPolicy {Y : Type z} {k m : ℕ} {alphabet : Bool}
    (stream : ℕ → AllowedBlock k m alphabet) (offset : ℕ)
    (π : NarrowWindowCost.Selector m Y) : Prop :=
  ∀ free archive B, π free archive = .inr B →
    B = (stream (archive.length - offset)).val

/-- All original requests have correct INITIAL labels within this additional
paid bound. Only independent remembered INITIAL bottom stops freely. -/
def RequestFeasible {Y : Type z} (k m : ℕ) (alphabet : Bool)
    (f : Option (LiveRecord k) → Y) (requests : Set (OperationalRequest k m))
    (restriction : NarrowWindowCost.Selector m Y → Prop) (d : ℕ) : Prop :=
  ∃ π : NarrowWindowCost.Selector m Y,
    SelectorLegal k alphabet π ∧ π none [] = .inl (f none) ∧ restriction π ∧
      ∀ request ∈ requests, ∃ issued,
        PaidTrace π request.initialReading request.current request.archive issued
          (f request.initial) ∧ issued.length ≤ d

/-- The infimum over natural budgets, with infinity for no feasible budget. -/
def BudgetPrice (feasible : ℕ → Prop) : ℕ∞ :=
  ⨅ d : {d : ℕ // feasible d}, (d.val : ℕ∞)

/-- Minimum additional adaptive fee on the whole actual child. -/
def ChildAdaptivePrice {Y : Type z} (k m : ℕ) (hk : 0 < k) (alphabet : Bool)
    (f : Option (LiveRecord k) → Y) (free : Option (ZMod 2))
    (archive : NarrowWindowCost.Archive m) : ℕ∞ :=
  BudgetPrice (RequestFeasible k m alphabet f
    (ChildRequests k m hk alphabet free archive) (fun _ => True))

/-- One suffix chosen for this child, with no unrelated sibling conditions. -/
def ChildPresetPrice {Y : Type z} (k m : ℕ) (hk : 0 < k) (alphabet : Bool)
    (f : Option (LiveRecord k) → Y) (free : Option (ZMod 2))
    (archive : NarrowWindowCost.Archive m) : ℕ∞ :=
  BudgetPrice (RequestFeasible k m alphabet f
    (ChildRequests k m hk alphabet free archive)
    (fun π => ∃ stream : ℕ → AllowedBlock k m alphabet,
      PresetPolicy stream archive.length π))

theorem price_exact (feasible : ℕ → Prop) (n : ℕ)
    (attains : feasible n) (least : ∀ d, feasible d → n ≤ d) :
    BudgetPrice feasible = (n : ℕ∞) := by
  rw [BudgetPrice, ENat.iInf_eq_natCast_iff]
  refine ⟨⟨⟨n, attains⟩, rfl⟩, fun d => ?_⟩
  exact_mod_cast least d.val d.property

/-- Every original adaptive competitor obeys the binary label bound on this
actual inherited common-tail child, irrespective of its literal actions. -/
theorem full_positive_lower {Y : Type z} (m : ℕ) (hm : 3 ≤ m) (odd : Odd m)
    (alphabet : Bool) (free previous : ZMod 2) (archive : NarrowWindowCost.Archive m)
    (parent : Fin m → Bool)
    (prior : archiveEndpoint (some free) archive = some previous)
    (full : initialSupport (m+1) m (by omega) alphabet free
      (archive ++ [(parent, some (previous+1))]) = physicalWindow (m+1) m archive.length)
    (f : Option (LiveRecord (m+1)) → Y) (initialLabels : ZMod (m+2) → Y)
    (wellDefined : ∀ initial current : LiveRecord (m+1),
      (some initial,some current) ∈ AcquiredPairs (m+1) m (by omega) alphabet (some free)
        (archive ++ [(parent,some (previous+1))]) →
      f (some initial) = initialLabels (-initial.phase))
    (h : ℕ) (feasible : RequestFeasible (m+1) m alphabet f
      (ChildRequests (m+1) m (by omega) alphabet (some free)
        (archive ++ [(parent,some (previous+1))])) (fun _ => True) h) :
    (labels (fun x : Fin (m+1) => initialLabels (vertex (m+1) m archive.length x.val))).card
      ≤ 2^h := by
  classical
  let table := fun x : Fin (m+1) => initialLabels (vertex (m+1) m archive.length x.val)
  let acquired := archive ++ [(parent,some (previous+1))]
  obtain ⟨π, legal, bottom, restriction, correct⟩ := feasible
  have facts := full_positive_history_trace (m+1) m hm odd rfl alphabet free previous
    archive parent prior full f initialLabels wellDefined
  have representatives (L : Label table) : ∃ (w : List Bool) (theta : ZMod (m+2)),
      OriginalRecord (m+1) (by omega) (w ++ archiveWords acquired) =
        some ⟨previous+1,theta,1⟩ ∧
      ∃ c, NarrowWindowCost.execute (m+1) (by omega) π h
        (w ++ archiveWords acquired) (some free) acquired = some (L.val,c) := by
    obtain ⟨x, _, labelEq⟩ := Finset.mem_image.mp L.property
    have supported : vertex (m+1) m archive.length x.val ∈
        initialSupport (m+1) m (by omega) alphabet free acquired := by
      rw [full]; exact ⟨x.val, by omega, rfl⟩
    obtain ⟨initial,current,member,pos⟩ := supported
    obtain ⟨i,q,ei,eq,label,support,value,tail,phase,rest⟩ :=
      facts.2 (some initial,current) member
    change some initial = some i at ei
    change current = some q at eq
    have liveMember : (some i,some q) ∈ AcquiredPairs (m+1) m (by omega)
        alphabet (some free) acquired := by simpa only [ei,eq] using member
    have sourceMember := liveMember
    obtain ⟨history,freeEq,matched,source,currentEq⟩ := sourceMember
    let w := history.flatMap (fun B => List.ofFn B.val)
    have qEq : q = ⟨previous+1,q.phase,1⟩ := by
      cases q; simp_all only [LiveRecord.mk.injEq, and_true, true_and]
    have currentRecord : OriginalRecord (m+1) (by omega) (w ++ archiveWords acquired) =
        some ⟨previous+1,q.phase,1⟩ := currentEq.symm.trans (congrArg some qEq)
    have immutable : f (some i) = L.val := by
      have initialSame : initial = i := Option.some.inj ei
      rw [wellDefined i q liveMember, ← initialSame, ← pos]
      exact labelEq
    let request : OperationalRequest (m+1) m := ⟨some i,some q,some free,acquired⟩
    obtain ⟨issued,traced,bounded⟩ := correct request ⟨rfl,rfl,liveMember⟩
    have native := (native_execute_paid_trace (m+1) m π h (some q)
      (some free) acquired (f (some i)) issued.length).mpr
      ⟨issued,traced,rfl,bounded⟩
    have original : NarrowWindowCost.execute (m+1) (by omega) π h
        (w ++ archiveWords acquired) (some free) acquired =
        some (L.val,issued.length) := by
      rw [OriginalExecutionBridge.execute_same (m+1) m (by omega)]
      change NativeExecute π h
        (OriginalRecord (m+1) (by omega) (w ++ archiveWords acquired)) _ _ = _
      rw [← currentEq, ← immutable]; exact native
    exact ⟨w,q.phase,currentRecord,issued.length,original⟩
  let ws : Label table → List Bool := fun L =>
    Classical.choose (representatives L) ++ archiveWords acquired
  let theta : Label table → ZMod (m+2) := fun L =>
    Classical.choose (Classical.choose_spec (representatives L))
  have record (L : Label table) : OriginalRecord (m+1) (by omega) (ws L) =
      some ⟨previous+1,theta L,1⟩ :=
    (Classical.choose_spec (Classical.choose_spec (representatives L))).1
  have success (L : Label table) : ∃ c, NarrowWindowCost.execute (m+1) (by omega)
      π h (ws L) (some free) acquired = some (L.val,c) :=
    (Classical.choose_spec (Classical.choose_spec (representatives L))).2
  obtain ⟨P,identifies⟩ := OriginalCommonTailCompression.compress (m+1) m (by omega)
    π (some free) (fun L : Label table => L.val) theta 1 h
    (fun t _ notDiv => False.elim (notDiv (one_dvd t))) h 0 (by omega)
    Set.univ ws (previous+1) 1 (by omega) acquired
    (fun L _ => by simpa using record L) (fun L _ => success L)
  have countEq : OriginalCommonTailCompression.count 1 0 h = h := by
    simp [OriginalCommonTailCompression.count]
  have injective : Function.Injective (adaptiveTranscript P) := by
    intro L M same
    apply Subtype.ext
    exact identifies L (Set.mem_univ L) M (Set.mem_univ M) same
  have bound := exact_identification_card_le_pow
    (id : (Label table → Fin 2) → Label table → Fin 2) (by decide)
    ⟨P, adaptiveProtocol_uses_identity_readout P, injective⟩
  simpa only [Fintype.card_coe, countEq] using bound

private theorem trace_terminal {Y : Type z} {k m : ℕ}
    (π : NarrowWindowCost.Selector m Y) (free : Option (ZMod 2))
    (issued : NarrowWindowCost.Archive m) (q : Option (LiveRecord k))
    (base : NarrowWindowCost.Archive m) (y : Y)
    (traced : PaidTrace π free q base issued y) : π free (base ++ issued) = .inl y := by
  induction issued generalizing q base with
  | nil => simpa only [List.append_nil,PaidTrace] using traced
  | cons entry rest ih =>
    obtain ⟨chosen,reply,next⟩ := traced
    simpa only [List.append_assoc, List.singleton_append] using ih _ _ next

theorem trace_congr {Y : Type z} {k m : ℕ}
    (π τ : NarrowWindowCost.Selector m Y) (free : Option (ZMod 2))
    (same : ∀ ar, π free ar = τ free ar)
    (issued : NarrowWindowCost.Archive m) (q : Option (LiveRecord k))
    (base : NarrowWindowCost.Archive m) (y : Y) :
    PaidTrace π free q base issued y ↔ PaidTrace τ free q base issued y := by
  induction issued generalizing q base with
  | nil => simp only [PaidTrace,same]
  | cons entry rest ih => simp only [PaidTrace, same, ih]

private theorem script_preset_feasible {Y : Type z} (m : ℕ) (hm : 1 ≤ m)
    (alphabet : Bool) (free : ZMod 2) (f : Option (LiveRecord (m+1)) → Y)
    (base : NarrowWindowCost.Archive m) (words : List (Fin m → Bool))
    (decode : NarrowWindowCost.Archive m → Y)
    (correct : ∀ initial current,
      (initial,current) ∈ AcquiredPairs (m+1) m (by omega) alphabet (some free) base →
      decode (scriptArchive words current) = f initial) :
    RequestFeasible (m+1) m alphabet f
      (ChildRequests (m+1) m (by omega) alphabet (some free) base)
      (fun π => ∃ stream : ℕ → AllowedBlock (m+1) m alphabet,
        PresetPolicy stream base.length π) words.length := by
  classical
  let τ := finalSelector base.length words decode
  let π : NarrowWindowCost.Selector m Y := fun reading ar =>
    if reading = none then .inl (f none) else τ reading ar
  let stream : ℕ → AllowedBlock (m+1) m alphabet := fun r =>
    ⟨words[r]?.getD (fun _ => false), fun _ => short_legal (m+1) m (by omega) (by omega) _⟩
  have policy : PresetPolicy stream base.length π := by
    intro reading ar B selected
    dsimp only [π] at selected
    split at selected
    · cases selected
    · change (match words[ar.length-base.length]? with
        | some word => Sum.inr word | none => Sum.inl (decode (ar.drop base.length))) =
        Sum.inr B at selected
      cases wordEq : words[ar.length-base.length]? with
      | none => simp only [wordEq] at selected; cases selected
      | some word =>
        simp only [wordEq] at selected
        have eq : word = B := Sum.inr.inj selected
        simp only [stream,wordEq,Option.getD_some,eq]
  refine ⟨π, ?_, by simp [π], ⟨stream,policy⟩, ?_⟩
  · intro reading ar B _ _; exact short_legal (m+1) m (by omega) (by omega) B
  · intro request member
    obtain ⟨reading,ar,member⟩ := member
    have sourceMember := member
    obtain ⟨history,freeEq,matched,source,currentEq⟩ := sourceMember
    let w := history.flatMap (fun B => List.ofFn B.val) ++ archiveWords base
    have current : OriginalRecord (m+1) (by omega) w = request.current := currentEq.symm
    have exactScript := original_final_script (m+1) m (by omega) words decode
      w (some free) base
    dsimp only at exactScript
    rw [current, correct request.initial request.current member] at exactScript
    refine ⟨scriptArchive words request.current, ?_, exactScript.2.2.1.le⟩
    rw [reading, ar]
    exact (trace_congr π τ (some free) (fun ar => by simp [π]) _ _ _ _).mpr exactScript.1

/-- The supplied physical decoder gives one actual attaining child suffix,
including its exceptional two-row seam and the m=3 boundary. -/
theorem full_positive_many_attains {Y : Type z} (m : ℕ) (hm : 3 ≤ m) (odd : Odd m)
    (alphabet : Bool) (free previous : ZMod 2) (archive : NarrowWindowCost.Archive m)
    (parent : Fin m → Bool)
    (prior : archiveEndpoint (some free) archive = some previous)
    (full : initialSupport (m+1) m (by omega) alphabet free
      (archive ++ [(parent,some (previous+1))]) = physicalWindow (m+1) m archive.length)
    (f : Option (LiveRecord (m+1)) → Y) (initialLabels : ZMod (m+2) → Y)
    (wellDefined : ∀ initial current : LiveRecord (m+1),
      (some initial,some current) ∈ AcquiredPairs (m+1) m (by omega) alphabet (some free)
        (archive ++ [(parent,some (previous+1))]) →
      f (some initial) = initialLabels (-initial.phase))
    (many : 3 ≤ (labels (fun x : Fin (m+1) =>
      initialLabels (vertex (m+1) m archive.length x.val))).card) :
    RequestFeasible (m+1) m alphabet f
      (ChildRequests (m+1) m (by omega) alphabet (some free)
        (archive ++ [(parent,some (previous+1))]))
      (fun π => ∃ stream : ℕ → AllowedBlock (m+1) m alphabet,
        PresetPolicy stream (archive ++ [(parent,some (previous+1))]).length π)
      (Nat.clog 2 (labels (fun x : Fin (m+1) =>
        initialLabels (vertex (m+1) m archive.length x.val))).card) := by
  classical
  let table := fun x : Fin (m+1) => initialLabels (vertex (m+1) m archive.length x.val)
  let acquired := archive ++ [(parent,some (previous+1))]
  obtain ⟨c,π,inj,length,legal,correct⟩ := original_physical_initial_decoder
    m hm odd alphabet free previous archive parent prior full f initialLabels wellDefined many
  let decode : NarrowWindowCost.Archive m → Y := fun issued =>
    match π (some free) (acquired ++ issued) with
    | .inl label => label | .inr _ => f none
  rw [← length]
  apply script_preset_feasible m (by omega) alphabet free f acquired (actualWords table c) decode
  intro initial current member
  obtain ⟨history,freeEq,matched,source,currentEq⟩ := member
  have supplied := correct history freeEq matched
  dsimp only at supplied
  have terminal := trace_terminal π (some free) _ _ acquired _ supplied.2.2.2.2.1
  change current = _ at currentEq
  change initial = _ at source
  rw [currentEq, source]
  dsimp only [decode]
  rw [terminal]

/-- The exact binary obstruction in the child's translated coordinates. -/
def BinaryException {Y : Type z} {m : ℕ} (table : Fin (m+1) → Y) : Prop :=
  ∃ L M, L ≠ M ∧ ∀ x, table x = if x.val = m ∨ x.val = m-2 then L else M

private theorem next_coordinates (m : ℕ) (hm : 3 ≤ m) (x : Fin (m+1)) :
    ((x.val : ZMod (m+2)) - (m : ℕ)).val =
      if x.val = m then 0 else if x.val = m-1 then m+1 else x.val+2 := by
  by_cases last : x.val = m
  · simp [last]
  by_cases missed : x.val = m-1
  · have eq : ((m-1 : ℕ) : ZMod (m+2)) - (m : ℕ) = -1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ m)]; ring
    simp [missed,eq,ZMod.val_neg_one,show m-1 ≠ m by omega]
  · have small : x.val+2 < m+2 := by have := x.isLt; omega
    have eq : (x.val : ZMod (m+2)) - (m : ℕ) = ((x.val+2 : ℕ) : ZMod (m+2)) := by
      have modulus : ((m+2 : ℕ) : ZMod (m+2)) = 0 := ZMod.natCast_self _
      push_cast at modulus ⊢
      linear_combination -modulus
    rw [eq,ZMod.val_natCast,Nat.mod_eq_of_lt small,if_neg last,if_neg missed]

private theorem full_script_correct {Y : Type z} (m : ℕ) (hm : 3 ≤ m) (odd : Odd m)
    (alphabet : Bool) (free previous : ZMod 2) (archive : NarrowWindowCost.Archive m)
    (parent : Fin m → Bool)
    (prior : archiveEndpoint (some free) archive = some previous)
    (full : initialSupport (m+1) m (by omega) alphabet free
      (archive ++ [(parent,some (previous+1))]) = physicalWindow (m+1) m archive.length)
    (f : Option (LiveRecord (m+1)) → Y) (initialLabels : ZMod (m+2) → Y)
    (wellDefined : ∀ initial current : LiveRecord (m+1),
      (some initial,some current) ∈ AcquiredPairs (m+1) m (by omega) alphabet (some free)
        (archive ++ [(parent,some (previous+1))]) →
      f (some initial) = initialLabels (-initial.phase))
    (words : List (Fin m → Bool)) (decode : NarrowWindowCost.Archive m → Y)
    (correct : ∀ x : Fin (m+1),
      decode (scriptArchive words
        (some (⟨previous+1,-(x.val : ZMod (m+2))+(m : ℕ),1⟩ : LiveRecord (m+1)))) =
      initialLabels (vertex (m+1) m archive.length x.val)) :
    RequestFeasible (m+1) m alphabet f
      (ChildRequests (m+1) m (by omega) alphabet (some free)
        (archive ++ [(parent,some (previous+1))]))
      (fun π => ∃ stream : ℕ → AllowedBlock (m+1) m alphabet,
        PresetPolicy stream (archive ++ [(parent,some (previous+1))]).length π) words.length := by
  apply script_preset_feasible m (by omega) alphabet free f _ words decode
  intro initial current member
  have facts := full_positive_history_trace (m+1) m hm odd rfl alphabet free previous
    archive parent prior full f initialLabels wellDefined
  obtain ⟨i,q,ei,eq,label,support,value,tail,phase,rest⟩ := facts.2 (initial,current) member
  change initial = some i at ei
  change current = some q at eq
  obtain ⟨h,bound,pos⟩ := support
  let x : Fin (m+1) := ⟨h,by omega⟩
  have currentPhase : q.phase = -(x.val : ZMod (m+2))+(m : ℕ) := by
    rw [phase]
    simp only [vertex,Nat.cast_add,Nat.cast_mul] at pos ⊢
    linear_combination -pos
  have native : current = some (⟨previous+1,-(x.val : ZMod (m+2))+(m : ℕ),1⟩ : LiveRecord (m+1)) := by
    rw [eq]
    congr 1
    cases q
    simp_all only [LiveRecord.mk.injEq]
  rw [native,correct x,label,pos]

private theorem one_tail_safe (m : ℕ) (hm : 1 ≤ m) (word : Fin m → Bool) :
    runAdmissible m (m-1) m word = true ↔ word ≠ (fun _ => true) := by
  have scanner : runAdmissible m m (m+1) (Fin.cons true word) =
      runAdmissible m (m-1) m word := by
    obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    rfl
  have closed := (D5.S1.Words.ClosedRunStarts.closed_word_run_start_equivalence
    (m+1) (m+1) (by omega) le_rfl (Fin.cons true word)).1
  change (runAdmissible m m (m+1) (Fin.cons true word) = true ↔ _) at closed
  rw [scanner] at closed
  rw [closed]
  constructor
  · intro avoids same
    apply avoids 0
    refine ⟨by omega,?_⟩
    intro j _ _
    rw [same]
    exact Fin.cases rfl (fun _ => rfl) j
  · intro different s ⟨length,all⟩
    have zero : s = 0 := by omega
    apply different
    funext i
    exact all i.succ (by omega) (by omega)

private theorem all_one_increment (m : ℕ) (hm : 3 ≤ m) (j : ZMod (m+2)) :
    wordIncrement (m+1) (-j) (fun _ : Fin m => true) =
      if j.val = 0 ∨ j.val = m then 1 else 0 := by
  rw [increment_derivative (m+1) (by omega) m (by omega)]
  by_cases first : j.val = 0
  · simp [first,extendedBit,WindowChargeInverse.bitScalar,show 0 < m by omega]
  by_cases last : j.val = m
  · simp [last,extendedBit,WindowChargeInverse.bitScalar,show m ≠ 0 by omega,
      show m-1 < m by omega]
  by_cases inner : j.val < m
  · have prev : j.val-1 < m := by omega
    simp [first,last,inner,prev,extendedBit,WindowChargeInverse.bitScalar,
      CharTwo.add_self_eq_zero]
  · simp [first,last,inner,show ¬j.val-1 < m by omega,extendedBit]

private theorem binary_orientation {Y : Type z} {m : ℕ} (hm : 3 ≤ m)
    (table : Fin (m+1) → Y) (two : (labels table).card = 2) :
    ∃ L, L ≠ table ⟨m-1,by omega⟩ ∧
      ∀ x, table x = L ∨ table x = table ⟨m-1,by omega⟩ := by
  obtain ⟨a,b,ne,eq⟩ := Finset.card_eq_two.mp two
  have missed : table ⟨m-1,by omega⟩ ∈ labels table :=
    Finset.mem_image.mpr ⟨⟨m-1,by omega⟩,Finset.mem_univ _,rfl⟩
  rw [eq,Finset.mem_insert,Finset.mem_singleton] at missed
  have all (x : Fin (m+1)) : table x = a ∨ table x = b := by
    have member : table x ∈ labels table := Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
    simpa only [eq,Finset.mem_insert,Finset.mem_singleton] using member
  rcases missed with ha | hb
  · refine ⟨b,by rwa [ha,ne_comm],fun x => ?_⟩
    simpa only [ha,or_comm] using all x
  · refine ⟨a,by rwa [hb],fun x => ?_⟩
    simpa only [hb] using all x

private theorem binary_safe_row {Y : Type z} (m : ℕ) (hm : 3 ≤ m)
    (table : Fin (m+1) → Y) (two : (labels table).card = 2)
    (ordinary : ¬ BinaryException table) :
    ∃ (word : Fin m → Bool) (decode : ZMod 2 → Y),
      runAdmissible m (m-1) m word = true ∧
      ∀ x : Fin (m+1), decode
        (wordIncrement (m+1) (-(x.val : ZMod (m+2))+(m : ℕ)) word) = table x := by
  obtain ⟨L,ne,orientation⟩ := binary_orientation hm table two
  let M := table ⟨m-1,by omega⟩
  let r : Fin (m+1) → ZMod 2 := fun x => if table x = M then 0 else 1
  let raw : ℕ → ZMod 2 := fun i =>
    if i = 0 then r ⟨m,by omega⟩ else
    if hi : 2 ≤ i ∧ i ≤ m then r ⟨i-2,by omega⟩ else 0
  let q : ℕ → ZMod 2 := fun i => raw i +
    if i = 1 then ∑ h ∈ Finset.range (m+1), raw h else 0
  have even : ∑ h ∈ Finset.range (m+1),q h = 0 := by
    dsimp only [q]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq',Finset.mem_range,show 1 < m+1 by omega,if_true]
    exact CharTwo.add_self_eq_zero _
  let word := prefixWord m q
  have inverse := short_window_charge_inverse (m+1) (by omega) m (by omega) (by omega) q even
  have matchedRow (x : Fin (m+1)) :
      wordIncrement (m+1) (-(x.val : ZMod (m+2))+(m : ℕ)) word = r x := by
    have phase : -(x.val : ZMod (m+2))+(m : ℕ) = -((x.val : ZMod (m+2))-(m : ℕ)) := by ring
    rw [phase,inverse.1,windowCharge,next_coordinates m hm x]
    by_cases last : x.val = m
    · have index : x = ⟨m,by omega⟩ := Fin.ext last
      simp [last,q,raw,index]
    by_cases missed : x.val = m-1
    · have index : x = ⟨m-1,by omega⟩ := Fin.ext missed
      simp [last,missed,index,r,M,show m-1 ≠ m by omega]
    · have small : x.val+2 ≤ m := by have := x.isLt; omega
      simp [last,missed,q,raw,small,show 2 ≤ x.val+2 by omega,
        show x.val+2 ≠ 0 by omega,show x.val+2 ≠ 1 by omega]
  have notAll : word ≠ (fun _ => true) := by
    intro all
    apply ordinary
    refine ⟨L,M,ne,?_⟩
    intro x
    have charged := matchedRow x
    rw [all] at charged
    have phase : -(x.val : ZMod (m+2))+(m : ℕ) = -((x.val : ZMod (m+2))-(m : ℕ)) := by ring
    rw [phase,all_one_increment m hm,next_coordinates m hm x] at charged
    by_cases endpoint : x.val = m ∨ x.val = m-2
    · have row : r x = 1 := by
        rcases endpoint with last | early
        · simpa [last] using charged.symm
        · simp [early,show m-2 ≠ m by omega,show m-2 ≠ m-1 by omega,
            show m-2+2 = m by omega] at charged
          exact charged.symm
      have different : table x ≠ M := by intro same; simp [r,same] at row
      exact (if_pos endpoint).symm ▸ (orientation x).resolve_right different
    · have notLast : x.val ≠ m := fun eq => endpoint (Or.inl eq)
      have row : r x = 0 := by
        by_cases missed : x.val = m-1
        · have index : x = ⟨m-1,by omega⟩ := Fin.ext missed
          rw [index]; simp [r,M]
        · have notSecond : x.val+2 ≠ m := by omega
          simpa [notLast,missed,notSecond,show x.val+2 ≠ 0 by omega] using charged.symm
      have equal : table x = M := by
        by_contra neq; simp [r,neq] at row
      simpa only [if_neg endpoint] using equal
  refine ⟨word,fun b => if b = 0 then M else L,(one_tail_safe m (by omega) word).mpr notAll,?_⟩
  intro x
  rw [matchedRow]
  rcases orientation x with same | same
  · simp [r,M,same,ne]
  · simp [r,M,same]

private theorem binary_attains_one {Y : Type z} (m : ℕ) (hm : 3 ≤ m) (odd : Odd m)
    (alphabet : Bool) (free previous : ZMod 2) (archive : NarrowWindowCost.Archive m)
    (parent : Fin m → Bool)
    (prior : archiveEndpoint (some free) archive = some previous)
    (full : initialSupport (m+1) m (by omega) alphabet free
      (archive ++ [(parent,some (previous+1))]) = physicalWindow (m+1) m archive.length)
    (f : Option (LiveRecord (m+1)) → Y) (initialLabels : ZMod (m+2) → Y)
    (wellDefined : ∀ initial current : LiveRecord (m+1),
      (some initial,some current) ∈ AcquiredPairs (m+1) m (by omega) alphabet (some free)
        (archive ++ [(parent,some (previous+1))]) →
      f (some initial) = initialLabels (-initial.phase))
    (two : (labels (fun x : Fin (m+1) =>
      initialLabels (vertex (m+1) m archive.length x.val))).card = 2)
    (ordinary : ¬ BinaryException (fun x : Fin (m+1) =>
      initialLabels (vertex (m+1) m archive.length x.val))) :
    RequestFeasible (m+1) m alphabet f
      (ChildRequests (m+1) m (by omega) alphabet (some free)
        (archive ++ [(parent,some (previous+1))]))
      (fun π => ∃ stream : ℕ → AllowedBlock (m+1) m alphabet,
        PresetPolicy stream (archive ++ [(parent,some (previous+1))]).length π) 1 := by
  obtain ⟨word,decode,safe,separates⟩ := binary_safe_row m hm _ two ordinary
  let read : NarrowWindowCost.Archive m → Y := fun issued =>
    match archiveEndpoint (some (previous+1)) issued with
    | none => f none | some value => decode (value-(previous+1))
  change RequestFeasible _ _ _ _ _ _ ([word] : List (Fin m → Bool)).length
  apply full_script_correct m hm odd alphabet free previous archive parent prior full
    f initialLabels wellDefined [word] read
  intro x
  have model := (literal_block_execution (m+1) (by omega) m word (previous+1)
    (-(x.val : ZMod (m+2))+(m : ℕ)) 1 (by omega)).1
  have scanner : runAdmissible (m+1-1) (m+1-1-1) m word = true := by
    simpa only [Nat.add_sub_cancel] using safe
  rw [show scriptArchive [word] _ = [(word,endpointReading (runBits (m+1) word _))] by rfl]
  dsimp only [read,archiveEndpoint]
  rw [model,if_pos scanner]
  simp only [endpointReading,add_sub_cancel_left]
  exact separates x

private theorem pulse_two_increment (m : ℕ) (hm : 3 ≤ m) (j : ZMod (m+2)) :
    wordIncrement (m+1) (-j) (fun i : Fin m => decide (i.val < 2)) =
      if j = 0 ∨ j = 2 then 1 else 0 := by
  rw [increment_derivative (m+1) (by omega) m (by omega)]
  have zero : j = 0 ↔ j.val = 0 := by
    constructor
    · intro h; rw [h,ZMod.val_zero]
    · intro h; apply ZMod.val_injective (m+2); simpa using h
  have two : j = 2 ↔ j.val = 2 := by
    constructor
    · intro h; rw [h]; change ((2 : ℕ) : ZMod (m+2)).val = 2
      exact ZMod.val_natCast_of_lt (by omega : 2 < m+2)
    · intro h; apply ZMod.val_injective (m+2)
      change j.val = ((2 : ℕ) : ZMod (m+2)).val
      rw [ZMod.val_natCast_of_lt (by omega : 2 < m+2)]; exact h
  simp only [zero,two]
  by_cases first : j.val = 0
  · simp [first,extendedBit,WindowChargeInverse.bitScalar,show 0 < m by omega]
  by_cases second : j.val = 1
  · simp [second,extendedBit,WindowChargeInverse.bitScalar,show 1 < m by omega,
      show 0 < m by omega,CharTwo.add_self_eq_zero]
  by_cases third : j.val = 2
  · simp [third,extendedBit,WindowChargeInverse.bitScalar,show 2 < m by omega,show 1 < m by omega]
  have large : 3 ≤ j.val := by omega
  simp [first,third,extendedBit,WindowChargeInverse.bitScalar,
    show ¬j.val < 2 by omega,show ¬j.val-1 < 2 by omega]

private theorem pulse_two_child (m : ℕ) (hm : 3 ≤ m) (x : Fin (m+1)) :
    wordIncrement (m+1) (-(x.val : ZMod (m+2))+(m : ℕ)+(m : ℕ))
      (fun i : Fin m => decide (i.val < 2)) =
      if x.val = m ∨ x.val = m-2 then 1 else 0 := by
  have calendar : (m : ZMod (m+2))+(m : ℕ) = ((m-2 : ℕ) : ZMod (m+2)) := by
    have modulus : ((m+2 : ℕ) : ZMod (m+2)) = 0 := ZMod.natCast_self _
    rw [Nat.cast_sub (by omega : 2 ≤ m)]
    push_cast at modulus
    linear_combination modulus
  have phase : -(x.val : ZMod (m+2))+(m : ℕ)+(m : ℕ) =
      -((x.val : ZMod (m+2))-((m-2 : ℕ) : ZMod (m+2))) := by
    rw [← calendar]; ring
  rw [phase,pulse_two_increment m hm]
  have first : (x.val : ZMod (m+2))-((m-2 : ℕ) : ZMod (m+2)) = 0 ↔ x.val = m-2 := by
    rw [sub_eq_zero]
    constructor
    · intro h; have eq := congrArg ZMod.val h
      simpa [ZMod.val_natCast,Nat.mod_eq_of_lt (by omega : x.val < m+2),
        Nat.mod_eq_of_lt (by omega : m-2 < m+2)] using eq
    · intro h; rw [h]
  have second : (x.val : ZMod (m+2))-((m-2 : ℕ) : ZMod (m+2)) = 2 ↔ x.val = m := by
    rw [sub_eq_iff_eq_add]
    have endpoint : (2 : ZMod (m+2))+((m-2 : ℕ) : ZMod (m+2)) = (m : ℕ) := by
      rw [Nat.cast_sub (by omega : 2 ≤ m)]; ring
    rw [endpoint]
    constructor
    · intro h; have eq := congrArg ZMod.val h
      simpa [ZMod.val_natCast,Nat.mod_eq_of_lt (by omega : x.val < m+2),
        Nat.mod_eq_of_lt (by omega : m < m+2)] using eq
    · intro h; rw [h]
  simp only [first,second,or_comm]

private theorem binary_attains_two {Y : Type z} (m : ℕ) (hm : 3 ≤ m) (odd : Odd m)
    (alphabet : Bool) (free previous : ZMod 2) (archive : NarrowWindowCost.Archive m)
    (parent : Fin m → Bool)
    (prior : archiveEndpoint (some free) archive = some previous)
    (full : initialSupport (m+1) m (by omega) alphabet free
      (archive ++ [(parent,some (previous+1))]) = physicalWindow (m+1) m archive.length)
    (f : Option (LiveRecord (m+1)) → Y) (initialLabels : ZMod (m+2) → Y)
    (wellDefined : ∀ initial current : LiveRecord (m+1),
      (some initial,some current) ∈ AcquiredPairs (m+1) m (by omega) alphabet (some free)
        (archive ++ [(parent,some (previous+1))]) →
      f (some initial) = initialLabels (-initial.phase))
    (exception : BinaryException (fun x : Fin (m+1) =>
      initialLabels (vertex (m+1) m archive.length x.val))) :
    RequestFeasible (m+1) m alphabet f
      (ChildRequests (m+1) m (by omega) alphabet (some free)
        (archive ++ [(parent,some (previous+1))]))
      (fun π => ∃ stream : ℕ → AllowedBlock (m+1) m alphabet,
        PresetPolicy stream (archive ++ [(parent,some (previous+1))]).length π) 2 := by
  obtain ⟨L,M,ne,table⟩ := exception
  let zero : Fin m → Bool := fun _ => false
  let pulse : Fin m → Bool := fun i => decide (i.val < 2)
  let read : NarrowWindowCost.Archive m → Y := fun issued =>
    match archiveEndpoint (some (previous+1)) issued with
    | none => f none | some value => if value = previous+1 then M else L
  change RequestFeasible _ _ _ _ _ _ ([zero,pulse] : List (Fin m → Bool)).length
  apply full_script_correct m hm odd alphabet free previous archive parent prior full
    f initialLabels wellDefined [zero,pulse] read
  intro x
  have clearing := (short_safe_execution (m+1) (by omega) m (by omega) (by omega) zero
    (previous+1) (-(x.val : ZMod (m+2))+(m : ℕ)) 1 (by omega) (Or.inr rfl)).1
  have zeroTail : tailAfter 0 zero = 0 := by
    obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    exact last_false_tail r zero 0 rfl
  have zeroCharge : wordIncrement (m+1) (-(x.val : ZMod (m+2))+(m : ℕ)) zero = 0 := by
    simp [wordIncrement,zero]
  rw [zeroTail,zeroCharge,add_zero] at clearing
  have testing := (short_safe_execution (m+1) (by omega) m (by omega) (by omega) pulse
    (previous+1) (-(x.val : ZMod (m+2))+(m : ℕ)+(m : ℕ)) 0 (by omega) (Or.inl rfl)).1
  rw [pulse_two_child m hm] at testing
  simp only [scriptArchive,clearing,testing,endpointReading]
  dsimp only [read,archiveEndpoint]
  have labelEq := table x
  change initialLabels (vertex (m+1) m archive.length x.val) = _ at labelEq
  rw [labelEq]
  by_cases endpoint : x.val = m ∨ x.val = m-2
  · simp [endpoint,show previous+1+(1 : ZMod 2) ≠ previous+1 by
      intro eq; have bad : (1 : ZMod 2) = 0 := add_left_cancel
        (eq.trans (add_zero (previous+1)).symm); exact one_ne_zero bad]
  · simp [endpoint]

private theorem binary_exception_obstruction {Y : Type z} (m : ℕ) (hm : 3 ≤ m)
    (table : Fin (m+1) → Y) (exception : BinaryException table)
    (π : NarrowWindowCost.Selector m Y) (free z : ZMod 2)
    (base : NarrowWindowCost.Archive m)
    (correct : ∀ x : Fin (m+1), ∃ c, NativeExecute π 1
      (some (⟨z,-(x.val : ZMod (m+2))+(m : ℕ),1⟩ : LiveRecord (m+1)))
      (some free) base = some (table x,c)) : False := by
  obtain ⟨L,M,ne,label⟩ := exception
  let high : Fin (m+1) := ⟨m,by omega⟩
  let missed : Fin (m+1) := ⟨m-1,by omega⟩
  have highLabel : table high = L := by simp [label high,high]
  have lowLabel : table missed = M := by
    simp [label missed,missed,show m-1 ≠ m by omega,show m-1 ≠ m-2 by omega]
  have notSame : table high ≠ table missed := by rwa [highLabel,lowLabel]
  have step (q : Option (LiveRecord (m+1))) : NativeExecute π 1 q (some free) base =
      match π (some free) base with
      | .inl y => some (y,0)
      | .inr B => (NativeExecute π 0 (runBits (m+1) B q) (some free)
          (base ++ [(B,endpointReading (runBits (m+1) B q))])).map
          (fun out => (out.1,out.2+1)) := by rfl
  cases selected : π (some free) base with
  | inl y =>
    obtain ⟨c,hc⟩ := correct high
    obtain ⟨d,hd⟩ := correct missed
    have equal : table high = table missed := by
      rw [step,selected] at hc hd
      exact (Prod.mk.inj (Option.some.inj hc)).1.symm.trans
        (Prod.mk.inj (Option.some.inj hd)).1
    exact notSame equal
  | inr B =>
    let charge : Fin (m+1) → ZMod 2 := fun x =>
      wordIncrement (m+1) (-(x.val : ZMod (m+2))+(m : ℕ)) B
    have model (x : Fin (m+1)) := (literal_block_execution (m+1) (by omega) m B z
      (-(x.val : ZMod (m+2))+(m : ℕ)) 1 (by omega)).1
    have sameReply : ∀ x y : Fin (m+1),
        endpointReading (runBits (m+1) B
          (some ⟨z,-(x.val : ZMod (m+2))+(m : ℕ),1⟩)) =
        endpointReading (runBits (m+1) B
          (some ⟨z,-(y.val : ZMod (m+2))+(m : ℕ),1⟩)) → table x = table y := by
      intro x y reply
      obtain ⟨c,hc⟩ := correct x
      obtain ⟨d,hd⟩ := correct y
      have equal : NativeExecute π 1
          (some (⟨z,-(x.val : ZMod (m+2))+(m : ℕ),1⟩ : LiveRecord (m+1)))
          (some free) base = NativeExecute π 1
          (some (⟨z,-(y.val : ZMod (m+2))+(m : ℕ),1⟩ : LiveRecord (m+1)))
          (some free) base := by
        rw [step,step,selected]
        have zero (q : Option (LiveRecord (m+1))) (ar : NarrowWindowCost.Archive m) :
            NativeExecute π 0 q (some free) ar =
              match π (some free) ar with
              | .inl y => some (y,0) | .inr _ => none := by rfl
        simp only [zero,reply]
      rw [hc,hd] at equal
      exact (Prod.mk.inj (Option.some.inj equal)).1
    by_cases safe : runAdmissible m (m-1) m B = true
    · have separates (x y : Fin (m+1)) (same : charge x = charge y) : table x = table y := by
        apply sameReply x y
        rw [model x,model y]
        simp only [Nat.add_sub_cancel,safe,if_true,endpointReading]
        exact congrArg some (congrArg (fun q => z+q) same)
      have missedZero : charge missed = 0 := by
        dsimp only [charge]
        have phase : -(missed.val : ZMod (m+2))+(m : ℕ) =
            -((missed.val : ZMod (m+2))-(m : ℕ)) := by ring
        rw [phase,increment_derivative (m+1) (by omega) m (by omega),next_coordinates m hm missed]
        simp [missed,show m-1 ≠ m by omega,extendedBit,
          show ¬m+1 < m by omega]
      have binary (q : ZMod 2) : q = 0 ∨ q = 1 := by
        fin_cases q
        · exact Or.inl rfl
        · exact Or.inr rfl
      have highOne : charge high = 1 := (binary (charge high)).resolve_left (fun zero =>
        notSame (separates high missed (zero.trans missedZero.symm)))
      have charges (x : Fin (m+1)) : charge x =
          if x.val = m ∨ x.val = m-2 then 1 else 0 := by
        by_cases endpoint : x.val = m ∨ x.val = m-2
        · rw [if_pos endpoint]
          apply (binary (charge x)).resolve_left
          intro zero
          have equal := separates x missed (zero.trans missedZero.symm)
          rw [label x,if_pos endpoint,lowLabel] at equal
          exact ne equal
        · rw [if_neg endpoint]
          apply (binary (charge x)).resolve_right
          intro one
          have equal := separates high x (highOne.trans one.symm)
          rw [highLabel,label x,if_neg endpoint] at equal
          exact ne equal
      have derivative (x : Fin (m+1)) : charge x =
          extendedBit B ((x.val : ZMod (m+2))-(m : ℕ)).val +
          (if ((x.val : ZMod (m+2))-(m : ℕ)).val = 0 then 0 else
            extendedBit B (((x.val : ZMod (m+2))-(m : ℕ)).val-1)) := by
        dsimp only [charge]
        have phase : -(x.val : ZMod (m+2))+(m : ℕ) =
            -((x.val : ZMod (m+2))-(m : ℕ)) := by ring
        rw [phase,increment_derivative (m+1) (by omega) m (by omega)]
      have first : B ⟨0,by omega⟩ = true := by
        have eq := (derivative high).symm.trans (charges high)
        simp only [next_coordinates m hm high,high,Fin.val_mk,if_true,zero_add,
          extendedBit,dif_pos (by omega : 0 < m),WindowChargeInverse.bitScalar] at eq
        cases bit : B ⟨0,by omega⟩ <;> simp_all
      have last : B ⟨m-1,by omega⟩ = true := by
        let x : Fin (m+1) := ⟨m-2,by omega⟩
        have eq := (derivative x).symm.trans (charges x)
        simp only [next_coordinates m hm x,x,Fin.val_mk,
          show m-2 ≠ m by omega,show m-2 ≠ m-1 by omega,
          show m-2+2 = m by omega,if_false,if_true,show m ≠ 0 by omega,
          extendedBit,dif_neg (lt_irrefl m),dif_pos (by omega : m-1 < m),zero_add,
          WindowChargeInverse.bitScalar] at eq
        cases bit : B ⟨m-1,by omega⟩ <;> simp_all
      have suffix : ∀ d, d < m-1 → B ⟨m-1-d,by omega⟩ = true := by
        intro d
        induction d with
        | zero => intro _; simpa using last
        | succ d ih =>
          intro bound
          have previous := ih (by omega)
          let x : Fin (m+1) := ⟨m-3-d,by omega⟩
          have eq := (derivative x).symm.trans (charges x)
          have xv : x.val+2 = m-1-d := by dsimp [x]; omega
          have notLast : x.val ≠ m := by dsimp [x]; omega
          have notMissed : x.val ≠ m-1 := by dsimp [x]; omega
          have notOther : x.val ≠ m-2 := by dsimp [x]; omega
          have leftIndex : m-1-d-1 = m-1-(d+1) := by omega
          simp only [next_coordinates m hm x,notLast,notMissed,notOther,or_self,
            if_false,xv,show m-1-d ≠ 0 by omega,extendedBit,
            dif_pos (by omega : m-1-d < m),
            dif_pos (by omega : m-1-d-1 < m),previous,leftIndex,
            WindowChargeInverse.bitScalar,if_true] at eq
          cases bit : B ⟨m-1-(d+1),by omega⟩ <;> simp_all
      have all : B = (fun _ => true) := by
        funext i
        by_cases zero : i.val = 0
        · simpa only [show i = ⟨0,by omega⟩ from Fin.ext zero] using first
        · have dBound : m-1-i.val < m-1 := by have := i.isLt; omega
          have back : m-1-(m-1-i.val) = i.val := by have := i.isLt; omega
          simpa only [back] using suffix (m-1-i.val) dBound
      exact (one_tail_safe m (by omega) B).mp safe all
    · apply notSame
      apply sameReply high missed
      rw [model high,model missed]
      simp [safe]

private theorem full_native_correct {Y : Type z} (m : ℕ) (hm : 3 ≤ m) (odd : Odd m)
    (alphabet : Bool) (free previous : ZMod 2) (archive : NarrowWindowCost.Archive m)
    (parent : Fin m → Bool)
    (prior : archiveEndpoint (some free) archive = some previous)
    (full : initialSupport (m+1) m (by omega) alphabet free
      (archive ++ [(parent,some (previous+1))]) = physicalWindow (m+1) m archive.length)
    (f : Option (LiveRecord (m+1)) → Y) (initialLabels : ZMod (m+2) → Y)
    (wellDefined : ∀ initial current : LiveRecord (m+1),
      (some initial,some current) ∈ AcquiredPairs (m+1) m (by omega) alphabet (some free)
        (archive ++ [(parent,some (previous+1))]) →
      f (some initial) = initialLabels (-initial.phase))
    (π : NarrowWindowCost.Selector m Y) (h : ℕ)
    (correct : ∀ request ∈ ChildRequests (m+1) m (by omega) alphabet (some free)
        (archive ++ [(parent,some (previous+1))]), ∃ issued,
      PaidTrace π request.initialReading request.current request.archive issued
        (f request.initial) ∧ issued.length ≤ h) :
    ∀ x : Fin (m+1), ∃ c, NativeExecute π h
      (some (⟨previous+1,-(x.val : ZMod (m+2))+(m : ℕ),1⟩ : LiveRecord (m+1)))
      (some free) (archive ++ [(parent,some (previous+1))]) =
        some (initialLabels (vertex (m+1) m archive.length x.val),c) := by
  intro x
  let acquired := archive ++ [(parent,some (previous+1))]
  have supported : vertex (m+1) m archive.length x.val ∈
      initialSupport (m+1) m (by omega) alphabet free acquired := by
    rw [full]; exact ⟨x.val,by omega,rfl⟩
  obtain ⟨initial,current,member,pos⟩ := supported
  have facts := full_positive_history_trace (m+1) m hm odd rfl alphabet free previous
    archive parent prior full f initialLabels wellDefined
  obtain ⟨i,q,ei,eq,label,support,value,tail,phase,rest⟩ := facts.2 (some initial,current) member
  change some initial = some i at ei
  change current = some q at eq
  have member' : (some i,some q) ∈ AcquiredPairs (m+1) m (by omega)
      alphabet (some free) acquired := by simpa only [ei,eq] using member
  have position : -i.phase = vertex (m+1) m archive.length x.val := by
    rw [← Option.some.inj ei]; exact pos.symm
  have currentPhase : q.phase = -(x.val : ZMod (m+2))+(m : ℕ) := by
    rw [phase]
    simp only [vertex,Nat.cast_add,Nat.cast_mul] at position ⊢
    linear_combination -position
  have native : some q =
      some (⟨previous+1,-(x.val : ZMod (m+2))+(m : ℕ),1⟩ : LiveRecord (m+1)) := by
    congr 1
    cases q
    simp_all only [LiveRecord.mk.injEq]
  let request : OperationalRequest (m+1) m := ⟨some i,some q,some free,acquired⟩
  obtain ⟨issued,traced,bounded⟩ := correct request ⟨rfl,rfl,member'⟩
  have result := (native_execute_paid_trace (m+1) m π h (some q) (some free)
    acquired (f (some i)) issued.length).mpr ⟨issued,traced,rfl,bounded⟩
  rw [native,wellDefined i q member',position] at result
  exact ⟨issued.length,result⟩

private theorem full_exception_lower {Y : Type z} (m : ℕ) (hm : 3 ≤ m) (odd : Odd m)
    (alphabet : Bool) (free previous : ZMod 2) (archive : NarrowWindowCost.Archive m)
    (parent : Fin m → Bool)
    (prior : archiveEndpoint (some free) archive = some previous)
    (full : initialSupport (m+1) m (by omega) alphabet free
      (archive ++ [(parent,some (previous+1))]) = physicalWindow (m+1) m archive.length)
    (f : Option (LiveRecord (m+1)) → Y) (initialLabels : ZMod (m+2) → Y)
    (wellDefined : ∀ initial current : LiveRecord (m+1),
      (some initial,some current) ∈ AcquiredPairs (m+1) m (by omega) alphabet (some free)
        (archive ++ [(parent,some (previous+1))]) →
      f (some initial) = initialLabels (-initial.phase))
    (exception : BinaryException (fun x : Fin (m+1) =>
      initialLabels (vertex (m+1) m archive.length x.val)))
    (h : ℕ) (feasible : RequestFeasible (m+1) m alphabet f
      (ChildRequests (m+1) m (by omega) alphabet (some free)
        (archive ++ [(parent,some (previous+1))])) (fun _ => True) h) : 2 ≤ h := by
  by_contra small
  have bound : h ≤ 1 := by omega
  obtain ⟨π,legal,bottom,restriction,correct⟩ := feasible
  have extended : ∀ request ∈ ChildRequests (m+1) m (by omega) alphabet (some free)
        (archive ++ [(parent,some (previous+1))]), ∃ issued,
      PaidTrace π request.initialReading request.current request.archive issued
        (f request.initial) ∧ issued.length ≤ 1 := by
    intro request member
    obtain ⟨issued,traced,bounded⟩ := correct request member
    exact ⟨issued,traced,bounded.trans bound⟩
  exact binary_exception_obstruction m hm _ exception π free (previous+1) _
    (full_native_correct m hm odd alphabet free previous archive parent prior full
      f initialLabels wellDefined π 1 extended)

/-- The full table's exact additional fee, with the supplied binary exception. -/
def fullFee {Y : Type z} {m : ℕ} (table : Fin (m+1) → Y) : ℕ :=
  if (labels table).card = 1 then 0 else
  if (labels table).card = 2 then if BinaryException table then 2 else 1
  else Nat.clog 2 (labels table).card

/-- Every acquired full-positive child has the original exact additional
adaptive and child-preset minima. The feasible witness is one literal suffix,
and the leastness assertion ranges over every original adaptive competitor. -/
theorem original_full_positive_price {Y : Type z} (m : ℕ) (hm : 3 ≤ m) (odd : Odd m)
    (alphabet : Bool) (free previous : ZMod 2) (archive : NarrowWindowCost.Archive m)
    (parent : Fin m → Bool)
    (prior : archiveEndpoint (some free) archive = some previous)
    (full : initialSupport (m+1) m (by omega) alphabet free
      (archive ++ [(parent,some (previous+1))]) = physicalWindow (m+1) m archive.length)
    (f : Option (LiveRecord (m+1)) → Y) (initialLabels : ZMod (m+2) → Y)
    (wellDefined : ∀ initial current : LiveRecord (m+1),
      (some initial,some current) ∈ AcquiredPairs (m+1) m (by omega) alphabet (some free)
        (archive ++ [(parent,some (previous+1))]) →
      f (some initial) = initialLabels (-initial.phase))
    : let table := fun x : Fin (m+1) => initialLabels (vertex (m+1) m archive.length x.val)
      let acquired := archive ++ [(parent,some (previous+1))]
      RequestFeasible (m+1) m alphabet f
        (ChildRequests (m+1) m (by omega) alphabet (some free) acquired)
        (fun π => ∃ stream : ℕ → AllowedBlock (m+1) m alphabet,
          PresetPolicy stream acquired.length π) (fullFee table) ∧
      (∀ h, RequestFeasible (m+1) m alphabet f
        (ChildRequests (m+1) m (by omega) alphabet (some free) acquired)
        (fun _ => True) h → fullFee table ≤ h) ∧
      ChildAdaptivePrice (m+1) m (by omega) alphabet f (some free) acquired =
        (fullFee table : ℕ∞) ∧
      ChildPresetPrice (m+1) m (by omega) alphabet f (some free) acquired =
        (fullFee table : ℕ∞) := by
  intro table acquired
  have positive : 0 < (labels table).card := by
    apply Finset.card_pos.mpr
    exact ⟨table ⟨0,by omega⟩,Finset.mem_image.mpr ⟨⟨0,by omega⟩,Finset.mem_univ _,rfl⟩⟩
  have attained : RequestFeasible (m+1) m alphabet f
      (ChildRequests (m+1) m (by omega) alphabet (some free) acquired)
      (fun π => ∃ stream : ℕ → AllowedBlock (m+1) m alphabet,
        PresetPolicy stream acquired.length π) (fullFee table) := by
    by_cases one : (labels table).card = 1
    · obtain ⟨L,singleton⟩ := Finset.card_eq_one.mp one
      have homogeneous (x : Fin (m+1)) : table x = L := by
        have mem : table x ∈ labels table := Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
        simpa only [singleton,Finset.mem_singleton] using mem
      rw [fullFee,if_pos one]
      change RequestFeasible _ _ _ _ _ _ ([] : List (Fin m → Bool)).length
      apply full_script_correct m hm odd alphabet free previous archive parent prior full
        f initialLabels wellDefined [] (fun _ => L)
      intro x; exact (homogeneous x).symm
    · by_cases two : (labels table).card = 2
      · by_cases exception : BinaryException table
        · rw [fullFee,if_neg one,if_pos two,if_pos exception]
          exact binary_attains_two m hm odd alphabet free previous archive parent prior full
            f initialLabels wellDefined exception
        · rw [fullFee,if_neg one,if_pos two,if_neg exception]
          exact binary_attains_one m hm odd alphabet free previous archive parent prior full
            f initialLabels wellDefined two exception
      · rw [fullFee,if_neg one,if_neg two]
        exact full_positive_many_attains m hm odd alphabet free previous archive parent prior full
          f initialLabels wellDefined (by change 3 ≤ (labels table).card; omega)
  have least : ∀ h, RequestFeasible (m+1) m alphabet f
      (ChildRequests (m+1) m (by omega) alphabet (some free) acquired)
      (fun _ => True) h → fullFee table ≤ h := by
    intro h feasible
    have lower := full_positive_lower m hm odd alphabet free previous archive parent prior full
      f initialLabels wellDefined h feasible
    have depth := Nat.clog_le_of_le_pow lower
    change Nat.clog 2 (labels table).card ≤ h at depth
    by_cases one : (labels table).card = 1
    · simp only [fullFee,if_pos one,Nat.zero_le]
    · by_cases two : (labels table).card = 2
      · by_cases exception : BinaryException table
        · rw [fullFee,if_neg one,if_pos two,if_pos exception]
          exact full_exception_lower m hm odd alphabet free previous archive parent prior full
            f initialLabels wellDefined exception h feasible
        · rw [fullFee,if_neg one,if_pos two,if_neg exception]
          norm_num [two] at depth
          exact depth
      · simpa only [fullFee,if_neg one,if_neg two] using depth
  have forget : ∀ h, RequestFeasible (m+1) m alphabet f
      (ChildRequests (m+1) m (by omega) alphabet (some free) acquired)
      (fun π => ∃ stream : ℕ → AllowedBlock (m+1) m alphabet,
        PresetPolicy stream acquired.length π) h →
      RequestFeasible (m+1) m alphabet f
        (ChildRequests (m+1) m (by omega) alphabet (some free) acquired) (fun _ => True) h := by
    rintro h ⟨π,legal,bottom,restriction,correct⟩
    exact ⟨π,legal,bottom,trivial,correct⟩
  refine ⟨attained,least,?_,?_⟩
  · exact price_exact _ _ (forget _ attained) least
  · exact price_exact _ _ attained (fun h feasible => least h (forget h feasible))

#print axioms full_positive_many_attains
#print axioms original_full_positive_price
#print axioms full_positive_lower
end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FullPositiveWindowPrice
