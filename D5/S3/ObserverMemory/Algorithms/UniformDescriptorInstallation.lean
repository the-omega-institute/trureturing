/- GID: D5/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/UniformDescriptorInstallation
   mirror-E: none(waiver:offline-original-source-materialization)
   anchors: []
   utility: none
   digest: Native unbounded witnesses materialize fixed literals and complete halt rows before execution. -/

import D5.S3.ObserverMemory.Algorithms.UniformDescriptorDesign
import D5.S0.Computability.NatPresburgerSolver

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

namespace D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation
open FirstOrder Language GuardedPhaseExecution UniformDescriptorPresentation
open UniformDescriptorSupport UniformDescriptorDesign

variable {S Y : Type} {letters c charts types s q : Nat} {Tsk : Task S Y letters c}

/-- Promote precisely the common descriptor tuple; the source and phase
quantifiers in the original conjunction remain inside it. -/
def descriptorQuery (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q)
    (G : Skeleton s c types) : presburger.BoundedFormula (Fin 0) (blockTotal (dims P G)) :=
  BoundedFormula.relabel (k := 0) (n := blockTotal (dims P G)) id
    ((Total P M G ⊓ Shared P M G ⊓ ValidFormula P G).relabel Sum.inr)

private theorem descriptor_query_correct (P : Presentation Tsk charts types)
    (M : ReachedTransport Tsk q) (G : Skeleton s c types)
    (delta : Fin (blockTotal (dims P G)) → Nat) :
    (descriptorQuery P M G).Realize Fin.elim0 delta ↔
      (Total P M G).Realize delta ∧ (Shared P M G).Realize delta ∧ Valid P G delta := by
  simp only [descriptorQuery, BoundedFormula.realize_relabel, Formula.realize_relabel,
    Function.comp_id, Fin.castAdd_zero, Fin.cast_refl,
    Formula.boundedFormula_realize_eq_realize, Formula.realize_relabel,
    Sum.elim_comp_inr, Formula.realize_inf]
  rw [valid_correct]
  tauto

/-- Source coordinates precede the independently returned terminal epoch in
this native witness tuple. Inner phase witnesses are the actual haltAt syntax. -/
def haltQuery (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q)
    (G : Skeleton s c types) (η : Fin charts) (h : Fin s) :
    presburger.BoundedFormula (Fin (blockTotal (dims P G))) (P.sourceDim η + 1) :=
  BoundedFormula.relabel (k := 0) (n := P.sourceDim η + 1) id
    (((P.adm η).relabel (fun i => Sum.inr (Fin.castAdd 1 i))) ⊓
      ((haltAt P M G η h).relabel
        (Sum.elim (Sum.elim Sum.inl (fun i => Sum.inr (Fin.castAdd 1 i)))
          (fun _ => Sum.inr (Fin.natAdd (P.sourceDim η) (0 : Fin 1))))))

private theorem halt_query_correct (P : Presentation Tsk charts types)
    (M : ReachedTransport Tsk q) (G : Skeleton s c types) (η : Fin charts)
    (h : Fin s) (delta : Fin (blockTotal (dims P G)) → Nat)
    (w : Fin (P.sourceDim η + 1) → Nat) :
    (haltQuery P M G η h).Realize delta w ↔
      (P.adm η).Realize (w ∘ Fin.castAdd 1) ∧
      (haltAt P M G η h).Realize
        (Sum.elim (Sum.elim delta (w ∘ Fin.castAdd 1))
          (fun _ => w (Fin.natAdd (P.sourceDim η) (0 : Fin 1)))) := by
  simp only [haltQuery, BoundedFormula.realize_relabel, Formula.realize_inf,
    Formula.realize_relabel, Function.comp_id, Fin.castAdd_zero, Fin.cast_refl,
    Formula.boundedFormula_realize_eq_realize, Formula.realize_inf, Formula.realize_relabel]
  have en : Sum.elim delta w ∘ (fun i => Sum.inr (Fin.castAdd 1 i)) =
      w ∘ Fin.castAdd 1 := rfl
  have ew : Sum.elim delta w ∘
      Sum.elim (Sum.elim Sum.inl (fun i => Sum.inr (Fin.castAdd 1 i)))
        (fun _ : Unit => Sum.inr (Fin.natAdd (P.sourceDim η) (0 : Fin 1))) =
      Sum.elim (Sum.elim delta (w ∘ Fin.castAdd 1))
        (fun _ => w (Fin.natAdd (P.sourceDim η) (0 : Fin 1))) := by
    funext i; rcases i with (i | i) | i <;> rfl
  rw [en, ew]

private theorem chosen_real (P : Presentation Tsk charts types) (G : Skeleton s c types)
    (delta : Fin (blockTotal (dims P G)) → Nat) (hv : Valid P G delta) :
    Realizes P G delta (chosenLiterals P G delta hv) := fun a => P.choose_mem _ _ _

/-- Only an admitted original source and its actual native run can inhabit this
certificate. Its proof is erased; it is not a runtime state component. -/
abbrev ReachingSource (P : Presentation Tsk charts types) (G : Skeleton s c types)
    (delta : Fin (blockTotal (dims P G)) → Nat) (hv : Valid P G delta) (h : Fin s) :=
  {u : Tsk.Source // ∃ J, Run (literalProgram G (chosenLiterals P G delta hv))
    (Tsk.observation u) G.start Tsk.entryEpoch h J}

/-- theta is called only in the some branch, after native solver soundness has
proved admission. No original source is fabricated on a failed query. -/
def chartSource (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q)
    (G : Skeleton s c types) (delta : Fin (blockTotal (dims P G)) → Nat)
    (hv : Valid P G delta) (h : Fin s) (η : Fin charts) :
    Option (ReachingSource P G delta hv h) :=
  match hw : NatPresburger.solveBounded (haltQuery P M G η h) delta with
  | none => none
  | some w =>
    let facts := (halt_query_correct P M G η h delta w).mp
      (NatPresburger.solve_bounded_sound _ _ _ hw)
    some ⟨P.theta η ⟨w ∘ Fin.castAdd 1, facts.1⟩,
      w (Fin.natAdd (P.sourceDim η) (0 : Fin 1)),
      (native_support P M G η delta _ facts.1 hv _ (chosen_real P G delta hv) h _).1.mp facts.2⟩

private theorem chart_source_none (P : Presentation Tsk charts types)
    (M : ReachedTransport Tsk q) (G : Skeleton s c types)
    (delta : Fin (blockTotal (dims P G)) → Nat) (hv : Valid P G delta)
    (h : Fin s) (η : Fin charts) :
    chartSource P M G delta hv h η = none ↔
      ¬ ∃ n, ∃ hn : (P.adm η).Realize n,
        ∃ J, Run (literalProgram G (chosenLiterals P G delta hv))
          (Tsk.observation (P.theta η ⟨n,hn⟩)) G.start Tsk.entryEpoch h J := by
  have exacts : (∃ w, (haltQuery P M G η h).Realize delta w) ↔
      ∃ n, ∃ hn : (P.adm η).Realize n, ∃ J,
        Run (literalProgram G (chosenLiterals P G delta hv))
          (Tsk.observation (P.theta η ⟨n,hn⟩)) G.start Tsk.entryEpoch h J := by
    constructor
    · rintro ⟨w,hw⟩
      have facts := (halt_query_correct P M G η h delta w).mp hw
      exact ⟨_,facts.1,_,(native_support P M G η delta _ facts.1 hv _
        (chosen_real P G delta hv) h _).1.mp facts.2⟩
    · rintro ⟨n,hn,J,path⟩
      refine ⟨Fin.append n (fun _ : Fin 1 => J), (halt_query_correct P M G η h delta _).mpr ?_⟩
      have en : (Fin.append n (fun _ : Fin 1 => J)) ∘ Fin.castAdd 1 = n := by
        funext i; exact Fin.append_left _ _ _
      simp only [en, Fin.append_right]
      exact ⟨hn,(native_support P M G η delta n hn hv _ (chosen_real P G delta hv) h J).1.mpr path⟩
  rw [← exacts, ← NatPresburger.solve_bounded_none_iff]
  unfold chartSource
  split <;> simp_all

/-- Every chart is searched before none is returned. -/
def sourceSearch (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q)
    (G : Skeleton s c types) (delta : Fin (blockTotal (dims P G)) → Nat)
    (hv : Valid P G delta) (h : Fin s) : List (Fin charts) →
    Option (ReachingSource P G delta hv h) :=
  List.findSome? (chartSource P M G delta hv h)

private theorem all_sources_none (P : Presentation Tsk charts types)
    (M : ReachedTransport Tsk q) (G : Skeleton s c types)
    (delta : Fin (blockTotal (dims P G)) → Nat) (hv : Valid P G delta) (h : Fin s) :
    sourceSearch P M G delta hv h (List.finRange charts) = none ↔
      ¬ ∃ u : Tsk.Source, ∃ J, Run (literalProgram G (chosenLiterals P G delta hv))
        (Tsk.observation u) G.start Tsk.entryEpoch h J := by
  rw [sourceSearch, List.findSome?_eq_none_iff]
  simp only [List.mem_finRange, forall_true_left, chart_source_none]
  constructor
  · intro law ⟨u,J,path⟩
    obtain ⟨⟨η,n,hn⟩,he⟩ := P.theta_bijective.2 u
    exact law η ⟨n,hn,J,by simpa only [he] using path⟩
  · intro law η ⟨n,hn,J,path⟩
    exact law ⟨P.theta η ⟨n,hn⟩,J,path⟩

/-- Full target rows are evaluated offline on certified original sources only.
The complete supplied default row handles exactly the all-chart-none case. -/
def haltRow (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q)
    (G : Skeleton s c types) (delta : Fin (blockTotal (dims P G)) → Nat)
    (hv : Valid P G delta) (h : Fin s) : Y :=
  match sourceSearch P M G delta hv h (List.finRange charts) with
  | some u => Tsk.target u.val
  | none => Tsk.defaultRow

private theorem halt_row_correct (P : Presentation Tsk charts types)
    (M : ReachedTransport Tsk q) (G : Skeleton s c types)
    (delta : Fin (blockTotal (dims P G)) → Nat) (hv : Valid P G delta)
    (shared : NativeShared G (chosenLiterals P G delta hv))
    (u : Tsk.Source) (h : Fin s) (J : Nat) (hh : G.program h = .halt)
    (path : Run (literalProgram G (chosenLiterals P G delta hv))
      (Tsk.observation u) G.start Tsk.entryEpoch h J) :
    haltRow P M G delta hv h = Tsk.target u := by
  unfold haltRow
  split
  · next v he =>
    obtain ⟨J',pv⟩ := v.property
    exact shared v.val u h J' J hh pv path
  · next he => exact False.elim ((all_sources_none P M G delta hv h).mp he ⟨u,J,path⟩)

/-- Literal and entry vectors are produced eagerly. Final entries retain only physical
literals, finite successors, and complete rows; they retain no producing closures. -/
def materialize (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q)
    (G : Skeleton (s + 1) c types) (delta : Fin (blockTotal (dims P G)) → Nat)
    (hv : Valid P G delta) : InstalledTable Tsk :=
  let literals := Vector.ofFn (chosenLiterals P G delta hv)
  ⟨s + 1, Nat.zero_lt_succ s, G.start, Vector.ofFn fun i =>
    match G.program i with
    | .read a next => .read (literals.get a) (Vector.ofFn next)
    | .update next => .update next
    | .halt => .halt (haltRow P M G delta hv i)⟩

private theorem vector_get_ofFn {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  simp only [Vector.get, Vector.toArray_ofFn, Array.getElem_ofFn]
  apply congrArg f
  apply Fin.ext
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem materialize_program (P : Presentation Tsk charts types)
    (M : ReachedTransport Tsk q) (G : Skeleton (s + 1) c types)
    (delta : Fin (blockTotal (dims P G)) → Nat) (hv : Valid P G delta) :
    (materialize P M G delta hv).program = literalProgram G (chosenLiterals P G delta hv) := by
  unfold materialize
  funext i
  simp only [InstalledTable.program]
  rw [vector_get_ofFn]
  simp only [literalProgram, transportProgram, Equiv.refl_symm, Equiv.refl_apply]
  cases he : G.program i <;> simp [he, Instruction.transport, vector_get_ofFn]
  congr 1
  funext a
  exact vector_get_ofFn _ a

set_option backward.isDefEq.respectTransparency false in
private theorem materialize_halt (P : Presentation Tsk charts types)
    (M : ReachedTransport Tsk q) (G : Skeleton (s + 1) c types)
    (delta : Fin (blockTotal (dims P G)) → Nat) (hv : Valid P G delta)
    (h : Fin (s + 1)) (hh : G.program h = .halt) :
    (materialize P M G delta hv).entries.get h = .halt (haltRow P M G delta hv h) := by
  simp only [materialize]
  rw [vector_get_ofFn, hh]

private theorem materialize_successful (P : Presentation Tsk charts types)
    (M : ReachedTransport Tsk q) (G : Skeleton (s + 1) c types)
    (delta : Fin (blockTotal (dims P G)) → Nat) (hv : Valid P G delta)
    (total : NativeTotal G (chosenLiterals P G delta hv))
    (shared : NativeShared G (chosenLiterals P G delta hv)) :
    (materialize P M G delta hv).Successful := by
  intro u
  obtain ⟨h,J,hh,path⟩ := total u
  exact ⟨h,J,haltRow P M G delta hv h,materialize_halt P M G delta hv h hh,
    halt_row_correct P M G delta hv shared u h J hh path,
    by rw [materialize_program]; exact path⟩

/-- Every halt-ended run is checked at its actual endpoint, using both halt
hypotheses in native determinism. This is a proof property, never an input field. -/
def EndpointCorrect (table : InstalledTable Tsk) : Prop :=
  ∀ (u : Tsk.Source) h J row, table.entries.get h = .halt row →
    Run table.program (Tsk.observation u) table.start Tsk.entryEpoch h J → row = Tsk.target u

private theorem successful_endpoint (table : InstalledTable Tsk) (hs : table.Successful) :
    EndpointCorrect table := by
  intro u h J row hh path
  obtain ⟨h',J',row',hh',hr',path'⟩ := hs u
  have halt : table.program h = .halt := by simp [InstalledTable.program, hh]
  have halt' : table.program h' = .halt := by simp [InstalledTable.program, hh']
  have ends := run_halt_unique path path' halt halt'
  have rows : row = row' := by
    rw [← ends.1] at hh'
    exact InstalledEntry.halt.inj (hh.symm.trans hh')
  exact rows.trans hr'

/-- The solver is used only while producing the option, before table execution. -/
def installCandidate (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q)
    (G : Skeleton (s + 1) c types) : Option (InstalledTable Tsk) :=
  match hd : NatPresburger.solveBounded (descriptorQuery P M G) Fin.elim0 with
  | none => none
  | some delta =>
    let facts := (descriptor_query_correct P M G delta).mp
      (NatPresburger.solve_bounded_sound _ _ _ hd)
    some (materialize P M G delta facts.2.2)

/-- A returned table preserves every state and start and stores every permitted
literal and complete row. Its actual native termination and endpoint output are derived. -/
theorem install_candidate_correct (P : Presentation Tsk charts types)
    (M : ReachedTransport Tsk q) (G : Skeleton (s + 1) c types)
    (table : InstalledTable Tsk) (hi : installCandidate P M G = some table) :
    ∃ delta, ∃ hv : Valid P G delta,
      table = materialize P M G delta hv ∧ table.Successful ∧ EndpointCorrect table := by
  unfold installCandidate at hi
  split at hi
  · contradiction
  · next delta hd =>
    have facts := (descriptor_query_correct P M G delta).mp
      (NatPresburger.solve_bounded_sound _ _ _ hd)
    have he : materialize P M G delta facts.2.2 = table := Option.some.inj hi
    subst table
    have exacts := design_correct P M G delta facts.2.2 _ (chosen_real P G delta facts.2.2)
    have success := materialize_successful P M G delta facts.2.2
      (exacts.2.1.mp facts.1) (exacts.2.2.mp facts.2.1)
    exact ⟨delta,facts.2.2,rfl,success,successful_endpoint _ success⟩

/-- A candidate has a returned installation exactly when it is feasible. -/
theorem install_candidate_exists_iff (P : Presentation Tsk charts types)
    (M : ReachedTransport Tsk q) (G : Skeleton (s + 1) c types) :
    (∃ table, installCandidate P M G = some table) ↔ Feasible P G := by
  have feasible : (∃ delta : Fin (blockTotal (dims P G)) → Nat,
      (descriptorQuery P M G).Realize (Fin.elim0 : Fin 0 → Nat) delta) ↔ Feasible P G := by
    rw [← phi_correct P M G]
    simp only [Phi, closeEx, descriptorQuery, BoundedFormula.realize_exs]
    rfl
  rw [← feasible, ← NatPresburger.solve_bounded_exists_some_iff]
  unfold installCandidate
  split <;> simp_all

/-- Candidate rejection excludes all unbounded valid descriptor valuations. -/
theorem install_candidate_none_iff (P : Presentation Tsk charts types)
    (M : ReachedTransport Tsk q) (G : Skeleton (s + 1) c types) :
    installCandidate P M G = none ↔ ¬ Feasible P G := by
  rw [← install_candidate_exists_iff P M G]
  cases installCandidate P M G <;> simp

/-- A complete literal table on arbitrary state labels. Rows are immutable
installation data; only a halt instruction emits its state's complete row. -/
structure LiteralTable (T : Task S Y letters c) (E : Type) where
  start : E
  program : E → Instruction E T.Literal (Fin c)
  row : E → Y

namespace LiteralTable
variable {E E' : Type}

def Successful (table : LiteralTable Tsk E) : Prop :=
  ∀ u : Tsk.Source, ∃ h J, table.program h = .halt ∧ table.row h = Tsk.target u ∧
    Run table.program (Tsk.observation u) table.start Tsk.entryEpoch h J

/-- Reindexing retains the complete state set, including all unreachable entries. -/
def reindex (table : LiteralTable Tsk E) (sigma : E ≃ E') : LiteralTable Tsk E' :=
  ⟨sigma table.start, transportProgram sigma id table.program, table.row ∘ sigma.symm⟩

private theorem reindex_run (table : LiteralTable Tsk E) (sigma : E ≃ E')
    (u : Tsk.Source) (x y : E) (a b : Nat) :
    Run table.program (Tsk.observation u) x a y b ↔
      Run (table.reindex sigma).program (Tsk.observation u) (sigma x) a (sigma y) b :=
  run_transport_iff sigma id
    (by intro i; simp [reindex, transportProgram]) (by intros; rfl)

private theorem reindex_successful (table : LiteralTable Tsk E) (sigma : E ≃ E')
    (hs : table.Successful) : (table.reindex sigma).Successful := by
  intro u
  obtain ⟨h,J,hh,hr,path⟩ := hs u
  refine ⟨sigma h,J,?_,?_,(reindex_run table sigma u _ _ _ _).mp path⟩
  · simp [reindex, transportProgram, hh, Instruction.transport]
  · simpa [reindex] using hr

private theorem endpoint (table : LiteralTable Tsk E) (hs : table.Successful)
    (u : Tsk.Source) (h : E) (J : Nat) (hh : table.program h = .halt)
    (path : Run table.program (Tsk.observation u) table.start Tsk.entryEpoch h J) :
    table.row h = Tsk.target u := by
  obtain ⟨h',J',halt',row',path'⟩ := hs u
  have he := run_halt_unique path path' hh halt'
  simpa only [he.1] using row'
end LiteralTable

/-- The proof view reads precisely the already stored entries and rows. -/
def literalTable (table : InstalledTable Tsk) : LiteralTable Tsk (Fin table.size) :=
  ⟨table.start, table.program, fun h => match table.entries.get h with
    | .halt row => row
    | _ => Tsk.defaultRow⟩

private theorem literal_table_successful (table : InstalledTable Tsk)
    (hs : table.Successful) : (literalTable table).Successful := by
  intro u
  obtain ⟨h,J,row,hh,hr,path⟩ := hs u
  exact ⟨h,J,by simp [literalTable,InstalledTable.program,hh],
    by simpa [literalTable,hh] using hr,path⟩

/-- Type coverage is selected once for every actual read, including unreachable reads. -/
def symbolicTable (P : Presentation Tsk charts types) (table : LiteralTable Tsk (Fin s)) :
    Skeleton s c types :=
  reindexSkeleton (Equiv.refl _) table.start table.program
    (fun _ p _ _ => (P.descriptorOf p).1)

private theorem symbolic_entry (P : Presentation Tsk charts types)
    (table : LiteralTable Tsk (Fin s)) (i : Fin s) :
    (symbolicTable P table).entries.get i =
      match table.program i with
      | .read p k => .read (P.descriptorOf p).1 (Vector.ofFn k)
      | .update k => .update k
      | .halt => .halt := by
  simp only [symbolicTable, reindexSkeleton, Equiv.refl_symm, Equiv.refl_apply]
  rw [vector_get_ofFn]
  cases table.program i <;> rfl

/-- This occurrence map can identify several read states with one physical literal. -/
def physicalLiteral (P : Presentation Tsk charts types) (table : LiteralTable Tsk (Fin s))
    (a : Fin (symbolicTable P table).readCount) : Tsk.Literal :=
  match h : table.program ((symbolicTable P table).readAt a).val with
  | .read p _ => p
  | .update _ => False.elim (by
      have hr := ((symbolicTable P table).readAt a).property
      rw [symbolic_entry, h] at hr
      simp [Skeleton.isRead] at hr)
  | .halt => False.elim (by
      have hr := ((symbolicTable P table).readAt a).property
      rw [symbolic_entry, h] at hr
      simp [Skeleton.isRead] at hr)

set_option backward.isDefEq.respectTransparency false in
private theorem physical_kind (P : Presentation Tsk charts types)
    (table : LiteralTable Tsk (Fin s)) (a : Fin (symbolicTable P table).readCount) :
    (symbolicTable P table).readKind a = (P.descriptorOf (physicalLiteral P table a)).1 := by
  cases hp : table.program ((symbolicTable P table).readAt a).val with
  | read p k =>
    have hg := symbolic_entry P table ((symbolicTable P table).readAt a).val
    simp only [hp] at hg
    have hl : physicalLiteral P table a = p := by
      unfold physicalLiteral
      split
      · next p' k' he => exact (Instruction.read.inj (he.symm.trans hp)).1
      · next k' he => cases he.symm.trans hp
      · next he => cases he.symm.trans hp
    rw [hl]
    unfold Skeleton.readKind
    split
    · next b next he => exact (TypedEntry.read.inj (he.symm.trans hg)).1
    · next next he => cases he.symm.trans hg
    · next he => cases he.symm.trans hg
  | update k =>
    have hr := ((symbolicTable P table).readAt a).property
    rw [symbolic_entry,hp] at hr
    simp [Skeleton.isRead] at hr
  | halt =>
    have hr := ((symbolicTable P table).readAt a).property
    rw [symbolic_entry,hp] at hr
    simp [Skeleton.isRead] at hr

set_option backward.isDefEq.respectTransparency false in
private theorem physical_program (P : Presentation Tsk charts types)
    (table : LiteralTable Tsk (Fin s)) :
    literalProgram (symbolicTable P table) (physicalLiteral P table) = table.program := by
  funext i
  simp only [literalProgram,transportProgram,Equiv.refl_symm,Equiv.refl_apply]
  cases hi : table.program i with
  | read p k =>
    have hg : (symbolicTable P table).entries.get i =
        .read (P.descriptorOf p).1 (Vector.ofFn k) := by rw [symbolic_entry,hi]
    unfold Skeleton.program
    split
    · next kind next he =>
      cases he.symm.trans hg
      have atRead (hr : Skeleton.isRead ((symbolicTable P table).entries.get i) = true) :
          ((symbolicTable P table).readAt (FinEnum.equiv ⟨i,hr⟩)).val = i := by
        exact congrArg Subtype.val (FinEnum.equiv.symm_apply_apply (⟨i,hr⟩ : (symbolicTable P table).Read))
      have lit (hr : Skeleton.isRead ((symbolicTable P table).entries.get i) = true) :
          physicalLiteral P table (FinEnum.equiv ⟨i,hr⟩) = p := by
        unfold physicalLiteral
        split
        · next p' k' hp =>
          rw [atRead] at hp
          exact (Instruction.read.inj (hp.symm.trans hi)).1
        · next k' hp => rw [atRead] at hp; cases hp.symm.trans hi
        · next hp => rw [atRead] at hp; cases hp.symm.trans hi
      simp only [Instruction.transport,lit]
      congr 1
      funext z
      exact vector_get_ofFn k z
    · next next he => cases he.symm.trans hg
    · next he => cases he.symm.trans hg
  | update k =>
    have hg : (symbolicTable P table).entries.get i = .update k := by rw [symbolic_entry,hi]
    unfold Skeleton.program
    split
    · next p' k' he => cases he.symm.trans hg
    · next k' he => cases he.symm.trans hg; rfl
    · next he => cases he.symm.trans hg
  | halt =>
    have hg : (symbolicTable P table).entries.get i = .halt := by rw [symbolic_entry,hi]
    unfold Skeleton.program
    split
    · next p' k' he => cases he.symm.trans hg
    · next k' he => cases he.symm.trans hg
    · next he => rfl

/-- Flattening is proof-only: it recovers the covered descriptor for every
occurrence without constraining its numeric coordinates. -/
noncomputable def coveredTuple (P : Presentation Tsk charts types)
    (table : LiteralTable Tsk (Fin s)) (a : Fin (symbolicTable P table).readCount) :
    Fin (dims P (symbolicTable P table) a) → Nat :=
  fun k => (P.descriptorOf (physicalLiteral P table a)).2
    (Fin.cast (congrArg P.descriptorDim (physical_kind P table a)) k)

noncomputable def coveredDelta (P : Presentation Tsk charts types)
    (table : LiteralTable Tsk (Fin s)) :
    Fin (blockTotal (dims P (symbolicTable P table))) → Nat :=
  Function.extend (descriptorLayout (dims P (symbolicTable P table)))
    (fun z => coveredTuple P table z.1 z.2) (fun _ => 0)

private theorem covered_tuple (P : Presentation Tsk charts types)
    (table : LiteralTable Tsk (Fin s)) (a : Fin (symbolicTable P table).readCount) :
    descriptorTuple P (symbolicTable P table) (coveredDelta P table) a = coveredTuple P table a := by
  funext k
  change Function.extend (descriptorLayout (dims P (symbolicTable P table)))
    (fun z => coveredTuple P table z.1 z.2) (fun _ => 0)
    (descriptorLayout (dims P (symbolicTable P table)) ⟨a,k⟩) = _
  exact (descriptorLayout _).injective.extend_apply _ _ ⟨a,k⟩

private theorem covered_valid_real (P : Presentation Tsk charts types)
    (table : LiteralTable Tsk (Fin s)) :
    Valid P (symbolicTable P table) (coveredDelta P table) ∧
    Realizes P (symbolicTable P table) (coveredDelta P table) (physicalLiteral P table) := by
  have validCast (b b' : Fin types) (t : Fin (P.descriptorDim b') → Nat) (he : b = b')
      (ht : (P.valid b').Realize t) :
      (P.valid b).Realize (fun k => t (Fin.cast (congrArg P.descriptorDim he) k)) := by
    subst b'
    simpa only [Fin.cast_refl, id_eq] using ht
  have realCast (b b' : Fin types) (t : Fin (P.descriptorDim b') → Nat) (he : b = b')
      (p : Tsk.Literal) (ht : P.real b' t p) :
      P.real b (fun k => t (Fin.cast (congrArg P.descriptorDim he) k)) p := by
    subst b'
    simpa only [Fin.cast_refl, id_eq] using ht
  constructor
  · intro a
    rw [covered_tuple]
    exact validCast _ _ _ (physical_kind P table a) (P.coverage (physicalLiteral P table a)).1
  · intro a
    rw [covered_tuple]
    exact realCast _ _ _ (physical_kind P table a) _ (P.coverage (physicalLiteral P table a)).2

private theorem realization_replies (P : Presentation Tsk charts types)
    (G : Skeleton s c types) (delta : Fin (blockTotal (dims P G)) → Nat)
    (hv : Valid P G delta) (literals : Fin G.readCount → Tsk.Literal)
    (hr : Realizes P G delta literals) (u : Tsk.Source) (j : Nat) (a : Fin G.readCount) :
    Tsk.observation u j (chosenLiterals P G delta hv a) = Tsk.observation u j (literals a) := by
  obtain ⟨⟨η,n,hn⟩,hu⟩ := P.theta_bijective.2 u
  subst u
  exact (P.reply_exact η (G.readKind a) n j (descriptorTuple P G delta a) hn (hv a)
    (chosenLiterals P G delta hv a) (P.choose_mem _ _ _)
    (Tsk.observation (P.theta η ⟨n,hn⟩) j (literals a))).mp
    ((P.reply_exact η (G.readKind a) n j (descriptorTuple P G delta a) hn (hv a)
      (literals a) (hr a) _).mpr rfl)

private theorem realization_run (P : Presentation Tsk charts types)
    (G : Skeleton s c types) (delta : Fin (blockTotal (dims P G)) → Nat)
    (hv : Valid P G delta) (literals : Fin G.readCount → Tsk.Literal)
    (hr : Realizes P G delta literals) (u : Tsk.Source) (x y : Fin s) (a b : Nat) :
    Run (literalProgram G literals) (Tsk.observation u) x a y b ↔
      Run (literalProgram G (chosenLiterals P G delta hv)) (Tsk.observation u) x a y b := by
  have old := run_transport_iff (Equiv.refl _) literals
    (prog := G.program) (prog' := literalProgram G literals)
    (obs := literalObs G u literals) (obs' := Tsk.observation u)
    (by intro i; simp [literalProgram,transportProgram]) (by intros; rfl)
    (x := x) (y := y) (a := a) (b := b)
  have new := run_transport_iff (Equiv.refl _) (chosenLiterals P G delta hv)
    (prog := G.program) (prog' := literalProgram G (chosenLiterals P G delta hv))
    (obs := literalObs G u literals) (obs' := Tsk.observation u)
    (by intro i; simp [literalProgram,transportProgram])
    (realization_replies P G delta hv literals hr u)
    (x := x) (y := y) (a := a) (b := b)
  exact old.symm.trans new

set_option backward.isDefEq.respectTransparency false in
/-- Any successful literal table, with every state retained, has a valid
covered tuple satisfying native Total and Shared. Actual halt uniqueness
identifies each endpoint with its original stored complete output row. -/
theorem successful_feasible (P : Presentation Tsk charts types)
    (table : LiteralTable Tsk (Fin s)) (hs : table.Successful) :
    Feasible P (symbolicTable P table) := by
  let G := symbolicTable P table
  let delta := coveredDelta P table
  have cover := covered_valid_real P table
  let hv := cover.1
  have paths (u : Tsk.Source) (x y : Fin s) (a b : Nat) :
      Run table.program (Tsk.observation u) x a y b ↔
        Run (literalProgram G (chosenLiterals P G delta hv)) (Tsk.observation u) x a y b := by
    rw [← physical_program P table]
    exact realization_run P G delta hv (physicalLiteral P table) cover.2 u x y a b
  have halt (h : Fin s) : G.program h = .halt ↔ table.program h = .halt := by
    rw [← congrFun (physical_program P table) h]
    change G.program h = .halt ↔ literalProgram G (physicalLiteral P table) h = .halt
    simp only [literalProgram,transportProgram,Equiv.refl_symm,Equiv.refl_apply]
    cases G.program h <;> simp [Instruction.transport]
  refine ⟨delta,hv,?_,?_⟩
  · intro u
    obtain ⟨h,J,hh,hr,path⟩ := hs u
    exact ⟨h,J,(halt h).mpr hh,(paths u _ _ _ _).mp path⟩
  · intro u v h J J' hh pu pv
    have hu := LiteralTable.endpoint table hs u h J ((halt h).mp hh)
      ((paths u _ _ _ _).mpr pu)
    have hval := LiteralTable.endpoint table hs v h J' ((halt h).mp hh)
      ((paths v _ _ _ _).mpr pv)
    exact hu.symm.trans hval

/-- Arbitrary finite state labels have the actual equivalence to a counted Fin
state set. No state is removed and no numeric descriptor cutoff is imposed. -/
theorem successful_budget (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q)
    {E : Type} [Fintype E] (table : LiteralTable Tsk E) (K : Nat)
    (bound : Fintype.card E ≤ K) (hs : table.Successful) :
    (Psi P M K).Realize (Fin.elim0 : Fin 0 → Nat) := by
  classical
  letI : Nonempty E := ⟨table.start⟩
  have pos : 0 < Fintype.card E := Fintype.card_pos
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt pos)
  let sigma : E ≃ Fin (n+1) := Fintype.equivFinOfCardEq hn
  have hb : n+1 ≤ K := by omega
  exact (budget_correct P M K).mpr ⟨n,hb,symbolicTable P (table.reindex sigma),
    successful_feasible P _ (LiteralTable.reindex_successful table sigma hs)⟩

/-- The original existence proposition explicitly permits every finite labeling. -/
def Solvable (T : Task S Y letters c) (K : Nat) : Prop :=
  ∃ E : Type, ∃ _ : Fintype E, ∃ table : LiteralTable T E,
    Fintype.card E ≤ K ∧ table.Successful

/-- The scan uses exactly the full size/type enumeration and native installation.
The option contains eager finite literals, full rows, control and initial state. -/
def synthesize (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q)
    (K : Nat) : Option (InstalledTable Tsk) :=
  List.findSome? (fun candidate => installCandidate P M candidate.2) (candidates K c types)

private theorem scan_none (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q)
    (K : Nat) : synthesize P M K = none ↔
      ¬ (Psi P M K).Realize (Fin.elim0 : Fin 0 → Nat) := by
  rw [synthesize,List.findSome?_eq_none_iff,Psi,realize_anyF]
  simp only [install_candidate_none_iff,phi_correct]
  constructor
  · intro hn ⟨candidate,hm,hf⟩; exact hn candidate hm hf
  · intro hn candidate hm hf; exact hn ⟨candidate,hm,hf⟩

/-- A returned finite table succeeds with its actual counted control size and
initial state. No phase, source, descriptor evaluator or solver is installed. -/
theorem synthesize_sound (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q)
    (K : Nat) (table : InstalledTable Tsk) (hs : synthesize P M K = some table) :
    table.size ≤ K ∧ table.Successful ∧ EndpointCorrect table := by
  obtain ⟨candidate,hm,hi⟩ := List.exists_of_findSome?_eq_some hs
  obtain ⟨delta,hv,he,success,endpoint⟩ := install_candidate_correct P M candidate.2 table hi
  have size : candidate.1+1 ≤ K := by
    simp only [candidates,List.mem_flatMap,List.mem_map] at hm
    obtain ⟨n,hn,G,hG,he⟩ := hm
    cases he
    simp only [List.mem_range] at hn
    change n+1 ≤ K
    omega
  refine ⟨?_,success,endpoint⟩
  rw [he]
  exact size

/-- Failure rejects every successful original complete literal table on every
nonempty finite state type, and all unbounded descriptor valuations. -/
theorem synthesize_none_iff (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q)
    (K : Nat) : synthesize P M K = none ↔ ¬ Solvable Tsk K := by
  constructor
  · intro hn ⟨E,inst,table,hb,hs⟩
    letI := inst
    exact (scan_none P M K).mp hn (successful_budget P M table K hb hs)
  · intro hn
    cases he : synthesize P M K with
    | none => rfl
    | some table =>
      have facts := synthesize_sound P M K table he
      exact False.elim (hn ⟨Fin table.size,inferInstance,literalTable table,
        by simpa using facts.1,literal_table_successful table facts.2.1⟩)

/-- Original-source correspondence compares observations only after the two
separate updates. It never applies the source bijection to a transported register. -/
structure TaskCorrespondence {S' : Type} (T : Task S Y letters c)
    (T' : Task S' Y letters c) where
  source : T.Source ≃ T'.Source
  permitted : ∀ p, T.permitted p ↔ T'.permitted p
  entry : T.entryEpoch = T'.entryEpoch
  observations : ∀ (u : T.Source) j (p : T.Literal),
    T'.observation (source u) j ⟨p.val,(permitted p.val).mp p.property⟩ = T.observation u j p
  rows : ∀ u, T'.target (source u) = T.target u

namespace TaskCorrespondence
variable {S' : Type} {T' : Task S' Y letters c}

def literal (C : TaskCorrespondence Tsk T') : Tsk.Literal ≃ T'.Literal where
  toFun p := ⟨p.val,(C.permitted p.val).mp p.property⟩
  invFun p := ⟨p.val,(C.permitted p.val).mpr p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Inverse original-source correspondence preserves physical words. -/
def symm (C : TaskCorrespondence Tsk T') : TaskCorrespondence T' Tsk where
  source := C.source.symm
  permitted p := (C.permitted p).symm
  entry := C.entry.symm
  observations u j p := by
    have h := C.observations (C.source.symm u) j
      ⟨p.val,(C.permitted p.val).mpr p.property⟩
    simpa only [Equiv.apply_symm_apply] using h.symm
  rows u := by simpa only [Equiv.apply_symm_apply] using (C.rows (C.source.symm u)).symm

/-- Only the literal's permission proof changes; all states, successors, full
rows and physical word bytes stay in the stored finite vectors. -/
def installed (C : TaskCorrespondence Tsk T') (table : InstalledTable Tsk) : InstalledTable T' :=
  ⟨table.size,table.positive,table.start,Vector.ofFn fun i => match table.entries.get i with
    | .read p next => .read (C.literal p) next
    | .update next => .update next
    | .halt row => .halt row⟩

private theorem installed_entry (C : TaskCorrespondence Tsk T') (table : InstalledTable Tsk)
    (i : Fin table.size) :
    (C.installed table).entries.get i = match table.entries.get i with
      | .read p next => .read (C.literal p) next
      | .update next => .update next
      | .halt row => .halt row := vector_get_ofFn _ _

private theorem installed_program (C : TaskCorrespondence Tsk T') (table : InstalledTable Tsk)
    (i : Fin table.size) : (C.installed table).program i =
      Instruction.transport (Equiv.refl _) C.literal (table.program i) := by
  simp only [InstalledTable.program,installed_entry]
  cases table.entries.get i <;> rfl
end TaskCorrespondence

/-- The same literal table has exact native runs in both directions under the
original source bijection at every epoch, without any source-domain closure. -/
theorem corresponding_run {S' : Type} {T' : Task S' Y letters c}
    (C : TaskCorrespondence Tsk T') (table : InstalledTable Tsk) (u : Tsk.Source)
    (x y : Fin table.size) (a b : Nat) :
    Run table.program (Tsk.observation u) x a y b ↔
      Run (C.installed table).program (T'.observation (C.source u)) x a y b :=
  run_transport_iff (Equiv.refl _) C.literal
    (C.installed_program table) (C.observations u)

set_option backward.isDefEq.respectTransparency false in
/-- Stored halt output and actual halt-ended execution are preserved in both
directions, with no shared terminal epoch required between different sources. -/
theorem corresponding_successful {S' : Type} {T' : Task S' Y letters c}
    (C : TaskCorrespondence Tsk T') (table : InstalledTable Tsk) :
    table.Successful ↔ (C.installed table).Successful := by
  constructor
  · intro hs u'
    let u := C.source.symm u'
    obtain ⟨h,J,row,hh,hr,path⟩ := hs u
    refine ⟨h,J,row,?_,?_,?_⟩
    · rw [C.installed_entry,hh]
    · simpa only [u,Equiv.apply_symm_apply] using hr.trans (C.rows u).symm
    · have mapped := (corresponding_run C table u _ _ _ _).mp path
      simpa only [u,Equiv.apply_symm_apply,C.entry,TaskCorrespondence.installed] using mapped
  · intro hs u
    obtain ⟨h,J,row,hh,hr,path⟩ := hs (C.source u)
    have oldhalt : table.entries.get h = .halt row := by
      have he := C.installed_entry table h
      rw [he] at hh
      cases he : table.entries.get h <;> simp_all
    refine ⟨h,J,row,oldhalt,hr.trans (C.rows u),?_⟩
    apply (corresponding_run C table u _ _ _ _).mpr
    simpa only [C.entry,TaskCorrespondence.installed] using path

/-- Original-source correspondence identifies the two complete synthesis
sentences even with different charts, dimensions, types and rank witnesses. -/
theorem corresponding_budget {S' : Type} {charts' types' q' : Nat}
    {T' : Task S' Y letters c} (C : TaskCorrespondence Tsk T')
    (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q)
    (P' : Presentation T' charts' types') (M' : ReachedTransport T' q') (K : Nat) :
    (Psi P M K).Realize (Fin.elim0 : Fin 0 → Nat) ↔
      (Psi P' M' K).Realize (Fin.elim0 : Fin 0 → Nat) := by
  have forward {S0 S1 : Type} {a0 b0 q0 a1 b1 q1 : Nat}
      {T0 : Task S0 Y letters c} {T1 : Task S1 Y letters c}
      (C0 : TaskCorrespondence T0 T1)
      (P0 : Presentation T0 a0 b0) (M0 : ReachedTransport T0 q0)
      (P1 : Presentation T1 a1 b1) (M1 : ReachedTransport T1 q1)
      (hp : (Psi P0 M0 K).Realize (Fin.elim0 : Fin 0 → Nat)) :
      (Psi P1 M1 K).Realize (Fin.elim0 : Fin 0 → Nat) := by
    cases ht : synthesize P0 M0 K with
    | none => exact False.elim ((scan_none P0 M0 K).mp ht hp)
    | some table =>
      have facts := synthesize_sound P0 M0 K table ht
      have transferred := (corresponding_successful C0 table).mp facts.2.1
      exact successful_budget P1 M1 (literalTable (C0.installed table)) K
        (by change Fintype.card (Fin table.size) ≤ K
            rw [Fintype.card_fin]
            exact facts.1)
        (literal_table_successful _ transferred)
  exact ⟨forward C P M P' M', forward C.symm P' M' P M⟩

#print axioms successful_feasible
#print axioms successful_budget
#print axioms synthesize
#print axioms synthesize_sound
#print axioms synthesize_none_iff
#print axioms corresponding_run
#print axioms corresponding_successful
#print axioms corresponding_budget
#print axioms installCandidate
#print axioms install_candidate_correct
#print axioms install_candidate_exists_iff
#print axioms install_candidate_none_iff
end D5.S3.ObserverMemory.Algorithms.UniformDescriptorInstallation
