/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeRepeatedPartnerControllers
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/NativeRepeatedPartnerControllers
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Acquired class roots install fixed whole-row finite controllers on the full repeated-partner origin fiber. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceMoore
import D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteRootMinimax

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeRepeatedPartnerControllers
open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualCutPartitionRecovery
open NativeCutFibers
open NativeClassRootImage
open NativeFullRootFeasibility
open NativeFiniteRootMinimax
open NativeSixSourceCones
open NativeSixSourceMoore (Controller Run)

attribute [local instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

private def ordinal : Fin 6 → Nat := ![0,1,3,4,5,7]
def coord (i : Fin 6) : Classes row := ⟨ordinal i,by fin_cases i <;> decide⟩
def index (d : Classes row) : Fin 6 :=
  if d.val = 0 then 0 else if d.val = 1 then 1 else if d.val = 3 then 2
  else if d.val = 4 then 3 else if d.val = 5 then 4 else 5
def inflate (θ : Fin 6 → Option Bool) (d : Classes row) : Option Bool := θ (index d)

theorem coord_index (d : Classes row) : coord (index d) = d := by
  apply Subtype.ext
  have hd := d.property
  simp only [row,labels,Finset.mem_union,Finset.mem_singleton] at hd
  rcases hd with ((h | h) | (h | h)) | ((h | h) | (h | h)) <;>
    simp_all [coord,index,ordinal]

def queryAddress : Fin 5 → Address :=
  ![position 0,position 1,position 3,position 5,position 7]
def queryCoord : Fin 5 → Fin 6 := ![0,1,2,4,5]
def replies (θ : Fin 6 → Option Bool) (j : Fin 5) : Reply :=
  NativeClassRootPadding.rootReply (θ (queryCoord j))
def acquiredLabel (θ : Fin 6 → Option Bool) : Fin 5 :=
  if θ 1 = some true then 1 else if θ 2 = some true then 2
  else if θ 4 = some true then 3 else if θ 5 = some true then 4 else 0

private theorem mask_by_label : ∀ θ : Fin 6 → Option Bool,
    Admissible row (inflate θ) →
    computedOldMask row (inflate θ) = (holeList (acquiredLabel θ)).toFinset := by
  simp only [← admissibleCode_spec]
  decide +kernel

private theorem decoder_holes (j : Fin 5) :
    ActualCutPartitionDecoder.decoderHoles (holeList j).toFinset row = holeList j := by
  unfold ActualCutPartitionDecoder.decoderHoles
  have filter_eq : ((holeList j).toFinset.filter (fun q => (rowAt q row).isSome)) =
      (holeList j).toFinset := by revert j; decide +kernel
  rw [filter_eq]
  apply (List.toFinset_sort _ (by revert j; decide +kernel)).mpr
  revert j
  decide +kernel

private theorem target_by_mask (j : Fin 5) :
    (NativePredecessorRowRecovery.back row (holeList j).toFinset).getD (.of (.inl true)) =
      predecessor j := by
  unfold NativePredecessorRowRecovery.back NativePredecessorRowRecovery.repair
  simp only [row, NativePredecessorRowRecovery.repairAt,
    ActualCutPartitionDecoder.decoderClass]
  have holes := decoder_holes j
  dsimp only [row] at holes
  simp only [holes]
  fin_cases j <;> decide +kernel

theorem type_finite_row (θ : Fin 6 → Option Bool)
    (ad : Admissible row (inflate θ)) :
    computedTarget row (inflate θ) = predecessor (acquiredLabel θ) := by
  rw [computedTarget,mask_by_label θ ad]
  exact target_by_mask _

/-- A stationary finite table before its literal address installation. -/
structure Table (n : Nat) where
  ask : Fin n → Fin 5
  next : Fin n → Reply → Fin n ⊕ Fin 5

def installed {n : Nat} (T : Table n) : Controller (Fin n) (Fin 5) where
  addr s := queryAddress (T.ask s)
  next := T.next
  out := predecessor

def evaluate {n : Nat} (T : Table n) (θ : Fin 6 → Option Bool) :
    Nat → Fin n ⊕ Fin 5 → Option (Fin 5 × List (Fin n))
  | 0, .inl _ => none
  | 0, .inr h => some (h,[])
  | k+1, .inr h => some (h,[])
  | k+1, .inl s => (evaluate T θ k (T.next s (replies θ (T.ask s)))).map
      (fun p => (p.1,s::p.2))

def ten : Table 5 where
  ask := id
  next s y := match s.val with
    | 0 => match y with
      | .beta => .inl 1 | .branch => .inl 3 | _ => .inr 0
    | 1 => if y = .alpha then .inr 1 else .inl 2
    | 2 => if y = .alpha then .inr 2 else .inr 0
    | 3 => if y = .alpha then .inr 3 else .inl 4
    | _ => if y = .alpha then .inr 4 else .inr 0

def nine : Table 4 where
  ask s := ⟨s.val+1,by omega⟩
  next s y := if y = .alpha then .inr ⟨s.val+1,by omega⟩
    else if h : s.val < 3 then .inl ⟨s.val+1,by omega⟩ else .inr 0

def eight : Table 3 where
  ask s := ⟨s.val+1,by omega⟩
  next s y := match s.val with
    | 0 => if y = .alpha then .inr 1 else .inl 1
    | 1 => if y = .alpha then .inr 2 else .inr 0
    | _ => if y = .alpha then .inr 3 else .inr 4

def seven : Table 2 where
  ask s := if s.val = 0 then 1 else 3
  next s y := if s.val = 0 then
      if y = .alpha then .inr 1 else .inr 2
    else if y = .alpha then .inr 3 else .inr 4

def six : Table 1 where
  ask _ := 3
  next _ y := if y = .alpha then .inr 3 else .inr 4

def five : Table 0 where
  ask s := Fin.elim0 s
  next s := Fin.elim0 s

def entryEight (h : Fin 5) : Fin 3 ⊕ Fin 5 :=
  if h.val ≤ 2 then .inl 0 else .inl 2
def entrySeven (h : Fin 5) : Fin 2 ⊕ Fin 5 :=
  if h = 0 then .inr 0 else if h.val ≤ 2 then .inl 0 else .inl 1
def entrySix (h : Fin 5) : Fin 1 ⊕ Fin 5 :=
  if h.val ≤ 2 then .inr h else .inl 0

def FiniteCorrect {n : Nat} (T : Table n) (entry : Fin 5 → Fin n ⊕ Fin 5)
    (q : Nat) (θ : Fin 6 → Option Bool) : Prop :=
  (match evaluate T θ q (entry (acquiredLabel θ)) with
  | none => false
  | some p => decide (p.1 = acquiredLabel θ ∧ p.2.length ≤ q)) = true


set_option maxHeartbeats 1600000 in
private theorem finite_controllers : ∀ θ : Fin 6 → Option Bool,
    Admissible row (inflate θ) →
    FiniteCorrect ten (fun _ => .inl 0) 3 θ ∧
    FiniteCorrect nine (fun _ => .inl 0) 4 θ ∧
    FiniteCorrect eight entryEight 2 θ ∧
    FiniteCorrect seven entrySeven 1 θ ∧
    FiniteCorrect six entrySix 1 θ ∧
    FiniteCorrect five Sum.inr 0 θ := by
  simp only [← admissibleCode_spec]
  unfold FiniteCorrect
  decide +kernel


private theorem root_reply (t : Source) :
    readout [] t = NativeClassRootPadding.rootReply (rootType t) := by
  cases t with
  | of b => cases b <;> rfl
  | mul l r => rfl

noncomputable def profile (x : Fiber) : Fin 6 → Option Bool :=
  fun i => types row (recover P NativeSixSourceCones.prefix_free row ⟨substitution x.val,x.property⟩).val (coord i)

private theorem actual_profile (x : Fiber) :
    Admissible row (inflate (profile x)) ∧
      (∀ j : Fin 5, readout (queryAddress j) (substitution x.val) = replies (profile x) j) ∧
      computedTarget row (inflate (profile x)) = canonicalRow P x.val := by
  let w : RowFiber P row := ⟨substitution x.val,x.property⟩
  let v : ImageValues row :=
    ⟨recover P NativeSixSourceCones.prefix_free row w,⟨x.val,(recover_fill P NativeSixSourceCones.prefix_free row w).symm⟩⟩
  have fill : substitution x.val = evaluateRow (extend row v.val.val) row :=
    (recover_fill P NativeSixSourceCones.prefix_free row w).symm
  let θ : Fin 6 → Option Bool := fun i => types row v.val.val (coord i)
  have inflate_eq : inflate θ = types row v.val.val := by
    funext d
    exact congrArg (types row v.val.val) (coord_index d)
  have actualTypes : ∀ v : ImageValues row, Admissible row (types row v.val.val) := by
    rw [← (six_source_realization.1 0).2.1]
    exact actual_type P NativeSixSourceCones.prefix_free (current 0)
  change Admissible row (inflate θ) ∧ _ ∧ computedTarget row (inflate θ) = _
  refine ⟨by rw [inflate_eq]; exact actualTypes v,?_,?_⟩
  · intro j
    rw [fill]
    have atRoot : readout (queryAddress j) (evaluateRow (extend row v.val.val) row) =
        readout [] (v.val.val (coord (queryCoord j))) := by
      fin_cases j <;> rfl
    rw [atRoot]
    exact root_reply _
  · rw [inflate_eq,(finite_root_minimax row []).2.2.2.2.2]
    have refrow : canonicalRow P (substitution (origin 0)) = row := by
      rw [(six_source_realization.1 0).1]
      exact (six_source_realization.1 0).2.1
    have bridge := native_full_root_feasibility P NativeSixSourceCones.prefix_free (origin 0) 1 0 (by decide)
    dsimp only at bridge
    rw [refrow] at bridge
    exact (bridge.1 v x fill).2.2

private theorem evaluate_sound {n : Nat} (T : Table n) (θ : Fin 6 → Option Bool)
    (t : Source) (reads : ∀ j, readout (queryAddress j) t = replies θ j)
    {q : Nat} {k : Fin n ⊕ Fin 5} {p : Fin 5 × List (Fin n)}
    (ev : evaluate T θ q k = some p) :
    Run (installed T) t k p.2 p.1 := by
  induction q generalizing k p with
  | zero =>
      cases k with
      | inl s => simp [evaluate] at ev
      | inr h =>
          have hp : (h,[]) = p := Option.some.inj ev
          subst p
          exact Run.halt h
  | succ q ih =>
      cases k with
      | inr h =>
          have hp : (h,[]) = p := Option.some.inj ev
          subst p
          exact Run.halt h
      | inl s =>
          cases tail : evaluate T θ q (T.next s (replies θ (T.ask s))) with
          | none => simp [evaluate,tail] at ev
          | some p' =>
              have hp : (p'.1,s::p'.2) = p := by simpa [evaluate,tail] using ev
              subst p
              have run := ih tail
              apply Run.read s
              simpa only [installed,reads] using run

/-- Full-fiber success, charging every running visit and returning the entire
fixed predecessor row directly from the terminal state. -/
def Succeeds {n : Nat} (T : Table n) (entry : Fin 5 → Fin n ⊕ Fin 5)
    (q : Nat) : Prop :=
  ∀ x : Fiber, ∃ (h : Fin 5) (tr : List (Fin n)),
    Run (installed T) (substitution x.val) (entry (acquiredLabel (profile x))) tr h ∧
    predecessor h = canonicalRow P x.val ∧ tr.length ≤ q

theorem install_correct {n : Nat} (T : Table n)
    (entry : Fin 5 → Fin n ⊕ Fin 5) (q : Nat)
    (finite : ∀ θ, Admissible row (inflate θ) → FiniteCorrect T entry q θ) :
    Succeeds T entry q := by
  intro x
  obtain ⟨ad,reads,target⟩ := actual_profile x
  have proof := finite (profile x) ad
  cases ev : evaluate T (profile x) q (entry (acquiredLabel (profile x))) with
  | none => simp [FiniteCorrect,ev] at proof
  | some p =>
      have hp : p.1 = acquiredLabel (profile x) ∧ p.2.length ≤ q := by
        simpa only [FiniteCorrect,ev,decide_eq_true_eq] using proof
      exact ⟨p.1,p.2,evaluate_sound T _ (substitution x.val) reads ev,
        (congrArg predecessor hp.1).trans ((type_finite_row _ ad).symm.trans target),hp.2⟩


private theorem profile_actual (z : Fin 6) : acquiredLabel (profile (actual z)) = label z := by
  apply six_source_realization.2
  exact (type_finite_row _ (actual_profile (actual z)).1).symm.trans
    ((actual_profile (actual z)).2.2.trans (six_source_realization.1 z).2.2)

private theorem label_surjective : Function.Surjective (fun x : Fiber => acquiredLabel (profile x)) := by
  intro h
  let chooseSource : Fin 5 → Fin 6 := ![0,2,3,4,5]
  refine ⟨actual (chooseSource h),?_⟩
  change acquiredLabel (profile (actual (chooseSource h))) = h
  rw [profile_actual]
  have eq : ∀ h : Fin 5, label (chooseSource h) = h := by decide +kernel
  exact eq h

/-- The exported value is the entire entry state. Its realized alphabet is
exactly this finite set, so inclusion is a recoverable entry normalization. -/
def Exports {n : Nat} (entry : Fin 5 → Fin n ⊕ Fin 5) (r : Nat) : Prop :=
  ∃ E : Finset (Fin n ⊕ Fin 5), E.card = r ∧
    Set.range (fun x : Fiber => entry (acquiredLabel (profile x))) = (E : Set (Fin n ⊕ Fin 5))

private theorem exports_of_card {n : Nat} (entry : Fin 5 → Fin n ⊕ Fin 5) (r : Nat)
    (card : (Finset.univ.image entry).card = r) : Exports entry r := by
  refine ⟨Finset.univ.image entry,card,?_⟩
  ext k
  constructor
  · rintro ⟨x,rfl⟩
    exact Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩
  · intro hk
    obtain ⟨h,_,eq⟩ := Finset.mem_image.mp hk
    obtain ⟨x,hx⟩ := label_surjective h
    exact ⟨x,(congrArg entry hx).trans eq⟩

private def exampleType (z : Fin 6) (i : Fin 6) : Option Bool := rootType (values z i)
private theorem example_reads : ∀ (z : Fin 6) (j : Fin 5),
    readout (queryAddress j) (current z) = replies (exampleType z) j := by decide +kernel

private theorem example_run {n : Nat} (T : Table n) (entry : Fin 5 → Fin n ⊕ Fin 5)
    (z : Fin 6) (q : Nat) (p : Fin 5 × List (Fin n))
    (ev : evaluate T (exampleType z) q (entry (label z)) = some p) :
    Run (installed T) (substitution (actual z).val)
      (entry (acquiredLabel (profile (actual z)))) p.2 p.1 := by
  rw [profile_actual]
  change Run (installed T) (substitution (origin z)) _ _ _
  rw [(six_source_realization.1 z).1]
  exact evaluate_sound T _ _ (example_reads z) ev

private abbrev Visits {n : Nat} (k : Fin n ⊕ Fin 5) (p : Fin 5 × List (Fin n)) : Prop :=
  k ∈ p.2.map Sum.inl ++ [Sum.inr p.1]

private instance visitsDecidable {n : Nat} (k : Fin n ⊕ Fin 5) (p : Fin 5 × List (Fin n)) :
    Decidable (Visits k p) := by
  cases k with
  | inl s => exact decidable_of_iff (s ∈ p.2) (by simp [Visits])
  | inr h => exact decidable_of_iff (h = p.1) (by simp [Visits])

/-- All named running and halting states are reached on actual origins. -/
def Reached {n : Nat} (T : Table n) (entry : Fin 5 → Fin n ⊕ Fin 5) : Prop :=
  ∀ k : Fin n ⊕ Fin 5, ∃ (x : Fiber) (h : Fin 5) (tr : List (Fin n)),
    Run (installed T) (substitution x.val) (entry (acquiredLabel (profile x))) tr h ∧
    Visits k (h,tr)

private theorem reached_of_finite {n : Nat} (T : Table n)
    (entry : Fin 5 → Fin n ⊕ Fin 5) (q : Nat)
    (finite : ∀ k : Fin n ⊕ Fin 5, ∃ z : Fin 6,
      (match evaluate T (exampleType z) q (entry (label z)) with
      | none => false | some p => decide (Visits k p)) = true) : Reached T entry := by
  intro k
  obtain ⟨z,hz⟩ := finite k
  cases ev : evaluate T (exampleType z) q (entry (label z)) with
  | none => simp [ev] at hz
  | some p =>
      exact ⟨actual z,p.1,p.2,example_run T entry z q p ev,by simpa only [ev,decide_eq_true_eq] using hz⟩

/-- The invocation maximum is attained by one actual finite origin. -/
def Worst {n : Nat} (T : Table n) (entry : Fin 5 → Fin n ⊕ Fin 5) (q : Nat) : Prop :=
  ∃ (x : Fiber) (h : Fin 5) (tr : List (Fin n)),
    Run (installed T) (substitution x.val) (entry (acquiredLabel (profile x))) tr h ∧
    predecessor h = canonicalRow P x.val ∧ tr.length = q

private theorem worst_of_finite {n : Nat} (T : Table n)
    (entry : Fin 5 → Fin n ⊕ Fin 5) (q : Nat)
    (finite : ∃ z : Fin 6,
      (match evaluate T (exampleType z) q (entry (label z)) with
      | none => false | some p => decide (p.1 = label z ∧ p.2.length = q)) = true) : Worst T entry q := by
  obtain ⟨z,hz⟩ := finite
  cases ev : evaluate T (exampleType z) q (entry (label z)) with
  | none => simp [ev] at hz
  | some p =>
      have hp : p.1 = label z ∧ p.2.length = q := by simpa only [ev,decide_eq_true_eq] using hz
      exact ⟨actual z,p.1,p.2,example_run T entry z q p ev,
        by rw [hp.1]; exact (six_source_realization.1 z).2.2.symm,hp.2⟩

/-- Exact attained export and call counts, complete whole-row correctness,
and reachability of every state in the finite disjoint running/halt set. -/
def Attains {n : Nat} (T : Table n) (entry : Fin 5 → Fin n ⊕ Fin 5) (r q : Nat) : Prop :=
  Exports entry r ∧ Succeeds T entry q ∧ Worst T entry q ∧ Reached T entry

/-- These six fixed common controllers attain the complete original table
on every actual origin, including all target-zero beta placements. -/
theorem matching_controllers :
    Attains ten (fun _ => .inl 0) 1 3 ∧
    Attains nine (fun _ => .inl 0) 1 4 ∧
    Attains eight entryEight 2 2 ∧
    Attains seven entrySeven 3 1 ∧
    Attains six entrySix 4 1 ∧
    Attains five Sum.inr 5 0 := by
  have a := fun θ ad => (finite_controllers θ ad)
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  all_goals
    refine ⟨exports_of_card _ _ (by decide +kernel),?_,worst_of_finite _ _ _ (by decide +kernel),
      reached_of_finite _ _ 4 (by decide +kernel)⟩
    apply install_correct
  · exact fun θ ad => (a θ ad).1
  · exact fun θ ad => (a θ ad).2.1
  · exact fun θ ad => (a θ ad).2.2.1
  · exact fun θ ad => (a θ ad).2.2.2.1
  · exact fun θ ad => (a θ ad).2.2.2.2.1
  · exact fun θ ad => (a θ ad).2.2.2.2.2

#print axioms matching_controllers
end D5.S3.Arith.FibonacciAtomic.Observer.NativeRepeatedPartnerControllers
