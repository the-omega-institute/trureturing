/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.sourceCell; instance=D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.wholeTerm
   digest: Finite feasible cells cover the entire actual old-row and mixed-epoch-history fiber. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
import D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicRecutting

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeHistoryCells

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address)
open ActualCutPartitionRecovery
open NativeDepthPatterns (Pattern Frontier fill depthEquiv History Consistent)
open NativeCutFibers (labels Classes LegalValues extend rowFiberEquiv)
open NativeGroundSeparation (Term evaluate simultaneous_ground_separation)
open NativeSymbolicRecutting

abbrev Patterns (C : LiteralRow) (d : Nat) := Classes C → Pattern d
abbrev Variables {C : LiteralRow} {d : Nat} (η : Patterns C d) := Σ b : Classes C, Frontier (η b)

/-- The class coordinate belongs to the variable name, so every occurrence of
one old class uses exactly the same variables. Distinct names may have equal values. -/
def patternTerm {X : Type} : {d : Nat} → (p : Pattern d) → (Frontier p → X) → Term X
  | 0, _, name => .of (.inr (name ()))
  | _ + 1, .inl b, _ => .of (.inl b)
  | _ + 1, .inr p, name => .mul (patternTerm p.1 (fun x => name (.inl x)))
      (patternTerm p.2 (fun x => name (.inr x)))

theorem pattern_evaluate {X : Type} (d : Nat) (p : Pattern d)
    (name : Frontier p → X) (v : X → Source) :
    evaluate v (patternTerm p name) = fill p (v ∘ name) := by
  induction d with
  | zero => rfl
  | succ d ih => cases p with
    | inl b => rfl
    | inr p => exact congrArg₂ FreeMagma.mul (ih p.1 _) (ih p.2 _)

theorem pattern_deep {X : Type} (d D : Nat) (p : Pattern d)
    (name : Frontier p → X) (a : Address) (bound : D ≤ a.length + d) :
    DeepAt D a (patternTerm p name) := by
  induction d generalizing a with
  | zero => exact bound
  | succ d ih => cases p with
    | inl b => trivial
    | inr p =>
        exact ⟨ih p.1 _ (a ++ [false]) (by simp only [List.length_append, List.length_singleton]; omega),
          ih p.2 _ (a ++ [true]) (by simp only [List.length_append, List.length_singleton]; omega)⟩

def oldTerm {C : LiteralRow} {d : Nat} (η : Patterns C d) (b : Classes C) : Term (Variables η) :=
  patternTerm (η b) (fun x => ⟨b,x⟩)

def oldValues {C : LiteralRow} {d : Nat} (η : Patterns C d) (v : Variables η → Source) :
    Classes C → Source := fun b => fill (η b) (fun x => v ⟨b,x⟩)

theorem oldTerm_evaluate {C : LiteralRow} {d : Nat} (η : Patterns C d)
    (v : Variables η → Source) (b : Classes C) : evaluate v (oldTerm η b) = oldValues η v b :=
  pattern_evaluate d (η b) _ v

/-- The entire retained row, with repeated old classes expanded synchronously. -/
def wholeTerm {C : LiteralRow} {d : Nat} (η : Patterns C d) : Term (Variables η) :=
  FreeMagma.lift (fun b => match b with
    | .inl b => .of (.inl b)
    | .inr n => if h : n ∈ labels C then oldTerm η ⟨n,h⟩ else .of (.inl true)) C

theorem whole_evaluate {C : LiteralRow} {d : Nat} (η : Patterns C d)
    (v : Variables η → Source) :
    evaluate v (wholeTerm η) = evaluateRow (extend C (oldValues η v)) C := by
  have general (t : LiteralRow) :
      evaluate v (FreeMagma.lift (fun b => match b with
        | .inl b => .of (.inl b)
        | .inr n => if h : n ∈ labels C then oldTerm η ⟨n,h⟩ else .of (.inl true)) t) =
      evaluateRow (extend C (oldValues η v)) t := by
    induction t with
    | of b => cases b with
      | inl b => rfl
      | inr n =>
          change evaluate v (if h : n ∈ labels C then oldTerm η ⟨n,h⟩ else .of (.inl true)) =
            extend C (oldValues η v) n
          by_cases hn : n ∈ labels C
          · rw [dif_pos hn, extend, dif_pos hn]; exact oldTerm_evaluate η v ⟨n,hn⟩
          · rw [dif_neg hn, extend, dif_neg hn]; rfl
    | mul l r ihl ihr => exact congrArg₂ FreeMagma.mul ihl ihr
  exact general C

private theorem whole_deep {C : LiteralRow} {d : Nat} (η : Patterns C d) :
    DeepAt d [] (wholeTerm η) := by
  have general (t : LiteralRow) (a : Address) :
      DeepAt d a (FreeMagma.lift (fun b => match b with
        | .inl b => .of (.inl b)
        | .inr n => if h : n ∈ labels C then oldTerm η ⟨n,h⟩ else .of (.inl true)) t) := by
    induction t generalizing a with
    | of b => cases b with
      | inl b => trivial
      | inr n =>
          by_cases hn : n ∈ labels C
          · simpa only [FreeMagma.lift_of, dif_pos hn, oldTerm] using
              pattern_deep (X := Variables η) d d (η ⟨n,hn⟩) (fun x => ⟨⟨n,hn⟩,x⟩) a (by omega)
          · simp [hn, DeepAt]
    | mul l r ihl ihr => exact ⟨ihl _, ihr _⟩
  exact general C []

/-- Exactly the native depth SLH.74.2; epochs do not enter it. -/
def requiredDepth (Q : CutSet) (H : History) : Nat :=
  1 + max (cutDepth Q) ((H.map (fun e => e.2.1)).toFinset.sup List.length)

theorem required_bounds (Q : CutSet) (H : History) :
    (∀ q ∈ Q, q.length < requiredDepth Q H) ∧
    (∀ e ∈ H, e.2.1.length < requiredDepth Q H) := by
  constructor
  · intro q hq
    have h := Finset.le_sup (f := List.length) hq
    change q.length < 1 + max (cutDepth Q) _
    dsimp [cutDepth] at *
    omega
  · intro e he
    have mem : e.2.1 ∈ (H.map (fun e => e.2.1)).toFinset := by
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e,he,rfl⟩)
    have h := Finset.le_sup (f := List.length) mem
    change e.2.1.length < 1 + max _ _
    omega

abbrev RawCell (C : LiteralRow) (d : Nat) := Σ η : Patterns C d, Variables η → Source

def rawValues {C : LiteralRow} {d : Nat} (x : RawCell C d) : Classes C → Source :=
  oldValues x.1 x.2

def splitValues (C : LiteralRow) (d : Nat) (values : Classes C → Source) : RawCell C d :=
  ⟨fun b => (depthEquiv d (values b)).1,
    fun x => (depthEquiv d (values x.1)).2 x.2⟩

private theorem raw_split (C : LiteralRow) (d : Nat) (values : Classes C → Source) :
    rawValues (splitValues C d values) = values := by
  funext b
  exact (depthEquiv d).left_inv (values b)

private theorem raw_injective (C : LiteralRow) (d : Nat) :
    Function.Injective (@rawValues C d) := by
  rintro ⟨η,v⟩ ⟨θ,w⟩ eq
  have shape (b : Classes C) : η b = θ b := by
    have he : (depthEquiv d).symm ⟨η b, fun x => v ⟨b,x⟩⟩ =
        (depthEquiv d).symm ⟨θ b, fun x => w ⟨b,x⟩⟩ := congrFun eq b
    exact congrArg Sigma.fst ((depthEquiv d).symm.injective he)
  have shapes : η = θ := funext shape
  subst θ
  have vals : v = w := by
    funext x
    have he := congrFun eq x.1
    change fill (η x.1) (fun z => v ⟨x.1,z⟩) = fill (η x.1) (fun z => w ⟨x.1,z⟩) at he
    have av := (NativeDepthPatterns.frontier_geometry d (η x.1)).2.1
      (fun z => v ⟨x.1,z⟩) x.2
    have aw := (NativeDepthPatterns.frontier_geometry d (η x.1)).2.1
      (fun z => w ⟨x.1,z⟩) x.2
    rw [he] at av
    exact Option.some.inj (av.symm.trans aw)
  subst w
  rfl

/-- Exact inverse decomposition of a finite tuple of old classes. -/
def valuesEquiv (C : LiteralRow) (d : Nat) : RawCell C d ≃ (Classes C → Source) where
  toFun := rawValues
  invFun := splitValues C d
  left_inv x := raw_injective C d (raw_split C d (rawValues x))
  right_inv := raw_split C d

/-- The fixed filling serves only the invariant history calculation. -/
def testHistory {C : LiteralRow} {d : Nat} (η : Patterns C d) (H : History) : Bool :=
  decide (Consistent H (evaluate (fun _ => .of true) (wholeTerm η)))

/-- All old disequalities are tested, including classes outside the new cones. -/
def syntaxLegal {C : LiteralRow} {d : Nat} (η : Patterns C d) : Prop :=
  ∀ b c : Classes C, b ≠ c → oldTerm η b ≠ oldTerm η c

instance syntaxLegalDecidable {C : LiteralRow} {d : Nat} (η : Patterns C d) :
    Decidable (syntaxLegal η) := inferInstanceAs (Decidable (∀ b c : Classes C,
      b ≠ c → oldTerm η b ≠ oldTerm η c))

def feasible {C : LiteralRow} {d : Nat} (η : Patterns C d) (H : History) : Bool :=
  testHistory η H && decide (syntaxLegal η)

/-- Finite pattern enumeration is source-free; every legal valuation remains in its cell. -/
def feasiblePatterns (C : LiteralRow) (d : Nat) (H : History) : Finset (Patterns C d) :=
  Finset.univ.filter (fun η => feasible η H = true)

def LegalFilling {C : LiteralRow} {d : Nat} (η : Patterns C d) (H : History)
    (v : Variables η → Source) : Prop :=
  Function.Injective (oldValues η v) ∧ Consistent H (evaluate v (wholeTerm η))

private theorem syntax_iff_ground {C : LiteralRow} {d : Nat} (η : Patterns C d) :
    syntaxLegal η ↔ ∃ v : Variables η → Source, Function.Injective (oldValues η v) := by
  classical
  let pairs := ((Finset.univ : Finset (Classes C × Classes C)).toList.filter
    (fun bc => bc.1 ≠ bc.2)).map (fun bc => (oldTerm η bc.1, oldTerm η bc.2))
  have member (b c : Classes C) (hne : b ≠ c) : (oldTerm η b, oldTerm η c) ∈ pairs := by
    apply List.mem_map.mpr
    exact ⟨(b,c), List.mem_filter.mpr ⟨by simp, by simpa using hne⟩, rfl⟩
  constructor
  · intro distinct
    have unequal : ∀ p ∈ pairs, p.1 ≠ p.2 := by
      intro p hp
      obtain ⟨bc,hbc,rfl⟩ := List.mem_map.mp hp
      exact distinct bc.1 bc.2 (by simpa using (List.mem_filter.mp hbc).2)
    obtain ⟨v,hv⟩ := (simultaneous_ground_separation pairs).mp unequal
    refine ⟨v, fun b c eq => ?_⟩
    by_contra hne
    exact hv _ (member b c hne) (by simpa only [oldTerm_evaluate] using eq)
  · rintro ⟨v,inj⟩ b c ne eq
    apply ne
    apply inj
    simpa only [oldTerm_evaluate] using congrArg (evaluate v) eq

/-- Total preprocessing accepts exactly cells with some entire legal valuation.
Contradictory, repeated and absent history reports need no exception path. -/
theorem cell_feasibility_exact {C : LiteralRow} {d : Nat} (η : Patterns C d) (H : History)
    (bound : ∀ e ∈ H, e.2.1.length < d) :
    feasible η H = true ↔ ∃ v : Variables η → Source, LegalFilling η H v := by
  rw [feasible, Bool.and_eq_true, decide_eq_true_eq, syntax_iff_ground]
  have history (v : Variables η → Source) : testHistory η H = true ↔
      Consistent H (evaluate v (wholeTerm η)) := by
    rw [testHistory, decide_eq_true_eq]
    exact symbolic_history_constant d _ (whole_deep η) H bound _ v
  constructor
  · rintro ⟨hist,v,inj⟩
    exact ⟨v,inj,(history v).mp hist⟩
  · rintro ⟨v,inj,hist⟩
    exact ⟨(history v).mpr hist,v,inj⟩

theorem feasible_history {C : LiteralRow} {d : Nat} (η : Patterns C d)
    (H : History) (bound : ∀ e ∈ H, e.2.1.length < d)
    (pass : feasible η H = true) (v : Variables η → Source) :
    Consistent H (evaluate v (wholeTerm η)) := by
  have test : testHistory η H = true := by
    have both : testHistory η H = true ∧ decide (syntaxLegal η) = true := by
      simpa only [feasible, Bool.and_eq_true] using pass
    exact both.1
  have hist : Consistent H (evaluate (fun _ => .of true) (wholeTerm η)) :=
    of_decide_eq_true test
  exact (symbolic_history_constant d _ (whole_deep η) H bound _ v).mp hist

/-- Coproduct over feasible finite patterns, each carrying its whole legal fiber. -/
abbrev Cell (C : LiteralRow) (d : Nat) (H : History) :=
  Σ η : {η : Patterns C d // η ∈ feasiblePatterns C d H},
    {v : Variables η.val → Source // Function.Injective (oldValues η.val v)}

abbrev ActualFiber (P : CutSet) (C : LiteralRow) (H : History) :=
  {u : Source // canonicalRow P u = C ∧ Consistent H u}

/-- Actual source reconstructed from one entire legal cell valuation. -/
def cellSource (P : CutSet) (hP : CutPrefixFree P) (u : Source) (d : Nat) (H : History)
    (bound : ∀ e ∈ H, e.2.1.length < d)
    (x : Cell (canonicalRow P u) d H) : ActualFiber P (canonicalRow P u) H :=
  ⟨evaluate x.2.val (wholeTerm x.1.val), by
    constructor
    · rw [whole_evaluate]
      exact NativeCutFibers.legal_values_row P hP u ⟨_,x.2.property⟩
    · exact feasible_history x.1.val H bound
        (by simpa only [feasiblePatterns, Finset.mem_filter, Finset.mem_univ, true_and]
          using x.1.property) x.2.val⟩

/-- Explicit source-to-cell inverse: recover every old class, then take its
unique depth pattern and all of its reached frontier subtrees. -/
def sourceCell (P : CutSet) (hP : CutPrefixFree P) (u : Source) (d : Nat) (H : History)
    (bound : ∀ e ∈ H, e.2.1.length < d) (s : ActualFiber P (canonicalRow P u) H) :
    Cell (canonicalRow P u) d H := by
  let values := (rowFiberEquiv P hP u).symm ⟨s.val,s.property.1⟩
  let raw := (valuesEquiv (canonicalRow P u) d).symm values.val
  have rv : oldValues raw.1 raw.2 = values.val := (valuesEquiv _ d).apply_symm_apply values.val
  have source : evaluate raw.2 (wholeTerm raw.1) = s.val := by
    rw [whole_evaluate, rv]
    exact congrArg Subtype.val ((rowFiberEquiv P hP u).apply_symm_apply ⟨s.val,s.property.1⟩)
  have legal : LegalFilling raw.1 H raw.2 :=
    ⟨by rw [rv]; exact values.property, by rw [source]; exact s.property.2⟩
  have feas := (cell_feasibility_exact raw.1 H bound).mpr ⟨raw.2,legal⟩
  exact ⟨⟨raw.1, by simp [feasiblePatterns, feas]⟩,⟨raw.2,legal.1⟩⟩

private theorem sourceCell_right (P : CutSet) (hP : CutPrefixFree P) (u : Source)
    (d : Nat) (H : History) (bound : ∀ e ∈ H, e.2.1.length < d)
    (s : ActualFiber P (canonicalRow P u) H) :
    cellSource P hP u d H bound (sourceCell P hP u d H bound s) = s := by
  apply Subtype.ext
  change evaluate (splitValues (canonicalRow P u) d
    ((rowFiberEquiv P hP u).symm ⟨s.val,s.property.1⟩).val).2
    (wholeTerm (splitValues (canonicalRow P u) d
      ((rowFiberEquiv P hP u).symm ⟨s.val,s.property.1⟩).val).1) = s.val
  rw [whole_evaluate, show oldValues _ _ = _ from raw_split _ _ _]
  exact congrArg Subtype.val ((rowFiberEquiv P hP u).apply_symm_apply ⟨s.val,s.property.1⟩)

private theorem cellSource_injective (P : CutSet) (hP : CutPrefixFree P) (u : Source)
    (d : Nat) (H : History) (bound : ∀ e ∈ H, e.2.1.length < d) :
    Function.Injective (cellSource P hP u d H bound) := by
  rintro ⟨⟨η,he⟩,⟨v,hv⟩⟩ ⟨⟨θ,hf⟩,⟨w,hw⟩⟩ eq
  have src := congrArg Subtype.val eq
  change evaluate v (wholeTerm η) = evaluate w (wholeTerm θ) at src
  rw [whole_evaluate,whole_evaluate] at src
  have vals : (⟨oldValues η v,hv⟩ : LegalValues (canonicalRow P u)) =
      ⟨oldValues θ w,hw⟩ := (rowFiberEquiv P hP u).injective (Subtype.ext src)
  have raw : (⟨η,v⟩ : RawCell (canonicalRow P u) d) = ⟨θ,w⟩ :=
    (valuesEquiv _ d).injective (congrArg Subtype.val vals)
  cases raw
  rfl

/-- SLH.74.8: the exact coproduct of entire feasible legal valuation fibers
and all actual original sources consistent with the retained complete row and H.
No nonemptiness premise is needed; contradictory histories give empty fibers. -/
def historyCellEquiv (P : CutSet) (hP : CutPrefixFree P) (u : Source) (Q : CutSet) (H : History) :
    Cell (canonicalRow P u) (requiredDepth Q H) H ≃ ActualFiber P (canonicalRow P u) H where
  toFun := cellSource P hP u (requiredDepth Q H) H (required_bounds Q H).2
  invFun := sourceCell P hP u (requiredDepth Q H) H (required_bounds Q H).2
  left_inv x := cellSource_injective P hP u (requiredDepth Q H) H (required_bounds Q H).2
    (sourceCell_right P hP u (requiredDepth Q H) H (required_bounds Q H).2 _)
  right_inv := sourceCell_right P hP u (requiredDepth Q H) H (required_bounds Q H).2

/-- The full record and its fieldwise actual-source bridges, before filling
can expose any additional physical address. -/
structure Recutting {C : LiteralRow} {d : Nat} (η : Patterns C d)
    (v : Variables η → Source) (Q : CutSet) where
  record : ActualCutPartitionDecoder.HoleExterior × Finset (Address × Address)
  symbolic : record = symbolicRecord Q (wholeTerm η) v
  actual : record = ActualCutPartitionDecoder.literalRecord Q (evaluate v (wholeTerm η))
  ordering : orderedHoles Q (evaluate v (wholeTerm η)) = symbolicOrdered Q (wholeTerm η)
  subtrees : ∀ q ∈ Q, ActualLeafHistoryRigidity.subtree q (evaluate v (wholeTerm η)) =
    (termAt q (wholeTerm η)).map (evaluate v)

/-- SLH.74.9, specialized to the actual whole-cell terms, with no externally
supplied factorization or row-equivalence premise. -/
def recutCell {C : LiteralRow} (Q : CutSet) (H : History) (hQ : CutPrefixFree Q)
    (η : Patterns C (requiredDepth Q H)) (v : Variables η → Source) : Recutting η v Q := by
  have exactCut := symbolic_recut_exact (requiredDepth Q H) Q hQ (required_bounds Q H).1
    (wholeTerm η) (whole_deep η) v
  exact ⟨symbolicRecord Q (wholeTerm η) v, rfl, exactCut.2.2.2.symm, exactCut.1, exactCut.2.2.1⟩

end D5.S3.Arith.FibonacciAtomic.Observer.NativeHistoryCells
