/- GID: D5/S3/ConceptDynamics/Experiment/PassivePolicyNormalization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Experiment/PassivePolicyNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Passive policy pruning preserves terminal fibers and pathwise costs and yields cardinality minimax recursion. -/

import D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization
attribute [local instance] Classical.propDecidable
universe u v w z
variable {W : Type u} {Q : Type v} {Y : Q → Type w} {L : Type z}
/-- Finite histories retain each query together with its dependent response. -/
abbrev Hist (Y : Q → Type w) := List (Sigma Y)

/-- Fuel-bounded execution returns the additional history and the terminal label. -/
def execute (read : (q : Q) → W → Y q) (policy : Hist Y → Sum Q L) :
    Nat → Hist Y → W → Option (Hist Y × L)
  | 0, _, _ => none
  | n+1, h, x => match policy h with
    | .inr l => some ([], l)
    | .inl q => (execute read policy n (h ++ [⟨q, read q x⟩]) x).map
        (fun p => (⟨q, read q x⟩ :: p.1, p.2))

/-- Candidates producing a specified response to a fixed passive query. -/
noncomputable def fiber (read : (q : Q) → W → Y q) (C : Finset W) (q : Q) (y : Y q) :
    Finset W := by classical exact C.filter (fun x => read q x = y)

/-- Every query strictly decreases candidate cardinality in each response branch. -/
def Pruned (read : (q : Q) → W → Y q) : Finset W → PassiveProtocol Q Y → Prop
  | _, .stop => True
  | C, .query q next => (∀ y, (fiber read C q y).card < C.card) ∧
      ∀ y, Pruned read (fiber read C q y) (next y)

/-- Follow a matching dependent response, stopping on a mismatched query. -/
noncomputable def advance (p : PassiveProtocol Q Y) (a : Sigma Y) : PassiveProtocol Q Y :=
  match p with
  | .stop => .stop
  | .query q next => if e : a.1 = q then next (e ▸ a.2) else .stop

/-- The continuation of a dependent tree after replaying a history. -/
noncomputable def residual (p : PassiveProtocol Q Y) (h : Hist Y) : PassiveProtocol Q Y :=
  h.foldl advance p

/-- A history selector induced by a dependent tree and a terminal decoder. -/
noncomputable def treePolicy (p : PassiveProtocol Q Y) (d : Hist Y → L) (h : Hist Y) : Sum Q L :=
  match residual p h with
  | .stop => .inr (d h)
  | .query q _ => .inl q

/-- The candidate fiber of the complete terminal history of a run. -/
noncomputable def leaf (C : Finset W) (tr : W → Hist Y) (x : W) : Finset W :=
  C.filter (fun y => tr y = tr x)

/-- Actual runs terminate, stop legally on their terminal fiber, and respect the budget. -/
def RawFeasible (read : (q : Q) → W → Y q) (price : Q → Nat)
    (Legal : Finset W → L → Prop) (tp : Finset W → L → Nat)
    (C : Finset W) (B : Nat) (policy : Hist Y → Sum Q L) (tr : W → Hist Y) (lab : W → L) : Prop :=
  (∀ x ∈ C, ∃ n, execute read policy n [] x = some (tr x, lab x)) ∧
  (∀ x ∈ C, Legal (leaf C tr x) (lab x)) ∧
  (∀ x ∈ C, ((tr x).map (fun a => price a.1)).sum + tp (leaf C tr x) (lab x) ≤ B)

/-- Tree labels agree on terminal histories, are legal there, and respect the budget. -/
def TreeFeasible (read : (q : Q) → W → Y q) (price : Q → Nat)
    (Legal : Finset W → L → Prop) (tp : Finset W → L → Nat)
    (C : Finset W) (B : Nat) (p : PassiveProtocol Q Y) (lab : W → L) : Prop :=
  (∀ x ∈ C, ∀ y ∈ C, runPassiveProtocol read p x = runPassiveProtocol read p y → lab x = lab y) ∧
  (∀ x ∈ C, Legal (leaf C (runPassiveProtocol read p) x) (lab x)) ∧
  (∀ x ∈ C, ((runPassiveProtocol read p x).map (fun a => price a.1)).sum +
      tp (leaf C (runPassiveProtocol read p) x) (lab x) ≤ B)

/-- Worst loss over a finite candidate set, with values in the extended nonnegative reals. -/
noncomputable def risk (loss : L → W → ENNReal) (C : Finset W) (lab : W → L) : ENNReal :=
  ⨆ x : C, loss (lab x.val) x.val

/-- Risk infimum over all feasible, pointwise terminating history selectors. -/
noncomputable def rawValue (read : (q : Q) → W → Y q) (price : Q → Nat)
    (Legal : Finset W → L → Prop) (tp : Finset W → L → Nat)
    (loss : L → W → ENNReal) (C : Finset W) (B : Nat) : ENNReal :=
  ⨅ policy, ⨅ tr, ⨅ lab, ⨅ (_ : RawFeasible read price Legal tp C B policy tr lab), risk loss C lab

/-- Risk infimum with an additional bound on actual query counts. -/
noncomputable def horizonValue (read : (q : Q) → W → Y q) (price : Q → Nat)
    (Legal : Finset W → L → Prop) (tp : Finset W → L → Nat)
    (loss : L → W → ENNReal) (C : Finset W) (B H : Nat) : ENNReal :=
  ⨅ policy, ⨅ tr, ⨅ lab, ⨅ (_ : RawFeasible read price Legal tp C B policy tr lab),
    ⨅ (_ : ∀ x ∈ C, (tr x).length ≤ H), risk loss C lab

/-- Feasible dependent trees whose queries strictly decrease candidate cardinality. -/
abbrev Plans (read : (q : Q) → W → Y q) (price : Q → Nat)
    (Legal : Finset W → L → Prop) (tp : Finset W → L → Nat) (C : Finset W) (B : Nat) :=
  {s : PassiveProtocol Q Y × (W → L) //
    TreeFeasible read price Legal tp C B s.1 s.2 ∧ Pruned read C s.1}

/-- Risk infimum over feasible pruned dependent trees. -/
noncomputable def normalValue (read : (q : Q) → W → Y q) (price : Q → Nat)
    (Legal : Finset W → L → Prop) (tp : Finset W → L → Nat)
    (loss : L → W → ENNReal) (C : Finset W) (B : Nat) : ENNReal :=
  ⨅ s : Plans read price Legal tp C B, risk loss C s.val.2

/-- The finite set of responses realized by the current candidates. -/
noncomputable def answers (read : (q : Q) → W → Y q) (C : Finset W) (q : Q) : Finset (Y q) := by
  classical exact C.image (read q)

/-- Risk infimum over affordable legal terminal labels. -/
noncomputable def stopRadius (Legal : Finset W → L → Prop) (tp : Finset W → L → Nat)
    (loss : L → W → ENNReal) (C : Finset W) (B : Nat) : ENNReal :=
  ⨅ l, ⨅ (_ : Legal C l ∧ tp C l ≤ B), risk loss C (fun _ => l)

/-- History selectors together with their actual terminal histories and labels. -/
abbrev RawStrategies (read : (q : Q) → W → Y q) (price : Q → Nat)
    (Legal : Finset W → L → Prop) (tp : Finset W → L → Nat) (C : Finset W) (B : Nat) :=
  {s : (Hist Y → Sum Q L) × (W → Hist Y) × (W → L) //
    RawFeasible read price Legal tp C B s.1 s.2.1 s.2.2}

/-- Worst metric error of the decoded labels over the current candidates. -/
noncomputable def realRisk {Z : Type*} [MetricSpace Z]
    (out : L → Z) (target : W → Z) (C : Finset W) (lab : W → L) : Real :=
  ⨆ x : C, dist (out (lab x.val)) (target x.val)

/-- Real risk infimum over all feasible pointwise terminating selectors. -/
noncomputable def realRawValue {Z : Type*} [MetricSpace Z]
    (read : (q : Q) → W → Y q) (price : Q → Nat)
    (Legal : Finset W → L → Prop) (tp : Finset W → L → Nat)
    (out : L → Z) (target : W → Z) (C : Finset W) (B : Nat) : Real :=
  ⨅ s : RawStrategies read price Legal tp C B, realRisk out target C s.val.2.2

/-- Candidates consistent with every query-response pair in a history. -/
noncomputable def candidates (read : (q : Q) → W → Y q) (C : Finset W) (t : Hist Y) : Finset W :=
  C.filter (fun x => ∀ a ∈ t, read a.1 x = a.2)

/-- Real risk infimum with a bound on actual query counts. -/
noncomputable def realHorizonValue {Z : Type*} [MetricSpace Z]
    (read : (q : Q) → W → Y q) (price : Q → Nat)
    (Legal : Finset W → L → Prop) (tp : Finset W → L → Nat)
    (out : L → Z) (target : W → Z) (C : Finset W) (B H : Nat) : Real :=
  ⨅ s : {s : RawStrategies read price Legal tp C B // ∀ x ∈ C, (s.val.2.1 x).length ≤ H},
    realRisk out target C s.val.val.2.2

/-- Real risk infimum over affordable legal terminal labels. -/
noncomputable def realStopRadius {Z : Type*} [MetricSpace Z]
    (Legal : Finset W → L → Prop) (tp : Finset W → L → Nat)
    (out : L → Z) (target : W → Z) (C : Finset W) (B : Nat) : Real :=
  ⨅ l : {l : L // Legal C l ∧ tp C l ≤ B}, realRisk out target C (fun _ => l.val)

/-- Passive normalization, exact terminal fibers, horizon equality and minimax recursion.
Only actual-world termination is required. Terminal labels, legality and prices
are retained, and the stopping and continuation risk infima need not be attained. -/
theorem result {Z : Type*} [MetricSpace Z] [Finite Q]
    (read : (q : Q) → W → Y q) (price : Q → Nat)
    (Legal : Finset W → L → Prop) (tp : Finset W → L → Nat)
    (out : L → Z) (target : W → Z) (C : Finset W) (hC : C.Nonempty) (B : Nat)
    (freeC : ∃ l, Legal C l ∧ tp C l = 0)
    (freeReply : ∀ q (y : answers read C q),
      ∃ l, Legal (fiber read C q y.val) l ∧ tp (fiber read C q y.val) l = 0) :
    (∀ (policy : Hist Y → Sum Q L),
      (∀ x ∈ C, ∃ n t l, execute read policy n [] x = some (t,l) ∧
        Legal (candidates read C t) l ∧
        (t.map (fun a => price a.1)).sum + tp (candidates read C t) l ≤ B) →
      ∃ (p : PassiveProtocol Q Y) (decode : Hist Y → L),
        Pruned read C p ∧
        (∀ x ∈ C, ∀ n t l, execute read policy n [] x = some (t,l) →
          decode (runPassiveProtocol read p x) = l ∧
          out (decode (runPassiveProtocol read p x)) = out l ∧
          (runPassiveProtocol read p x).Sublist t ∧
          (runPassiveProtocol read p x).length ≤ C.card-1 ∧
          candidates read C (runPassiveProtocol read p x) = candidates read C t ∧
          Legal (candidates read C (runPassiveProtocol read p x)) (decode (runPassiveProtocol read p x)) ∧
          ((runPassiveProtocol read p x).map (fun a => price a.1)).sum +
            tp (candidates read C (runPassiveProtocol read p x)) (decode (runPassiveProtocol read p x)) ≤
              (t.map (fun a => price a.1)).sum + tp (candidates read C t) l ∧
          ((runPassiveProtocol read p x).map (fun a => price a.1)).sum +
            tp (candidates read C (runPassiveProtocol read p x)) (decode (runPassiveProtocol read p x)) ≤ B) ∧
        (∀ x ∈ C, ∀ y ∈ C, ∀ n t l m s k,
          execute read policy n [] x = some (t,l) →
          execute read policy m [] y = some (s,k) →
          (runPassiveProtocol read p x = runPassiveProtocol read p y ↔ t = s))) ∧
    realRawValue read price Legal tp out target C B =
      realHorizonValue read price Legal tp out target C B (C.card-1) ∧
    ENNReal.ofReal (realRawValue read price Legal tp out target C B) =
      min (ENNReal.ofReal (realStopRadius Legal tp out target C B))
        (⨅ q, ⨅ (_ : 2 ≤ (answers read C q).card ∧ price q ≤ B),
          ⨆ y : answers read C q,
            ENNReal.ofReal (realRawValue read price Legal tp out target (fiber read C q y.val) (B-price q))) ∧
    (∀ q, 2 ≤ (answers read C q).card →
      ∀ y : answers read C q, (fiber read C q y.val).card < C.card) ∧
    (let eligible := fun q => 2 ≤ (answers read C q).card ∧ price q ≤ B
     let branch := fun q => ⨆ y : answers read C q,
       rawValue read price Legal tp (fun l x => ENNReal.ofReal (dist (out l) (target x)))
         (fiber read C q y.val) (B-price q)
     ((¬ ∃ q, eligible q) → (⨅ q, ⨅ (_ : eligible q), branch q) = ⊤) ∧
     ((∃ q, eligible q) → ∃ q, eligible q ∧ (⨅ q, ⨅ (_ : eligible q), branch q) = branch q)) ∧
    (ENNReal.ofReal (realRawValue read price Legal tp out target C B) =
       rawValue read price Legal tp (fun l x => ENNReal.ofReal (dist (out l) (target x))) C B ∧
     rawValue read price Legal tp (fun l x => ENNReal.ofReal (dist (out l) (target x))) C B ≠ ⊤) := by
  classical
  have execute_mono (read : (q : Q) → W → Y q) (policy : Hist Y → Sum Q L) :
      ∀ n m h x t l, n ≤ m → execute read policy n h x = some (t,l) →
        execute read policy m h x = some (t,l) := by
    intro n
    induction n with
    | zero => simp [execute]
    | succ n ih =>
      intro m h x t l hnm hr
      cases m with
      | zero => omega
      | succ m =>
        cases hp : policy h with
        | inr a => simpa [execute,hp] using hr
        | inl q =>
          simp only [execute,hp] at hr ⊢
          obtain ⟨r,er,ee⟩ := Option.map_eq_some_iff.mp hr
          exact Option.map_eq_some_iff.mpr ⟨r,ih m _ _ _ _ (by omega) er,ee⟩
  have normalize_bounded
      (read : (q : Q) → W → Y q) (policy : Hist Y → Sum Q L)
      (n : Nat) (h : Hist Y) (C : Finset W) (tr : W → Hist Y) (lab : W → L)
      (runs : ∀ x ∈ C, execute read policy n h x = some (tr x, lab x)) :
      ∃ p : PassiveProtocol Q Y,
        Pruned read C p ∧
        (∀ x ∈ C, (runPassiveProtocol read p x).Sublist (tr x) ∧
          (runPassiveProtocol read p x).length < C.card) ∧
        (∀ x ∈ C, ∀ x' ∈ C,
          runPassiveProtocol read p x = runPassiveProtocol read p x' ↔ tr x = tr x') := by
    classical
    induction n generalizing h C tr lab with
    | zero =>
      have ce : C = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
        intro x hx
        simpa [execute] using runs x hx)
      subst C
      exact ⟨.stop, trivial, by simp⟩
    | succ n ih =>
      cases hp : policy h with
      | inr l =>
        have ht : ∀ x ∈ C, tr x = [] := by
          intro x hx
          have := runs x hx
          simpa [execute, hp] using (congrArg (fun t => t.map Prod.fst) this).symm
        refine ⟨.stop, trivial, ?_, ?_⟩
        · intro x hx
          simp only [runPassiveProtocol, List.nil_sublist, List.length_nil, true_and]
          exact Finset.card_pos.mpr ⟨x, hx⟩
        · intro x hx x' hx'
          simp [runPassiveProtocol, ht x hx, ht x' hx']
      | inl q =>
        have tailrun : ∀ x ∈ C,
            execute read policy n (h ++ [⟨q, read q x⟩]) x =
              some ((tr x).tail, lab x) ∧ tr x = ⟨q, read q x⟩ :: (tr x).tail := by
          intro x hx
          have hr := runs x hx
          simp only [execute, hp] at hr
          obtain ⟨a, ha, he⟩ := Option.map_eq_some_iff.mp hr
          cases a with
          | mk t l =>
            simp only [Prod.mk.injEq] at he
            rcases he with ⟨he, hl⟩
            simp only [← he, List.tail_cons, hl] at *
            exact ⟨ha, trivial⟩
        by_cases hc : ∃ y : Y q, ∀ x ∈ C, read q x = y
        · obtain ⟨y, hy⟩ := hc
          obtain ⟨p, hpr, hs, hk⟩ := ih (h ++ [⟨q,y⟩]) C (fun x => (tr x).tail) lab (by
            intro x hx
            simpa [hy x hx] using (tailrun x hx).1)
          refine ⟨p, hpr, ?_, ?_⟩
          · intro x hx
            refine ⟨(hs x hx).1.trans ?_, (hs x hx).2⟩
            exact List.tail_sublist _
          · intro x hx x' hx'
            rw [hk x hx x' hx', (tailrun x hx).2, (tailrun x' hx').2]
            simp [hy x hx, hy x' hx']
        · have smaller : ∀ y : Y q, (fiber read C q y).card < C.card := by
            intro y
            apply Finset.card_lt_card
            refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
            intro he
            apply hc
            refine ⟨y, ?_⟩
            intro x hx
            have hm : x ∈ fiber read C q y := by rw [he]; exact hx
            exact (Finset.mem_filter.mp hm).2
          have branches : ∀ y : Y q, ∃ p : PassiveProtocol Q Y,
              Pruned read (fiber read C q y) p ∧
              (∀ x ∈ fiber read C q y, (runPassiveProtocol read p x).Sublist ((tr x).tail) ∧
                (runPassiveProtocol read p x).length < (fiber read C q y).card) ∧
              (∀ x ∈ fiber read C q y, ∀ x' ∈ fiber read C q y,
                runPassiveProtocol read p x = runPassiveProtocol read p x' ↔
                  (tr x).tail = (tr x').tail) := by
            intro y
            apply ih (h ++ [⟨q,y⟩]) (fiber read C q y) (fun x => (tr x).tail) lab
            intro x hx
            have hx' := Finset.mem_filter.mp hx
            simpa [hx'.2] using (tailrun x hx'.1).1
          choose next hpr hn hk using branches
          refine ⟨.query q next, ⟨smaller, hpr⟩, ?_, ?_⟩
          · intro x hx
            have hf : x ∈ fiber read C q (read q x) := by simp [fiber, hx]
            have hh := hn (read q x) x hf
            constructor
            · rw [(tailrun x hx).2]
              exact hh.1.cons_cons ⟨q, read q x⟩
            · simp only [runPassiveProtocol, List.length_cons]
              have := smaller (read q x)
              omega
          · intro x hx x' hx'
            have hf : x ∈ fiber read C q (read q x) := by simp [fiber, hx]
            have hf' : x' ∈ fiber read C q (read q x') := by simp [fiber, hx']
            simp only [runPassiveProtocol, List.cons.injEq]
            constructor
            · rintro ⟨he, ht⟩
              have he' : read q x = read q x' := by simpa using he
              have hx'f : x' ∈ fiber read C q (read q x) := by simpa [he'] using hf'
              have ht' : (tr x).tail = (tr x').tail :=
                (hk (read q x) x hf x' hx'f).mp (by simpa [he'] using ht)
              rw [(tailrun x hx).2, (tailrun x' hx').2, he', ht']
            · intro he
              have he' : read q x = read q x' := by
                have heads := congrArg List.head? he
                rw [(tailrun x hx).2, (tailrun x' hx').2] at heads
                simpa using heads
              have hx'f : x' ∈ fiber read C q (read q x) := by simpa [he'] using hf'
              refine ⟨by simp [he'], ?_⟩
              have ht' := (hk (read q x) x hf x' hx'f).mpr (congrArg List.tail he)
              simpa [he'] using ht'

  have normalization
      (read : (q : Q) → W → Y q) (policy : Hist Y → Sum Q L)
      (C : Finset W) (hC : C.Nonempty) (h : Hist Y)
      (tr : W → Hist Y) (lab : W → L)
      (runs : ∀ x ∈ C, ∃ n, execute read policy n h x = some (tr x, lab x))
      (price : Q → Nat) (Legal : Finset W → L → Prop) (terminalPrice : Finset W → L → Nat)
      (B : Nat)
      (legal : ∀ x ∈ C, Legal (C.filter (fun y => tr y = tr x)) (lab x))
      (budget : ∀ x ∈ C, ((tr x).map (fun a => price a.1)).sum +
        terminalPrice (C.filter (fun y => tr y = tr x)) (lab x) ≤ B) :
      ∃ (p : PassiveProtocol Q Y) (decode : Hist Y → L),
        Pruned read C p ∧
        (∀ x ∈ C, decode (runPassiveProtocol read p x) = lab x ∧
          (runPassiveProtocol read p x).Sublist (tr x) ∧
          (runPassiveProtocol read p x).length ≤ C.card - 1 ∧
          C.filter (fun y => runPassiveProtocol read p y = runPassiveProtocol read p x) =
            C.filter (fun y => tr y = tr x) ∧
          Legal (C.filter (fun y => runPassiveProtocol read p y = runPassiveProtocol read p x))
            (decode (runPassiveProtocol read p x)) ∧
          (((runPassiveProtocol read p x).map (fun a => price a.1)).sum +
            terminalPrice (C.filter (fun y => runPassiveProtocol read p y = runPassiveProtocol read p x))
              (decode (runPassiveProtocol read p x)) ≤
            ((tr x).map (fun a => price a.1)).sum +
              terminalPrice (C.filter (fun y => tr y = tr x)) (lab x) ∧
          ((runPassiveProtocol read p x).map (fun a => price a.1)).sum +
            terminalPrice (C.filter (fun y => runPassiveProtocol read p y = runPassiveProtocol read p x))
              (decode (runPassiveProtocol read p x)) ≤ B)) ∧
        (∀ x ∈ C, ∀ y ∈ C,
          runPassiveProtocol read p x = runPassiveProtocol read p y ↔ tr x = tr y) := by
    classical
    have mono := execute_mono read policy
    have endpoint : ∀ n h x t l, execute read policy n h x = some (t,l) →
        policy (h ++ t) = .inr l := by
      intro n
      induction n with
      | zero => simp [execute]
      | succ n ih =>
        intro h x t l hr
        cases hp : policy h with
        | inr a =>
          simp only [execute, hp, Option.some.injEq, Prod.mk.injEq] at hr
          rcases hr with ⟨rfl,rfl⟩
          simpa using hp
        | inl q =>
          simp only [execute, hp] at hr
          obtain ⟨⟨s,a⟩, hs, he⟩ := Option.map_eq_some_iff.mp hr
          simp only [Prod.mk.injEq] at he
          rcases he with ⟨rfl,rfl⟩
          simpa [List.append_assoc] using ih _ _ _ _ hs
    choose fuel hfuel using runs
    let n := C.attach.sup (fun x => fuel x.val x.property)
    have bounded : ∀ x ∈ C, execute read policy n h x = some (tr x,lab x) := by
      intro x hx
      exact mono _ n _ _ _ _ (Finset.le_sup (f := fun x : C => fuel x.val x.property)
        (Finset.mem_attach C ⟨x,hx⟩)) (hfuel x hx)
    obtain ⟨p, hp, hs, hk⟩ := normalize_bounded read policy n h C tr lab bounded
    have historyFactors : Function.FactorsThrough (fun x : C => tr x.val)
        (fun x : C => runPassiveProtocol read p x.val) :=
      fun x y he => (hk x.val x.property y.val y.property).mp he
    obtain ⟨restore,hrestore⟩ := (Function.factorsThrough_iff _).mp historyFactors
    have compressionFactors : Function.FactorsThrough (fun x : C => runPassiveProtocol read p x.val)
        (fun x : C => tr x.val) :=
      fun x y he => (hk x.val x.property y.val y.property).mpr he
    obtain ⟨compress,hcompress⟩ := (Function.factorsThrough_iff _).mp compressionFactors
    have kernels : ∀ x ∈ C, ∀ y ∈ C,
        runPassiveProtocol read p x = runPassiveProtocol read p y ↔ tr x = tr y := by
      intro x hx y hy
      constructor
      · intro he
        exact (congrFun hrestore ⟨x,hx⟩).trans ((congrArg restore he).trans (congrFun hrestore ⟨y,hy⟩).symm)
      · intro he
        exact (congrFun hcompress ⟨x,hx⟩).trans ((congrArg compress he).trans (congrFun hcompress ⟨y,hy⟩).symm)
    have labels : Function.FactorsThrough (fun x : C => lab x.val)
        (fun x : C => runPassiveProtocol read p x.val) := by
      intro x y he
      have ht := (kernels x.val x.property y.val y.property).mp he
      have hx := endpoint _ _ _ _ _ (hfuel x.val x.property)
      have hy := endpoint _ _ _ _ _ (hfuel y.val y.property)
      rw [ht, hy] at hx
      exact Sum.inr.inj hx.symm
    let : Nonempty L := ⟨lab hC.choose⟩
    obtain ⟨decode, hd⟩ := (Function.factorsThrough_iff _).mp labels
    refine ⟨p, decode, hp, ?_, kernels⟩
    intro x hx
    have hdx : decode (runPassiveProtocol read p x) = lab x :=
      (congrFun hd ⟨x,hx⟩).symm
    have hf : C.filter (fun y => runPassiveProtocol read p y = runPassiveProtocol read p x) =
        C.filter (fun y => tr y = tr x) := by
      apply Finset.filter_congr
      intro y hy
      exact hk y hy x hx
    refine ⟨hdx, (hs x hx).1, by have := (hs x hx).2; omega, hf, ?_, ?_⟩
    · simpa only [hdx, hf] using legal x hx
    · rw [hdx, hf]
      have hc := Nat.add_le_add_right
        (((hs x hx).1.map (fun a => price a.1)).sum_le_sum (by simp))
        (terminalPrice (C.filter (fun y => tr y = tr x)) (lab x))
      exact ⟨hc,hc.trans (budget x hx)⟩

  have tree_execution (read : (q : Q) → W → Y q) (p : PassiveProtocol Q Y)
      (d : Hist Y → L) (x : W) :
      execute read (treePolicy p d) ((runPassiveProtocol read p x).length + 1) [] x =
        some (runPassiveProtocol read p x, d (runPassiveProtocol read p x)) := by
    have aux : ∀ (t : PassiveProtocol Q Y) h, residual p h = t →
        execute read (treePolicy p d) ((runPassiveProtocol read t x).length + 1) h x =
          some (runPassiveProtocol read t x, d (h ++ runPassiveProtocol read t x)) := by
      intro t
      induction t with
      | stop =>
        intro h he
        simp [runPassiveProtocol, execute, treePolicy, he]
      | query q next ih =>
        intro h he
        have hn : residual p (h ++ [⟨q, read q x⟩]) = next (read q x) := by
          simp only [residual, List.foldl_append, List.foldl_cons, List.foldl_nil]
          change advance (residual p h) ⟨q, read q x⟩ = _
          simp [he, advance]
        have hp : treePolicy p d h = .inl q := by simp [treePolicy, he]
        simp only [runPassiveProtocol, List.length_cons, Nat.add_assoc]
        change execute read (treePolicy p d) ((runPassiveProtocol read (next (read q x)) x).length + 1 + 1) h x = _
        rw [execute, hp]
        dsimp only
        rw [ih _ _ hn]
        simp [List.append_assoc]
    simpa [residual] using aux p [] rfl

  have horizon_identity (read : (q : Q) → W → Y q) (price : Q → Nat)
      (Legal : Finset W → L → Prop) (tp : Finset W → L → Nat)
      (loss : L → W → ENNReal) (C : Finset W) (hC : C.Nonempty) (B : Nat) :
      rawValue read price Legal tp loss C B = horizonValue read price Legal tp loss C B (C.card-1) := by
    classical
    apply le_antisymm
    · unfold horizonValue
      refine le_iInf (fun pol => le_iInf (fun tr => le_iInf (fun lab => le_iInf (fun hf => ?_))))
      exact le_iInf (fun _ => iInf_le_of_le pol (iInf_le_of_le tr (iInf_le_of_le lab
        (iInf_le_of_le hf le_rfl))))
    · unfold rawValue
      refine le_iInf (fun pol => le_iInf (fun tr => le_iInf (fun lab => le_iInf (fun hf => ?_))))
      obtain ⟨p,d,_,hn,_⟩ := normalization read pol C hC [] tr lab hf.1 price Legal tp B hf.2.1 hf.2.2
      have raw : RawFeasible read price Legal tp C B (treePolicy p d) (runPassiveProtocol read p)
          (fun x => d (runPassiveProtocol read p x)) := by
        refine ⟨?_, ?_, ?_⟩
        · intro x _
          exact ⟨_, tree_execution read p d x⟩
        · intro x hx
          exact (hn x hx).2.2.2.2.1
        · intro x hx
          exact (hn x hx).2.2.2.2.2.2
      have he : risk loss C (fun x => d (runPassiveProtocol read p x)) = risk loss C lab := by
        unfold risk
        congr 1
        funext x
        exact congrArg (fun l => loss l x.val) (hn x.val x.property).1
      rw [← he]
      exact iInf_le_of_le _ (iInf_le_of_le _ (iInf_le_of_le _ (iInf_le_of_le raw
        (iInf_le_of_le (fun x hx => (hn x hx).2.2.1) le_rfl))))

  have raw_eq_normal (read : (q : Q) → W → Y q) (price : Q → Nat)
      (Legal : Finset W → L → Prop) (tp : Finset W → L → Nat)
      (loss : L → W → ENNReal) (C : Finset W) (hC : C.Nonempty) (B : Nat) :
      rawValue read price Legal tp loss C B = normalValue read price Legal tp loss C B := by
    classical
    apply le_antisymm
    · apply le_iInf
      intro s
      rcases s with ⟨⟨p,lab⟩,hf,hpr⟩
      let : Nonempty L := ⟨lab hC.choose⟩
      have factors : Function.FactorsThrough (fun x : C => lab x.val)
          (fun x : C => runPassiveProtocol read p x.val) :=
        fun x y he => hf.1 x.val x.property y.val y.property he
      obtain ⟨d,hd⟩ := (Function.factorsThrough_iff _).mp factors
      have hdx : ∀ x ∈ C, d (runPassiveProtocol read p x) = lab x :=
        fun x hx => (congrFun hd ⟨x,hx⟩).symm
      have hr : RawFeasible read price Legal tp C B (treePolicy p d) (runPassiveProtocol read p) lab := by
        refine ⟨?_,hf.2⟩
        intro x hx
        exact ⟨_, by simpa only [hdx x hx] using tree_execution read p d x⟩
      exact iInf_le_of_le _ (iInf_le_of_le _ (iInf_le_of_le _ (iInf_le_of_le hr le_rfl)))
    · unfold rawValue
      refine le_iInf (fun pol => le_iInf (fun tr => le_iInf (fun lab => le_iInf (fun hf => ?_))))
      obtain ⟨p,d,hp,hn,hk⟩ := normalization read pol C hC [] tr lab hf.1 price Legal tp B hf.2.1 hf.2.2
      have ht : TreeFeasible read price Legal tp C B p lab := by
        refine ⟨?_,?_,?_⟩
        · intro x hx y hy he
          rw [← (hn x hx).1, ← (hn y hy).1, he]
        · intro x hx
          simpa only [leaf, (hn x hx).1] using (hn x hx).2.2.2.2.1
        · intro x hx
          simpa only [leaf, (hn x hx).1] using (hn x hx).2.2.2.2.2.2
      exact iInf_le (fun s : Plans read price Legal tp C B => risk loss C s.val.2) ⟨⟨p,lab⟩,ht,hp⟩

  have actual_query_leaf (read : (q : Q) → W → Y q) (C : Finset W)
      (q : Q) (next : Y q → PassiveProtocol Q Y) (x : W) :
      leaf C (runPassiveProtocol read (.query q next)) x =
        leaf (fiber read C q (read q x)) (runPassiveProtocol read (next (read q x))) x := by
    classical
    ext y
    simp only [leaf, fiber, Finset.mem_filter, runPassiveProtocol, List.cons.injEq,
      Sigma.mk.inj_iff, heq_eq_eq, true_and]
    constructor
    · rintro ⟨hy,he,ht⟩
      exact ⟨⟨hy,he⟩, by simpa only [he] using ht⟩
    · rintro ⟨⟨hy,he⟩,ht⟩
      exact ⟨hy,he,by simpa only [he] using ht⟩

  have split_iff (read : (q : Q) → W → Y q) (C : Finset W) (hC : C.Nonempty) (q : Q) :
      2 ≤ (answers read C q).card ↔ ∀ y, (fiber read C q y).card < C.card := by
    classical
    constructor
    · intro hs y
      apply Finset.card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
      intro he
      have hc : (answers read C q).card ≤ 1 := Finset.card_le_one.mpr (by
        intro a ha b hb
        obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hb
        have hx' : x ∈ fiber read C q y := by rw [he]; exact hx
        have hz' : z ∈ fiber read C q y := by rw [he]; exact hz
        exact (Finset.mem_filter.mp hx').2.trans (Finset.mem_filter.mp hz').2.symm)
      omega
    · intro hs
      by_contra hn
      have hc : (answers read C q).card ≤ 1 := by omega
      obtain ⟨x,hx⟩ := hC
      have he : fiber read C q (read q x) = C := by
        apply Finset.filter_eq_self.mpr
        intro z hz
        exact Finset.card_le_one.mp hc _ (Finset.mem_image_of_mem _ hz) _ (Finset.mem_image_of_mem _ hx)
      have := hs (read q x)
      rw [he] at this
      omega

  have glue_actual (read : (q : Q) → W → Y q) (price : Q → Nat)
      (Legal : Finset W → L → Prop) (tp : Finset W → L → Nat)
      (loss : L → W → ENNReal) (C : Finset W) (B : Nat) (q : Q)
      (hq : price q ≤ B) (hsplit : ∀ y, (fiber read C q y).card < C.card)
      (fallback : L)
      (f : (y : answers read C q) → Plans read price Legal tp (fiber read C q y.val) (B-price q)) :
      ∃ s : Plans read price Legal tp C B,
        risk loss C s.val.2 = ⨆ y : answers read C q, risk loss (fiber read C q y.val) (f y).val.2 := by
    classical
    let next : Y q → PassiveProtocol Q Y := fun y =>
      if hy : y ∈ answers read C q then (f ⟨y,hy⟩).val.1 else .stop
    let lab : W → L := fun x => if hx : x ∈ C then
      (f ⟨read q x, Finset.mem_image_of_mem _ hx⟩).val.2 x else fallback
    have hn : ∀ y : answers read C q, next y.val = (f y).val.1 := by
      intro y
      simp [next,y.property]
    have hl : ∀ (y : answers read C q) x, x ∈ fiber read C q y.val → lab x = (f y).val.2 x := by
      intro y x hx
      have hx' := Finset.mem_filter.mp hx
      have he : (⟨read q x, Finset.mem_image_of_mem _ hx'.1⟩ : answers read C q) = y :=
        Subtype.ext hx'.2
      simp only [lab, dif_pos hx'.1]
      exact congrArg (fun a : answers read C q => (f a).val.2 x) he
    have hf : TreeFeasible read price Legal tp C B (.query q next) lab := by
      refine ⟨?_,?_,?_⟩
      · intro x hx z hz he
        have hc : read q x = read q z := by
          have := congrArg List.head? he
          simpa [runPassiveProtocol] using this
        let y : answers read C q := ⟨read q x,Finset.mem_image_of_mem _ hx⟩
        have hxy : x ∈ fiber read C q y.val := by simp [fiber,y,hx]
        have hzy : z ∈ fiber read C q y.val := by simp [fiber,y,hz,hc]
        rw [hl y x hxy,hl y z hzy]
        apply (f y).property.1.1 x hxy z hzy
        have ht := congrArg List.tail he
        simp only [runPassiveProtocol,List.tail_cons] at ht
        change runPassiveProtocol read (next y.val) x = runPassiveProtocol read (next (read q z)) z at ht
        rw [← hc] at ht
        change runPassiveProtocol read (next y.val) x = runPassiveProtocol read (next y.val) z at ht
        simpa only [hn y] using ht
      · intro x hx
        let y : answers read C q := ⟨read q x,Finset.mem_image_of_mem _ hx⟩
        have hxy : x ∈ fiber read C q y.val := by simp [fiber,y,hx]
        rw [actual_query_leaf]
        change Legal (leaf (fiber read C q y.val) (runPassiveProtocol read (next y.val)) x) (lab x)
        rw [hn y, hl y x hxy]
        exact (f y).property.1.2.1 x hxy
      · intro x hx
        let y : answers read C q := ⟨read q x,Finset.mem_image_of_mem _ hx⟩
        have hxy : x ∈ fiber read C q y.val := by simp [fiber,y,hx]
        rw [actual_query_leaf]
        simp only [runPassiveProtocol,List.map_cons,List.sum_cons]
        change price q + ((runPassiveProtocol read (next y.val) x).map (fun a => price a.1)).sum +
          tp (leaf (fiber read C q y.val) (runPassiveProtocol read (next y.val)) x) (lab x) ≤ B
        rw [hn y,hl y x hxy]
        have hb := (f y).property.1.2.2 x hxy
        omega
    have hp : Pruned read C (.query q next) := by
      refine ⟨hsplit,?_⟩
      intro y
      by_cases hy : y ∈ answers read C q
      · simpa only [next,dif_pos hy] using (f ⟨y,hy⟩).property.2
      · simp [next,hy,Pruned]
    refine ⟨⟨⟨.query q next,lab⟩,hf,hp⟩,?_⟩
    change risk loss C lab = _
    apply le_antisymm
    · apply iSup_le
      intro x
      let y : answers read C q := ⟨read q x.val,Finset.mem_image_of_mem _ x.property⟩
      have hxy : x.val ∈ fiber read C q y.val := by simp [fiber,y,x.property]
      rw [hl y x.val hxy]
      exact le_iSup_of_le y (le_iSup_of_le ⟨x.val,hxy⟩ le_rfl)
    · apply iSup_le
      intro y
      apply iSup_le
      intro x
      have hx := Finset.mem_filter.mp x.property
      rw [← hl y x.val x.property]
      exact le_iSup_of_le ⟨x.val,hx.1⟩ le_rfl

  have normal_bellman (read : (q : Q) → W → Y q) (price : Q → Nat)
      (Legal : Finset W → L → Prop) (tp : Finset W → L → Nat)
      (loss : L → W → ENNReal) (C : Finset W) (hC : C.Nonempty) (B : Nat) :
      normalValue read price Legal tp loss C B =
        min (stopRadius Legal tp loss C B)
          (⨅ q, ⨅ (_ : 2 ≤ (answers read C q).card ∧ price q ≤ B),
            ⨆ y : answers read C q, normalValue read price Legal tp loss (fiber read C q y.val) (B-price q)) := by
    classical
    apply le_antisymm
    · apply le_min
      · unfold stopRadius
        refine le_iInf (fun l => le_iInf (fun hl => ?_))
        have hf : TreeFeasible read price Legal tp C B .stop (fun _ => l) := by
          refine ⟨by simp, ?_, ?_⟩
          · intro x hx
            simpa [leaf,runPassiveProtocol] using hl.1
          · intro x hx
            simpa [leaf,runPassiveProtocol] using hl.2
        exact iInf_le (fun s : Plans read price Legal tp C B => risk loss C s.val.2)
          ⟨⟨.stop,fun _ => l⟩,hf,trivial⟩
      · refine le_iInf (fun q => le_iInf (fun hq => ?_))
        simp only [normalValue]
        rw [iSup_iInf_eq_of_finite]
        apply le_iInf
        intro f
        obtain ⟨x,hx⟩ := hC
        let y : answers read C q := ⟨read q x, Finset.mem_image_of_mem _ hx⟩
        obtain ⟨s,hs⟩ := glue_actual read price Legal tp loss C B q hq.2
          ((split_iff read C ⟨x,hx⟩ q).mp hq.1) ((f y).val.2 x) f
        exact (iInf_le _ s).trans hs.le
    · apply le_iInf
      rintro ⟨⟨p,lab⟩,hf,hp⟩
      cases p with
      | stop =>
        apply le_trans (min_le_left _ _)
        obtain ⟨x,hx⟩ := hC
        have hl : ∀ z ∈ C, lab z = lab x := fun z hz => hf.1 z hz x hx rfl
        have hlegal : Legal C (lab x) ∧ tp C (lab x) ≤ B := by
          constructor
          · simpa [leaf,runPassiveProtocol] using hf.2.1 x hx
          · simpa [leaf,runPassiveProtocol] using hf.2.2 x hx
        have he : risk loss C (fun _ => lab x) = risk loss C lab := by
          apply iSup_congr
          intro z
          rw [hl z.val z.property]
        exact (iInf_le_of_le (lab x) (iInf_le_of_le hlegal le_rfl)).trans he.le
      | query q next =>
        apply le_trans (min_le_right _ _)
        have affordable : price q ≤ B := by
          obtain ⟨x,hx⟩ := hC
          have hb := hf.2.2 x hx
          simp only [runPassiveProtocol,List.map_cons,List.sum_cons] at hb
          omega
        refine iInf_le_of_le q (iInf_le_of_le ⟨(split_iff read C hC q).mpr hp.1,affordable⟩ ?_)
        apply iSup_le
        intro y
        have child : TreeFeasible read price Legal tp (fiber read C q y.val) (B-price q) (next y.val) lab := by
          refine ⟨?_,?_,?_⟩
          · intro x hx z hz he
            have hxx := Finset.mem_filter.mp hx
            have hzz := Finset.mem_filter.mp hz
            apply hf.1 x hxx.1 z hzz.1
            simpa only [runPassiveProtocol,hxx.2,hzz.2] using congrArg (List.cons ⟨q,y.val⟩) he
          · intro x hx
            have hxx := Finset.mem_filter.mp hx
            have hl := hf.2.1 x hxx.1
            rw [actual_query_leaf,hxx.2] at hl
            exact hl
          · intro x hx
            have hxx := Finset.mem_filter.mp hx
            have hb := hf.2.2 x hxx.1
            rw [actual_query_leaf] at hb
            simp only [runPassiveProtocol,List.map_cons,List.sum_cons,hxx.2] at hb
            omega
        apply le_trans (iInf_le (fun s : Plans read price Legal tp (fiber read C q y.val) (B-price q) =>
          risk loss (fiber read C q y.val) s.val.2) ⟨⟨next y.val,lab⟩,child,hp.2 y.val⟩)
        apply iSup_le
        intro x
        exact le_iSup_of_le ⟨x.val,(Finset.mem_filter.mp x.property).1⟩ le_rfl

  have minimax_identity (read : (q : Q) → W → Y q) (price : Q → Nat)
      (Legal : Finset W → L → Prop) (tp : Finset W → L → Nat)
      (loss : L → W → ENNReal) (C : Finset W) (hC : C.Nonempty) (B : Nat) :
      rawValue read price Legal tp loss C B =
        min (stopRadius Legal tp loss C B)
          (⨅ q, ⨅ (_ : 2 ≤ (answers read C q).card ∧ price q ≤ B),
            ⨆ y : answers read C q, rawValue read price Legal tp loss (fiber read C q y.val) (B-price q)) := by
    rw [raw_eq_normal read price Legal tp loss C hC B,normal_bellman read price Legal tp loss C hC B]
    congr 1
    apply iInf_congr
    intro q
    apply iInf_congr
    intro hq
    apply iSup_congr
    intro y
    have hy : (fiber read C q y.val).Nonempty := by
      obtain ⟨x,hx,he⟩ := Finset.mem_image.mp y.property
      exact ⟨x,Finset.mem_filter.mpr ⟨hx,he⟩⟩
    exact (raw_eq_normal read price Legal tp loss _ hy _).symm

  have metric_value_correspondence
      (read : (q : Q) → W → Y q) (price : Q → Nat)
      (Legal : Finset W → L → Prop) (tp : Finset W → L → Nat)
      (out : L → Z) (target : W → Z) (C : Finset W) (B : Nat)
      (free : ∃ l, Legal C l ∧ tp C l = 0) :
      ENNReal.ofReal (realRawValue read price Legal tp out target C B) =
        rawValue read price Legal tp (fun l x => ENNReal.ofReal (dist (out l) (target x))) C B ∧
      rawValue read price Legal tp (fun l x => ENNReal.ofReal (dist (out l) (target x))) C B ≠ ⊤ := by
    classical
    let loss : L → W → ENNReal := fun l x => ENNReal.ofReal (dist (out l) (target x))
    have hfinite : ∀ lab : W → L, risk loss C lab ≠ ⊤ := by
      intro lab
      exact iSup_ne_top (fun _ => ENNReal.ofReal_ne_top)
    have hreal : ∀ lab : W → L, ENNReal.ofReal (realRisk out target C lab) = risk loss C lab := by
      intro lab
      have ht : (risk loss C lab).toReal = realRisk out target C lab := by
        rw [risk,ENNReal.toReal_iSup (fun _ => ENNReal.ofReal_ne_top)]
        simp only [ENNReal.toReal_ofReal dist_nonneg,realRisk]
      rw [← ht,ENNReal.ofReal_toReal (hfinite lab)]
    obtain ⟨l,hl,hp⟩ := free
    have hs : RawFeasible read price Legal tp C B (fun _ => .inr l) (fun _ => []) (fun _ => l) := by
      refine ⟨?_,?_,?_⟩
      · intro x _
        exact ⟨1,rfl⟩
      · intro x _
        simpa [leaf] using hl
      · intro x _
        simp [leaf,hp]
    let s : RawStrategies read price Legal tp C B := ⟨⟨fun _ => .inr l,fun _ => [],fun _ => l⟩,hs⟩
    have : Nonempty (RawStrategies read price Legal tp C B) := ⟨s⟩
    have hev : (⨅ s : RawStrategies read price Legal tp C B, risk loss C s.val.2.2) =
        rawValue read price Legal tp loss C B := by
      simp only [RawStrategies,iInf_subtype,iInf_prod,rawValue]
    constructor
    · change ENNReal.ofReal (⨅ s : RawStrategies read price Legal tp C B,
          realRisk out target C s.val.2.2) = _
      rw [ENNReal.ofReal_iInf]
      simp only [hreal]
      exact hev
    · apply ne_top_of_le_ne_top (hfinite (fun _ => l))
      exact iInf_le_of_le _ (iInf_le_of_le _ (iInf_le_of_le _ (iInf_le_of_le hs le_rfl)))

  have terminal_candidates (read : (q : Q) → W → Y q) (policy : Hist Y → Sum Q L)
      (C : Finset W) (tr : W → Hist Y) (lab : W → L)
      (runs : ∀ x ∈ C, ∃ n, execute read policy n [] x = some (tr x,lab x)) :
      ∀ x ∈ C, candidates read C (tr x) = leaf C tr x := by
    classical
    have transfer : ∀ n h x t l, execute read policy n h x = some (t,l) →
        (∀ a ∈ t, read a.1 x = a.2) ∧
        ∀ y, (∀ a ∈ t, read a.1 y = a.2) → execute read policy n h y = some (t,l) := by
      intro n
      induction n with
      | zero => simp [execute]
      | succ n ih =>
        intro h x t l hr
        cases hp : policy h with
        | inr a =>
          simp only [execute,hp,Option.some.injEq,Prod.mk.injEq] at hr
          rcases hr with ⟨rfl,rfl⟩
          exact ⟨by simp,fun y _ => by simp [execute,hp]⟩
        | inl q =>
          simp only [execute,hp] at hr
          obtain ⟨⟨s,a⟩,hs,he⟩ := Option.map_eq_some_iff.mp hr
          simp only [Prod.mk.injEq] at he
          rcases he with ⟨rfl,rfl⟩
          obtain ⟨hc,ht⟩ := ih _ _ _ _ hs
          refine ⟨?_,?_⟩
          · simpa using hc
          · intro y hy
            have hyq : read q y = read q x := hy _ (List.mem_cons_self ..)
            have hys : ∀ a ∈ s, read a.1 y = a.2 := fun a ha => hy a (List.mem_cons_of_mem _ ha)
            rw [execute,hp]
            dsimp only
            rw [hyq,ht y hys]
            rfl
    have mono := execute_mono read policy
    intro x hx
    obtain ⟨n,hn⟩ := runs x hx
    obtain ⟨hc,ht⟩ := transfer _ _ _ _ _ hn
    ext y
    simp only [candidates,leaf,Finset.mem_filter]
    constructor
    · rintro ⟨hy,hcy⟩
      obtain ⟨m,hm⟩ := runs y hy
      have hn' := mono n (max n m) _ _ _ _ (le_max_left _ _) (ht y hcy)
      have hm' := mono m (max n m) _ _ _ _ (le_max_right _ _) hm
      have he := Option.some.inj (hm'.symm.trans hn')
      exact ⟨hy,congrArg Prod.fst he⟩
    · rintro ⟨hy,he⟩
      obtain ⟨m,hm⟩ := runs y hy
      have hc' := (transfer _ _ _ _ _ hm).1
      exact ⟨hy,he ▸ hc'⟩

  have source_value_clauses
      (read : (q : Q) → W → Y q) (price : Q → Nat)
      (Legal : Finset W → L → Prop) (tp : Finset W → L → Nat)
      (out : L → Z) (target : W → Z) (C : Finset W) (hC : C.Nonempty) (B : Nat)
      (freeC : ∃ l, Legal C l ∧ tp C l = 0)
      (freeReply : ∀ q (y : answers read C q),
        ∃ l, Legal (fiber read C q y.val) l ∧ tp (fiber read C q y.val) l = 0) :
      realRawValue read price Legal tp out target C B =
        realHorizonValue read price Legal tp out target C B (C.card-1) ∧
      ENNReal.ofReal (realRawValue read price Legal tp out target C B) =
        min (ENNReal.ofReal (realStopRadius Legal tp out target C B))
          (⨅ q, ⨅ (_ : 2 ≤ (answers read C q).card ∧ price q ≤ B),
            ⨆ y : answers read C q,
              ENNReal.ofReal (realRawValue read price Legal tp out target (fiber read C q y.val) (B-price q))) ∧
      (∀ q, 2 ≤ (answers read C q).card →
        ∀ y : answers read C q, (fiber read C q y.val).card < C.card) := by
    classical
    let loss : L → W → ENNReal := fun l x => ENNReal.ofReal (dist (out l) (target x))
    have realrisk : ∀ (D : Finset W) (lab : W → L),
        ENNReal.ofReal (realRisk out target D lab) = risk loss D lab := by
      intro D lab
      have ht : (risk loss D lab).toReal = realRisk out target D lab := by
        rw [risk,ENNReal.toReal_iSup (fun _ => ENNReal.ofReal_ne_top)]
        simp only [ENNReal.toReal_ofReal dist_nonneg,realRisk]
      rw [← ht]
      exact ENNReal.ofReal_toReal (show risk loss D lab ≠ ⊤ from iSup_ne_top (fun _ => ENNReal.ofReal_ne_top))
    have rawcorr := (metric_value_correspondence read price Legal tp out target C B freeC).1
    have hcorr : ENNReal.ofReal (realHorizonValue read price Legal tp out target C B (C.card-1)) =
        horizonValue read price Legal tp loss C B (C.card-1) := by
      obtain ⟨l,hl,hp⟩ := freeC
      have hs : RawFeasible read price Legal tp C B (fun _ => .inr l) (fun _ => []) (fun _ => l) := by
        refine ⟨fun _ _ => ⟨1,rfl⟩,?_,?_⟩
        · intro x _
          simpa [leaf] using hl
        · intro x _
          simp [leaf,hp]
      have : Nonempty {s : RawStrategies read price Legal tp C B //
          ∀ x ∈ C, (s.val.2.1 x).length ≤ C.card-1} :=
        ⟨⟨⟨⟨fun _ => .inr l,fun _ => [],fun _ => l⟩,hs⟩,by simp⟩⟩
      unfold realHorizonValue
      rw [ENNReal.ofReal_iInf]
      simp only [realrisk,RawStrategies,iInf_subtype,iInf_prod,horizonValue]
    have stopcorr : ENNReal.ofReal (realStopRadius Legal tp out target C B) = stopRadius Legal tp loss C B := by
      obtain ⟨l,hl,hp⟩ := freeC
      have : Nonempty {l : L // Legal C l ∧ tp C l ≤ B} := ⟨⟨l,hl,by omega⟩⟩
      unfold realStopRadius
      rw [ENNReal.ofReal_iInf]
      simp only [realrisk,iInf_subtype,stopRadius]
    refine ⟨?_,?_,fun q hq y => (split_iff read C hC q).mp hq y.val⟩
    · have he : ENNReal.ofReal (realRawValue read price Legal tp out target C B) =
          ENNReal.ofReal (realHorizonValue read price Legal tp out target C B (C.card-1)) := by
        rw [rawcorr,hcorr]
        exact horizon_identity read price Legal tp loss C hC B
      have ha : 0 ≤ realRawValue read price Legal tp out target C B :=
        Real.iInf_nonneg (fun _ => Real.iSup_nonneg (fun _ => dist_nonneg))
      have hb : 0 ≤ realHorizonValue read price Legal tp out target C B (C.card-1) :=
        Real.iInf_nonneg (fun _ => Real.iSup_nonneg (fun _ => dist_nonneg))
      exact (ENNReal.ofReal_eq_ofReal_iff ha hb).mp he
    · rw [rawcorr,stopcorr,minimax_identity read price Legal tp loss C hC B]
      congr 1
      apply iInf_congr
      intro q
      apply iInf_congr
      intro hq
      apply iSup_congr
      intro y
      have hy : (fiber read C q y.val).Nonempty := by
        obtain ⟨x,hx,he⟩ := Finset.mem_image.mp y.property
        exact ⟨x,Finset.mem_filter.mpr ⟨hx,he⟩⟩
      have hf := freeReply q y
      exact (metric_value_correspondence read price Legal tp out target _ (B-price q) hf).1.symm

  have finite_query_minimum (read : (q : Q) → W → Y q) (price : Q → Nat)
      (Legal : Finset W → L → Prop) (tp : Finset W → L → Nat)
      (loss : L → W → ENNReal) (C : Finset W) (B : Nat) :
      let eligible := fun q => 2 ≤ (answers read C q).card ∧ price q ≤ B
      let branch := fun q => ⨆ y : answers read C q,
        rawValue read price Legal tp loss (fiber read C q y.val) (B-price q)
      ((¬ ∃ q, eligible q) → (⨅ q, ⨅ (_ : eligible q), branch q) = ⊤) ∧
      ((∃ q, eligible q) → ∃ q, eligible q ∧ (⨅ q, ⨅ (_ : eligible q), branch q) = branch q) := by
    classical
    dsimp only
    constructor
    · intro he
      simp only [not_exists] at he
      simp [he]
    · rintro ⟨q,hq⟩
      let I := {q : Q // 2 ≤ (answers read C q).card ∧ price q ≤ B}
      have : Nonempty I := ⟨⟨q,hq⟩⟩
      obtain ⟨a,ha⟩ := exists_eq_ciInf_of_finite (f := fun q : I =>
        ⨆ y : answers read C q.val, rawValue read price Legal tp loss (fiber read C q.val y.val) (B-price q.val))
      exact ⟨a.val,a.property,by simpa only [I,iInf_subtype] using ha.symm⟩
  have values := source_value_clauses read price Legal tp out target C hC B freeC freeReply
  refine ⟨?_,values.1,values.2.1,values.2.2,
    finite_query_minimum read price Legal tp (fun l x => ENNReal.ofReal (dist (out l) (target x))) C B,
    metric_value_correspondence read price Legal tp out target C B freeC⟩
  intro policy feasible
  choose fuel trace label hrun hlegal hbudget using feasible
  let tr : W → Hist Y := fun x => if hx : x ∈ C then trace x hx else []
  let lab : W → L := fun x => if hx : x ∈ C then label x hx else freeC.choose
  have runs : ∀ x ∈ C, ∃ n, execute read policy n [] x = some (tr x,lab x) := by
    intro x hx
    exact ⟨fuel x hx,by simpa only [tr,lab,dif_pos hx] using hrun x hx⟩
  have legal : ∀ x ∈ C, Legal (candidates read C (tr x)) (lab x) := by
    intro x hx
    simpa only [tr,lab,dif_pos hx] using hlegal x hx
  have budget : ∀ x ∈ C, ((tr x).map (fun a => price a.1)).sum + tp (candidates read C (tr x)) (lab x) ≤ B := by
    intro x hx
    simpa only [tr,lab,dif_pos hx] using hbudget x hx
  have unique : ∀ x ∈ C, ∀ n t l, execute read policy n [] x = some (t,l) → tr x = t ∧ lab x = l := by
    intro x hx n t l hr
    obtain ⟨m,hm⟩ := runs x hx
    have hm' := execute_mono read policy m (max m n) _ _ _ _ (le_max_left _ _) hm
    have hn' := execute_mono read policy n (max m n) _ _ _ _ (le_max_right _ _) hr
    exact Prod.mk.inj (Option.some.inj (hm'.symm.trans hn'))
  have oldCandidates := terminal_candidates read policy C tr lab runs
  have legal' : ∀ x ∈ C, Legal (leaf C tr x) (lab x) := by
    intro x hx
    simpa only [oldCandidates x hx] using legal x hx
  have budget' : ∀ x ∈ C, ((tr x).map (fun a => price a.1)).sum + tp (leaf C tr x) (lab x) ≤ B := by
    intro x hx
    simpa only [oldCandidates x hx] using budget x hx
  obtain ⟨p,d,hp,hn,hk⟩ := normalization read policy C hC [] tr lab runs price Legal tp B legal' budget'
  have newRuns : ∀ x ∈ C, ∃ n, execute read (treePolicy p d) n [] x =
      some (runPassiveProtocol read p x,d (runPassiveProtocol read p x)) :=
    fun x _ => ⟨_,tree_execution read p d x⟩
  have newCandidates := terminal_candidates read (treePolicy p d) C (runPassiveProtocol read p)
    (fun x => d (runPassiveProtocol read p x)) newRuns
  refine ⟨p,d,hp,?_,?_⟩
  · intro x hx n t l hr
    rcases unique x hx n t l hr with ⟨rfl,rfl⟩
    have hf : candidates read C (runPassiveProtocol read p x) = candidates read C (tr x) := by
      rw [newCandidates x hx,oldCandidates x hx]
      exact (hn x hx).2.2.2.1
    refine ⟨(hn x hx).1,congrArg out (hn x hx).1,(hn x hx).2.1,(hn x hx).2.2.1,hf,?_,?_,?_⟩
    · simpa only [newCandidates x hx,leaf] using (hn x hx).2.2.2.2.1
    · simpa only [newCandidates x hx,oldCandidates x hx,leaf] using (hn x hx).2.2.2.2.2.1
    · simpa only [newCandidates x hx,leaf] using (hn x hx).2.2.2.2.2.2
  · intro x hx y hy n t l m s k hrx hry
    rcases unique x hx n t l hrx with ⟨rfl,rfl⟩
    rcases unique y hy m s k hry with ⟨rfl,rfl⟩
    exact hk x hx y hy

#print axioms result
end D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization
