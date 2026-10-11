/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Operations
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Operations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual operation traces and equal-weight codebooks bound complete storage. -/

import D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
import D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Constructions
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Data.EReal.Basic
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply

open D5.S3.ConceptDynamics.Coding.DecoderOperationTrace

/-- Exactly the original legal affine source predicate. -/
def OperationOmega (a : ℕ → Label) (x : ℕ → ℝ) : Prop :=
  ∃ path : ℕ → Guard, path 0 = .G0 ∧
    (∀ p, nextGuard (path p) (a p) = some (path (p+1))) ∧
    (∀ p, InSupport (path p) (x p)) ∧
    (∀ p, x p = branch (a p) (x (p+1)))

def OperationRecord (o : Ownership) (b : ℝ) (contract : Contract)
    (a : ℕ → Label) (r : ℕ → Color) : Prop :=
  ∃ x : ℕ → ℝ, OperationOmega a x ∧ ∃ err : ℕ → ℝ,
    ErrorBound b contract err ∧ ∀ p, observe o (x p) (err p) = r p

def OperationFiniteSource (a : ℕ → Label) : Prop := ∃ M : ℕ, ∀ p, M ≤ p → a p = .L0

noncomputable def OperationPairedRecord (model : Model) (o : Ownership) (xs : List Return)
    (j : Side) (p : ℕ) : Color :=
  if hp : p < (history model xs).length then (history model xs)[p]
  else observe o (coordinate (tailPrefix j) (p - (history model xs).length)) 0

/-- Source suppliers are instantiated unchanged; this helper adds no mathematical content. -/
theorem operation_pair_membership (model : Model) (o : Ownership) (b : ℝ)
    (contract : Contract) (xs : List Return) (supply : ActualPairSupply model o b contract xs)
    (j : Side) : OperationRecord o b contract (source j model xs)
      (OperationPairedRecord model o xs j) ∧ OperationFiniteSource (source j model xs) := by
  have reconstruction := paired_source_reconstruction j model xs
  obtain ⟨path,hzero,hedges,hsupport,haffine⟩ :=
    literal_address_path .G0 .G0 (sourcePrefix j model xs) reconstruction.1
  obtain ⟨err,hbound,hslots,hzeroErr,hfuture⟩ := supply j
  have lengths : (observedPrefix j model xs).length = (history model xs).length :=
    reconstruction.2.2.2.2.1.trans reconstruction.2.2.2.2.2.1.symm
  constructor
  · refine ⟨coordinate (sourcePrefix j model xs),⟨path,hzero,hedges,hsupport,haffine⟩,
      err,hbound,?_⟩
    intro p
    by_cases hp : p < (history model xs).length
    · simpa only [OperationPairedRecord,dif_pos hp] using hslots p hp
    · have hge : (history model xs).length ≤ p := Nat.le_of_not_gt hp
      have he : (observedPrefix j model xs).length + (p - (history model xs).length) = p := by
        rw [lengths,Nat.add_sub_of_le hge]
      have hf := hfuture (p - (history model xs).length)
      rw [he] at hf
      simpa only [OperationPairedRecord,dif_neg hp] using hf
  · refine ⟨(sourcePrefix j model xs).length,?_⟩
    intro p hp
    simp only [source,address,List.getElem?_eq_none hp,Option.getD_none]

/-- The exhaustive independent family is the unchanged anonymous45 construction. -/
theorem operation_exact_family (model : Model) (o : Ownership) (b : ℝ)
    (contract : Contract) (N : ℕ) :
    ∃ family : Finset (List Return),
      (∀ xs, xs ∈ family ↔ ActualPairSupply model o b contract xs ∧ listWeight xs = N) ∧
      family.card = Nat.card {xs : List Return //
        ActualPairSupply model o b contract xs ∧ listWeight xs = N} ∧
      Finite {xs : List Return // ActualPairSupply model o b contract xs ∧ listWeight xs = N} := by
  classical
  have lengthBound (w : List CuLetter) : w.length ≤ wordWeight w := by
    induction w with
    | nil => rfl
    | cons l w ih => cases l <;> simp [wordWeight] <;> omega
  have finiteWords (n : ℕ) : Finite {w : List CuLetter // wordWeight w = n} := by
    let f : {w : List CuLetter // wordWeight w = n} → Fin (n + 1) × (Fin n → CuLetter) :=
      fun w => (⟨w.val.length, by have hh := lengthBound w.val; rw [w.property] at hh; omega⟩,
        fun k => w.val[k.val]?.getD .u)
    apply Finite.of_injective f
    intro v w heq
    apply Subtype.ext
    have hlen : v.val.length = w.val.length := congrArg (fun p => p.1.val) heq
    apply List.ext_getElem hlen
    intro i hi hi'
    have hn : i < n := by have hh := lengthBound v.val; rw [v.property] at hh; omega
    have hh := congrFun (congrArg Prod.snd heq) ⟨i, hn⟩
    simpa [f, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi'] using hh
  let X := {xs : List Return // ActualPairSupply model o b contract xs ∧ listWeight xs = N}
  letI := finiteWords N
  let f : X → {w : List CuLetter // wordWeight w = N} := fun xs =>
    ⟨executionWord xs.val, (complete_execution_word_parser.2.2.2.1 xs.val).trans xs.property.2⟩
  have inj : Function.Injective f := by
    intro v w heq
    apply Subtype.ext
    exact complete_execution_word_parser.2.2.1 (congrArg Subtype.val heq)
  letI : Finite X := Finite.of_injective f inj
  letI : Fintype X := Fintype.ofFinite X
  let family : Finset (List Return) := Finset.univ.image (fun xs : X => xs.val)
  have membership (xs : List Return) :
      xs ∈ family ↔ ActualPairSupply model o b contract xs ∧ listWeight xs = N := by
    constructor
    · intro hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      exact v.property
    · intro hx
      exact Finset.mem_image.mpr ⟨(⟨xs, hx⟩ : X), Finset.mem_univ _, rfl⟩
  have card : family.card = Nat.card X := by
    calc
      family.card = (Finset.univ : Finset X).card :=
        Finset.card_image_of_injOn (by
          intro v hv w hw heq
          exact Subtype.ext heq)
      _ = Nat.card X := by simp [Nat.card_eq_fintype_card]
  exact ⟨family,membership,card,inferInstance⟩

set_option maxHeartbeats 1000000 in
/-- Finite primitive operations, actual D cuts and the full original code peak separate
all independent paired sources. Universal prose representation is a separate obligation. -/
theorem original_operation_decoder_storage {Configuration : Type*}
    (action : Configuration → Op Configuration Color Label) (initialConfiguration : Configuration)
    (model : Model) (o : Ownership) (b : ℝ) (contract : Contract) (N : ℕ)
    (processing : Processing action initialConfiguration (OperationRecord o b contract))
    (safety : ∀ a r, OperationRecord o b contract a r → ∀ t,
      Run action (full r) ⟨initialConfiguration,0,[]⟩ t →
      ∀ p (hp : p < t.output.length), t.output[p] = a p)
    (liveness : ∀ a r, OperationRecord o b contract a r → OperationFiniteSource a → ∀ p,
      ∃ t, Run action (full r) ⟨initialConfiguration,0,[]⟩ t ∧ p < t.output.length)
    (encoding : Configuration → List Bool)
    (faithful : Set.InjOn encoding {c | ∃ H,
      ReachThrough action initialConfiguration (OperationRecord o b contract) H c}) :
    let X := {xs : List Return // ActualPairSupply model o b contract xs ∧ listWeight xs = N}
    letI := Classical.decEq Configuration
    ∃ (family : Finset (List Return)) (cuts : X → Frame Configuration Label),
      (∀ xs, xs ∈ family ↔ ActualPairSupply model o b contract xs ∧ listWeight xs = N) ∧
      family.card = Nat.card X ∧
      (∀ x, Cut action initialConfiguration (history model x.val) (cuts x) ∧
        (∀ t, Cut action initialConfiguration (history model x.val) t → t = cuts x) ∧
        (cuts x).acquired = observationOffset model + N ∧ (cuts x).output = [] ∧
        ReachThrough action initialConfiguration (OperationRecord o b contract)
          (observationOffset model + N) (cuts x).state) ∧
      Function.Injective (fun x => (cuts x).state) ∧
      (∃ states : Finset Configuration, states.card = Nat.card X ∧
        ∀ c, c ∈ states ↔ ∃ x, (cuts x).state = c) ∧
      (∀ B : ℕ, Peak action initialConfiguration (OperationRecord o b contract) encoding
        (observationOffset model + N) ≤ (B : WithTop ℕ) → Nat.card X ≤ 2^(B+1)-1) ∧
      (∀ B : ℕ, (∀ x, (encoding (cuts x).state).length = B) → Nat.card X ≤ 2^B) ∧
      Monotone (Peak action initialConfiguration (OperationRecord o b contract) encoding) ∧
      (∀ a r t vertices, OperationRecord o b contract a r →
        Trace action (full r) ⟨initialConfiguration,0,[]⟩ t vertices →
        t.acquired ≤ observationOffset model+N → ∀ c ∈ vertices,
          ((encoding c).length : WithTop ℕ) ≤
            Peak action initialConfiguration (OperationRecord o b contract) encoding
              (observationOffset model+N)) := by
  classical
  dsimp only
  let X := {xs : List Return // ActualPairSupply model o b contract xs ∧ listWeight xs = N}
  obtain ⟨family,membership,card,finite⟩ := operation_exact_family model o b contract N
  letI : Finite X := finite
  letI : Fintype X := Fintype.ofFinite X
  have past (xs : List Return) (j : Side) :
      front (OperationPairedRecord model o xs j) (history model xs).length = history model xs := by
    apply List.ext_getElem (by simp [front])
    intro p hp hq
    simp [front,OperationPairedRecord,hq]
  have existsCut (x : X) : ∃ t, Cut action initialConfiguration (history model x.val) t ∧
      Run action (full (OperationPairedRecord model o x.val .high)) ⟨initialConfiguration,0,[]⟩ t := by
    have actual := operation_pair_membership model o b contract x.val x.property.1 .high
    simpa only [past] using actual_cut_exists action initialConfiguration
      (OperationRecord o b contract) OperationFiniteSource processing liveness
      (source .high model x.val) (OperationPairedRecord model o x.val .high)
      actual.1 actual.2 (history model x.val).length
  let cuts : X → Frame Configuration Label := fun x => Classical.choose (existsCut x)
  have spec (x : X) := Classical.choose_spec (existsCut x)
  have lowRun (x : X) : Run action (full (OperationPairedRecord model o x.val .low))
      ⟨initialConfiguration,0,[]⟩ (cuts x) := by
    obtain ⟨v,hv⟩ := (spec x).1.1
    refine ⟨v,?_⟩
    apply (prefix_trace_iff (OperationPairedRecord model o x.val .low)
      (history model x.val).length (by rw [(spec x).1.2.1])).mpr
    simpa only [past] using hv
  have empty (x : X) : (cuts x).output = [] := by
    have ah := (operation_pair_membership model o b contract x.val x.property.1 .high).1
    have al := (operation_pair_membership model o b contract x.val x.property.1 .low).1
    cases he : (cuts x).output with
    | nil => rfl
    | cons l rest =>
      have hp : 0 < (cuts x).output.length := by simp [he]
      have hh := safety _ _ ah _ (spec x).2 0 hp
      have hl := safety _ _ al _ (lowRun x) 0 hp
      change (cuts x).output[0] = source .high model x.val 0 at hh
      change (cuts x).output[0] = source .low model x.val 0 at hl
      have eh : l = Label.L5 := by
        simpa [he,source,address,sourcePrefix,observedPrefix,stem,block,U] using hh
      have el : l = Label.L0 := by
        simpa [he,source,address,sourcePrefix,observedPrefix,stem,block,V] using hl
      cases eh.symm.trans el
  have injective : Function.Injective (fun x : X => (cuts x).state) := by
    intro x y state
    have ax := operation_pair_membership model o b contract x.val x.property.1 .high
    have ay := operation_pair_membership model o b contract y.val y.property.1 .high
    have same : ∀ j, OperationPairedRecord model o x.val .high ((cuts x).acquired+j) =
        OperationPairedRecord model o y.val .high ((cuts y).acquired+j) := by
      intro j
      rw [(spec x).1.2.1,(spec y).1.2.1]
      simp [OperationPairedRecord,Nat.not_lt.mpr (Nat.le_add_right _ _)]
    have addresses := actual_address_eq action initialConfiguration
      (OperationRecord o b contract) OperationFiniteSource safety liveness
      (source .high model x.val) (source .high model y.val)
      (OperationPairedRecord model o x.val .high) (OperationPairedRecord model o y.val .high)
      ax.1 ay.1 ax.2 (cuts x) (cuts y) (spec x).2 (spec y).2 state
      ((empty x).trans (empty y).symm) same
    apply Subtype.ext
    exact actual_source_address_injection .high model x.val y.val
      (x.property.2.trans y.property.2.symm) addresses
  have reached (x : X) : ReachThrough action initialConfiguration (OperationRecord o b contract)
      (observationOffset model+N) (cuts x).state := by
    refine ⟨source .high model x.val,OperationPairedRecord model o x.val .high,cuts x,
      (operation_pair_membership model o b contract x.val x.property.1 .high).1,(spec x).2,?_,rfl⟩
    have length := (paired_source_reconstruction .high model x.val).2.2.2.2.2.1
    rw [(spec x).1.2.1,length,x.property.2]
  let codes := (Finset.univ : Finset X).image (fun x => encoding (cuts x).state)
  have codeInj : Function.Injective (fun x : X => encoding (cuts x).state) := by
    intro x y eq
    apply injective
    exact faithful ⟨_,reached x⟩ ⟨_,reached y⟩ eq
  have cards : codes.card = Nat.card X := by
    rw [Finset.card_image_of_injOn (by intro x hx y hy he; exact codeInj he)]
    simp [Nat.card_eq_fintype_card]
  refine ⟨family,cuts,membership,card,?_,injective,?_,?_,?_,
    peak_monotone action initialConfiguration (OperationRecord o b contract) encoding,?_⟩
  · intro x
    refine ⟨(spec x).1,(fun t ht => cut_unique action initialConfiguration _ ht (spec x).1),
      ?_,empty x,reached x⟩
    rw [(spec x).1.2.1,(paired_source_reconstruction .high model x.val).2.2.2.2.2.1,x.property.2]
  · refine ⟨(Finset.univ : Finset X).image (fun x => (cuts x).state),?_,?_⟩
    · change ((Finset.univ : Finset X).image (fun x => (cuts x).state)).card = Nat.card X
      rw [Finset.card_image_of_injOn (by intro x hx y hy he; exact injective he)]
      simp [Nat.card_eq_fintype_card]
    · intro c
      change c ∈ ((Finset.univ : Finset X).image (fun x => (cuts x).state)) ↔ ∃ x : X, (cuts x).state = c
      simp only [Finset.mem_image,Finset.mem_univ,true_and]
  · intro B peak
    have lengths : ∀ v ∈ codes, v.length ≤ B := by
      intro v hv
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
      have bound := (peak_bound action initialConfiguration (OperationRecord o b contract)
        encoding (observationOffset model+N) (cuts x).state (reached x)).trans peak
      exact_mod_cast bound
    have partition : codes.card = ∑ n ∈ Finset.range (B+1),
        (codes.filter (fun v => v.length = n)).card :=
      Finset.card_eq_sum_card_fiberwise (by
        intro v hv
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (lengths v hv)))
    calc Nat.card X = codes.card := cards.symm
         _ = ∑ n ∈ Finset.range (B+1), (codes.filter (fun v => v.length = n)).card := partition
         _ ≤ ∑ n ∈ Finset.range (B+1), 2^n := by
           apply Finset.sum_le_sum
           intro n hn
           simpa only [Fintype.card_bool] using
             (Finset.card_filter_length_eq_le (T := codes) (s := n))
         _ = 2^(B+1)-1 := by
           simpa using (geom_sum_mul_of_one_le (by norm_num : (1 : ℕ) ≤ 2) (B+1))
  · intro B width
    have eq : codes.filter (fun v => v.length = B) = codes := by
      apply Finset.filter_eq_self.mpr
      intro v hv
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
      exact width x
    rw [← cards,← eq]
    simpa only [Fintype.card_bool] using
      (Finset.card_filter_length_eq_le (T := codes) (s := B))

  · intro a r t vertices ha hr hq c hc
    exact peak_trace_bound action initialConfiguration (OperationRecord o b contract) encoding
      (observationOffset model+N) a r t vertices ha hr hq c hc

set_option maxHeartbeats 1000000 in
/-- Actual paired records with a single shared stem force an external prefix tag.
The record hypotheses use the original predicates and assert no decoder separation. -/
theorem original_operation_common_stem {Configuration Z : Type*} [Finite Z]
    (action : Configuration → Op Configuration Color Label) (initialConfiguration : Configuration)
    (o : Ownership) (b : ℝ) (contract : Contract)
    (processing : Processing action initialConfiguration (OperationRecord o b contract))
    (safety : ∀ a r, OperationRecord o b contract a r → ∀ t,
      Run action (full r) ⟨initialConfiguration,0,[]⟩ t →
      ∀ p (hp : p < t.output.length), t.output[p] = a p)
    (liveness : ∀ a r, OperationRecord o b contract a r → OperationFiniteSource a → ∀ p,
      ∃ t, Run action (full r) ⟨initialConfiguration,0,[]⟩ t ∧ p < t.output.length)
    (alpha beta : Z → ℕ → Label) (highRecord lowRecord : Z → ℕ → Color)
    (n : ℕ) (w : List Label)
    (actualHigh : ∀ z, OperationRecord o b contract (alpha z) (highRecord z) ∧
      OperationFiniteSource (alpha z))
    (actualLow : ∀ z, OperationRecord o b contract (beta z) (lowRecord z))
    (past : ∀ z p, p < n → highRecord z p = lowRecord z p)
    (future : ∀ z z' p, highRecord z (n+p) = highRecord z' (n+p))
    (stemHigh : ∀ z i (hi : i < w.length), alpha z i = w[i])
    (stemLow : ∀ z i (hi : i < w.length), beta z i = w[i])
    (different : ∀ z, alpha z w.length ≠ beta z w.length)
    (sourceInjection : Function.Injective alpha) :
    letI := Classical.decEq Configuration
    ∃ (cuts : Z → Frame Configuration Label) (states : Finset Configuration),
      (∀ z, Cut action initialConfiguration (front (highRecord z) n) (cuts z) ∧
        (cuts z).output.length ≤ w.length ∧
        (cuts z).output = w.take (cuts z).output.length ∧
        (cuts z).output <+: w) ∧
      Function.Injective (fun z => ((cuts z).state,(cuts z).output)) ∧
      (∀ c, c ∈ states ↔ ∃ z, (cuts z).state = c) ∧
      Nat.card Z ≤ states.card * (w.length+1) := by
  classical
  letI : Fintype Z := Fintype.ofFinite Z
  have existsCut (z : Z) : ∃ t, Cut action initialConfiguration (front (highRecord z) n) t ∧
      Run action (full (highRecord z)) ⟨initialConfiguration,0,[]⟩ t :=
    actual_cut_exists action initialConfiguration (OperationRecord o b contract)
      OperationFiniteSource processing liveness (alpha z) (highRecord z)
      (actualHigh z).1 (actualHigh z).2 n
  let cuts : Z → Frame Configuration Label := fun z => Classical.choose (existsCut z)
  have spec (z : Z) := Classical.choose_spec (existsCut z)
  have lowRun (z : Z) : Run action (full (lowRecord z)) ⟨initialConfiguration,0,[]⟩ (cuts z) := by
    obtain ⟨v,hv⟩ := (spec z).2
    refine ⟨v,trace_input_transfer hv ?_⟩
    intro q hq hqt
    have eq : (cuts z).acquired = n := by
      have hh : (cuts z).acquired = (front (highRecord z) n).length := (spec z).1.2.1
      simpa only [front,List.length_ofFn] using hh
    dsimp [full]
    rw [past z q (by omega)]
  have bounded (z : Z) : (cuts z).output.length ≤ w.length := by
    by_contra h
    have hp : w.length < (cuts z).output.length := by omega
    have hh := safety _ _ (actualHigh z).1 _ (spec z).2 w.length hp
    have hl := safety _ _ (actualLow z) _ (lowRun z) w.length hp
    exact different z (hh.symm.trans hl)
  have isTake (z : Z) : (cuts z).output = w.take (cuts z).output.length := by
    apply List.ext_getElem (by simp [List.length_take,Nat.min_eq_left (bounded z)])
    intro i hi hi'
    have hw : i < w.length := hi.trans_le (bounded z)
    calc (cuts z).output[i] = alpha z i :=
           safety _ _ (actualHigh z).1 _ (spec z).2 i hi
         _ = beta z i := (stemHigh z i hw).trans (stemLow z i hw).symm
         _ = w[i] := stemLow z i hw
         _ = (w.take (cuts z).output.length)[i] := by simp
  have joint : Function.Injective (fun z => ((cuts z).state,(cuts z).output)) := by
    intro z z' eq
    apply sourceInjection
    apply actual_address_eq action initialConfiguration (OperationRecord o b contract)
      OperationFiniteSource safety liveness (alpha z) (alpha z') (highRecord z) (highRecord z')
      (actualHigh z).1 (actualHigh z').1 (actualHigh z).2 (cuts z) (cuts z')
      (spec z).2 (spec z').2 (congrArg Prod.fst eq) (congrArg Prod.snd eq)
    intro p
    have q : (cuts z).acquired = n := by
      have hh : (cuts z).acquired = (front (highRecord z) n).length := (spec z).1.2.1
      simpa only [front,List.length_ofFn] using hh
    have q' : (cuts z').acquired = n := by
      have hh : (cuts z').acquired = (front (highRecord z') n).length := (spec z').1.2.1
      simpa only [front,List.length_ofFn] using hh
    rw [q,q']
    exact future z z' p
  let states : Finset Configuration := Finset.univ.image (fun z => (cuts z).state)
  have membership (c : Configuration) : c ∈ states ↔ ∃ z, (cuts z).state = c := by
    simp [states]
  let f : Z → {c // c ∈ states} × Fin (w.length+1) := fun z =>
    (⟨(cuts z).state,(membership _).mpr ⟨z,rfl⟩⟩,
      ⟨(cuts z).output.length,Nat.lt_succ_of_le (bounded z)⟩)
  have inj : Function.Injective f := by
    intro z z' he
    apply joint
    have hs : (cuts z).state = (cuts z').state :=
      congrArg (fun p : {c // c ∈ states} × Fin (w.length+1) => p.1.val) he
    have hl : (cuts z).output.length = (cuts z').output.length :=
      congrArg (fun p : {c // c ∈ states} × Fin (w.length+1) => p.2.val) he
    refine Prod.ext hs ?_
    change (cuts z).output = (cuts z').output
    rw [isTake z,isTake z',hl]
  have capacity := Fintype.card_le_of_injective f inj
  refine ⟨cuts,states,?_,joint,membership,?_⟩
  · intro z
    refine ⟨(spec z).1,bounded z,isTake z,?_⟩
    rw [isTake z]
    exact List.take_prefix _ _
  · simpa [Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_coe] using capacity


def resetConcatenation (R : Return) : List (List Return) → List Return
  | [] => []
  | xs :: words => (R :: xs) ++ resetConcatenation R words

set_option maxHeartbeats 3000000 in
/-- A fixed full equal-weight weak codebook has one reset and one positive
error margin for all its finite joint concatenations, from either actual start.
Positive cumulative weights recover the choices even when their lengths differ. -/
theorem original_equal_weight_codebook (o : Ownership) (b : ℝ) (K : ℕ)
    (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K *
      (aSide .high / (1 - rho * chi ^ K))) :
    ∃ R : Return, R.r = 1 ∧ ∀ (sourceModel : Model) (N : ℕ), 0 < N →
    let d := (lam - b) / g ^ 2 / chi ^ K
    let V := {xs : List Return //
      GuardTrace K d false .high xs (initial .high sourceModel) ∧ listWeight xs = N}
    Finite V ∧ ∃ eps : ℝ, 0 < eps ∧ 0 < N + (20 + 6*R.m) ∧
      (∀ (targetModel : Model) (words : List (List Return)),
        (∀ xs ∈ words, GuardTrace K d false .high xs (initial .high sourceModel) ∧
          listWeight xs = N) →
        ActualPairSupply targetModel o (b-eps) .closed (resetConcatenation R words) ∧
        (∀ contract : Contract, ActualPairSupply targetModel o b contract
          (resetConcatenation R words)) ∧
        listWeight (resetConcatenation R words) = words.length * (N + (20 + 6*R.m))) ∧
      (∀ (targetModel : Model) (contract : Contract) (q : ℕ),
        Nat.card V ^ q ≤ Nat.card {xs : List Return //
          ActualPairSupply targetModel o b contract xs ∧
          listWeight xs = q * (N + (20 + 6*R.m))}) := by
  classical
  obtain ⟨R,hr,hB,hstrict,hweak,htransfer,hweight,hfirst⟩ :=
    actual_reset_first_return o b K hK hqb hbp
  refine ⟨R,hr,?_⟩
  intro sourceModel N hN
  dsimp only
  let d := (lam - b) / g ^ 2 / chi ^ K
  let V := {xs : List Return //
    GuardTrace K d false .high xs (initial .high sourceModel) ∧ listWeight xs = N}
  let A := aSide .high
  let H := hSide .high
  let B := H - rho ^ R.m * (H - chi * A)
  let D := initial .high sourceModel
  have DA : A < D := (actual_complete_boundary_geometry sourceModel []).1 .high 0 |>.1
  have DB : D < B := by
    have hh : D ≤ max (max (xSide .high) (ySide .high)) d := by
      cases sourceModel
      · exact le_trans (le_max_left _ _) (le_max_left _ _)
      · exact le_trans (le_max_right _ _) (le_max_left _ _)
    exact hh.trans_lt hB
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have gp : 0 < g := by dsimp [g,t]; nlinarith [Real.sqrt_nonneg (5 : ℝ)]
  have g1 : g < 1 := by dsimp [g,t]; nlinarith [Real.sqrt_nonneg (5 : ℝ)]
  let delta := B-D
  let gamma := delta * g^N
  have dp : 0 < delta := sub_pos.mpr DB
  have gap : 0 < gamma := mul_pos dp (pow_pos gp N)
  let scale := g^2 * chi^K
  have sp : 0 < scale := mul_pos (pow_pos gp 2) (pow_pos (pow_pos gp 20) K)
  let eps := min ((b - (lam - scale*H))/2) (scale*gamma/4)
  have ep : 0 < eps := lt_min (by dsimp [scale,H] at *; linarith) (by positivity)
  have qe : lam - g^2*chi^K*hSide .high < b-eps := by
    have hh := min_le_left ((b-(lam-scale*H))/2) (scale*gamma/4)
    change eps ≤ (b-(lam-scale*H))/2 at hh
    dsimp [scale,H] at *; linarith
  have pe : b-eps < lam - g^2*chi^K*(aSide .high/(1-rho*chi^K)) := by linarith
  have shiftThreshold : (lam-(b-eps))/g^2/chi^K = d + eps/scale := by
    dsimp [d,scale]; field_simp; ring
  have esmall : eps/scale < gamma := by
    have hh := min_le_right ((b-(lam-scale*H))/2) (scale*gamma/4)
    change eps ≤ scale*gamma/4 at hh
    rw [div_lt_iff₀ sp]
    nlinarith
  have weightAppend (xs ys : List Return) : listWeight (xs++ys) = listWeight xs + listWeight ys := by
    induction xs with
    | nil => simp [listWeight]
    | cons a xs ih => simp only [List.cons_append,listWeight,ih]; omega
  have weightZero (xs : List Return) : listWeight xs = 0 → xs = [] := by
    cases xs with
    | nil => intro _; rfl
    | cons a xs => intro hh; have := a.m_pos; simp only [listWeight] at hh; omega
  have executeAppend (xs ys : List Return) (z : ℝ) :
      execute .high (xs++ys) z = execute .high ys (execute .high xs z) := by
    induction xs generalizing z with
    | nil => rfl
    | cons a xs ih => simp only [List.cons_append,execute,ih]
  have affineDifference (xs : List Return) (x y : ℝ) :
      execute .high xs y - execute .high xs x = g^(listWeight xs)*(y-x) := by
    induction xs generalizing x y with
    | nil => simp [execute,listWeight]
    | cons a xs ih =>
      simp only [execute,listWeight,ih,returnMap]
      have pw : rho^a.m * chi^a.r = g^(6*a.m+20*a.r) := by
        simp only [rho,chi,← pow_mul,← pow_add]
      rw [pow_add]
      calc
        _ = g^(listWeight xs)*(rho^a.m*chi^a.r)*(y-x) := by ring
        _ = _ := by rw [pw]; ring
  have positions (xs : List Return) (threshold z : ℝ) (st : Bool) :
      GuardTrace K threshold st .high xs z ↔
      ∀ i : Fin xs.length, xs[i].r ≤ K ∧
        (xs[i].r = K → if st then threshold < execute .high (xs.take i.val) z
          else threshold ≤ execute .high (xs.take i.val) z) := by
    induction xs generalizing z with
    | nil => simp [GuardTrace]
    | cons a xs ih =>
      rw [GuardTrace,ih]
      constructor
      · rintro ⟨hc,hg,ht⟩ ⟨i,hi⟩
        cases i with
        | zero => simpa [execute] using And.intro hc hg
        | succ i => simpa [execute] using ht ⟨i,by simpa using hi⟩
      · intro ht
        have hh := ht ⟨0,by simp⟩
        refine ⟨by simpa using hh.1,by simpa [execute] using hh.2,?_⟩
        intro i; simpa [execute] using ht ⟨i.val+1,by simpa using i.isLt⟩
  have improve (xs : List Return)
      (hw : GuardTrace K d false .high xs D) (wn : listWeight xs = N)
      (E : ℝ) (hE : B ≤ E) :
      GuardTrace K ((lam-(b-eps))/g^2/chi^K) true .high xs E ∧
      A < execute .high xs E := by
    have ED : D < E := DB.trans_le hE
    constructor
    · apply (positions _ _ _ _).mpr
      intro i
      have hh := (positions _ _ _ _).mp hw i
      refine ⟨hh.1,?_⟩
      intro hi
      have wd : listWeight (xs.take i.val) ≤ N := by
        have ww := weightAppend (xs.take i.val) (xs.drop i.val)
        rw [List.take_append_drop,wn] at ww; omega
      have pg : g^N ≤ g^(listWeight (xs.take i.val)) :=
        pow_le_pow_of_le_one gp.le g1.le wd
      have gain : gamma ≤ execute .high (xs.take i.val) E - execute .high (xs.take i.val) D := by
        rw [affineDifference]
        have dd : delta ≤ E-D := by dsimp [delta]; linarith
        change delta*g^N ≤ g^(listWeight (xs.take i.val))*(E-D)
        calc delta*g^N ≤ delta*g^(listWeight (xs.take i.val)) := mul_le_mul_of_nonneg_left pg dp.le
             _ ≤ g^(listWeight (xs.take i.val))*(E-D) := by
               simpa only [mul_comm] using mul_le_mul_of_nonneg_left dd (pow_pos gp (listWeight (xs.take i.val))).le
      have old := hh.2 hi
      simp only [Bool.false_eq_true,if_false] at old
      simp only [Bool.true_eq,if_true]
      rw [shiftThreshold]
      linarith
    · have base := (actual_complete_boundary_geometry sourceModel xs).1 .high xs.length
      simp only [List.take_length] at base
      have pos := mul_pos (pow_pos gp (listWeight xs)) (sub_pos.mpr ED)
      rw [← affineDifference] at pos
      have ba : A < execute .high xs D := base.1
      linarith
  have traceAppend (xs ys : List Return) (z threshold : ℝ) :
      GuardTrace K threshold true .high (xs++ys) z ↔
      GuardTrace K threshold true .high xs z ∧
      GuardTrace K threshold true .high ys (execute .high xs z) := by
    induction xs generalizing z with
    | nil => simp [GuardTrace,execute]
    | cons a xs ih => simp only [List.cons_append,GuardTrace,execute,ih]; tauto
  have joint (words : List (List Return))
      (hw : ∀ xs ∈ words, GuardTrace K d false .high xs D ∧ listWeight xs = N)
      (E : ℝ) (hE : A < E) :
      GuardTrace K ((lam-(b-eps))/g^2/chi^K) true .high (resetConcatenation R words) E := by
    induction words generalizing E with
    | nil => trivial
    | cons xs words ih =>
      obtain ⟨ht,wn⟩ := hw xs (by simp)
      have im := improve xs ht wn (returnMap .high R E) (hweak E hE.le)
      apply (traceAppend _ _ _ _).mpr
      refine ⟨⟨by rw [hr]; omega,?_,im.1⟩,?_⟩
      · intro hk; omega
      · apply ih (by intro x hx; exact hw x (by simp [hx]))
        simpa only [execute] using im.2
  have uniform (targetModel : Model) (words : List (List Return))
      (hw : ∀ xs ∈ words, GuardTrace K d false .high xs D ∧ listWeight xs = N) :
      ActualPairSupply targetModel o (b-eps) .closed (resetConcatenation R words) ∧
      (∀ contract : Contract, ActualPairSupply targetModel o b contract (resetConcatenation R words)) ∧
      listWeight (resetConcatenation R words) = words.length*(N+(20+6*R.m)) := by
    have tr := joint words hw (initial .high targetModel)
      ((actual_complete_boundary_geometry targetModel []).1 .high 0).1
    have supply := (actual_strict_record_supply targetModel o (b-eps)
      (resetConcatenation R words) K hK qe pe).1.mpr tr
    have closed : ActualPairSupply targetModel o (b-eps) .closed (resetConcatenation R words) := by
      intro j
      obtain ⟨err,he,hh,hz,hf⟩ := supply j
      exact ⟨err,fun p => (he p).le,hh,hz,hf⟩
    refine ⟨closed,?_,?_⟩
    · intro contract j
      obtain ⟨err,he,hh,hz,hf⟩ := closed j
      refine ⟨err,?_,hh,hz,hf⟩
      cases contract with
      | closed => exact fun p => (he p).trans (by linarith)
      | strict => exact fun p => (he p).trans_lt (by linarith)
      | recordMargin => exact ⟨eps,ep,he⟩
    · clear tr supply closed
      induction words with
      | nil => simp [resetConcatenation,listWeight]
      | cons xs words ih =>
        have wn := (hw xs (by simp)).2
        have htail := ih (by intro x hx; exact hw x (by simp [hx]))
        rw [resetConcatenation,weightAppend,hweight xs,wn,htail,List.length_cons]
        ring
  have finite : Finite V := by
    obtain ⟨family,hm,hc,hf⟩ := operation_exact_family sourceModel o b .strict (N+(20+6*R.m))
    letI := hf
    let f : V → {xs : List Return // ActualPairSupply sourceModel o b .strict xs ∧
        listWeight xs = N+(20+6*R.m)} := fun xs =>
      ⟨R::xs.val,htransfer sourceModel sourceModel xs.val xs.property.1,
        by rw [hweight,xs.property.2]; omega⟩
    exact Finite.of_injective f (by intro x y h; apply Subtype.ext; exact List.cons.inj (congrArg Subtype.val h) |>.2)
  letI : Finite V := finite
  have firstBlock (xs ys tx ty : List Return) (wx : listWeight xs = N) (wy : listWeight ys = N)
      (he : (R::xs)++tx = (R::ys)++ty) : xs=ys := by
    rcases List.append_eq_append_iff.mp he with ⟨as,ha,ht⟩ | ⟨bs,hb,ht⟩
    · have wz : listWeight as = 0 := by
        have hh := congrArg listWeight ha
        rw [weightAppend,hweight,hweight,wx,wy] at hh; omega
      have zz := weightZero as wz
      simpa [zz] using (List.cons.inj ha).2.symm
    · have wz : listWeight bs = 0 := by
        have hh := congrArg listWeight hb
        rw [weightAppend,hweight,hweight,wx,wy] at hh; omega
      have zz := weightZero bs wz
      simpa [zz] using (List.cons.inj hb).2
  have concatInjective (words words' : List (List Return))
      (hw : ∀ xs ∈ words, listWeight xs=N)
      (hw' : ∀ xs ∈ words', listWeight xs=N)
      (he : resetConcatenation R words = resetConcatenation R words') : words=words' := by
    induction words generalizing words' with
    | nil => cases words' <;> simp_all [resetConcatenation]
    | cons xs words ih =>
      cases words' with
      | nil => simp [resetConcatenation] at he
      | cons ys words' =>
        have xy := firstBlock xs ys _ _ (hw xs (by simp)) (hw' ys (by simp)) he
        subst ys
        have ht : resetConcatenation R words = resetConcatenation R words' :=
          List.append_cancel_left (by simpa only [resetConcatenation] using he)
        congr 1
        exact ih words' (by intro x hx; exact hw x (by simp [hx]))
          (by intro x hx; exact hw' x (by simp [hx])) ht
  refine ⟨finite,eps,ep,by omega,uniform,?_⟩
  intro targetModel contract q
  let f : (Fin q → V) → {xs : List Return // ActualPairSupply targetModel o b contract xs ∧
      listWeight xs = q*(N+(20+6*R.m))} := fun z =>
    ⟨resetConcatenation R (List.ofFn (fun i => (z i).val)), by
      have hw : ∀ xs ∈ List.ofFn (fun i => (z i).val),
          GuardTrace K d false .high xs D ∧ listWeight xs=N := by
        intro xs hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx; exact (z i).property
      have uu := uniform targetModel (List.ofFn (fun i => (z i).val)) hw
      exact ⟨uu.2.1 contract,by simpa using uu.2.2⟩⟩
  have inj : Function.Injective f := by
    intro z z' he
    have hw (u : Fin q → V) : ∀ xs ∈ List.ofFn (fun i => (u i).val), listWeight xs=N := by
      intro xs hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx; exact (u i).property.2
    have lists := concatInjective _ _ (hw z) (hw z') (congrArg Subtype.val he)
    funext i
    apply Subtype.ext
    have hh := congrArg (fun l => l[i.val]?) lists
    simpa using hh
  obtain ⟨family,hm,hc,hf⟩ := operation_exact_family targetModel o b contract (q*(N+(20+6*R.m)))
  letI := hf
  have card := Nat.card_le_card_of_injective f inj
  simpa [Nat.card_fun,Nat.card_fin] using card


open D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open Filter
open scoped Topology

set_option maxHeartbeats 2000000 in
/-- One reset works at all weights. Every fixed nonempty full weak codebook
forces its exact-denominator coefficient in the full storage liminf, including
infinite peaks. Startup is derived from the actual first-label competitors. -/
theorem original_codebook_storage_liminf {Configuration : Type*}
    (action : Configuration → Op Configuration Color Label) (initialConfiguration : Configuration)
    (o : Ownership) (b : ℝ) (contract : Contract) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K)))
    (safety : ∀ a r, OperationRecord o b contract a r → ∀ t,
      Run action (full r) ⟨initialConfiguration,0,[]⟩ t →
      ∀ p (hp : p < t.output.length), t.output[p] = a p)
    (liveness : ∀ a r, OperationRecord o b contract a r → OperationFiniteSource a → ∀ p,
      ∃ t, Run action (full r) ⟨initialConfiguration,0,[]⟩ t ∧ p < t.output.length)
    (postprocessing : ∀ a r, OperationRecord o b contract a r →
      ∀ (c d : Configuration) (q : ℕ) (out batch : List Label)
        (f : Color → Option (Configuration × List Label)),
      Run action (full r) ⟨initialConfiguration,0,[]⟩ ⟨c,q,out⟩ →
      action c = .acquire f → f (r q) = some (d,batch) →
      ∃ t, Drain action ⟨d,q+1,out++batch⟩ t)
    (encoding : Configuration → List Bool)
    (faithful : Set.InjOn encoding {c | ∃ H,
      ReachThrough action initialConfiguration (OperationRecord o b contract) H c}) :
    ∃ R : Return, R.r = 1 ∧ ∀ (sourceModel : Model) (N : ℕ), 0 < N →
      let a := Nat.card {xs : List Return //
        GuardTrace K ((lam-b)/g^2/chi^K) false .high xs (initial .high sourceModel) ∧
        listWeight xs = N}
      1 ≤ a → ∀ model : Model,
      let L := N+(20+6*R.m)
      let fullPeak := Peak action initialConfiguration (OperationRecord o b contract) encoding
      (∀ H B : ℕ, observationOffset model ≤ H → fullPeak H ≤ (B : WithTop ℕ) →
        (((H-observationOffset model)/L : ℕ) : ℝ)*Real.logb 2 (a : ℝ)-1 ≤ B) ∧
      ENNReal.ofReal (Real.logb 2 (a : ℝ)/(L : ℝ)) ≤
        liminf (fun H : ℕ => ENat.toENNReal (fullPeak H)/(H : ENNReal)) atTop := by
  classical
  obtain ⟨R,hr,books⟩ := original_equal_weight_codebook o b K hK hqb hbp
  refine ⟨R,hr,?_⟩
  intro sourceModel N hN
  dsimp only
  let V := {xs : List Return //
    GuardTrace K ((lam-b)/g^2/chi^K) false .high xs (initial .high sourceModel) ∧
    listWeight xs=N}
  let a := Nat.card V
  intro ha model
  let L := N+(20+6*R.m)
  let Delta := observationOffset model
  let fullPeak := Peak action initialConfiguration (OperationRecord o b contract) encoding
  obtain ⟨finite,eps,ep,Lpos,uniform,count⟩ := books sourceModel N hN
  have emptySupply : ActualPairSupply model o b contract [] := by
    have hh := uniform model [] (by simp)
    simpa [resetConcatenation] using hh.2.1 contract
  have high := operation_pair_membership model o b contract [] emptySupply .high
  have low := operation_pair_membership model o b contract [] emptySupply .low
  have different : source .high model [] 0 ≠ source .low model [] 0 := by
    simp [source,address,sourcePrefix,observedPrefix,stem,block,U,FibonacciLiteralSource.V]
  have processing := processing_of_safe_live_pair action initialConfiguration
    (OperationRecord o b contract) OperationFiniteSource safety liveness
    (source .high model []) (source .low model [])
    (OperationPairedRecord model o [] .high) (OperationPairedRecord model o [] .low)
    high.1 low.1 high.2 different postprocessing
  have mono : Monotone fullPeak :=
    peak_monotone action initialConfiguration (OperationRecord o b contract) encoding
  have capacity (q B : ℕ) (hp : fullPeak (Delta+q*L) ≤ (B : WithTop ℕ)) :
      a^q ≤ 2^(B+1)-1 := by
    obtain ⟨family,cuts,hm,hc,hcut,hinj,hstates,hcap,hfixed,hmono,hvertices⟩ :=
      original_operation_decoder_storage action initialConfiguration model o b contract (q*L)
        processing safety liveness encoding faithful
    exact (count model contract q).trans (hcap B hp)
  have lp : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Lpos
  have ap : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ha)
  let loga := Real.logb 2 (a : ℝ)
  have lognonneg : 0 ≤ loga := Real.logb_nonneg (by norm_num) (by exact_mod_cast ha)
  have finiteFloor (H B : ℕ) (hH : Delta ≤ H) (hp : fullPeak H ≤ (B : WithTop ℕ)) :
      (((H-Delta)/L : ℕ) : ℝ)*loga-1 ≤ (B : ℝ) := by
    let q := (H-Delta)/L
    have lower : Delta+q*L ≤ H := by
      have hh := Nat.div_mul_le_self (H-Delta) L
      dsimp [q]; omega
    have cn : a^q ≤ 2^(B+1) := (capacity q B ((mono lower).trans hp)).trans (Nat.sub_le _ _)
    have cr : (a : ℝ)^q ≤ (2 : ℝ)^(B+1) := by exact_mod_cast cn
    have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2) (pow_pos ap q) cr
    simp only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2),mul_one,
      Nat.cast_add,Nat.cast_one] at hl
    change (q : ℝ)*loga-1 ≤ (B : ℝ)
    dsimp [loga] at *; linarith
  refine ⟨finiteFloor,?_⟩
  let slope := loga/(L : ℝ)
  let loss := (((Delta : ℝ)+(L : ℝ))*loga+(L : ℝ))/(L : ℝ)
  have lowerReal (H B : ℕ) (hH : max Delta 1 ≤ H) (hp : fullPeak H ≤ (B : WithTop ℕ)) :
      slope-loss/(H : ℝ) ≤ (B : ℝ)/(H : ℝ) := by
    have Hpos : (0 : ℝ)<(H : ℝ) := by exact_mod_cast (show 0<H by omega)
    have hd : Delta≤H := by omega
    let q := (H-Delta)/L
    have Lpos' : 0<L := Lpos
    have remainder := Nat.mod_lt (H-Delta) Lpos'
    have decomp : (H-Delta)/L*L+(H-Delta)%L = H-Delta := by
      simpa only [Nat.mul_comm] using Nat.div_add_mod (H-Delta) L
    have bound : H ≤ Delta+q*L+L := by dsimp [q]; omega
    have br : (H : ℝ) ≤ (Delta : ℝ)+(q : ℝ)*(L : ℝ)+(L : ℝ) := by exact_mod_cast bound
    have mulbound := mul_le_mul_of_nonneg_right br lognonneg
    have floor := finiteFloor H B hd hp
    have interpolate : slope*(H : ℝ)-loss ≤ (q : ℝ)*loga-1 := by
      have identity : slope*(H : ℝ)-loss =
          (loga*(H : ℝ)-(((Delta : ℝ)+(L : ℝ))*loga+(L : ℝ)))/(L : ℝ) := by
        dsimp [slope,loss]; ring
      rw [identity,div_le_iff₀ lp]
      nlinarith only [mulbound]
    have identity : slope-loss/(H : ℝ) = (slope*(H : ℝ)-loss)/(H : ℝ) := by
      field_simp
    rw [identity,div_le_div_iff_of_pos_right Hpos]
    exact interpolate.trans floor
  have eventual : ∀ᶠ H : ℕ in atTop,
      ENNReal.ofReal (slope-loss/(H : ℝ)) ≤ ENat.toENNReal (fullPeak H)/(H : ENNReal) := by
    filter_upwards [eventually_ge_atTop (max Delta 1)] with H hH
    have Hpos : (0 : ℝ)<(H : ℝ) := by exact_mod_cast (show 0<H by omega)
    rcases eq_or_ne (fullPeak H) ⊤ with ht | hf
    · rw [ht]
      change ENNReal.ofReal (slope-loss/(H : ℝ)) ≤ (⊤ : ENNReal)/(H : ENNReal)
      rw [ENNReal.top_div_of_ne_top (by simp)]
      exact le_top
    · obtain ⟨B,hB⟩ := WithTop.ne_top_iff_exists.mp hf
      have rr := lowerReal H B hH (by rw [← hB]; exact le_rfl)
      have er := ENNReal.ofReal_le_ofReal rr
      rw [← hB]
      change ENNReal.ofReal (slope-loss/(H : ℝ)) ≤ (B : ENNReal)/(H : ENNReal)
      simpa [ENNReal.ofReal_div_of_pos Hpos] using er
  have conv : Tendsto (fun H : ℕ => ENNReal.ofReal (slope-loss/(H : ℝ))) atTop
      (𝓝 (ENNReal.ofReal slope)) := by
    apply ENNReal.tendsto_ofReal
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat loss)
  change ENNReal.ofReal slope ≤ _
  rw [← conv.liminf_eq]
  exact liminf_le_liminf eventual



end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
