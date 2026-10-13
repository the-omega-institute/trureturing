/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleJointChoice
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleJointChoice
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A total finite choice on whole five-hole strata with joint witnesses at every depth. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleCompiler
import D5.S3.Arith.FibonacciAtomic.Observer.NativeHistoryCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleJointChoice

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address readout)
open ActualLeafHistoryRigidity (subtree)
open NativeFiveHoleFiber
open NativeFiveHoleCompiler
open NativeDepthPatterns (Pattern Frontier fill decompose depthEquiv
  original_prefix_locality original_present_transport frontier_geometry)
open NativeUniformResidualRealization (rankedEval uniformSeparator)
open NativeSimultaneousPrefixSeparation (fixedEval prefixTuple simultaneous_prefix_separation)
open NativeHistoryCells (patternTerm pattern_deep pattern_evaluate)
open NativeSymbolicRecutting (original_fill_reply)

/-- Inclusive agreement quantifies every address, including absent replies. -/
def Agree (h : Nat) (u v : Source) : Prop :=
  ∀ a : Address, a.length ≤ h → readout a u = readout a v

private theorem pair_lift (h : Nat) (u v s t : Source)
    (hu : Agree h u v) (hs : Agree h s t) :
    Agree (h+1) (.mul u s) (.mul v t) := by
  intro a ha
  cases a with
  | nil => rfl
  | cons b a =>
      have small : a.length ≤ h := by simpa using ha
      cases b
      · exact hu a small
      · exact hs a small

private theorem pair_agree (h : Nat) (u v s t : Source)
    (hu : Agree h u v) (hs : Agree h s t) :
    Agree h (.mul u s) (.mul v t) := by
  intro a ha
  exact pair_lift h u v s t hu hs a (by omega)

private theorem rho_agree (n h : Nat) (u v : Source) (hu : Agree h u v) :
    Agree h (substitution^[n] u) (substitution^[n] v) := by
  intro a ha
  exact original_prefix_locality n a u v (fun b hb => hu b (hb.trans ha))

private theorem F_lift (h : Nat) (u v : Source) (hu : Agree h u v) :
    Agree (h+1) (F u) (F v) :=
  pair_lift h _ _ _ _ (fun _ _ => rfl) (rho_agree 1 h u v hu)

private theorem F_agree (h : Nat) (u v : Source) (hu : Agree h u v) :
    Agree h (F u) (F v) := by
  intro a ha
  exact F_lift h u v hu a (by omega)

/-- Finite iterates of the actual F, with no rho/F commutation. -/
def approximation (n : Nat) : Source := F^[n] (.of true)

private theorem approximation_succ (n : Nat) :
    approximation (n+1) = F (approximation n) :=
  Function.iterate_succ_apply' F n (.of true)

private theorem finite_contact (h : Nat) :
    Agree h (approximation (h+1)) (F (approximation (h+1))) := by
  induction h with
  | zero =>
      intro a ha
      have ae : a = [] := List.length_eq_zero_iff.mp (by omega)
      subst a
      rfl
  | succ h ih =>
      rw [show h+1+1 = (h+1)+1 from rfl,approximation_succ]
      exact F_lift h _ _ ih

private theorem reached_spine (n : Nat) :
    subtree (List.replicate n true) (approximation n) =
      some (substitution^[n] (.of true)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [approximation_succ,List.replicate_succ,F,subtree]
      have transported := original_present_transport 1 (List.replicate n true)
        (approximation n) (substitution^[n] (.of true)) ih
      simpa only [Function.iterate_one,Function.iterate_succ_apply',Function.iterate_zero,id_eq] using transported

def fullBranch : Nat → Source
  | 0 => .of true
  | n+1 => .mul (fullBranch n) (fullBranch n)

private theorem reached_full (n : Nat) :
    subtree (List.replicate n true) (fullBranch n) = some (.of true) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ,fullBranch,subtree] using ih

def bases (h : Nat) : Fin 2 → Source := ![approximation (h+1),fullBranch (h+1)]
def depths (h : Nat) : Fin 2 → Nat := fun _ => h+1
def patterns (h : Nat) (i : Fin 2) : Pattern (depths h i) :=
  (decompose (depths h i) (bases h i)).1

def fixed : Fin 0 → Source := fun i => nomatch i

/-- Two separate runs use the same live patterns and their own complete tables. -/
def filling (side : Bool) (H : History) (h : Nat) : Fin 2 → Source :=
  prefixTuple ranks fixed (depths h) (patterns h) (table side H)

private theorem patterns_live (h : Nat) (i : Fin 2) :
    Nonempty (Frontier (patterns h i)) := by
  have reached : (subtree (List.replicate (h+1) true) (bases h i)).isSome := by
    fin_cases i
    · change (subtree (List.replicate (h+1) true) (approximation (h+1))).isSome = true
      rw [reached_spine]; rfl
    · change (subtree (List.replicate (h+1) true) (fullBranch (h+1))).isSome = true
      rw [reached_full]; rfl
  have rebuilt : fill (patterns h i) (decompose (depths h i) (bases h i)).2 = bases h i :=
    (depthEquiv (depths h i)).symm_apply_apply (bases h i)
  have geometry := (frontier_geometry (depths h i) (patterns h i)).2.2
    (decompose (depths h i) (bases h i)).2 (List.replicate (h+1) true)
    (by simp [depths])
  rw [rebuilt] at geometry
  obtain ⟨x,_⟩ := geometry.mp reached
  exact ⟨x⟩

private theorem fixed_eval_zero (t : Fin 2 → Source) (E : Expr) :
    fixedEval ranks fixed t E = rankedEval ranks t E := by
  unfold fixedEval
  have valuation : Sum.elim fixed t ∘ finSumFinEquiv.symm = t := by
    funext i
    have forward : finSumFinEquiv (Sum.inr i : Fin 0 ⊕ Fin 2) = i := by
      apply Fin.ext
      simp [finSumFinEquiv]
    have backward := finSumFinEquiv.symm_apply_apply (Sum.inr i : Fin 0 ⊕ Fin 2)
    rw [forward] at backward
    simp only [Function.comp_apply,backward,Sum.elim_inr]
  rw [valuation]

private theorem filling_negatives (side : Bool) (H : History)
    (pass : Negatives side H (uniformSeparator (table side H))) (h : Nat) :
    Negatives side H (filling side H h) := by
  have seed : ∃ z : Fin 2 → Source, True ∧ ∀ e ∈ table side H,
      fixedEval ranks fixed z e.1 ≠ fixedEval ranks fixed z e.2 :=
    ⟨uniformSeparator (table side H),trivial,by simpa only [fixed_eval_zero,Negatives] using pass⟩
  have separated := (simultaneous_prefix_separation 0 0 2 (table side H)
    (fun _ => True) ranks fixed (depths h) (patterns h) (patterns_live h)).mp seed
  simpa only [filling,fixed_eval_zero,Negatives] using separated.2.2

private theorem filling_agrees (side : Bool) (H : History) (h : Nat) (i : Fin 2) :
    Agree h (filling side H h i) (bases h i) := by
  intro a ha
  let w : Frontier (patterns h i) → Source := fun x =>
    uniformSeparator (NativeSimultaneousPrefixSeparation.expandedList ranks fixed
      (depths h) (patterns h) (table side H))
      (NativeSimultaneousPrefixSeparation.holeNumbering (depths h) (patterns h) ⟨i,x⟩)
  let v : Frontier (patterns h i) → Source := (decompose (depths h i) (bases h i)).2
  have eq := original_fill_reply (depths h i) [] a (patternTerm (patterns h i) id)
    (pattern_deep (depths h i) (depths h i) (patterns h i) id [] (by simp))
    (by simp [depths]; omega) w v
  rw [pattern_evaluate,pattern_evaluate] at eq
  simp only [Function.comp_id] at eq
  have rebuilt : fill (patterns h i) v = bases h i :=
    (depthEquiv (depths h i)).symm_apply_apply (bases h i)
  rw [rebuilt] at eq
  exact eq

private theorem joint_agreement (H : History) (h : Nat) :
    Agree h (source false (filling false H h 0) (filling false H h 1))
      (source true (filling true H h 0) (filling true H h 1)) := by
  let y := filling false H h 0
  let z := filling false H h 1
  let y' := filling true H h 0
  let z' := filling true H h 1
  have yy : Agree h y y' := fun a ha =>
    (filling_agrees false H h 0 a ha).trans (filling_agrees true H h 0 a ha).symm
  have zz : Agree h z z' := fun a ha =>
    (filling_agrees false H h 1 a ha).trans (filling_agrees true H h 1 a ha).symm
  have first : Agree h y (F y') := by
    have back : Agree h (approximation (h+1)) y' := fun a ha =>
      (filling_agrees true H h 0 a ha).symm
    intro a ha
    exact (filling_agrees false H h 0 a ha).trans
      ((finite_contact h a ha).trans (F_agree h _ _ back a ha))
  exact pair_agree h _ _ _ _ first
    (pair_agree h _ _ _ _ yy (pair_agree h _ _ _ _ zz
      (pair_agree h _ _ _ _ (F_agree h _ _ yy) (F_agree h _ _ zz))))

/-- Actual finite source pairs, with both original complete membership proofs. -/
abbrev Witness (H : History) (h : Nat) :=
  {p : Source × Source // Stratum false H p.1 ∧ Stratum true H p.2 ∧ Agree h p.1 p.2}

def jointWitness (H : History)
    (passZero : Negatives false H (uniformSeparator (table false H)))
    (passOne : Negatives true H (uniformSeparator (table true H))) (h : Nat) : Witness H h :=
  ⟨(source false (filling false H h 0) (filling false H h 1),
    source true (filling true H h 0) (filling true H h 1)),
   (stratum_compile_iff false H _).mpr ⟨filling false H h,rfl,filling_negatives false H passZero h⟩,
   (stratum_compile_iff true H _).mpr ⟨filling true H h,rfl,filling_negatives true H passOne h⟩,
   joint_agreement H h⟩

def J (H : History) (h : Nat) : Prop := Nonempty (Witness H h)

/-- An empty result excludes a whole original stratum; the other branch is a
structural finite program for every supplied depth. -/
inductive Choice (H : History)
  | empty (side : Bool) (excluded : ∀ u : Source, ¬ Stratum side H u)
  | allDepth (produce : (h : Nat) → Witness H h)

private theorem whole_empty (side : Bool) (H : History)
    (fail : ¬ Negatives side H (uniformSeparator (table side H))) :
    ∀ u : Source, ¬ Stratum side H u := by
  intro u hu
  obtain ⟨t,_,neg⟩ := (stratum_compile_iff side H u).mp hu
  exact fail ((separator_exact side H).mpr ⟨t,neg⟩)

/-- The only branch tests are finite lists of decidable finite-tree inequalities. -/
def choose (H : History) : Choice H :=
  if hZero : Negatives false H (uniformSeparator (table false H)) then
    if hOne : Negatives true H (uniformSeparator (table true H)) then
      .allDepth (jointWitness H hZero hOne)
    else .empty true (whole_empty true H hOne)
  else .empty false (whole_empty false H hZero)

/-- Original Theorem 5.1 on the entire raw/history fiber, for arbitrary epochs,
repetitions and depths. The empty branch also proves exclusion at zero. -/
theorem joint_finite_choice (H : OriginalHistory) (supported : Supported H) :
    (∃ side : Bool, (∀ u : Source, ¬ Stratum side ⟨H,supported⟩ u) ∧
      ¬ J ⟨H,supported⟩ 0) ∨ (∀ h : Nat, J ⟨H,supported⟩ h) := by
  cases choose ⟨H,supported⟩ with
  | empty side excluded =>
      refine Or.inl ⟨side,excluded,?_⟩
      rintro ⟨p⟩
      cases side
      · exact excluded p.val.1 p.property.1
      · exact excluded p.val.2 p.property.2.1
  | allDepth produce => exact Or.inr (fun h => ⟨produce h⟩)

end D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleJointChoice
