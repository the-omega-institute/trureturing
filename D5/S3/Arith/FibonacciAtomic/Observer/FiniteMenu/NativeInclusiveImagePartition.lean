/- GID: D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeInclusiveImagePartition
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeInclusiveImagePartition
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact inclusive image cells and multiplicities on the complete native origin fiber. -/

import D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis
import D5.S0.Computability.PreorderTreeEvaluation
import Mathlib.Data.Countable.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeInclusiveImagePartition

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualLeafHistoryRigidity (subtree)
open ActualCutPartitionRecovery (LiteralRow evaluateRow canonicalRow)
open NativeCutFibers (labels Classes LegalValues extend)
open NativeClassRootImage (Image rootType)
open NativeGroundSeparation (Term evaluate)
open FourExitRawEndpointSpectrum (comb comb_foundation)
open scoped BigOperators

/-- A zero-depth profile records the root itself; only a branch has a name. -/
def Pattern : Nat → Type
  | 0 => Bool ⊕ Unit
  | b+1 => Bool ⊕ (Pattern b × Pattern b)

instance patternFinite (b : Nat) : Fintype (Pattern b) := by
  induction b with
  | zero => exact inferInstanceAs (Fintype (Bool ⊕ Unit))
  | succ b ih => exact inferInstanceAs (Fintype (Bool ⊕ (Pattern b × Pattern b)))

/-- Positions are disjoint; an early literal leaf has no frontier positions. -/
def Frontier : {b : Nat} → Pattern b → Type
  | 0, .inl _ => PEmpty
  | 0, .inr _ => Unit
  | _+1, .inl _ => PEmpty
  | _+1, .inr p => Frontier p.1 ⊕ Frontier p.2

instance frontierFinite {b : Nat} (p : Pattern b) : Fintype (Frontier p) := by
  induction b with
  | zero => cases p with
    | inl c => exact inferInstanceAs (Fintype PEmpty)
    | inr q => exact inferInstanceAs (Fintype Unit)
  | succ b ih => cases p with
    | inl c => exact inferInstanceAs (Fintype PEmpty)
    | inr p =>
      letI := ih p.1
      letI := ih p.2
      exact inferInstanceAs (Fintype (Frontier p.1 ⊕ Frontier p.2))

/-- A name is filled by an entire finite tree, at its recorded branch root. -/
def fill : {b : Nat} → (p : Pattern b) → (Frontier p → Source) → Source
  | 0, .inl c, _ => .of c
  | 0, .inr _, f => f ()
  | _+1, .inl c, _ => .of c
  | _+1, .inr p, f => .mul (fill p.1 (fun x => f (.inl x)))
      (fill p.2 (fun x => f (.inr x)))

/-- The original inclusive prefix, including frontier branch observations. -/
def expose : (b : Nat) → Source → Pattern b
  | 0, .of c => .inl c
  | 0, .mul _ _ => .inr ()
  | _+1, .of c => .inl c
  | b+1, .mul l r => .inr (expose b l, expose b r)

/-- Actual subtree values at all and only the named branch positions. -/
def extract : (b : Nat) → (t : Source) → Frontier (expose b t) → Source
  | 0, .of _, x => PEmpty.elim x
  | 0, .mul l r, _ => .mul l r
  | _+1, .of _, x => PEmpty.elim x
  | b+1, .mul l _r, .inl x => extract b l x
  | b+1, .mul _l r, .inr x => extract b r x

private theorem fill_extract (b : Nat) (t : Source) :
    fill (expose b t) (extract b t) = t := by
  induction b generalizing t with
  | zero => cases t <;> rfl
  | succ b ih => cases t with
    | of c => rfl
    | mul l r => exact congrArg₂ FreeMagma.mul (ih l) (ih r)

private theorem extract_branch (b : Nat) (t : Source) (x : Frontier (expose b t)) :
    rootType (extract b t x) = none := by
  induction b generalizing t with
  | zero => cases t with
    | of c => exact PEmpty.elim x
    | mul l r => rfl
  | succ b ih => cases t with
    | of c => exact PEmpty.elim x
    | mul l r => cases x with
      | inl x => exact ih l x
      | inr x => exact ih r x

private theorem expose_fill (b : Nat) (p : Pattern b) (f : Frontier p → Source)
    (branch : ∀ x, rootType (f x) = none) : expose b (fill p f) = p := by
  induction b with
  | zero => cases p with
    | inl c => rfl
    | inr q =>
      cases q
      cases h : f () with
      | of c => have bad := branch (); rw [h] at bad; cases c <;> cases bad
      | mul l r => change expose 0 (f ()) = _; rw [h]; rfl
  | succ b ih => cases p with
    | inl c => rfl
    | inr p => exact congrArg Sum.inr (congrArg₂ Prod.mk
        (ih p.1 _ (fun x => branch (.inl x)))
        (ih p.2 _ (fun x => branch (.inr x))))

/-- Each position has its original relative address. -/
def address : {b : Nat} → (p : Pattern b) → Frontier p → Address
  | 0, .inl _, x => PEmpty.elim x
  | 0, .inr _, _ => []
  | _+1, .inl _, x => PEmpty.elim x
  | _+1, .inr p, .inl x => false :: address p.1 x
  | _+1, .inr p, .inr x => true :: address p.2 x

private theorem fill_at (b : Nat) (p : Pattern b) (f : Frontier p → Source)
    (x : Frontier p) : subtree (address p x) (fill p f) = some (f x) := by
  induction b with
  | zero => cases p with
    | inl c => exact PEmpty.elim x
    | inr q => cases x; rfl
  | succ b ih => cases p with
    | inl c => exact PEmpty.elim x
    | inr p => cases x with
      | inl x => exact ih p.1 _ x
      | inr x => exact ih p.2 _ x

private theorem fill_injective (b : Nat) (p : Pattern b) :
    Function.Injective (fill p) := by
  intro f g eq
  funext x
  have h := congrArg (subtree (address p x)) eq
  rw [fill_at,fill_at] at h
  exact Option.some.inj h

private theorem prefix_fixed (b : Nat) (p : Pattern b)
    (f g : Frontier p → Source)
    (hf : ∀ x, rootType (f x) = none) (hg : ∀ x, rootType (g x) = none)
    (a : Address) (ha : a.length ≤ b) : readout a (fill p f) = readout a (fill p g) := by
  induction b generalizing a with
  | zero =>
    have ae : a = [] := List.length_eq_zero_iff.mp (by omega)
    subst a
    cases p with
    | inl c => rfl
    | inr q =>
      cases q
      cases ef : f () with
      | of c => have bad := hf (); rw [ef] at bad; cases c <;> cases bad
      | mul l r =>
        cases eg : g () with
        | of c => have bad := hg (); rw [eg] at bad; cases c <;> cases bad
        | mul l' r' => change readout [] (f ()) = readout [] (g ()); rw [ef,eg]; rfl
  | succ b ih =>
    cases p with
    | inl c => rfl
    | inr p => cases a with
      | nil => rfl
      | cons c a =>
        have hb : a.length ≤ b := by simpa using ha
        cases c
        · exact ih p.1 _ _ (fun x => hf (.inl x)) (fun x => hg (.inl x)) a hb
        · exact ih p.2 _ _ (fun x => hf (.inr x)) (fun x => hg (.inr x)) a hb

/-- Branch images; a live name can neither become a leaf nor a nonimage. -/
abbrev BranchImage := {t : Source // rootType t = none ∧ Image t}

/-- A class coordinate is part of a name. Repeated partners use this same coordinate. -/
abbrev Profiles (C : LiteralRow) (b : Nat) := Classes C → Pattern b
abbrev Variables {C : LiteralRow} {b : Nat} (η : Profiles C b) :=
  Σ d : Classes C, Frontier (η d)

/-- Exact ordered free syntax with no distinctness condition on name values. -/
def patternTerm {X : Type} : {b : Nat} → (p : Pattern b) → (Frontier p → X) → Term X
  | 0, .inl c, _ => .of (.inl c)
  | 0, .inr _, name => .of (.inr (name ()))
  | _+1, .inl c, _ => .of (.inl c)
  | _+1, .inr p, name => .mul (patternTerm p.1 (fun x => name (.inl x)))
      (patternTerm p.2 (fun x => name (.inr x)))

private theorem pattern_evaluate {X : Type} (b : Nat) (p : Pattern b)
    (name : Frontier p → X) (v : X → Source) :
    evaluate v (patternTerm p name) = fill p (v ∘ name) := by
  induction b with
  | zero => cases p <;> rfl
  | succ b ih => cases p with
    | inl c => rfl
    | inr p => exact congrArg₂ FreeMagma.mul (ih p.1 _) (ih p.2 _)

def oldTerm {C : LiteralRow} {b : Nat} (η : Profiles C b) (d : Classes C) :
    Term (Variables η) := patternTerm (η d) (fun x => ⟨d,x⟩)

def oldValues {C : LiteralRow} {b : Nat} (η : Profiles C b) (v : Variables η → Source) :
    Classes C → Source := fun d => fill (η d) (fun x => v ⟨d,x⟩)

private theorem old_evaluate {C : LiteralRow} {b : Nat} (η : Profiles C b)
    (v : Variables η → Source) (d : Classes C) :
    evaluate v (oldTerm η d) = oldValues η v d := pattern_evaluate b (η d) _ v

/-- The whole current exterior, with every occurrence of a partner synchronized. -/
def wholeTerm {C : LiteralRow} {b : Nat} (η : Profiles C b) : Term (Variables η) :=
  FreeMagma.lift (fun c => match c with
    | .inl c => .of (.inl c)
    | .inr n => if h : n ∈ labels C then oldTerm η ⟨n,h⟩ else .of (.inl true)) C

private theorem whole_evaluate {C : LiteralRow} {b : Nat} (η : Profiles C b)
    (v : Variables η → Source) :
    evaluate v (wholeTerm η) = evaluateRow (extend C (oldValues η v)) C := by
  have general (t : LiteralRow) :
      evaluate v (FreeMagma.lift (fun c => match c with
        | .inl c => .of (.inl c)
        | .inr n => if h : n ∈ labels C then oldTerm η ⟨n,h⟩ else .of (.inl true)) t) =
      evaluateRow (extend C (oldValues η v)) t := by
    induction t with
    | of c => cases c with
      | inl c => rfl
      | inr n =>
        change evaluate v (if h : n ∈ labels C then oldTerm η ⟨n,h⟩ else .of (.inl true)) =
          extend C (oldValues η v) n
        by_cases hn : n ∈ labels C
        · rw [dif_pos hn,extend,dif_pos hn]; exact old_evaluate η v ⟨n,hn⟩
        · rw [dif_neg hn,extend,dif_neg hn]; rfl
    | mul l r ihl ihr => exact congrArg₂ FreeMagma.mul ihl ihr
  exact general C

/-- The finite numbering of actual names is used only to call the original image grammar. -/
def number {X : Type} [Fintype X] (x : X) : Nat := (Fintype.equivFin X x).val

def numbered {X : Type} [Fintype X] : Term X →ₙ* LiteralRow :=
  FreeMagma.lift (Sum.elim (fun c => .of (.inl c)) (fun x => .of (.inr (number x))))

/-- FTC.22 on the original free syntax: names have branch root type. -/
def J {X : Type} [Fintype X] (A : Term X) : Prop :=
  NativeClassRootImage.im (fun _ => none) (numbered A)

private def betaPair : BranchImage :=
  ⟨.mul (.of false) (.of false),rfl,⟨.mul (.of true) (.of true),rfl⟩⟩

private def namedFill {X : Type} [Fintype X] (v : X → BranchImage) (n : Nat) : Source :=
  if h : n < Fintype.card X then (v ((Fintype.equivFin X).symm ⟨n,h⟩)).val else betaPair.val

private theorem namedFill_number {X : Type} [Fintype X] (v : X → BranchImage) (x : X) :
    namedFill v (number x) = (v x).val := by
  simp [namedFill,number]

private theorem namedFill_branch {X : Type} [Fintype X] (v : X → BranchImage) (n : Nat) :
    rootType (namedFill v n) = none := by
  unfold namedFill
  split
  · exact (v _).property.1
  · exact betaPair.property.1

private theorem numbered_evaluate {X : Type} [Fintype X] (v : X → BranchImage) (A : Term X) :
    evaluateRow (namedFill v) (numbered A) = evaluate (fun x => (v x).val) A := by
  induction A with
  | of c => cases c with
    | inl c => rfl
    | inr x => exact namedFill_number v x
  | mul l r ihl ihr => exact congrArg₂ FreeMagma.mul ihl ihr

private theorem image_test_exact {X : Type} [Fintype X] (v : X → BranchImage) (A : Term X) :
    Image (evaluate (fun x => (v x).val) A) ↔ J A := by
  rw [← numbered_evaluate,NativeClassRootImage.filling_image_iff]
  have roots : (fun n => rootType (namedFill v n)) = fun _ => none :=
    funext (namedFill_branch v)
  rw [roots]
  have lawful : NativeClassRootImage.BranchImages (numbered A) (namedFill v) := by
    intro n _ _
    unfold namedFill
    split
    · exact (v _).property.2
    · exact betaPair.property.2
  exact and_iff_right lawful

/-- Every branch subtree is an image; leaves, including alpha, carry no obligation. -/
def Safe : Source → Prop
  | .of _ => True
  | .mul l r => Image (.mul l r) ∧ Safe l ∧ Safe r

private theorem substitution_safe (u : Source) : Safe (substitution u) := by
  induction u with
  | of c =>
    cases c
    · exact ⟨⟨.of false,rfl⟩,True.intro,True.intro⟩
    · exact True.intro
  | mul l r ihl ihr => exact ⟨⟨.mul l r,rfl⟩,ihl,ihr⟩

private theorem image_safe {t : Source} (h : Image t) : Safe t := by
  obtain ⟨u,rfl⟩ := h
  exact substitution_safe u

private theorem safe_value (C : LiteralRow) (f : Nat → Source)
    (safe : Safe (evaluateRow f C)) (n : Nat) (hn : n ∈ labels C) : Safe (f n) := by
  induction C with
  | of c => cases c with
    | inl c => simp [labels] at hn
    | inr m => have eq : n = m := by simpa [labels] using hn
               subst n; exact safe
  | mul l r ihl ihr =>
    rcases Finset.mem_union.mp hn with hn | hn
    · exact ihl safe.2.1 hn
    · exact ihr safe.2.2 hn

private theorem extract_image (b : Nat) (t : Source) (safe : Safe t)
    (x : Frontier (expose b t)) : Image (extract b t x) := by
  induction b generalizing t with
  | zero => cases t with
    | of c => exact PEmpty.elim x
    | mul l r => exact safe.1
  | succ b ih => cases t with
    | of c => exact PEmpty.elim x
    | mul l r => cases x with
      | inl x => exact ih l safe.2.1 x
      | inr x => exact ih r safe.2.2 x

/-- Equal-mass image markers retain the original Boolean distinction. -/
private def marker (c : Bool) : Source :=
  if c then .mul (.mul (.of false) (.of false)) (.of false)
  else .mul (.of false) (.mul (.of false) (.of false))

private theorem marker_mass (c : Bool) : (marker c).length = 3 := by cases c <;> rfl
private theorem marker_injective : Function.Injective marker := by decide +kernel
private theorem marker_image (c : Bool) : Image (marker c) := by
  cases c
  · exact ⟨.mul (.of true) (.mul (.of true) (.of true)),rfl⟩
  · exact ⟨.mul (.mul (.of true) (.of true)) (.of true),rfl⟩

private theorem image_comb (n : Nat) (f : Fin n → Source) (q : Source)
    (hf : ∀ i, Image (f i)) (hq : Image q) : Image (comb n f q) := by
  induction n with
  | zero => exact hq
  | succ n ih =>
    obtain ⟨u,hu⟩ := hf 0
    obtain ⟨v,hv⟩ := ih (fun i => f i.succ) (fun i => hf i.succ)
    exact ⟨.mul u v,by
      change FreeMagma.mul (substitution u) (substitution v) = _
      rw [hu,hv]; rfl⟩

/-- An injective finite tuple of actual branch images with common unbounded mass. -/
def branchCode (n : Nat) (i : Fin n) : BranchImage :=
  ⟨.mul (comb n (fun j => marker (decide (j = i))) (.of false)) (.of false),
    rfl,by
      obtain ⟨u,hu⟩ := image_comb n (fun j => marker (decide (j = i))) (.of false)
        (fun j => marker_image _) ⟨.of true,rfl⟩
      exact ⟨.mul u (.of true),by
        change FreeMagma.mul (substitution u) (substitution (.of true)) = _
        rw [hu]; rfl⟩⟩

private theorem branchCode_mass (n : Nat) (i : Fin n) :
    (branchCode n i).val.length = 3*n+2 := by
  change (comb n (fun j => marker (decide (j = i))) (.of false)).length + 1 = _
  rw [(comb_foundation n (fun j => marker (decide (j = i)))
    (fun j => marker (decide (j = i))) (.of false) (.of false)).2.1]
  simp only [marker_mass,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    smul_eq_mul,FreeMagma.length]
  omega

private theorem branchCode_injective (n : Nat) : Function.Injective (branchCode n) := by
  intro i j eq
  have vals := congrArg Subtype.val eq
  have head : comb n (fun k => marker (decide (k = i))) (.of false) =
      comb n (fun k => marker (decide (k = j))) (.of false) := by injection vals
  have hs := ((comb_foundation n _ _ _ _).2.2.1.mp head).1
  have hi := marker_injective (congrFun hs i)
  simpa using hi.symm

/-- Retention is exactly the original image grammar and all whole-class syntax negatives. -/
abbrev Retained (C : LiteralRow) (b : Nat) :=
  {η : Profiles C b // J (wholeTerm η) ∧ Function.Injective (oldTerm η)}

/-- All lawful fillings, including coincidences between independent names. -/
abbrev Valuations {C : LiteralRow} {b : Nat} (η : Retained C b) :=
  {v : Variables η.val → BranchImage //
    Function.Injective (oldValues η.val (fun x => (v x).val))}

/-- The common mass is chosen above every whole free term in the tuple. -/
def syntaxBound {C : LiteralRow} {b : Nat} (η : Profiles C b) : Nat :=
  Finset.univ.sup (fun d => (oldTerm η d).length)

def codeSize {C : LiteralRow} {b : Nat} (η : Profiles C b) : Nat :=
  max (Fintype.card (Variables η)) (syntaxBound η)

/-- A single parameter varies every live value while leaving the profile fixed. -/
def familyValue {C : LiteralRow} {b : Nat} (η : Profiles C b) (k : Nat)
    (x : Variables η) : BranchImage :=
  branchCode (codeSize η+k) ⟨(Fintype.equivFin (Variables η) x).val,
    lt_of_lt_of_le (Fintype.equivFin (Variables η) x).isLt
      ((Nat.le_max_left _ _).trans (Nat.le_add_right _ _))⟩

private theorem family_mass {C : LiteralRow} {b : Nat} (η : Profiles C b)
    (k : Nat) (x : Variables η) :
    (familyValue η k x).val.length = 3*(codeSize η+k)+2 := branchCode_mass _ _

private theorem family_injective {C : LiteralRow} {b : Nat} (η : Profiles C b) (k : Nat) :
    Function.Injective (fun x => (familyValue η k x).val) := by
  intro x y h
  have hs := branchCode_injective (codeSize η+k) (Subtype.ext h)
  apply (Fintype.equivFin (Variables η)).injective
  apply Fin.ext
  exact congrArg (fun z : Fin (codeSize η+k) => z.val) hs

private theorem term_bound {C : LiteralRow} {b : Nat} (η : Profiles C b)
    (k : Nat) (d : Classes C) : (oldTerm η d).length < 3*(codeSize η+k)+2 := by
  have h := Finset.le_sup (f := fun d => (oldTerm η d).length) (Finset.mem_univ d)
  have hb : syntaxBound η ≤ codeSize η := Nat.le_max_right _ _
  change (oldTerm η d).length ≤ syntaxBound η at h
  omega

private theorem family_legal {C : LiteralRow} {b : Nat} (η : Retained C b) (k : Nat) :
    Function.Injective (oldValues η.val (fun x => (familyValue η.val k x).val)) := by
  intro d e eq
  apply η.property.2
  exact NativeGroundSeparation.bounded_eval_injective
    (fun x => (familyValue η.val k x).val) (3*(codeSize η.val+k)+2)
    (by omega) (family_mass η.val k) (family_injective η.val k)
    (oldTerm η.val d) (oldTerm η.val e) (term_bound η.val k d) (term_bound η.val k e)
    (by simpa only [old_evaluate] using eq)

/-- One simultaneous joint-negative solution for every parameter, including a closed profile. -/
def family {C : LiteralRow} {b : Nat} (η : Retained C b) (k : Nat) : Valuations η :=
  ⟨familyValue η.val k,family_legal η k⟩

private theorem family_parameter_injective {C : LiteralRow} {b : Nat} (η : Retained C b)
    (live : Nonempty (Variables η.val)) : Function.Injective (family η) := by
  obtain ⟨x⟩ := live
  intro k l h
  have eq := congrArg (fun v : Valuations η => (v.val x).val.length) h
  change (familyValue η.val k x).val.length = (familyValue η.val l x).val.length at eq
  rw [family_mass,family_mass] at eq
  omega

/-- The complete current tree of any lawful retained filling is an actual image. -/
def assemble {C : LiteralRow} {b : Nat} (η : Retained C b) (v : Valuations η) :
    NativeClassRootImage.ImageValues C :=
  ⟨⟨oldValues η.val (fun x => (v.val x).val),v.property⟩,by
    rw [← whole_evaluate]
    exact (image_test_exact v.val (wholeTerm η.val)).mpr η.property.1⟩

/-- The actual inclusive profile of all recovered whole class values. -/
def actualProfiles {C : LiteralRow} (b : Nat) (v : NativeClassRootImage.ImageValues C) :
    Profiles C b := fun d => expose b (v.val.val d)

private theorem value_safe {C : LiteralRow} (v : NativeClassRootImage.ImageValues C)
    (d : Classes C) : Safe (v.val.val d) := by
  have h := safe_value C (extend C v.val.val) (image_safe v.property) d.val d.property
  simpa only [extend,dif_pos d.property] using h

/-- Extracted live values are their original reached branch subtrees. -/
def actualFilling {C : LiteralRow} (b : Nat) (v : NativeClassRootImage.ImageValues C) :
    Variables (actualProfiles b v) → BranchImage := fun x =>
  ⟨extract b (v.val.val x.1) x.2,extract_branch b _ x.2,
    extract_image b _ (value_safe v x.1) x.2⟩

private theorem actual_values {C : LiteralRow} (b : Nat)
    (v : NativeClassRootImage.ImageValues C) :
    oldValues (actualProfiles b v) (fun x => (actualFilling b v x).val) = v.val.val := by
  funext d
  exact fill_extract b (v.val.val d)

/-- Every actual image valuation passes exactly the two retention tests. -/
def retain {C : LiteralRow} (b : Nat) (v : NativeClassRootImage.ImageValues C) : Retained C b :=
  ⟨actualProfiles b v,by
    constructor
    · apply (image_test_exact (actualFilling b v) (wholeTerm (actualProfiles b v))).mp
      rw [whole_evaluate,actual_values]
      exact v.property
    · intro d e eq
      apply v.val.property
      have he := congrArg (evaluate (fun x => (actualFilling b v x).val)) eq
      simpa only [old_evaluate,actual_values] using he⟩

/-- Actual extraction, with all joint negatives inherited from the original whole values. -/
def decompose {C : LiteralRow} (b : Nat) (v : NativeClassRootImage.ImageValues C) :
    Σ η : Retained C b, Valuations η :=
  ⟨retain b v,⟨actualFilling b v,by
    dsimp only [retain]
    rw [actual_values]
    exact v.val.property⟩⟩

private theorem assemble_decompose {C : LiteralRow} (b : Nat)
    (v : NativeClassRootImage.ImageValues C) :
    assemble (decompose b v).1 (decompose b v).2 = v := by
  apply Subtype.ext
  apply Subtype.ext
  exact actual_values b v

private theorem assemble_profiles {C : LiteralRow} {b : Nat}
    (η : Retained C b) (v : Valuations η) : actualProfiles b (assemble η v) = η.val := by
  funext d
  exact expose_fill b (η.val d) _ (fun x => (v.val ⟨d,x⟩).property.1)

private theorem assemble_injective {C : LiteralRow} {b : Nat} :
    Function.Injective (fun x : Σ η : Retained C b, Valuations η => assemble x.1 x.2) := by
  rintro ⟨η,v⟩ ⟨θ,w⟩ eq
  have ep : η = θ := by
    apply Subtype.ext
    have he := congrArg (actualProfiles b) eq
    simpa only [assemble_profiles] using he
  cases ep
  apply congrArg (Sigma.mk η)
  apply Subtype.ext
  funext x
  apply Subtype.ext
  have values := congrArg (fun z : NativeClassRootImage.ImageValues C => z.val.val) eq
  have hd := congrFun values x.1
  have hf := fill_injective b (η.val x.1) hd
  exact congrFun hf x.2

/-- Exact all-origin decomposition into retained inclusive profiles and lawful valuations. -/
def imageProfileEquiv (C : LiteralRow) (b : Nat) :
    NativeClassRootImage.ImageValues C ≃ Σ η : Retained C b, Valuations η where
  toFun := decompose b
  invFun x := assemble x.1 x.2
  left_inv := assemble_decompose b
  right_inv x := assemble_injective (assemble_decompose b (assemble x.1 x.2))

/-- The fixed row is the complete original repeated-partner row, on an actual current tree. -/
def currentRow : LiteralRow :=
  canonicalRow NativeSixSourceCones.P (substitution (NativeSixSourceCones.origin 0))

private theorem currentRow_original : currentRow = NativeSixSourceCones.row := by
  rw [currentRow,(NativeSixSourceCones.six_source_realization.1 0).1]
  exact (NativeSixSourceCones.six_source_realization.1 0).2.1

/-- This row-expression equivalence preserves the same original source. -/
def originalFiberEquiv : NativeSixSourceCones.Fiber ≃
    NativeClassRootImage.OriginFiber NativeSixSourceCones.P currentRow where
  toFun u := ⟨u.val,by rw [currentRow_original]; exact u.property⟩
  invFun u := ⟨u.val,by rw [← currentRow_original]; exact u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def originImageEquiv : NativeClassRootImage.ImageValues currentRow ≃
    NativeClassRootImage.OriginFiber NativeSixSourceCones.P currentRow :=
  NativeClassRootImage.imageOriginEquiv NativeSixSourceCones.P NativeSixSourceCones.prefix_free
    (substitution (NativeSixSourceCones.origin 0))

private theorem origin_evaluation (v : NativeClassRootImage.ImageValues currentRow) :
    substitution (originImageEquiv v).val = evaluateRow (extend currentRow v.val.val) currentRow := by
  have h := NativeCutFibers.recover_fill NativeSixSourceCones.P NativeSixSourceCones.prefix_free
    currentRow ⟨substitution (originImageEquiv v).val,(originImageEquiv v).property⟩
  change evaluateRow (extend currentRow (originImageEquiv.symm (originImageEquiv v)).val.val)
    currentRow = substitution (originImageEquiv v).val at h
  rw [originImageEquiv.symm_apply_apply] at h
  exact h.symm

/-- The equivalence acts on every actual origin in the original, unbounded fiber. -/
def partitionEquiv (b : Nat) : NativeSixSourceCones.Fiber ≃
    Σ η : Retained currentRow b, Valuations η :=
  originalFiberEquiv.trans (originImageEquiv.symm.trans (imageProfileEquiv currentRow b))

def profile (b : Nat) (u : NativeSixSourceCones.Fiber) : Retained currentRow b :=
  (partitionEquiv b u).1

/-- An actual cell, rather than a sample family or an unattainable reply vector. -/
abbrev Cell {b : Nat} (η : Retained currentRow b) :=
  {u : NativeSixSourceCones.Fiber // profile b u = η}

/-- The original actual inverse origin of a complete lawful filling. -/
def point {b : Nat} (η : Retained currentRow b) (v : Valuations η) :
    NativeSixSourceCones.Fiber := (partitionEquiv b).symm ⟨η,v⟩

private theorem point_profile {b : Nat} (η : Retained currentRow b) (v : Valuations η) :
    profile b (point η v) = η :=
  congrArg Sigma.fst ((partitionEquiv b).apply_symm_apply ⟨η,v⟩)

private theorem point_injective {b : Nat} (η : Retained currentRow b) :
    Function.Injective (point η) := by
  intro v w h
  have eq := (partitionEquiv b).symm.injective h
  exact eq_of_heq (Sigma.mk.inj eq).2

private theorem point_image {b : Nat} (η : Retained currentRow b) (v : Valuations η) :
    substitution (point η v).val =
      evaluateRow (extend currentRow (oldValues η.val (fun x => (v.val x).val))) currentRow :=
  origin_evaluation (assemble η v)

/-- The valuation equivalence restricts to precisely this one attained original cell. -/
def cellEquiv {b : Nat} (η : Retained currentRow b) : Valuations η ≃ Cell η :=
  Equiv.ofBijective (fun v => ⟨point η v,point_profile η v⟩) (by
    constructor
    · intro v w h
      exact point_injective η (congrArg Subtype.val h)
    · intro u
      generalize he : partitionEquiv b u.val = data
      rcases data with ⟨θ,w⟩
      have eq : θ = η := by
        have hp := u.property
        change (partitionEquiv b u.val).1 = η at hp
        rw [he] at hp
        exact hp
      cases eq
      refine ⟨w,?_⟩
      apply Subtype.ext
      have back := congrArg (partitionEquiv b).symm he
      rw [(partitionEquiv b).symm_apply_apply] at back
      exact back.symm)

private theorem cell_closed {b : Nat} (η : Retained currentRow b)
    (closed : IsEmpty (Variables η.val)) :
    ∃! u : NativeSixSourceCones.Fiber, profile b u = η := by
  letI := closed
  refine ⟨point η (family η 0),point_profile η _,?_⟩
  intro u hu
  have eq : (⟨u,hu⟩ : Cell η) = cellEquiv η (family η 0) := by
    apply (cellEquiv η).symm.injective
    apply Subtype.ext
    funext x
    exact isEmptyElim x
  exact congrArg Subtype.val eq

private theorem cell_live {b : Nat} (η : Retained currentRow b)
    (live : Nonempty (Variables η.val)) :
    ∃ f : Nat → Cell η, Function.Injective f := by
  exact ⟨fun k => cellEquiv η (family η k),
    (cellEquiv η).injective.comp (family_parameter_injective η live)⟩

private theorem cell_countable {b : Nat} (η : Retained currentRow b) : Countable (Cell η) := by
  exact inferInstance

private theorem point_target {b : Nat} (η : Retained currentRow b) (v : Valuations η) :
    NativeFullRootFeasibility.target currentRow
      (NativeClassRootImage.types currentRow (assemble η v).val.val) =
      canonicalRow NativeSixSourceCones.P (point η v).val := by
  have bridge := NativeFullRootFeasibility.native_full_root_feasibility
    NativeSixSourceCones.P NativeSixSourceCones.prefix_free (NativeSixSourceCones.origin 0)
    1 0 (by decide)
  exact (bridge.1 (assemble η v) (originImageEquiv (assemble η v))
    (origin_evaluation (assemble η v))).2.2

private theorem point_roots {b : Nat} (η : Retained currentRow b) (v w : Valuations η) :
    NativeClassRootImage.types currentRow (assemble η v).val.val =
      NativeClassRootImage.types currentRow (assemble η w).val.val := by
  funext d
  have h := prefix_fixed b (η.val d)
    (fun x => (v.val ⟨d,x⟩).val) (fun x => (w.val ⟨d,x⟩).val)
    (fun x => (v.val ⟨d,x⟩).property.1) (fun x => (w.val ⟨d,x⟩).property.1) [] (by simp)
  change rootType (fill (η.val d) _) = rootType (fill (η.val d) _)
  simp only [rootType,ActualImageSevenLeafSeparation.leafLabel,h]

private theorem point_targets {b : Nat} (η : Retained currentRow b) (v w : Valuations η) :
    canonicalRow NativeSixSourceCones.P (point η v).val =
      canonicalRow NativeSixSourceCones.P (point η w).val := by
  rw [← point_target,← point_target,point_roots η v w]

/-- The inclusive relative exposure bound uses every installed literal word. -/
def relativeDepth {Q H : Type} [Fintype Q] (M : NativeSixSourceMoore.Controller Q H) : Nat :=
  Finset.univ.sup (fun q => (M.addr q).length-3)

private theorem installed_bound {Q H : Type} [Fintype Q]
    (M : NativeSixSourceMoore.Controller Q H) (q : Q) :
    (M.addr q).length ≤ 3+relativeDepth M := by
  have h := Finset.le_sup (f := fun q => (M.addr q).length-3) (Finset.mem_univ q)
  change (M.addr q).length-3 ≤ relativeDepth M at h
  omega

private theorem row_prefix_fixed (b : Nat) (f g : Nat → Source)
    (same : ∀ n ∈ labels NativeSixSourceCones.row, ∀ w : Address, w.length ≤ b →
      readout w (f n) = readout w (g n)) (a : Address) (ha : a.length ≤ 3+b) :
    readout a (evaluateRow f NativeSixSourceCones.row) =
      readout a (evaluateRow g NativeSixSourceCones.row) := by
  rcases a with _ | ⟨c,a⟩
  · rfl
  rcases a with _ | ⟨d,a⟩
  · cases c <;> rfl
  rcases a with _ | ⟨e,w⟩
  · cases c <;> cases d <;> rfl
  have hw : w.length ≤ b := by simp only [List.length_cons] at ha; omega
  cases c <;> cases d <;> cases e
  · exact same 0 (by decide +kernel) w hw
  · exact same 1 (by decide +kernel) w hw
  · exact same 0 (by decide +kernel) w hw
  · exact same 3 (by decide +kernel) w hw
  · exact same 4 (by decide +kernel) w hw
  · exact same 5 (by decide +kernel) w hw
  · exact same 4 (by decide +kernel) w hw
  · exact same 7 (by decide +kernel) w hw

private theorem point_replies {Q H : Type} [Fintype Q]
    (M : NativeSixSourceMoore.Controller Q H) (η : Retained currentRow (relativeDepth M))
    (v w : Valuations η) (q : Q) :
    readout (M.addr q) (substitution (point η v).val) =
      readout (M.addr q) (substitution (point η w).val) := by
  rw [point_image,point_image]
  let f := extend currentRow (oldValues η.val (fun x => (v.val x).val))
  let g := extend currentRow (oldValues η.val (fun x => (w.val x).val))
  change readout (M.addr q) (evaluateRow f currentRow) =
    readout (M.addr q) (evaluateRow g currentRow)
  rw [congrArg (evaluateRow f) currentRow_original,congrArg (evaluateRow g) currentRow_original]
  apply row_prefix_fixed (relativeDepth M) f g _ _ (installed_bound M q)
  intro n hn a ha
  have hc : n ∈ labels currentRow := by simpa only [currentRow_original] using hn
  dsimp only [f,g,extend]
  rw [dif_pos hc,dif_pos hc]
  exact prefix_fixed (relativeDepth M) (η.val ⟨n,hc⟩) _ _
    (fun x => (v.val ⟨⟨n,hc⟩,x⟩).property.1)
    (fun x => (w.val ⟨⟨n,hc⟩,x⟩).property.1) a ha

/-- Original native Good: same substituted register, actual paid calls, and the whole stored row. -/
def Good {Q H : Type} (M : NativeSixSourceMoore.Controller Q H) (e : Q ⊕ H)
    (L : Nat) (u : NativeSixSourceCones.Fiber) : Prop :=
  ∃ h tr, NativeSixSourceMoore.Run M (substitution u.val) e tr h ∧
    tr.length ≤ L ∧ M.out h = canonicalRow NativeSixSourceCones.P u.val

private theorem point_good {Q H : Type} [Fintype Q]
    (M : NativeSixSourceMoore.Controller Q H) (e : Q ⊕ H) (L : Nat)
    (η : Retained currentRow (relativeDepth M)) (v w : Valuations η) :
    Good M e L (point η v) ↔ Good M e L (point η w) := by
  have step : (fun s => M.next s (readout (M.addr s) (substitution (point η v).val))) =
      (fun s => M.next s (readout (M.addr s) (substitution (point η w).val))) := by
    funext s
    rw [point_replies M η v w s]
  have evaluator (h : H) (tr : List Q) :
      (NativeSixSourceMoore.Run M (substitution (point η v).val) e tr h ∧ tr.length ≤ L) ↔
      (NativeSixSourceMoore.Run M (substitution (point η w).val) e tr h ∧ tr.length ≤ L) := by
    rw [← NativeSharedMooreSynthesis.native_evaluate_iff,
      ← NativeSharedMooreSynthesis.native_evaluate_iff,step]
  constructor
  · rintro ⟨h,tr,run,budget,out⟩
    have hp := (evaluator h tr).mp ⟨run,budget⟩
    exact ⟨h,tr,hp.1,hp.2,out.trans (point_targets η v w)⟩
  · rintro ⟨h,tr,run,budget,out⟩
    have hp := (evaluator h tr).mpr ⟨run,budget⟩
    exact ⟨h,tr,hp.1,hp.2,out.trans (point_targets η w v)⟩

/-- Recovered values concern this same source and this same substitution register. -/
def sourceValues (u : NativeSixSourceCones.Fiber) : Classes currentRow → Source :=
  (originImageEquiv.symm (originalFiberEquiv u)).val.val

private theorem source_evaluation (u : NativeSixSourceCones.Fiber) :
    evaluateRow (extend currentRow (sourceValues u)) currentRow = substitution u.val :=
  NativeCutFibers.recover_fill NativeSixSourceCones.P NativeSixSourceCones.prefix_free
    currentRow ⟨substitution u.val,(originalFiberEquiv u).property⟩

private theorem source_at (u : NativeSixSourceCones.Fiber) (d : Classes currentRow) :
    subtree (NativeWholeRowService.representative currentRow d) (substitution u.val) =
      some (sourceValues u d) := by
  rw [← source_evaluation u]
  exact NativeWholeRowService.representative_subtree currentRow (sourceValues u) d

private theorem point_values {b : Nat} (η : Retained currentRow b) (v : Valuations η) :
    sourceValues (point η v) = oldValues η.val (fun x => (v.val x).val) := by
  change (originImageEquiv.symm (originImageEquiv (assemble η v))).val.val = _
  rw [originImageEquiv.symm_apply_apply]
  rfl

/-- A fixed installed reply, defined using an attained point of the same exact cell. -/
def cellReplies {Q H : Type} [Fintype Q] (M : NativeSixSourceMoore.Controller Q H)
    (η : Retained currentRow (relativeDepth M)) (q : Q) : Reply :=
  readout (M.addr q) (substitution (point η (family η 0)).val)

def cellTarget {b : Nat} (η : Retained currentRow b) : LiteralRow :=
  canonicalRow NativeSixSourceCones.P (point η (family η 0)).val

def cellGood {Q H : Type} [Fintype Q] (M : NativeSixSourceMoore.Controller Q H)
    (e : Q ⊕ H) (L : Nat) (η : Retained currentRow (relativeDepth M)) : Prop :=
  Good M e L (point η (family η 0))

/-- The complete original finite-table partition: exact inclusive source
correspondence, joint branch-image attainment, actual multiplicities and both
native Good predicates on the very same cells. -/
theorem finite_exact_native_partition {Q H : Type} [Fintype Q] [Fintype H]
    (M : NativeSixSourceMoore.Controller Q H) (e₀ e₁ : Q ⊕ H)
    (_entriesDistinct : e₀ ≠ e₁) (L : Nat) :
    let b := relativeDepth M
    currentRow = NativeSixSourceCones.row ∧
    Fintype.card (Classes currentRow) = 6 ∧
    Finite (Retained currentRow b) ∧
    (∀ (η : Profiles currentRow b) (v : Variables η → BranchImage),
      Image (evaluate (fun x => (v x).val) (wholeTerm η)) ↔ J (wholeTerm η)) ∧
    (∀ u : NativeSixSourceCones.Fiber,
      evaluateRow (extend currentRow (sourceValues u)) currentRow = substitution u.val ∧
      (profile b u).val = (fun d => expose b (sourceValues u d)) ∧
      (∀ d : Classes currentRow,
        subtree (NativeWholeRowService.representative currentRow d) (substitution u.val) =
          some (sourceValues u d)) ∧
      point (profile b u) (partitionEquiv b u).2 = u) ∧
    (∀ (η : Retained currentRow b) (v : Valuations η),
      partitionEquiv b (point η v) = ⟨η,v⟩ ∧
      substitution (point η v).val =
        evaluateRow (extend currentRow (oldValues η.val (fun x => (v.val x).val))) currentRow ∧
      ∀ (d : Classes currentRow) (x : Frontier (η.val d)),
        subtree (address (η.val d) x) (sourceValues (point η v) d) =
          some (v.val ⟨d,x⟩).val) ∧
    (∀ η : Retained currentRow b,
      Nonempty (Cell η) ∧
      (IsEmpty (Variables η.val) → ∃! u : NativeSixSourceCones.Fiber, profile b u = η) ∧
      (Nonempty (Variables η.val) → ∃ f : Nat → Cell η, Function.Injective f) ∧
      Countable (Cell η) ∧
      ∀ u : NativeSixSourceCones.Fiber, profile b u = η →
        (∀ q : Q, readout (M.addr q) (substitution u.val) = cellReplies M η q) ∧
        canonicalRow NativeSixSourceCones.P u.val = cellTarget η ∧
        (Good M e₀ L u ↔ cellGood M e₀ L η) ∧
        (Good M e₁ L u ↔ cellGood M e₁ L η)) := by
  dsimp only
  refine ⟨currentRow_original,?_,inferInstance,?_,?_,?_,?_⟩
  · rw [currentRow_original]
    decide +kernel
  · intro η v
    exact image_test_exact v (wholeTerm η)
  · intro u
    exact ⟨source_evaluation u,rfl,source_at u,
      (partitionEquiv (relativeDepth M)).symm_apply_apply u⟩
  · intro η v
    refine ⟨(partitionEquiv (relativeDepth M)).apply_symm_apply ⟨η,v⟩,point_image η v,?_⟩
    intro d x
    rw [point_values]
    exact fill_at (relativeDepth M) (η.val d) _ x
  · intro η
    refine ⟨⟨cellEquiv η (family η 0)⟩,cell_closed η,cell_live η,cell_countable η,?_⟩
    intro u hu
    let v := (cellEquiv η).symm ⟨u,hu⟩
    have back : point η v = u :=
      congrArg Subtype.val ((cellEquiv η).apply_symm_apply ⟨u,hu⟩)
    rw [← back]
    exact ⟨point_replies M η v (family η 0),point_targets η v (family η 0),
      point_good M e₀ L η v (family η 0),point_good M e₁ L η v (family η 0)⟩

#print axioms finite_exact_native_partition
end D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeInclusiveImagePartition
