/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Recursive image filling and exact class-root realization on full native fibers. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
import D5.S3.Arith.FibonacciAtomic.SourceCoordinates.IntrinsicSubstitutionCoordinates
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage

open GenealogicalFiberTransport (Source substitution)
open ActualImageSevenLeafSeparation (leafLabel)
open ActualCutPartitionRecovery (LiteralRow evaluateRow CutSet CutPrefixFree canonicalRow)
open NativeCutFibers
open SourceCoordinates.IntrinsicSubstitutionCoordinates (no_alpha pair_image)

/-- The reached root has three types: some true, some false, and none. -/
abbrev rootType (t : Source) : Option Bool := leafLabel t []

/-- Membership in the image of the original substitution. -/
def Image (t : Source) : Prop := ∃ u : Source, substitution u = t

/-- Literal leaves in the exterior, including shared class leaves. -/
def lit (θ : Nat → Option Bool) (b : Bool) : LiteralRow → Prop
  | .of (.inl c) => c = b
  | .of (.inr n) => θ n = some b
  | .mul _ _ => False

/-- The finite image grammar with the exceptional beta-alpha block. -/
def im (θ : Nat → Option Bool) : LiteralRow → Prop
  | .of (.inl b) => b = false
  | .of (.inr n) => θ n ≠ some true
  | .mul l r => (lit θ false l ∧ lit θ true r) ∨ (im θ l ∧ im θ r)

/-- Only actually occurring branch values carry an image obligation. -/
def BranchImages (C : LiteralRow) (f : Nat → Source) : Prop :=
  ∀ n ∈ labels C, rootType (f n) = none → Image (f n)

private theorem root_leaf (t : Source) (b : Bool) : rootType t = some b ↔ t = .of b := by
  cases t with
  | of c => cases c <;> cases b <;> decide
  | mul l r => simp [rootType, leafLabel, ActualTreeReadoutAcquisition.readout]

private theorem image_leaf (b : Bool) : Image (.of b) ↔ b = false := by
  cases b with
  | false => exact ⟨fun _ => rfl, fun _ => ⟨.of true, rfl⟩⟩
  | true => exact ⟨fun ⟨u,hu⟩ => False.elim (no_alpha u hu), fun h => Bool.noConfusion h⟩

theorem evaluate_leaf (C : LiteralRow) (f : Nat → Source) (b : Bool) :
    evaluateRow f C = .of b ↔ lit (fun n => rootType (f n)) b C := by
  cases C with
  | of a => cases a with
    | inl c =>
        change FreeMagma.of c = .of b ↔ c = b
        constructor
        · intro h; injection h
        · rintro rfl; rfl
    | inr n => exact (root_leaf (f n) b).symm
  | mul l r => simp [evaluateRow, lit]

private theorem leaf_branch_vacuous (C : LiteralRow) (f : Nat → Source) (b : Bool)
    (h : evaluateRow f C = .of b) : BranchImages C f := by
  cases C with
  | of a => cases a with
    | inl c => simp [BranchImages, labels]
    | inr n =>
        intro m hm hr
        have mn : m = n := by simpa [labels] using hm
        subst m
        have hb : rootType (f n) = some b := (root_leaf _ _).mpr h
        rw [hb] at hr
        cases hr
  | mul l r => change FreeMagma.mul _ _ = .of b at h; cases h

/-- Every actual filling is an image exactly when its occurring branches are
images and its complete exterior satisfies the finite recursive grammar. -/
theorem filling_image_iff (C : LiteralRow) (f : Nat → Source) :
    Image (evaluateRow f C) ↔
      BranchImages C f ∧ im (fun n => rootType (f n)) C := by
  induction C with
  | of a => cases a with
    | inl b => simp [evaluateRow, image_leaf, BranchImages, labels, im]
    | inr n =>
        change Image (f n) ↔ _
        cases hf : f n with
        | of b => cases b <;>
            simp [BranchImages, labels, im, hf, rootType, leafLabel,
              ActualTreeReadoutAcquisition.readout, image_leaf]
        | mul l r =>
            simp [BranchImages, labels, im, hf, rootType, leafLabel,
              ActualTreeReadoutAcquisition.readout]
  | mul l r ihl ihr =>
      change Image (.mul (evaluateRow f l) (evaluateRow f r)) ↔ _
      rw [show Image (.mul (evaluateRow f l) (evaluateRow f r)) ↔
        (evaluateRow f l = .of false ∧ evaluateRow f r = .of true) ∨
        (Image (evaluateRow f l) ∧ Image (evaluateRow f r)) from pair_image _ _]
      have split : BranchImages (.mul l r) f ↔ BranchImages l f ∧ BranchImages r f := by
        simp only [BranchImages, labels, Finset.mem_union]
        constructor
        · intro h; exact ⟨fun n hn => h n (Or.inl hn), fun n hn => h n (Or.inr hn)⟩
        · rintro ⟨hl,hr⟩ n (hn | hn)
          · exact hl n hn
          · exact hr n hn
      rw [split]
      constructor
      · rintro (⟨hl,hr⟩ | ⟨hl,hr⟩)
        · exact ⟨⟨leaf_branch_vacuous l f false hl, leaf_branch_vacuous r f true hr⟩,
            Or.inl ⟨(evaluate_leaf l f false).mp hl, (evaluate_leaf r f true).mp hr⟩⟩
        · exact ⟨⟨(ihl.mp hl).1,(ihr.mp hr).1⟩, Or.inr ⟨(ihl.mp hl).2,(ihr.mp hr).2⟩⟩
      · rintro ⟨⟨hl,hr⟩, (⟨ll,lr⟩ | ⟨il,ir⟩)⟩
        · exact Or.inl ⟨(evaluate_leaf l f false).mpr ll,(evaluate_leaf r f true).mpr lr⟩
        · exact Or.inr ⟨ihl.mpr ⟨hl,il⟩,ihr.mpr ⟨hr,ir⟩⟩

/-- Extend a type assignment only to evaluate the finite exterior predicate. -/
def typeExtend (C : LiteralRow) (θ : Classes C → Option Bool) (n : Nat) : Option Bool :=
  if h : n ∈ labels C then θ ⟨n,h⟩ else some true

/-- The roots of all and only the appearing class values. -/
def types (C : LiteralRow) (v : Classes C → Source) : Classes C → Option Bool :=
  fun d => rootType (v d)

/-- Finite feasible chart; the two bounds count distinct classes. -/
def Admissible (C : LiteralRow) (θ : Classes C → Option Bool) : Prop :=
  im (typeExtend C θ) C ∧
  (Finset.univ.filter (fun d => θ d = some true)).card ≤ 1 ∧
  (Finset.univ.filter (fun d => θ d = some false)).card ≤ 1

/-- Actual origins whose one-step image has the complete prescribed row. -/
abbrev OriginFiber (P : CutSet) (C : LiteralRow) :=
  {u : Source // canonicalRow P (substitution u) = C}

theorem root_extend (C : LiteralRow) (v : Classes C → Source) :
    (fun n => rootType (extend C v n)) = typeExtend C (types C v) := by
  funext n
  by_cases h : n ∈ labels C
  · simp [extend, typeExtend, types, h]
  · simp [extend, typeExtend, h, rootType, leafLabel, ActualTreeReadoutAcquisition.readout]

private theorem types_leaf_bound (C : LiteralRow) (v : LegalValues C) (b : Bool) :
    (Finset.univ.filter (fun d => types C v.val d = some b)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro d hd e he
  have hd' : rootType (v.val d) = some b := (Finset.mem_filter.mp hd).2
  have he' : rootType (v.val e) = some b := (Finset.mem_filter.mp he).2
  exact v.property (((root_leaf _ _).mp hd').trans ((root_leaf _ _).mp he').symm)

private theorem prescribed_values (C : LiteralRow) (θ : Classes C → Option Bool)
    (ha : (Finset.univ.filter (fun d => θ d = some true)).card ≤ 1)
    (hb : (Finset.univ.filter (fun d => θ d = some false)).card ≤ 1) :
    ∃ v : LegalValues C, types C v.val = θ ∧ BranchImages C (extend C v.val) := by
  classical
  let k := Fintype.card (Classes C)
  let e := Fintype.equivFin (Classes C)
  let w (d : Classes C) : Source :=
    substitution (.mul (NativeGroundSeparation.code k (e d)) (.of true))
  have wr (d : Classes C) : rootType (w d) = none := by
    simp [w, substitution.map_mul, rootType, leafLabel, ActualTreeReadoutAcquisition.readout]
  have wi : Function.Injective w := by
    intro d c h
    have inj : Function.Injective substitution :=
      SourceTransportCentralizer.source_transport_centralizer.2.2.1 substitution
        ⟨substitution.map_mul, fun _ => rfl⟩
    have hp := inj h
    have hc : NativeGroundSeparation.code k (e d) = NativeGroundSeparation.code k (e c) :=
      by injection hp
    exact e.injective (NativeGroundSeparation.code_injective k hc)
  let v (d : Classes C) : Source := match θ d with
    | some b => .of b
    | none => w d
  have vt (d : Classes C) : rootType (v d) = θ d := by
    dsimp [v]
    cases ht : θ d with
    | none => exact wr d
    | some b => cases b <;> rfl
  have vi : Function.Injective v := by
    intro d c eq
    have rt : θ d = θ c := (vt d).symm.trans ((congrArg rootType eq).trans (vt c))
    cases hd : θ d with
    | none =>
        have hc : θ c = none := rt.symm.trans hd
        apply wi
        simpa [v,hd,hc] using eq
    | some b =>
        have hc : θ c = some b := rt.symm.trans hd
        have bound : (Finset.univ.filter (fun d => θ d = some b)).card ≤ 1 := by
          cases b
          · exact hb
          · exact ha
        exact Finset.card_le_one.mp bound d (by simp [hd]) c (by simp [hc])
  refine ⟨⟨v,vi⟩, funext vt, ?_⟩
  intro n hn hr
  let d : Classes C := ⟨n,hn⟩
  have hd : θ d = none := by simpa [extend,hn,← vt d] using hr
  refine ⟨.mul (NativeGroundSeparation.code k (e d)) (.of true), ?_⟩
  simp [extend,hn,v,hd,w,d]

private theorem chart_values (C : LiteralRow) (θ : Classes C → Option Bool) :
    Admissible C θ ↔ ∃ v : LegalValues C,
      Image (evaluateRow (extend C v.val) C) ∧ types C v.val = θ := by
  constructor
  · rintro ⟨hi,ha,hb⟩
    obtain ⟨v,ht,hbr⟩ := prescribed_values C θ ha hb
    refine ⟨v, (filling_image_iff C _).mpr ⟨hbr, ?_⟩, ht⟩
    rwa [root_extend,ht]
  · rintro ⟨v,hi,rfl⟩
    refine ⟨?_, types_leaf_bound C v true, types_leaf_bound C v false⟩
    have h := ((filling_image_iff C _).mp hi).2
    rwa [root_extend] at h

/-- Injective appearing-class valuations whose filled exterior is an image. -/
abbrev ImageValues (C : LiteralRow) :=
  {v : LegalValues C // Image (evaluateRow (extend C v.val) C)}

/-- The exact legal-row equivalence composed with the original image inverse. -/
def imageOriginEquiv (P : CutSet) (hP : CutPrefixFree P) (t₀ : Source) :
    ImageValues (canonicalRow P t₀) ≃ OriginFiber P (canonicalRow P t₀) := by
  let C := canonicalRow P t₀
  let E := rowFiberEquiv P hP t₀
  have inverse : ∃! δ : Set.range substitution → Source,
      (∀ t : Source, δ ⟨substitution t,⟨t,rfl⟩⟩ = t) ∧
      (∀ y : Set.range substitution, (⟨substitution (δ y),⟨δ y,rfl⟩⟩ :
        Set.range substitution) = y) := by
    exact (SourceTransportCentralizer.source_transport_centralizer.2.2.2.2 1 (by decide)).1
  let δ := inverse.choose
  have left := inverse.choose_spec.1.1
  have right := inverse.choose_spec.1.2
  let out (v : ImageValues C) : OriginFiber P C :=
    ⟨δ ⟨(E v.val).val,v.property⟩, by
      have h := congrArg Subtype.val (right ⟨(E v.val).val,v.property⟩)
      change substitution (δ ⟨(E v.val).val,v.property⟩) = (E v.val).val at h
      exact (congrArg (canonicalRow P) h).trans (E v.val).property⟩
  let back (u : OriginFiber P C) : ImageValues C :=
    ⟨E.symm ⟨substitution u.val,u.property⟩, by
      have h := congrArg Subtype.val (E.apply_symm_apply ⟨substitution u.val,u.property⟩)
      exact ⟨u.val,h.symm⟩⟩
  refine ⟨out,back,?_,?_⟩
  · intro v
    apply Subtype.ext
    apply E.injective
    have h := congrArg Subtype.val (right ⟨(E v.val).val,v.property⟩)
    exact (E.apply_symm_apply _).trans (Subtype.ext h)
  · intro u
    apply Subtype.ext
    have h := E.apply_symm_apply ⟨substitution u.val,u.property⟩
    change δ ⟨(E (E.symm ⟨substitution u.val,u.property⟩)).val,_⟩ = u.val
    simpa only [h] using left u.val

/-- The finite chart equals exactly the types attained by every actual finite
origin in the full one-image fiber of a complete prefix-free native row. -/
theorem class_root_chart (P : CutSet) (hP : CutPrefixFree P) (t₀ : Source)
    (θ : Classes (canonicalRow P t₀) → Option Bool) :
    Admissible (canonicalRow P t₀) θ ↔
      ∃ u : OriginFiber P (canonicalRow P t₀),
        types (canonicalRow P t₀)
          (recover P hP (canonicalRow P t₀) ⟨substitution u.val,u.property⟩).val = θ := by
  let C := canonicalRow P t₀
  let E := imageOriginEquiv P hP t₀
  constructor
  · intro h
    obtain ⟨v,hv,ht⟩ := (chart_values C θ).mp h
    refine ⟨E ⟨v,hv⟩, ?_⟩
    change types C (E.symm (E ⟨v,hv⟩)).val.val = θ
    rw [E.symm_apply_apply]
    exact ht
  · rintro ⟨u,ht⟩
    exact (chart_values C θ).mpr ⟨(E.symm u).val,(E.symm u).property,ht⟩

#print axioms filling_image_iff
#print axioms imageOriginEquiv
#print axioms class_root_chart
end D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage
