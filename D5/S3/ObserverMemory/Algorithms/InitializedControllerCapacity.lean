/- GID: D5/S3/ObserverMemory/Algorithms/InitializedControllerCapacity
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/InitializedControllerCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual silent states force finite embeddings into every persistent fiber. -/

import D5.S3.ObserverMemory.Algorithms.SaturatedControlRegion
import Mathlib.FieldTheory.Finiteness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.InitializedControllerCapacity

open D5.S3.ObserverMemory.Algorithms.InitializedControlProtocol
open D5.S3.ObserverMemory.Algorithms.FixedSplitRewriteBudget
open D5.S3.ObserverMemory.Algorithms.SaturatedControlRegion
open D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
attribute [local instance] Classical.propDecidable
universe u v w

set_option maxHeartbeats 1000000 in
-- Actual silent states and local leaf outputs supply the live separation inference.
/-- Every uniformly cumulatively bounded compliant controller, including those
with infinite persistent carriers, admits the necessary finite embeddings into
each readout fiber, both local carriers and its actual operational joint carrier.
The opposite-control comparisons use actual states in one saturated region. -/
theorem initialized_controller_capacity (d : Nat) (hd : 2 ≤ d)
    (A B : Submodule (ZMod 2) (Source d)) (split : IsCompl A B)
    (hA : 0 < Module.finrank (ZMod 2) A) (hB : 0 < Module.finrank (ZMod 2) B)
    {MA : Type u} {MB : Type v} {Root : Type w}
    (C : Controller split MA MB Root) (K : Nat) (hK : UniformCumulativeBudget C K) :
    (∀ a : A, Nonempty (Fin (1 + 2 ^ Module.finrank (ZMod 2)
      (LinearMap.range (controlRestriction B))) ↪ {m : MA // C.readA m = a})) ∧
    (∀ b : B, Nonempty (Fin (1 + 2 ^ Module.finrank (ZMod 2)
      (LinearMap.range (controlRestriction A))) ↪ {m : MB // C.readB m = b})) ∧
    Nonempty (Fin ((1 + 2 ^ Module.finrank (ZMod 2)
      (LinearMap.range (controlRestriction B))) * 2 ^ Module.finrank (ZMod 2) A) ↪ MA) ∧
    Nonempty (Fin ((1 + 2 ^ Module.finrank (ZMod 2)
      (LinearMap.range (controlRestriction A))) * 2 ^ Module.finrank (ZMod 2) B) ↪ MB) ∧
    Nonempty (Fin (2 ^ (d + 2)) ↪ C.State) := by
  classical
  let pA := A.projectionOnto B split
  let pB := B.projectionOnto A split.symm
  let ellA := controlRestriction A
  let ellB := controlRestriction B
  let e : Fin d → Source d := fun i => (Pi.single i 1, 0)
  obtain ⟨mstar, h, _, _, silent, _, coverage, initialInternal, successorLeaf⟩ :=
    saturated_silent_source_region d hd A B split hA hB C K hK
  let word : Source d → List (Action d) := fun z => Classical.choose (coverage z)
  let state : Source d → C.State := fun z => runWord C.step (word z) mstar
  have current (z : Source d) : C.readout (state z) = z :=
    Classical.choose_spec (coverage z)
  have readLeft (z : Source d) : C.readA (state z).val.1 = pA z := by
    have hh := congrArg pA (current z)
    simpa [Controller.readout, pA] using hh
  have readRight (z : Source d) : C.readB (state z).val.2 = pB z := by
    have hh := congrArg pB (current z)
    simpa [Controller.readout, pB] using hh
  have emptyTrace (z : Source d) (f : Action d) : C.trace f (state z) = [] :=
    List.eq_nil_of_length_eq_zero (silent (word z) f)
  have initialDifferentLeft (a : A) (z : Source d) :
      (state z).val.1 ≠ C.initA a := by
    intro he
    have hl := successorLeaf (word z)
    change (C.protocol (.rewrite h) (C.rootA (.rewrite h) (state z).val.1)).node [] =
      .inr () at hl
    rw [he] at hl
    exact initialInternal a 0 hl
  have initialDifferentRight (b : B) (z : Source d) :
      (state z).val.2 ≠ C.initB b := by
    intro he
    have hl := successorLeaf (word z)
    change (C.protocol (.rewrite h) (C.rootA (.rewrite h) (state z).val.1)).node [] =
      .inr () at hl
    rw [C.root_agree (state z).val (state z).property (.rewrite h), he] at hl
    have hi := C.root_agree (C.initial 0 b).val (C.initial 0 b).property (.rewrite h)
    change C.rootA (.rewrite h) (C.initA 0) = C.rootB (.rewrite h) (C.initB b) at hi
    rw [← hi] at hl
    exact initialInternal 0 b hl
  have binary (q : ZMod 2) : q = 0 ∨ q = 1 := by
    fin_cases q
    · exact Or.inl rfl
    · exact Or.inr rfl
  have onto {S : Submodule (ZMod 2) (Source d)}
      (hn : controlRestriction S ≠ 0) (q : ZMod 2) : ∃ a : S, controlRestriction S a = q := by
    obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hn
    have ha1 : controlRestriction S a = 1 := (binary _).resolve_left ha
    rcases binary q with rfl | rfl
    · exact ⟨0, map_zero _⟩
    · exact ⟨a, ha1⟩
  have dataExt {T : Type} [AddCommGroup T] [Module (ZMod 2) T]
      (F : Source d →ₗ[ZMod 2] T) (hz : ∀ i, F (e i) = 0)
      (z : Source d) (hc : z.2 = 0) : F z = 0 := by
    let incl := LinearMap.inl (ZMod 2) (Fin d → ZMod 2) (ZMod 2)
    have hF : F.comp incl = 0 := by
      apply (Pi.basisFun (ZMod 2) (Fin d)).ext
      intro i
      simpa [incl, e] using hz i
    have he : z = incl z.1 := Prod.ext rfl hc
    rw [he]
    exact LinearMap.congr_fun hF z.1
  have leftColumn (hn : ellB ≠ 0) : ∃ i, pA (e i) ≠ 0 := by
    by_contra hh
    push Not at hh
    obtain ⟨a, ha⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hA
    obtain ⟨b, hb⟩ := onto hn (ellA a)
    have hz : ((a : Source d) + (b : Source d)).2 = 0 := by
      change ellA a + ellB b = 0
      rw [hb]
      simpa only [ZModModule.neg_eq_self] using neg_add_cancel (ellA a)
    have he := dataExt pA hh (a.val + b.val) hz
    have hp : pA (a.val + b.val) = a := by simp [pA]
    exact ha (hp.symm.trans he)
  have rightColumn (hn : ellA ≠ 0) : ∃ i, pB (e i) ≠ 0 := by
    by_contra hh
    push Not at hh
    obtain ⟨b, hb⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hB
    obtain ⟨a, ha⟩ := onto hn (ellB b)
    have hz : ((a : Source d) + (b : Source d)).2 = 0 := by
      change ellA a + ellB b = 0
      rw [ha]
      simpa only [ZModModule.neg_eq_self] using neg_add_cancel (ellB b)
    have he := dataExt pB hh (a.val + b.val) hz
    have hp : pB (a.val + b.val) = b := by simp [pB]
    exact hb (hp.symm.trans he)
  have scalar (i : Fin d) (q : ZMod 2) : (Pi.single i q, 0) = q • e i := by
    ext j <;> simp [e, Pi.single_apply, smul_eq_mul]
  have outputLeft (z : Source d) (i : Fin d) :
      C.readA (C.step (.rewrite i) (state z)).val.1 = z.2 • pA (e i) := by
    have hh := (C.correct (state z).val (state z).property (.rewrite i)
      (C.trace (.rewrite i) (state z))
      (Classical.choose_spec (C.terminates (state z).val (state z).property (.rewrite i)))).1
    change C.readA (C.step (.rewrite i) (state z)).val.1 =
      pA ((Action.rewrite i).apply (C.readout (state z))) at hh
    rw [current, Action.apply, controlRewrite, scalar, map_smul] at hh
    exact hh
  have outputRight (z : Source d) (i : Fin d) :
      C.readB (C.step (.rewrite i) (state z)).val.2 = z.2 • pB (e i) := by
    have hh := (C.correct (state z).val (state z).property (.rewrite i)
      (C.trace (.rewrite i) (state z))
      (Classical.choose_spec (C.terminates (state z).val (state z).property (.rewrite i)))).2
    change C.readB (C.step (.rewrite i) (state z)).val.2 =
      pB ((Action.rewrite i).apply (C.readout (state z))) at hh
    rw [current, Action.apply, controlRewrite, scalar, map_smul] at hh
    exact hh
  have controlsLeft (hn : ellB ≠ 0) (z z' : Source d)
      (he : (state z).val.1 = (state z').val.1) : z.2 = z'.2 := by
    obtain ⟨i, hi⟩ := leftColumn hn
    apply smul_left_injective (ZMod 2) hi
    change z.2 • pA (e i) = z'.2 • pA (e i)
    rw [← outputLeft, ← outputLeft]
    change C.readA ((C.protocol (.rewrite i) (C.rootA (.rewrite i) (state z).val.1)).outA
      (state z).val.1 (bits (C.trace (.rewrite i) (state z)))) =
      C.readA ((C.protocol (.rewrite i) (C.rootA (.rewrite i) (state z').val.1)).outA
        (state z').val.1 (bits (C.trace (.rewrite i) (state z'))))
    rw [emptyTrace, emptyTrace, he]
  have controlsRight (hn : ellA ≠ 0) (z z' : Source d)
      (he : (state z).val.2 = (state z').val.2) : z.2 = z'.2 := by
    obtain ⟨i, hi⟩ := rightColumn hn
    apply smul_left_injective (ZMod 2) hi
    change z.2 • pB (e i) = z'.2 • pB (e i)
    rw [← outputRight, ← outputRight]
    change C.readB ((C.protocol (.rewrite i) (C.rootA (.rewrite i) (state z).val.1)).outB
      (state z).val.2 (bits (C.trace (.rewrite i) (state z)))) =
      C.readB ((C.protocol (.rewrite i) (C.rootA (.rewrite i) (state z').val.1)).outB
        (state z').val.2 (bits (C.trace (.rewrite i) (state z'))))
    rw [C.root_agree (state z).val (state z).property (.rewrite i),
      C.root_agree (state z').val (state z').property (.rewrite i),
      emptyTrace, emptyTrace, he]
  let RB := LinearMap.range ellB
  let RA := LinearMap.range ellA
  let partnerB : RB → B := fun q => Classical.choose q.property
  let partnerA : RA → A := fun q => Classical.choose q.property
  have partnerBValue (q : RB) : ellB (partnerB q) = q.val := Classical.choose_spec q.property
  have partnerAValue (q : RA) : ellA (partnerA q) = q.val := Classical.choose_spec q.property
  have fiberLeft (a : A) : Nonempty ((Unit ⊕ RB) ↪ {m : MA // C.readA m = a}) := by
    let g : Unit ⊕ RB → MA
      | .inl _ => C.initA a
      | .inr q => (state (a.val + (partnerB q).val)).val.1
    have hg (q : Unit ⊕ RB) : C.readA (g q) = a := by
      cases q with
      | inl _ => exact C.read_initA a
      | inr q => rw [readLeft]; simp [pA]
    refine ⟨⟨fun q => ⟨g q, hg q⟩, ?_⟩⟩
    intro q q' he
    have hval : g q = g q' := congrArg Subtype.val he
    cases q with
    | inl u => cases q' with
      | inl u' => exact congrArg Sum.inl (Subsingleton.elim u u')
      | inr q' => exact False.elim (initialDifferentLeft a _ hval.symm)
    | inr q => cases q' with
      | inl _ => exact False.elim (initialDifferentLeft a _ hval)
      | inr q' =>
        apply congrArg Sum.inr
        apply Subtype.ext
        by_cases hn : ellB = 0
        · have hq := partnerBValue q
          have hq' := partnerBValue q'
          rw [hn] at hq hq'
          exact hq.symm.trans hq'
        · have hc := controlsLeft hn (a.val + (partnerB q).val)
            (a.val + (partnerB q').val) hval
          change ellA a + ellB (partnerB q) = ellA a + ellB (partnerB q') at hc
          rw [partnerBValue, partnerBValue] at hc
          exact add_left_cancel hc
  have fiberRight (b : B) : Nonempty ((Unit ⊕ RA) ↪ {m : MB // C.readB m = b}) := by
    let g : Unit ⊕ RA → MB
      | .inl _ => C.initB b
      | .inr q => (state ((partnerA q).val + b.val)).val.2
    have hg (q : Unit ⊕ RA) : C.readB (g q) = b := by
      cases q with
      | inl _ => exact C.read_initB b
      | inr q => rw [readRight]; simp [pB]
    refine ⟨⟨fun q => ⟨g q, hg q⟩, ?_⟩⟩
    intro q q' he
    have hval : g q = g q' := congrArg Subtype.val he
    cases q with
    | inl u => cases q' with
      | inl u' => exact congrArg Sum.inl (Subsingleton.elim u u')
      | inr q' => exact False.elim (initialDifferentRight b _ hval.symm)
    | inr q => cases q' with
      | inl _ => exact False.elim (initialDifferentRight b _ hval)
      | inr q' =>
        apply congrArg Sum.inr
        apply Subtype.ext
        by_cases hn : ellA = 0
        · have hq := partnerAValue q
          have hq' := partnerAValue q'
          rw [hn] at hq hq'
          exact hq.symm.trans hq'
        · have hc := controlsRight hn ((partnerA q).val + b.val)
            ((partnerA q').val + b.val) hval
          change ellA (partnerA q) + ellB b = ellA (partnerA q') + ellB b at hc
          rw [partnerAValue, partnerAValue] at hc
          exact add_right_cancel hc
  have joint : Nonempty ((Source d ⊕ Source d) ↪ C.State) := by
    let g : Source d ⊕ Source d → C.State
      | .inl z => C.initial (pA z) (pB z)
      | .inr z => state z
    have hg (q : Source d ⊕ Source d) : C.readout (g q) = Sum.elim id id q := by
      cases q with
      | inl z =>
        change (C.readA (C.initA (pA z)) : Source d) +
          (C.readB (C.initB (pB z)) : Source d) = z
        rw [C.read_initA, C.read_initB]
        exact Submodule.projection_add_projection_eq_self split z
      | inr z => exact current z
    refine ⟨⟨g, ?_⟩⟩
    intro q q' he
    have hr := congrArg C.readout he
    rw [hg, hg] at hr
    cases q with
    | inl z => cases q' with
      | inl z' => exact congrArg Sum.inl hr
      | inr z' =>
        have hv := congrArg (fun m : C.State => m.val.1) he
        exact False.elim (initialDifferentLeft (pA z) z' hv.symm)
    | inr z => cases q' with
      | inl z' =>
        have hv := congrArg (fun m : C.State => m.val.1) he
        exact False.elim (initialDifferentLeft (pA z') z hv)
      | inr z' => exact congrArg Sum.inr hr
  let _ := Fintype.ofFinite A
  let _ := Fintype.ofFinite B
  let _ := Fintype.ofFinite RA
  let _ := Fintype.ofFinite RB
  have rangeCountB : Fintype.card RB = 2 ^ Module.finrank (ZMod 2) RB := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  have rangeCountA : Fintype.card RA = 2 ^ Module.finrank (ZMod 2) RA := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  have fiberCountB : Fintype.card (Unit ⊕ RB) = 1 + 2 ^ Module.finrank (ZMod 2) RB := by
    rw [Fintype.card_sum, Fintype.card_unit, rangeCountB]
  have fiberCountA : Fintype.card (Unit ⊕ RA) = 1 + 2 ^ Module.finrank (ZMod 2) RA := by
    rw [Fintype.card_sum, Fintype.card_unit, rangeCountA]
  have totalLeft : Nonempty ((A × (Unit ⊕ RB)) ↪ MA) := by
    let ef := fun a => Classical.choice (fiberLeft a)
    refine ⟨⟨fun x => (ef x.1 x.2).val, ?_⟩⟩
    intro x y he
    have ha : x.1 = y.1 := (ef x.1 x.2).property.symm.trans
      ((congrArg C.readA he).trans (ef y.1 y.2).property)
    rcases x with ⟨a, q⟩
    rcases y with ⟨b, q'⟩
    dsimp only at ha
    subst b
    exact Prod.ext rfl ((ef a).injective (Subtype.ext he))
  have totalRight : Nonempty ((B × (Unit ⊕ RA)) ↪ MB) := by
    let ef := fun b => Classical.choice (fiberRight b)
    refine ⟨⟨fun x => (ef x.1 x.2).val, ?_⟩⟩
    intro x y he
    have hb : x.1 = y.1 := (ef x.1 x.2).property.symm.trans
      ((congrArg C.readB he).trans (ef y.1 y.2).property)
    rcases x with ⟨a, q⟩
    rcases y with ⟨b, q'⟩
    dsimp only at hb
    subst b
    exact Prod.ext rfl ((ef a).injective (Subtype.ext he))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a
    exact ⟨(Fintype.equivFinOfCardEq fiberCountB).symm.toEmbedding.trans
      (Classical.choice (fiberLeft a))⟩
  · intro b
    exact ⟨(Fintype.equivFinOfCardEq fiberCountA).symm.toEmbedding.trans
      (Classical.choice (fiberRight b))⟩
  · have hc : Fintype.card (A × (Unit ⊕ RB)) =
        (1 + 2 ^ Module.finrank (ZMod 2) RB) * 2 ^ Module.finrank (ZMod 2) A := by
      rw [Fintype.card_prod, fiberCountB, Module.card_eq_pow_finrank (K := ZMod 2),
        ZMod.card, Nat.mul_comm]
    exact ⟨(Fintype.equivFinOfCardEq hc).symm.toEmbedding.trans
      (Classical.choice totalLeft)⟩
  · have hc : Fintype.card (B × (Unit ⊕ RA)) =
        (1 + 2 ^ Module.finrank (ZMod 2) RA) * 2 ^ Module.finrank (ZMod 2) B := by
      rw [Fintype.card_prod, fiberCountA, Module.card_eq_pow_finrank (K := ZMod 2),
        ZMod.card, Nat.mul_comm]
    exact ⟨(Fintype.equivFinOfCardEq hc).symm.toEmbedding.trans
      (Classical.choice totalRight)⟩
  · have hc : Fintype.card (Source d ⊕ Source d) = 2 ^ (d + 2) := by
      simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fun,
        Fintype.card_fin, ZMod.card]
      rw [show d + 2 = d + 1 + 1 by omega, pow_succ, pow_succ]
      ring
    exact ⟨(Fintype.equivFinOfCardEq hc).symm.toEmbedding.trans (Classical.choice joint)⟩

#print axioms initialized_controller_capacity

end D5.S3.ObserverMemory.Algorithms.InitializedControllerCapacity
