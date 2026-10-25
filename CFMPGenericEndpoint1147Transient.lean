import CFMPRawFaceCapSlice1053Transient
import D5.S3.Geometry.Gluing.ActualEndpointReturnClasses

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace D5.S3.Geometry.Gluing.RawFaceEndpointCandidate
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing)
open D5.S3.Geometry.Gluing.ActualLinkCornerChains (Dart)
open D5.S3.Geometry.Gluing.ActualEndpointReturnClasses (delta)
open D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate
variable {T : Type*}
-- Temporary bind-only checks; no fixed group action or finite hypothesis is used.
def dartMove (P : RawFacePairing T) (f : Fin 4) (d : Dart T) : Dart T :=
  (((P.facePair (d.1.1,f)).1, sigma P (d.1.1,f) d.1.2), sigma P (d.1.1,f) d.2)
def DartStep (P : RawFacePairing T) (d e : Dart T) : Prop :=
  ∃ f : Fin 4, f ≠ d.1.2 ∧ f ≠ d.2 ∧ e = dartMove P f d
abbrev DartRelated (P : RawFacePairing T) := Relation.EqvGen (DartStep P)
def Flag (P : RawFacePairing T) (ν : Vertex P) :=
  {d : Dart T // d.1.2 ≠ d.2 ∧ label P d.1 = ν}
private theorem delta_carrier (P : RawFacePairing T) (d : Dart T) (hd : d.1.2 ≠ d.2) :
    (d.1, delta d.2) ∈ Carrier P (label P d.1) := by
  refine ⟨by simp [delta, hd], ?_, ?_, rfl⟩
  · intro i; simp only [delta]; split_ifs <;> norm_num
  · simp [delta]
def endpoint (P : RawFacePairing T) {ν : Vertex P} (d : Flag P ν) : Point P ν :=
  ⟨(d.val.1, delta d.val.2), by
    simpa only [d.property.2] using delta_carrier P d.val d.property.1⟩
theorem delta_move (s : Equiv.Perm (Fin 4)) (k : Fin 4) :
    (fun i => delta k (s.symm i)) = delta (s k) := by
  funext i; simp only [delta, Equiv.symm_apply_eq]
theorem endpoint_injective (P : RawFacePairing T) {ν : Vertex P} :
    Function.Injective (endpoint P (ν := ν)) := by
  intro d e h
  have hc := congrArg Prod.fst (congrArg Subtype.val h)
  have hk := congrFun (congrArg Prod.snd (congrArg Subtype.val h)) d.val.2
  have ht : d.val.2 = e.val.2 := by
    by_contra hn; simp [endpoint, delta, hn] at hk
  exact Subtype.ext (Prod.ext hc ht)
theorem dart_step_flags (P : RawFacePairing T) (ν : Vertex P)
    {d e : Dart T} (h : DartStep P d e) :
    (d.1.2 ≠ d.2 ∧ label P d.1 = ν) ↔ (e.1.2 ≠ e.2 ∧ label P e.1 = ν) := by
  obtain ⟨f, hfj, _, rfl⟩ := h
  have hn : (dartMove P f d).1.2 ≠ (dartMove P f d).2 ↔ d.1.2 ≠ d.2 :=
    (sigma P (d.1.1,f)).injective.ne_iff
  by_cases hd : d.1.2 = d.2
  · simp only [hn, hd, ne_eq, not_true_eq_false, false_and]
  · let x : Point P (label P d.1) := ⟨(d.1, delta d.2), delta_carrier P d hd⟩
    have hl := (pairedPoint P x f hfj).property.2.2.2
    change label P (dartMove P f d).1 = label P d.1 at hl
    rw [hn, hl]
theorem dart_chain_flags (P : RawFacePairing T) (ν : Vertex P)
    {d e : Dart T} (h : DartRelated P d e) :
    (d.1.2 ≠ d.2 ∧ label P d.1 = ν) ↔ (e.1.2 ≠ e.2 ∧ label P e.1 = ν) := by
  induction h with
  | rel d e h => exact dart_step_flags P ν h
  | refl d => rfl
  | symm d e _ ih => exact ih.symm
  | trans d e f _ _ ih₁ ih₂ => exact ih₁.trans ih₂
theorem endpoint_step (P : RawFacePairing T) {ν : Vertex P} (d e : Flag P ν) :
    Step P (endpoint P d) (endpoint P e) ↔ DartStep P d.val e.val := by
  constructor
  · rintro ⟨f, hj, hzero, he⟩
    have hk : f ≠ d.val.2 := by intro hk; simp [endpoint, delta, hk] at hzero
    refine ⟨f, hj, hk, ?_⟩
    have hc := congrArg Prod.fst he
    have ht := congrFun (congrArg Prod.snd he) (sigma P (d.val.1.1,f) d.val.2)
    change delta e.val.2 (sigma P (d.val.1.1,f) d.val.2) =
      delta d.val.2 ((sigma P (d.val.1.1,f)).symm
        (sigma P (d.val.1.1,f) d.val.2)) at ht
    simp only [Equiv.symm_apply_apply, delta, ite_true] at ht
    have heq : sigma P (d.val.1.1,f) d.val.2 = e.val.2 := by
      by_contra hh; simp [hh] at ht
    exact Prod.ext hc heq.symm
  · rintro ⟨f, hj, hk, he⟩
    refine ⟨f, hj, by simp [endpoint, delta, hk], ?_⟩
    apply Prod.ext
    · change e.val.1 = (dartMove P f d.val).1
      exact congrArg Prod.fst he
    · change delta e.val.2 = fun i => delta d.val.2 ((sigma P (d.val.1.1,f)).symm i)
      rw [delta_move]
      exact congrArg delta (congrArg Prod.snd he)
private theorem saturated_restriction {A : Type*} (r : A → A → Prop) (S : Set A)
    (hs : ∀ {a b}, Relation.EqvGen r a b → (a ∈ S ↔ b ∈ S)) (x y : ↥S) :
    Relation.EqvGen r x.val y.val ↔
      Relation.EqvGen (fun a b : ↥S => r a.val b.val) x y := by
  constructor
  · intro h
    have lift : ∀ {a b}, Relation.EqvGen r a b → ∀ ha hb,
        Relation.EqvGen (fun a b : ↥S => r a.val b.val) ⟨a,ha⟩ ⟨b,hb⟩ := by
      intro a b hab
      induction hab with
      | rel a b h => exact fun _ _ => Relation.EqvGen.rel _ _ h
      | refl a => exact fun _ _ => Relation.EqvGen.refl _
      | symm a b _ ih => exact fun ha hb => (ih hb ha).symm
      | trans a b c hab _ ih₁ ih₂ =>
        exact fun ha hc => (ih₁ ha ((hs hab).mp ha)).trans _ _ _
          (ih₂ ((hs hab).mp ha) hc)
    exact lift h x.property y.property
  · intro h
    induction h with
    | rel a b h => exact Relation.EqvGen.rel _ _ h
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans _ _ _ ih₂
theorem flag_chain_restriction (P : RawFacePairing T) {ν : Vertex P} (d e : Flag P ν) :
    DartRelated P d.val e.val ↔
      Relation.EqvGen (fun a b : Flag P ν => DartStep P a.val b.val) d e :=
  saturated_restriction (DartStep P) {d | d.1.2 ≠ d.2 ∧ label P d.1 = ν}
    (fun h => dart_chain_flags P ν h) d e
def Endpoints (P : RawFacePairing T) (ν : Vertex P) : Set (Point P ν) :=
  Set.range (endpoint P (ν := ν))
theorem endpoint_saturation (P : RawFacePairing T) {ν : Vertex P}
    {x y : Point P ν} (h : Related P x y) :
    x ∈ Endpoints P ν ↔ y ∈ Endpoints P ν := by
  have step {x y : Point P ν} (h : Step P x y) :
      x ∈ Endpoints P ν ↔ y ∈ Endpoints P ν := by
    obtain ⟨f, _, _, hy⟩ := h
    have forward (x y : Point P ν) (f : Fin 4) (hy : y.val = move P f x.val)
        (hx : x ∈ Endpoints P ν) : y ∈ Endpoints P ν := by
      obtain ⟨d, rfl⟩ := hx
      let s := sigma P (d.val.1.1,f)
      let e : Flag P ν := ⟨(y.val.1,s d.val.2), by
        refine ⟨?_, y.property.2.2.2⟩
        rw [hy]
        exact s.injective.ne d.property.1⟩
      refine ⟨e, ?_⟩
      apply Subtype.ext
      refine Prod.ext rfl ?_
      rw [hy]
      exact (delta_move s d.val.2).symm
    refine ⟨forward x y f hy, ?_⟩
    rintro ⟨e, rfl⟩
    let s := sigma P (x.val.1.1,f)
    have hcorner : e.val.1.2 = s x.val.1.2 :=
      congrArg (fun z : Raw T => z.1.2) hy
    have hd : x.val.1.2 ≠ s.symm e.val.2 := by
      intro hh
      apply e.property.1
      rw [hcorner, hh, Equiv.apply_symm_apply]
    let d : Flag P ν := ⟨(x.val.1,s.symm e.val.2),hd,x.property.2.2.2⟩
    refine ⟨d, ?_⟩
    apply Subtype.ext
    refine Prod.ext rfl ?_
    funext i
    have hi := congrFun (congrArg Prod.snd hy) (s i)
    change delta e.val.2 (s i) = x.val.2 (s.symm (s i)) at hi
    simpa only [endpoint, d, Equiv.symm_apply_apply, delta,
      Equiv.apply_eq_iff_eq_symm_apply] using hi
  induction h with
  | rel x y h => exact step h
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
theorem endpoint_related (P : RawFacePairing T) {ν : Vertex P} (d e : Flag P ν) :
    Related P (endpoint P d) (endpoint P e) ↔ DartRelated P d.val e.val := by
  constructor
  · intro h
    have lift : ∀ {x y : Point P ν}, Related P x y → ∀ a b : Flag P ν,
        endpoint P a = x → endpoint P b = y → DartRelated P a.val b.val := by
      intro x y hxy
      induction hxy with
      | rel x y h =>
        intro a b ha hb
        rw [← ha, ← hb] at h
        exact Relation.EqvGen.rel _ _ ((endpoint_step P a b).mp h)
      | refl x =>
        intro a b ha hb
        have hab := endpoint_injective P (ha.trans hb.symm)
        subst b
        exact Relation.EqvGen.refl _
      | symm x y _ ih => exact fun a b ha hb => (ih b a hb ha).symm
      | trans x y z hxy _ ih₁ ih₂ =>
        intro a c ha hc
        obtain ⟨b,hb⟩ := (endpoint_saturation P hxy).mp ⟨a,ha⟩
        exact (ih₁ a b ha hb).trans _ _ _ (ih₂ b c hb hc)
    exact lift h d e rfl rfl
  · intro h
    have hh := (flag_chain_restriction P d e).mp h
    clear h
    induction hh with
    | rel a b h => exact Relation.EqvGen.rel _ _ ((endpoint_step P a b).mpr h)
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans _ _ _ ih₂
theorem endpoint_chain_restriction (P : RawFacePairing T) {ν : Vertex P}
    (x y : ↥(Endpoints P ν)) : Related P x.val y.val ↔
      Relation.EqvGen (fun a b : ↥(Endpoints P ν) => Step P a.val b.val) x y :=
  saturated_restriction (Step P) (Endpoints P ν) (fun h => endpoint_saturation P h) x y
theorem endpoint_component_saturation (P : RawFacePairing T) {ν : Vertex P}
    (d : Flag P ν) (y : Point P ν) : Related P (endpoint P d) y ↔
      ∃ e : Flag P ν, DartRelated P d.val e.val ∧ endpoint P e = y := by
  constructor
  · intro h
    obtain ⟨e,he⟩ := (endpoint_saturation P h).mp ⟨d,rfl⟩
    exact ⟨e,(endpoint_related P d e).mp (he.symm ▸ h),he⟩
  · rintro ⟨e,h,rfl⟩
    exact (endpoint_related P d e).mpr h
theorem endpoint_truncated_related (P : RawFacePairing T) {ν : Vertex P}
    (d e : Flag P ν) : DartRelated P d.val e.val ↔
      Relation.EqvGen (TruncatedStep P) (toTruncation P (endpoint P d))
        (toTruncation P (endpoint P e)) :=
  (endpoint_related P d e).symm.trans (actual_slice_eqvgen_iff P _ _)
end D5.S3.Geometry.Gluing.RawFaceEndpointCandidate
run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.RawFaceEndpointCandidate.endpoint_injective,
      ``D5.S3.Geometry.Gluing.RawFaceEndpointCandidate.endpoint_step,
      ``D5.S3.Geometry.Gluing.RawFaceEndpointCandidate.dart_chain_flags,
      ``D5.S3.Geometry.Gluing.RawFaceEndpointCandidate.flag_chain_restriction,
      ``D5.S3.Geometry.Gluing.RawFaceEndpointCandidate.endpoint_saturation,
      ``D5.S3.Geometry.Gluing.RawFaceEndpointCandidate.endpoint_related,
      ``D5.S3.Geometry.Gluing.RawFaceEndpointCandidate.endpoint_chain_restriction,
      ``D5.S3.Geometry.Gluing.RawFaceEndpointCandidate.endpoint_component_saturation,
      ``D5.S3.Geometry.Gluing.RawFaceEndpointCandidate.endpoint_truncated_related] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1147 endpoint target absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1147 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP1147 CHECKED {name} axioms={axioms}"
