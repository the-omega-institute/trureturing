/- GID: D5/S3/Geometry/Gluing/ActualEndpointReturnClasses
   generality: G
   mirror-B: D5/B/S3/Geometry/Gluing/ActualEndpointReturnClasses
   mirror-E: none(waiver:actual-endpoint-return-class-correspondence)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.Cycle.Basic]
   utility: none
   digest: Pure original endpoints have exactly the four actual fiber return-cycle classes. -/

import D5.S3.Geometry.Gluing.ActualCornerPointPeriods

set_option autoImplicit false
noncomputable section
open scoped BigOperators Fin.NatCast
namespace D5.S3.Geometry.Gluing.ActualEndpointReturnClasses
open D5.S3.Geometry.Hyperideal.ActualCornerTransport
open D5.S3.Geometry.Hyperideal.NoncommutativeCornerOrbits
open D5.S3.Geometry.Gluing.ActualLinkCornerChains
open D5.S3.Geometry.Gluing.ActualCornerPointPeriods

variable {G Ω : Type*} [Group G] [MulAction Gᵐᵒᵖ Ω]

/-- Flags retain both the original unequal ordered endpoints and the original label. -/
def Flag (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) :=
  {d : Dart Ω // d.1.2 ≠ d.2 ∧ label (pairing u v) d.1 = ν}

/-- Literal barycentric delta coordinates. -/
def delta (k : Fin 4) (i : Fin 4) : ℝ := if i = k then 1 else 0

private theorem delta_carrier (u v : G) (d : Dart Ω) (hd : d.1.2 ≠ d.2) :
    (d.1, delta d.2) ∈ Carrier u v (label (pairing u v) d.1) := by
  refine ⟨by simp [delta, hd], ?_, ?_, rfl⟩
  · intro i; simp only [delta]; split_ifs <;> norm_num
  · simp [delta]

/-- An endpoint in the full, unchanged original carrier. -/
def endpoint (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (d : Flag u v ν) : Point u v ν :=
  ⟨(d.val.1, delta d.val.2), by
    have h := delta_carrier u v d.val d.property.1
    simpa only [d.property.2] using h⟩

private theorem delta_move (f k : Fin 4) :
    (fun i => delta k ((facePerm f).symm i)) = delta (facePerm f k) := by
  funext i
  simp only [delta, Equiv.symm_apply_eq]

private theorem dart_step_flags (u v : G) (ν : Vertex (pairing (Ω := Ω) u v))
    {d e : Dart Ω} (h : DartStep u v d e) :
    (d.1.2 ≠ d.2 ∧ label (pairing u v) d.1 = ν) ↔
      (e.1.2 ≠ e.2 ∧ label (pairing u v) e.1 = ν) := by
  obtain ⟨f, hfj, _, rfl⟩ := h
  have hn : (dartMove u v f d).1.2 ≠ (dartMove u v f d).2 ↔ d.1.2 ≠ d.2 :=
    (facePerm f).injective.ne_iff
  by_cases hd : d.1.2 = d.2
  · simp only [hn, hd, ne_eq, not_true_eq_false, false_and]
  · let x : Point u v (label (pairing u v) d.1) :=
      ⟨(d.1, delta d.2), delta_carrier u v d hd⟩
    have hl := (pairedPoint u v x f hfj).property.2.2.2
    change label (pairing u v) (dartMove u v f d).1 = label (pairing u v) d.1 at hl
    rw [hn, hl]

private theorem dart_chain_flags (u v : G) (ν : Vertex (pairing (Ω := Ω) u v))
    {d e : Dart Ω} (h : DartRelated u v d e) :
    (d.1.2 ≠ d.2 ∧ label (pairing u v) d.1 = ν) ↔
      (e.1.2 ≠ e.2 ∧ label (pairing u v) e.1 = ν) := by
  induction h with
  | rel d e h => exact dart_step_flags u v ν h
  | refl d => rfl
  | symm d e _ ih => exact ih.symm
  | trans d e f _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem endpoint_step (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (d e : Flag u v ν) : Step u v (endpoint u v d) (endpoint u v e) ↔
      DartStep u v d.val e.val := by
  constructor
  · rintro ⟨f, hj, hzero, he⟩
    have hk : f ≠ d.val.2 := by
      intro hk; simp [endpoint, delta, hk] at hzero
    refine ⟨f, hj, hk, ?_⟩
    have hc := congrArg Prod.fst he
    have ht := congrFun (congrArg Prod.snd he) (facePerm f d.val.2)
    change delta e.val.2 (facePerm f d.val.2) =
      delta d.val.2 ((facePerm f).symm (facePerm f d.val.2)) at ht
    simp only [Equiv.symm_apply_apply, delta, ite_true] at ht
    have heq : facePerm f d.val.2 = e.val.2 := by
      by_contra hh; simp [hh] at ht
    exact Prod.ext hc heq.symm
  · rintro ⟨f, hj, hk, he⟩
    refine ⟨f, hj, by simp [endpoint, delta, hk], ?_⟩
    apply Prod.ext
    · change e.val.1 = (dartMove u v f d.val).1
      exact congrArg Prod.fst he
    · change delta e.val.2 = fun i => delta d.val.2 ((facePerm f).symm i)
      rw [delta_move]
      exact congrArg delta (congrArg Prod.snd he)

private theorem flag_chain_restriction (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (d e : Flag u v ν) : DartRelated u v d.val e.val ↔
      Relation.EqvGen (fun a b : Flag u v ν => DartStep u v a.val b.val) d e := by
  constructor
  · intro h
    have lift : ∀ {a b : Dart Ω}, DartRelated u v a b →
        ∀ ha hb, Relation.EqvGen (fun a b : Flag u v ν => DartStep u v a.val b.val)
          ⟨a, ha⟩ ⟨b, hb⟩ := by
      intro a b hab
      induction hab with
      | rel a b h => exact fun _ _ => Relation.EqvGen.rel _ _ h
      | refl a => exact fun _ _ => Relation.EqvGen.refl _
      | symm a b _ ih => exact fun ha hb => (ih hb ha).symm
      | trans a b c hab _ ih₁ ih₂ =>
        intro ha hc
        have hb := (dart_chain_flags u v ν hab).mp ha
        exact (ih₁ ha hb).trans _ _ _ (ih₂ hb hc)
    exact lift h d.property e.property
  · intro h
    induction h with
    | rel a b h => exact Relation.EqvGen.rel _ _ h
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans _ _ _ ih₂

private theorem endpoint_related (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (d e : Flag u v ν) : Related u v (endpoint u v d) (endpoint u v e) ↔
      DartRelated u v d.val e.val := by
  constructor
  · intro h
    have hd : endpoint u v d ∈ Neighborhood u v d.val :=
      ⟨d.val.2, by norm_num [endpoint, delta], Relation.EqvGen.refl _⟩
    have he := ((actual_guarded_point_analysis u v (endpoint u v d)
      (endpoint u v e)).2.2.1 d.val h).mp hd
    obtain ⟨k, hk, he⟩ := he
    have hke : k = e.val.2 := by
      by_contra hh
      simp [endpoint, delta, hh] at hk
      norm_num at hk
    simpa only [endpoint, hke] using he
  · intro h
    have hh := (flag_chain_restriction u v d e).mp h
    clear h
    induction hh with
    | rel a b h => exact Relation.EqvGen.rel _ _ ((endpoint_step u v a b).mpr h)
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans _ _ _ ih₂

/-- The endpoint locus consists of the literal pure coordinates in the original carrier. -/
def Endpoints (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) : Set (Point u v ν) :=
  Set.range (endpoint u v)

private theorem endpoint_saturation (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    {x y : Point u v ν} (h : Related u v x y) :
    x ∈ Endpoints u v ν ↔ y ∈ Endpoints u v ν := by
  have step {x y : Point u v ν} (h : Step u v x y) :
      x ∈ Endpoints u v ν ↔ y ∈ Endpoints u v ν := by
    obtain ⟨f, _, _, hy⟩ := h
    have forward (x y : Point u v ν) (f : Fin 4) (hy : y.val = move u v f x.val)
        (hx : x ∈ Endpoints u v ν) : y ∈ Endpoints u v ν := by
      obtain ⟨d, rfl⟩ := hx
      let e : Flag u v ν := ⟨(y.val.1, facePerm f d.val.2), by
        refine ⟨?_, y.property.2.2.2⟩
        rw [hy]
        exact (facePerm f).injective.ne d.property.1⟩
      refine ⟨e, ?_⟩
      apply Subtype.ext
      refine Prod.ext rfl ?_
      rw [hy]
      exact (delta_move f d.val.2).symm
    refine ⟨forward x y f hy, ?_⟩
    rintro ⟨e, rfl⟩
    have hcorner : e.val.1.2 = facePerm f x.val.1.2 :=
      congrArg (fun z : Raw Ω => z.1.2) hy
    have hd : x.val.1.2 ≠ (facePerm f).symm e.val.2 := by
      intro hh
      apply e.property.1
      rw [hcorner, hh, Equiv.apply_symm_apply]
    let d : Flag u v ν := ⟨(x.val.1, (facePerm f).symm e.val.2), hd, x.property.2.2.2⟩
    refine ⟨d, ?_⟩
    apply Subtype.ext
    refine Prod.ext rfl ?_
    funext i
    have hi := congrFun (congrArg Prod.snd hy) (facePerm f i)
    change delta e.val.2 (facePerm f i) = x.val.2 ((facePerm f).symm (facePerm f i)) at hi
    simpa only [endpoint, d, Equiv.symm_apply_apply, delta,
      Equiv.apply_eq_iff_eq_symm_apply] using hi
  induction h with
  | rel x y h => exact step h
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem endpoint_chain_restriction (u v : G)
    {ν : Vertex (pairing (Ω := Ω) u v)} (x y : ↥(Endpoints u v ν)) :
    Related u v x.val y.val ↔
      Relation.EqvGen (fun a b : ↥(Endpoints u v ν) => Step u v a.val b.val) x y := by
  constructor
  · intro h
    have lift : ∀ {a b : Point u v ν}, Related u v a b →
        ∀ ha hb, Relation.EqvGen (fun a b : ↥(Endpoints u v ν) =>
          Step u v a.val b.val) ⟨a, ha⟩ ⟨b, hb⟩ := by
      intro a b hab
      induction hab with
      | rel a b h => exact fun _ _ => Relation.EqvGen.rel _ _ h
      | refl a => exact fun _ _ => Relation.EqvGen.refl _
      | symm a b _ ih => exact fun ha hb => (ih hb ha).symm
      | trans a b c hab _ ih₁ ih₂ =>
        intro ha hc
        have hb := (endpoint_saturation u v hab).mp ha
        exact (ih₁ ha hb).trans _ _ _ (ih₂ hb hc)
    exact lift h x.property y.property
  · intro h
    induction h with
    | rel a b h => exact Relation.EqvGen.rel _ _ h
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans _ _ _ ih₂

/-- The original full point quotient, with no new relation replacing Step. -/
abbrev PointQuotient (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) :=
  Quotient (Relation.EqvGen.setoid (Step u v (ν := ν)))

/-- Restriction of the original full dart equivalence relation to its saturated fiber. -/
def flagSetoid (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) : Setoid (Flag u v ν) :=
  (Relation.EqvGen.setoid (DartStep u v)).comap Subtype.val

abbrev FlagQuotient (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) :=
  Quotient (flagSetoid u v ν)

/-- The actual map to original point classes. -/
def endpointClassMap (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) :
    FlagQuotient u v ν → PointQuotient u v ν :=
  Quotient.map (endpoint u v) (fun d e h => (endpoint_related u v d e).mpr h)

private theorem endpointClassMap_injective (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) :
    Function.Injective (endpointClassMap u v ν) := by
  intro a b
  induction a using Quotient.inductionOn with
  | h d =>
    induction b using Quotient.inductionOn with
    | h e =>
      intro h
      exact Quotient.sound ((endpoint_related u v d e).mp (Quotient.exact h))

/-- The four root fibers retain their original corner numbers 0, 1, 2, 0. -/
def Root (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) (c : Fin 4) :=
  {x : Ω // label (pairing u v) (x, corner c 0) = ν}

/-- The actual row return on the full action, used only through its saturated root fiber. -/
def returnPerm (u v : G) (c : Fin 4) : Equiv.Perm Ω where
  toFun x := act x (returnWord u v c)
  invFun x := act x (returnWord u v c)⁻¹
  left_inv x := by simp [act_mul]
  right_inv x := by simp [act_mul]

private theorem root_unequal (c : Fin 4) : corner c 0 ≠ tip c 0 := by
  fin_cases c <;> decide

private theorem offset_zero (u v : G) (c : Fin 4) : offset u v c 0 = 1 := by
  fin_cases c <;> rfl

private theorem root_match (u v : G) [Finite Ω] (c d : Fin 4) (x y : Ω) (s : Fin 3)
    (h : encode u v c (x, s) = encode u v d (y, 0)) : c = d ∧ s = 0 ∧ x = y := by
  have hc := congrArg (fun z : Dart Ω => z.1.2) h
  have ht := congrArg (fun z : Dart Ω => z.2) h
  obtain ⟨cs, _, hu⟩ := ((actual_component_enumeration u v d y).2.2.2.1
    (corner d 0) (tip d 0)).mp (root_unequal d)
  have hcs : (c, s) = (d, 0) :=
    (hu (c, s) ⟨hc, ht⟩).trans (hu (d, 0) ⟨rfl, rfl⟩).symm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hcs
  refine ⟨rfl, rfl, ?_⟩
  have hx := congrArg (fun z : Dart Ω => z.1.1) h
  simpa only [encode, offset_zero, act_one] using hx

private theorem root_related_iff (u v : G) [Finite Ω] (c d : Fin 4) (x y : Ω) :
    DartRelated u v (encode u v c (x, 0)) (encode u v d (y, 0)) ↔
      ∃ _ : c = d, (returnPerm u v c).SameCycle x y := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := ((actual_component_enumeration u v c x).2.2.1 _).mp h
    rw [(actual_component_enumeration u v c x).2.2.2.2.2.2 i] at hi
    obtain ⟨hc, _, hx⟩ := root_match u v c d _ y (i.val : Fin 3) hi
    refine ⟨hc, ?_⟩
    refine ⟨(i.val/3 : ℕ), ?_⟩
    simpa only [zpow_natCast, ← Equiv.Perm.iterate_eq_pow, returnPerm, Equiv.coe_fn_mk] using hx
  · rintro ⟨rfl, h⟩
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    have hp := (actual_component_enumeration u v c x).1
    let r := pointPeriod u v c x
    let i : Fin (3 * r) := ⟨3 * (n % r), by
      have hm := Nat.mod_lt n hp
      dsimp [r] at *
      omega⟩
    apply ((actual_component_enumeration u v c x).2.2.1 _).mpr
    refine ⟨i, ?_⟩
    rw [(actual_component_enumeration u v c x).2.2.2.2.2.2 i]
    have hphase : (i.val : Fin 3) = 0 := by dsimp [i]; simp
    have hdiv : i.val/3 = n % r := by dsimp [i]; omega
    rw [hphase, hdiv]
    have hmod : (fun z : Ω => act z (returnWord u v c))^[n % r] x =
        (fun z : Ω => act z (returnWord u v c))^[n] x :=
      Function.iterate_mod_minimalPeriod_eq
    rw [hmod]
    have hn' : (fun z : Ω => act z (returnWord u v c))^[n] x = y := by
      simpa only [← Equiv.Perm.iterate_eq_pow, returnPerm, Equiv.coe_fn_mk] using hn
    rw [hn']

private theorem root_fiber_invariant (u v : G) [Finite Ω]
    (ν : Vertex (pairing (Ω := Ω) u v)) (c : Fin 4) (x : Ω) :
    label (pairing u v) (act x (returnWord u v c), corner c 0) = ν ↔
      label (pairing u v) (x, corner c 0) = ν := by
  have h : DartRelated u v (encode u v c (x, 0))
      (encode u v c (act x (returnWord u v c), 0)) :=
    (root_related_iff u v c c _ _).mpr
      ⟨rfl, (Equiv.Perm.SameCycle.refl (returnPerm u v c) x).apply_right⟩
  have hs := dart_chain_flags u v ν h
  simp only [encode, offset_zero, act_one] at hs
  exact ⟨fun h => (hs.mpr ⟨root_unequal c, h⟩).2,
    fun h => (hs.mp ⟨root_unequal c, h⟩).2⟩

/-- Restrict the actual return permutation after proving label-fiber saturation. -/
def rootReturn (u v : G) [Finite Ω] (ν : Vertex (pairing (Ω := Ω) u v))
    (c : Fin 4) : Equiv.Perm (Root u v ν c) :=
  (returnPerm u v c).subtypePerm (root_fiber_invariant u v ν c)

abbrev RootCycles (u v : G) [Finite Ω] (ν : Vertex (pairing (Ω := Ω) u v))
    (c : Fin 4) := Quotient (Equiv.Perm.SameCycle.setoid (rootReturn u v ν c))

/-- Four disjoint actual root-return cycle quotients, in the supplier's row order. -/
abbrev ReturnClasses (u v : G) [Finite Ω] (ν : Vertex (pairing (Ω := Ω) u v)) :=
  (c : Fin 4) × RootCycles u v ν c

def rootFlag (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)} (c : Fin 4)
    (x : Root u v ν c) : Flag u v ν :=
  ⟨encode u v c (x.val, 0), by
    simpa only [encode, offset_zero, act_one] using And.intro (root_unequal c) x.property⟩

/-- Return classes map to the original dart quotient through their actual phase-zero flags. -/
def returnClassMap (u v : G) [Finite Ω] (ν : Vertex (pairing (Ω := Ω) u v)) :
    ReturnClasses u v ν → FlagQuotient u v ν := fun a =>
  Quotient.lift (fun x => Quotient.mk (flagSetoid u v ν) (rootFlag u v a.1 x))
    (by
      intro x y h
      apply Quotient.sound
      exact (root_related_iff u v a.1 a.1 x.val y.val).mpr
        ⟨rfl, Equiv.Perm.sameCycle_subtypePerm.mp h⟩) a.2

private theorem returnClassMap_injective (u v : G) [Finite Ω]
    (ν : Vertex (pairing (Ω := Ω) u v)) : Function.Injective (returnClassMap u v ν) := by
  rintro ⟨c, a⟩ ⟨d, b⟩
  induction a using Quotient.inductionOn with
  | h x =>
    induction b using Quotient.inductionOn with
    | h y =>
      intro h
      have hrel : DartRelated u v (encode u v c (x.val, 0)) (encode u v d (y.val, 0)) :=
        Quotient.exact h
      obtain ⟨rfl, hcycle⟩ := (root_related_iff u v c d x.val y.val).mp hrel
      have hq : Quotient.mk (Equiv.Perm.SameCycle.setoid (rootReturn u v ν c)) x =
          Quotient.mk _ y := Quotient.sound (Equiv.Perm.sameCycle_subtypePerm.mpr hcycle)
      exact congrArg (Sigma.mk c) hq

private theorem returnClassMap_surjective (u v : G) [Finite Ω]
    (ν : Vertex (pairing (Ω := Ω) u v)) : Function.Surjective (returnClassMap u v ν) := by
  intro a
  induction a using Quotient.inductionOn with
  | h d =>
    obtain ⟨⟨c, s⟩, ⟨hj, hk⟩, _⟩ :=
      ((actual_component_enumeration u v 0 d.val.1.1).2.2.2.1 _ _).mp d.property.1
    let x := act d.val.1.1 (offset u v c s)⁻¹
    have hencode : encode u v c (x, s) = d.val := by
      apply Prod.ext
      · apply Prod.ext
        · simp [encode, x, act_mul]
        · exact hj
      · exact hk
    have hp := (actual_component_enumeration u v c x).1
    let i : Fin (3 * pointPeriod u v c x) := ⟨s.val, by have := s.isLt; omega⟩
    have hreach : DartRelated u v (encode u v c (x, 0)) d.val := by
      apply ((actual_component_enumeration u v c x).2.2.1 _).mpr
      refine ⟨i, ?_⟩
      rw [(actual_component_enumeration u v c x).2.2.2.2.2.2 i]
      have hdiv : i.val/3 = 0 := by have := s.isLt; dsimp [i]; omega
      have hphase : (i.val : Fin 3) = s := by simp [i]
      simpa only [hdiv, hphase, Function.iterate_zero, id_eq] using hencode
    have hx := (dart_chain_flags u v ν hreach).mpr d.property
    have hxroot : label (pairing u v) (x, corner c 0) = ν := by
      simpa only [encode, offset_zero, act_one] using hx.2
    refine ⟨⟨c, Quotient.mk _ ⟨x, hxroot⟩⟩, ?_⟩
    exact Quotient.sound hreach

/-- The equivalence is constructed from the actual class map, with full component exhaustion. -/
def returnClassesEquiv (u v : G) [Finite Ω] (ν : Vertex (pairing (Ω := Ω) u v)) :
    ReturnClasses u v ν ≃ FlagQuotient u v ν :=
  Equiv.ofBijective (returnClassMap u v ν)
    ⟨returnClassMap_injective u v ν, returnClassMap_surjective u v ν⟩

/-- Marked endpoint classes as an actual subset of the original point quotient. -/
def EndpointClasses (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) :=
  Set.range (endpointClassMap u v ν)

def endpointClassesEquiv (u v : G) [Finite Ω] (ν : Vertex (pairing (Ω := Ω) u v)) :
    ReturnClasses u v ν ≃ EndpointClasses u v ν :=
  (returnClassesEquiv u v ν).trans
    (Equiv.ofBijective (fun a => (⟨endpointClassMap u v ν a, a, rfl⟩ : EndpointClasses u v ν))
      ⟨by
        intro a b h
        exact endpointClassMap_injective u v ν (congrArg Subtype.val h),
       by
        rintro ⟨q, a, rfl⟩
        exact ⟨a, rfl⟩⟩)

/-- Slot-zero labels, retaining the selected original corner class. -/
abbrev ZeroFiber (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) :=
  {x : Ω // label (pairing u v) (x, 0) = ν}

private theorem normalized_label (u v : G) (a : Corner Ω) :
    label (pairing u v) a = label (pairing u v) (normalize u a, 0) := by
  apply Quotient.sound
  exact (actual_corner_orbit_iff u v a (normalize u a, 0)).mpr
    ⟨1, (boundaryGroup u v).one_mem, by
      simp [D5.S3.Geometry.Hyperideal.NoncommutativeCornerOrbits.normalize]⟩

/-- Conjugate each distinct root fiber to slot zero only after preserving its label. -/
def rootToZero (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) (c : Fin 4) :
    Root u v ν c ≃ ZeroFiber u v ν where
  toFun x := ⟨act x.val (u ^ (corner c 0).val),
    (normalized_label u v (x.val, corner c 0)).symm.trans x.property⟩
  invFun x := ⟨act x.val (u ^ (corner c 0).val)⁻¹, by
    rw [normalized_label]
    simpa [D5.S3.Geometry.Hyperideal.NoncommutativeCornerOrbits.normalize, act_mul] using x.property⟩
  left_inv x := by apply Subtype.ext; simp [act_mul]
  right_inv x := by apply Subtype.ext; simp [act_mul]

/-- The return on slot zero is the conjugate of the actual restricted root return. -/
def zeroReturn (u v : G) [Finite Ω] (ν : Vertex (pairing (Ω := Ω) u v))
    (c : Fin 4) : Equiv.Perm (ZeroFiber u v ν) :=
  (rootToZero u v ν c).permCongrHom (rootReturn u v ν c)

/-- These are c1, inverse c3, c2, inverse c4 in the original row order. -/
def normalizedWord (u v : G) (c : Fin 4) : G :=
  ![(sWord u v)⁻¹, (tWord u v)⁻¹, sWord u v * kWord u v, kWord u v * tWord u v] c

private theorem zeroReturn_action (u v : G) [Finite Ω]
    (ν : Vertex (pairing (Ω := Ω) u v)) (c : Fin 4) (x : ZeroFiber u v ν) :
    (zeroReturn u v ν c x).val = act x.val (normalizedWord u v c) := by
  change act (act (act x.val (u ^ (corner c 0).val)⁻¹) (returnWord u v c))
    (u ^ (corner c 0).val) = _
  fin_cases c <;>
    simp [act_mul, normalizedWord, returnWord, corner, sWord, tWord, kWord,
      pow_succ, mul_assoc]

private theorem conjugate_cycles (u v : G) [Finite Ω]
    (ν : Vertex (pairing (Ω := Ω) u v)) (c : Fin 4) (x y : Root u v ν c) :
    (rootReturn u v ν c).SameCycle x y ↔
      (zeroReturn u v ν c).SameCycle (rootToZero u v ν c x) (rootToZero u v ν c y) := by
  unfold Equiv.Perm.SameCycle
  apply exists_congr
  intro n
  have hp := map_zpow (rootToZero u v ν c).permCongrHom (rootReturn u v ν c) n
  have hpapp := congrArg (fun q : Equiv.Perm (ZeroFiber u v ν) =>
    q (rootToZero u v ν c x)) hp
  have hi : ((zeroReturn u v ν c)^n) (rootToZero u v ν c x) =
      rootToZero u v ν c (((rootReturn u v ν c)^n) x) := by
    simpa only [zeroReturn, Equiv.permCongrHom_coe, Equiv.permCongr_apply,
      Equiv.symm_apply_apply] using hpapp.symm
  rw [hi]
  exact (rootToZero u v ν c).injective.eq_iff.symm

/-- Move to c1, c2, c3, c4 order only after the root-fiber conjugacy. -/
def rowOrder : Equiv.Perm (Fin 4) where
  toFun i := ![0, 2, 1, 3] i
  invFun i := ![0, 2, 1, 3] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The original boundary words, in c1, c2, c3, c4 order. -/
def boundaryWord (u v : G) (i : Fin 4) : G :=
  ![(sWord u v)⁻¹, sWord u v * kWord u v, tWord u v,
    (kWord u v * tWord u v)⁻¹] i

/-- Correct orientations of the actual slot-zero returns. -/
def boundaryReturn (u v : G) [Finite Ω] (ν : Vertex (pairing (Ω := Ω) u v))
    (i : Fin 4) : Equiv.Perm (ZeroFiber u v ν) :=
  if i = 2 ∨ i = 3 then (zeroReturn u v ν (rowOrder i))⁻¹
    else zeroReturn u v ν (rowOrder i)

abbrev BoundaryCycles (u v : G) [Finite Ω] (ν : Vertex (pairing (Ω := Ω) u v))
    (i : Fin 4) := Quotient (Equiv.Perm.SameCycle.setoid (boundaryReturn u v ν i))

abbrev BoundaryClasses (u v : G) [Finite Ω] (ν : Vertex (pairing (Ω := Ω) u v)) :=
  (i : Fin 4) × BoundaryCycles u v ν i

private theorem boundaryReturn_action (u v : G) [Finite Ω]
    (ν : Vertex (pairing (Ω := Ω) u v)) (i : Fin 4) (x : ZeroFiber u v ν) :
    (boundaryReturn u v ν i x).val = act x.val (boundaryWord u v i) := by
  have inverse (c : Fin 4) : ((zeroReturn u v ν c)⁻¹ x).val =
      act x.val (normalizedWord u v c)⁻¹ := by
    have h := zeroReturn_action u v ν c ((zeroReturn u v ν c).symm x)
    rw [Equiv.apply_symm_apply] at h
    have hh := congrArg (fun z : Ω => act z (normalizedWord u v c)⁻¹) h
    simpa only [Equiv.Perm.inv_def, act_mul, mul_inv_cancel, act_one] using hh.symm
  fin_cases i
  · simpa [boundaryReturn, rowOrder, boundaryWord, normalizedWord] using
      zeroReturn_action u v ν 0 x
  · simpa [boundaryReturn, rowOrder, boundaryWord, normalizedWord] using
      zeroReturn_action u v ν 2 x
  · simpa [boundaryReturn, rowOrder, boundaryWord, normalizedWord] using inverse 1
  · simpa [boundaryReturn, rowOrder, boundaryWord, normalizedWord] using inverse 3

private theorem boundary_cycles (u v : G) [Finite Ω]
    (ν : Vertex (pairing (Ω := Ω) u v)) (i : Fin 4) (x y : ZeroFiber u v ν) :
    (zeroReturn u v ν (rowOrder i)).SameCycle x y ↔
      (boundaryReturn u v ν i).SameCycle x y := by
  unfold boundaryReturn
  split_ifs <;> simp

/-- Reuse quotient congruence, inverse-cycle invariance and the explicit row permutation. -/
def boundaryClassesEquiv (u v : G) [Finite Ω] (ν : Vertex (pairing (Ω := Ω) u v)) :
    BoundaryClasses u v ν ≃ ReturnClasses u v ν :=
  (Equiv.sigmaCongrRight (fun i =>
    (show BoundaryCycles u v ν i ≃ RootCycles u v ν (rowOrder i) from
      (Quotient.congr
        (ra := Equiv.Perm.SameCycle.setoid (boundaryReturn u v ν i))
        (rb := Equiv.Perm.SameCycle.setoid (zeroReturn u v ν (rowOrder i)))
        (Equiv.refl (ZeroFiber u v ν)) (fun x y =>
        (boundary_cycles u v ν i x y).symm)).trans
      (Quotient.congr
        (ra := Equiv.Perm.SameCycle.setoid (rootReturn u v ν (rowOrder i)))
        (rb := Equiv.Perm.SameCycle.setoid (zeroReturn u v ν (rowOrder i)))
        (rootToZero u v ν (rowOrder i))
        (conjugate_cycles u v ν (rowOrder i))).symm))).trans
    (Equiv.sigmaCongrLeft (β := RootCycles u v ν) rowOrder)

/-- Boundary-return cycles identify the same marked original point classes. -/
def boundaryEndpointEquiv (u v : G) [Finite Ω] (ν : Vertex (pairing (Ω := Ω) u v)) :
    BoundaryClasses u v ν ≃ EndpointClasses u v ν :=
  (boundaryClassesEquiv u v ν).trans (endpointClassesEquiv u v ν)

/-- Complete endpoint restriction and its actual return-class consumer. -/
theorem actual_endpoint_return_classes (u v : G) [Finite Ω]
    (ν : Vertex (pairing (Ω := Ω) u v)) :
    (∀ d e : Flag u v ν, Related u v (endpoint u v d) (endpoint u v e) ↔
      DartRelated u v d.val e.val) ∧
    (∀ d e : Flag u v ν, DartRelated u v d.val e.val ↔
      Relation.EqvGen (fun a b : Flag u v ν => DartStep u v a.val b.val) d e) ∧
    (∀ x y : Point u v ν, Related u v x y →
      (x ∈ Endpoints u v ν ↔ y ∈ Endpoints u v ν)) ∧
    (∀ x y : ↥(Endpoints u v ν), Related u v x.val y.val ↔
      Relation.EqvGen (fun a b : ↥(Endpoints u v ν) => Step u v a.val b.val) x y) ∧
    (∀ a : ReturnClasses u v ν,
      (endpointClassesEquiv u v ν a).val =
        endpointClassMap u v ν (returnClassesEquiv u v ν a)) ∧
    (∀ (c : Fin 4) (x : Root u v ν c),
      0 < pointPeriod u v c x.val ∧
      Function.minimalPeriod (tour u v c) (x.val, 0) = 3 * pointPeriod u v c x.val) ∧
    (∀ (c : Fin 4) (x : ZeroFiber u v ν),
      (zeroReturn u v ν c x).val = act x.val (normalizedWord u v c)) ∧
    (∀ (c : Fin 4) (x y : Root u v ν c),
      (rootReturn u v ν c).SameCycle x y ↔
        (zeroReturn u v ν c).SameCycle (rootToZero u v ν c x) (rootToZero u v ν c y)) ∧
    (∀ (i : Fin 4) (x : ZeroFiber u v ν),
      (boundaryReturn u v ν i x).val = act x.val (boundaryWord u v i)) ∧
    (∀ a : BoundaryClasses u v ν,
      (boundaryEndpointEquiv u v ν a).val =
        endpointClassMap u v ν (returnClassesEquiv u v ν (boundaryClassesEquiv u v ν a))) := by
  refine ⟨endpoint_related u v, flag_chain_restriction u v, ?_,
    endpoint_chain_restriction u v, fun _ => rfl, ?_,
    zeroReturn_action u v ν, conjugate_cycles u v ν, boundaryReturn_action u v ν,
    fun _ => rfl⟩
  · exact fun _ _ h => endpoint_saturation u v h
  · intro c x
    exact ⟨(actual_component_enumeration u v c x.val).1,
      (actual_component_enumeration u v c x.val).2.2.2.2.2.1⟩

end D5.S3.Geometry.Gluing.ActualEndpointReturnClasses
