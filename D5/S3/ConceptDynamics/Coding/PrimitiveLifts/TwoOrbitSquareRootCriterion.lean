/- GID: D5/S3/ConceptDynamics/Coding/PrimitiveLifts/TwoOrbitSquareRootCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PrimitiveLifts/TwoOrbitSquareRootCriterion
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Two actual lift orbits admit exactly the local or conjugate exchange roots. -/

import D5.S3.ConceptDynamics.Coding.PrimitiveLifts.PrimitiveLiftRootCriterion

/-! Square roots on the full union of two distinct primitive base orbits. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.ConceptDynamics.Coding.PrimitiveLifts.TwoOrbitSquareRootCriterion

open PrimitiveLiftRootCriterion
universe u v w

section Charts
variable {H : Type u} [Group H] {X : Type v} {Y : Type w}
  (A : ReturnAtlas H X) (B : ReturnAtlas H Y)

private def jointTime : X ⊕ Y → X ⊕ Y := Sum.map A.time B.time
private def jointDeck (a : H) : X ⊕ Y → X ⊕ Y := Sum.map (A.deck a) (B.deck a)

private def Local (A : ReturnAtlas H X) : Prop :=
  ∃ s : Fin A.period, ∃ m : ℤ, ∃ b : H, Commute b A.holonomy ∧
    (2:ℤ)*(s.val:ℤ) = 1 + (A.period:ℤ)*m ∧ b^2*A.holonomy^m = 1

theorem forward (f : X → Y)
    (hf : ∀ a x, f (A.deck a x) = B.deck a (f x))
    (ht : ∀ x, f (A.time x) = B.time (f x))
    {s : ℤ} {b : H} (hzero : f (A.point 0 1) = B.point s b) :
    ∀ q : ℕ, ∀ z, f (A.point q z) = B.point ((q:ℤ)+s) (z*b) := by
  intro q
  induction q with
  | zero =>
    intro z
    simpa only [Nat.cast_zero, zero_add, mul_one, A.deck_point, B.deck_point] using
      (hf z (A.point 0 1)).trans (congrArg (B.deck z) hzero)
  | succ q ih =>
    intro z
    rw [show ((q+1:ℕ):ℤ) = (q:ℤ)+1 by omega, ← A.time_point, ht, ih,
      B.time_point]
    congr 1; omega

theorem seam_obstruction (f : X → Y)
    (hf : ∀ a x, f (A.deck a x) = B.deck a (f x))
    (ht : ∀ x, f (A.time x) = B.time (f x)) :
    ∃ m : ℤ, ∃ b : H, (A.period:ℤ) = (B.period:ℤ)*m ∧
      b * B.holonomy^m = A.holonomy * b := by
  obtain ⟨s,b,hzero⟩ := B.covers (f (A.point 0 1))
  have law := forward A B f hf ht hzero.symm
  have seam : A.point (A.period:ℤ) 1 = A.point 0 A.holonomy :=
    (A.relation _ _ _ _).2 ⟨1, by omega, by simp⟩
  have h := congrArg f seam
  rw [law A.period 1] at h
  have hzero := law 0 A.holonomy
  simp only [Nat.cast_zero, zero_add] at hzero
  rw [hzero] at h
  simp only [one_mul, Nat.cast_zero, zero_add] at h
  obtain ⟨m,hm,hb⟩ := (B.relation _ _ _ _).1 h
  exact ⟨m,b,by omega,hb⟩

def transport (b : H) : X → Y := fun x =>
  let q := A.coordinates.symm x
  B.point q.1.val (q.2*b)

theorem transport_point (hd : A.period = B.period) (b : H)
    (hb : b * B.holonomy = A.holonomy * b) (t : ℤ) (z : H) :
    transport A B b (A.point t z) = B.point t (z*b) := by
  let q := A.coordinates.symm (A.point t z)
  have he : A.point t z = A.point q.1.val q.2 := (A.coordinates.apply_symm_apply _).symm
  obtain ⟨m,hm,hz⟩ := (A.relation _ _ _ _).1 he
  change B.point q.1.val (q.2*b) = B.point t (z*b)
  symm
  apply (B.relation _ _ _ _).2
  refine ⟨m, by simpa [hd] using hm, ?_⟩
  have hc := (SemiconjBy.zpow_right (show SemiconjBy b B.holonomy A.holonomy from hb) m)
  calc
    (z*b)*B.holonomy^m = z*(b * B.holonomy^m) := mul_assoc _ _ _
    _ = z*(A.holonomy^m*b) := congrArg (z*·) hc
    _ = q.2*b := by rw [← mul_assoc,hz]

theorem transport_deck (hd : A.period = B.period) (b : H)
    (hb : b * B.holonomy = A.holonomy * b) (a : H) (x : X) :
    transport A B b (A.deck a x) = B.deck a (transport A B b x) := by
  obtain ⟨t,z,rfl⟩ := A.covers x
  rw [A.deck_point, transport_point A B hd b hb, transport_point A B hd b hb,
    B.deck_point, mul_assoc]

private def tag : X ⊕ Y → Bool := Sum.elim (fun _ => false) (fun _ => true)

private theorem component_constant {Z : Type*} (S : ReturnAtlas H Z)
    (f : Z → X ⊕ Y)
    (hf : ∀ a x, f (S.deck a x) = jointDeck A B a (f x))
    (ht : ∀ x, f (S.time x) = jointTime A B (f x)) :
    ∀ x, tag (f x) = tag (f (S.point 0 1)) := by
  have td : ∀ a y, tag (jointDeck A B a y) = tag y := by intro a y; cases y <;> rfl
  have tt : ∀ y, tag (jointTime A B y) = tag y := by intro y; cases y <;> rfl
  have hp : ∀ q : ℕ, ∀ z, tag (f (S.point q z)) = tag (f (S.point 0 1)) := by
    intro q
    induction q with
    | zero =>
      intro z
      have h := congrArg tag (hf z (S.point 0 1))
      simpa only [S.deck_point, mul_one, td, Nat.cast_zero] using h
    | succ q ih =>
      intro z
      rw [show ((q+1:ℕ):ℤ) = (q:ℤ)+1 by omega, ← S.time_point, ht, tt, ih]
  intro x
  obtain ⟨⟨q,z⟩,rfl⟩ := S.coordinates.surjective x
  exact hp q.val z

private theorem preserving (r : X ⊕ Y → X ⊕ Y)
    (hr : ∀ a x, r (jointDeck A B a x) = jointDeck A B a (r x))
    (hs : ∀ x, r (r x) = jointTime A B x)
    (hl : ∀ x : X, ∃ y : X, r (.inl x) = .inl y)
    (hh : ∀ x : Y, ∃ y : Y, r (.inr x) = .inr y) : Local A ∧ Local B := by
  choose f hfl using hl
  choose g hgr using hh
  have hf : A.Equivariant f := by
    intro a x
    apply Sum.inl.inj
    simpa only [jointDeck, Sum.map_inl, hfl] using hr a (.inl x)
  have hg : B.Equivariant g := by
    intro a x
    apply Sum.inr.inj
    simpa only [jointDeck, Sum.map_inr, hgr] using hr a (.inr x)
  have fs : f^[2] = A.time := by
    funext x
    apply Sum.inl.inj
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply, jointTime,
      Sum.map_inl, hfl] using hs (.inl x)
  have gs : g^[2] = B.time := by
    funext x
    apply Sum.inr.inj
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply, jointTime,
      Sum.map_inr, hgr] using hs (.inr x)
  exact ⟨(A.root_criterion 2).1 ⟨f,hf,fs⟩,(B.root_criterion 2).1 ⟨g,hg,gs⟩⟩

private theorem exchanging (r : X ⊕ Y → X ⊕ Y)
    (hr : ∀ a x, r (jointDeck A B a x) = jointDeck A B a (r x))
    (ht : ∀ x, r (jointTime A B x) = jointTime A B (r x))
    (hl : ∀ x : X, ∃ y : Y, r (.inl x) = .inr y)
    (hh : ∀ x : Y, ∃ y : X, r (.inr x) = .inl y) :
    A.period = B.period ∧ ∃ b : H, b * B.holonomy = A.holonomy * b := by
  choose f hfl using hl
  choose g hgr using hh
  have hf : ∀ a x, f (A.deck a x) = B.deck a (f x) := by
    intro a x
    apply Sum.inr.inj
    simpa only [jointDeck, Sum.map_inl, Sum.map_inr, hfl] using hr a (.inl x)
  have hg : ∀ a x, g (B.deck a x) = A.deck a (g x) := by
    intro a x
    apply Sum.inl.inj
    simpa only [jointDeck, Sum.map_inl, Sum.map_inr, hgr] using hr a (.inr x)
  have ft : ∀ x, f (A.time x) = B.time (f x) := by
    intro x
    apply Sum.inr.inj
    simpa only [jointTime, Sum.map_inl, Sum.map_inr, hfl] using ht (.inl x)
  have gt : ∀ x, g (B.time x) = A.time (g x) := by
    intro x
    apply Sum.inl.inj
    simpa only [jointTime, Sum.map_inl, Sum.map_inr, hgr] using ht (.inr x)
  obtain ⟨m,b,hm,hb⟩ := seam_obstruction A B f hf ft
  obtain ⟨k,c,hk,_⟩ := seam_obstruction B A g hg gt
  have ha : (0:ℤ) < A.period := by exact_mod_cast A.positive
  have hbpos : (0:ℤ) < B.period := by exact_mod_cast B.positive
  have hmpos : 1 ≤ m := by nlinarith
  have hkpos : 1 ≤ k := by nlinarith
  have hd : A.period = B.period := by
    have : (A.period:ℤ) = B.period := by nlinarith
    exact_mod_cast this
  have hmone : m = 1 := by rw [hd] at hm; nlinarith
  exact ⟨hd,b,by simpa [hmone] using hb⟩

private theorem chart_criterion :
    (∃ r : X ⊕ Y → X ⊕ Y,
      (∀ a x, r (jointDeck A B a x) = jointDeck A B a (r x)) ∧
      r^[2] = jointTime A B) ↔
    ((Local A ∧ Local B) ∨
      (A.period = B.period ∧ ∃ b : H, b * B.holonomy = A.holonomy * b)) := by
  constructor
  · rintro ⟨r,hr,hs⟩
    have sq : ∀ x, r (r x) = jointTime A B x := by
      intro x
      simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using congrFun hs x
    have ht : ∀ x, r (jointTime A B x) = jointTime A B (r x) := by
      intro x
      rw [← hs]
      exact Function.Commute.self_iterate r 2 x
    have hl := component_constant A B A (fun x => r (.inl x))
      (by intro a x; exact hr a (.inl x)) (by intro x; exact ht (.inl x))
    have hh := component_constant A B B (fun x => r (.inr x))
      (by intro a x; exact hr a (.inr x)) (by intro x; exact ht (.inr x))
    cases hzero : tag (r (.inl (A.point 0 1))) <;>
      cases hone : tag (r (.inr (B.point 0 1)))
    · have allfalse : ∀ x, tag (r x) = false := by
        intro x; cases x with
        | inl x => exact (hl x).trans hzero
        | inr y => exact (hh y).trans hone
      have bad := allfalse (r (.inr (B.point 0 1)))
      rw [sq] at bad
      cases bad
    · left
      apply preserving A B r hr sq
      · intro x
        have hx := (hl x).trans hzero
        cases h : r (.inl x) with
        | inl y => exact ⟨y,rfl⟩
        | inr y => simp only [h,tag,Sum.elim_inr] at hx; cases hx
      · intro x
        have hx := (hh x).trans hone
        cases h : r (.inr x) with
        | inr y => exact ⟨y,rfl⟩
        | inl y => simp only [h,tag,Sum.elim_inl] at hx; cases hx
    · right
      apply exchanging A B r hr ht
      · intro x
        have hx := (hl x).trans hzero
        cases h : r (.inl x) with
        | inr y => exact ⟨y,rfl⟩
        | inl y => simp only [h,tag,Sum.elim_inl] at hx; cases hx
      · intro x
        have hx := (hh x).trans hone
        cases h : r (.inr x) with
        | inl y => exact ⟨y,rfl⟩
        | inr y => simp only [h,tag,Sum.elim_inr] at hx; cases hx
    · have alltrue : ∀ x, tag (r x) = true := by
        intro x; cases x with
        | inl x => exact (hl x).trans hzero
        | inr y => exact (hh y).trans hone
      have bad := alltrue (r (.inl (A.point 0 1)))
      rw [sq] at bad
      cases bad
  · rintro (⟨hl,hh⟩ | ⟨hd,b,hb⟩)
    · obtain ⟨f,hf,fs⟩ := (A.root_criterion 2).2 hl
      obtain ⟨g,hg,gs⟩ := (B.root_criterion 2).2 hh
      refine ⟨Sum.map f g, ?_, ?_⟩
      · intro a x; cases x with
        | inl x => exact congrArg Sum.inl (hf a x)
        | inr y => exact congrArg Sum.inr (hg a y)
      · funext x
        cases x with
        | inl x => exact congrArg Sum.inl (congrFun fs x)
        | inr y => exact congrArg Sum.inr (congrFun gs y)
    · have hb' : b⁻¹*A.holonomy = B.holonomy*b⁻¹ := by
        apply (mul_left_cancel (a := b))
        simpa [mul_assoc] using
          congrArg (· * b⁻¹) hb.symm
      let r : X ⊕ Y → X ⊕ Y := Sum.elim
        (fun x => .inr (transport A B b x))
        (fun y => .inl (A.time (transport B A b⁻¹ y)))
      refine ⟨r, ?_, ?_⟩
      · intro a x
        cases x with
        | inl x =>
          exact congrArg Sum.inr (transport_deck A B hd b hb a x)
        | inr y =>
          obtain ⟨t,z,rfl⟩ := B.covers y
          change Sum.inl _ = Sum.inl _
          congr 1
          rw [B.deck_point, transport_point B A hd.symm b⁻¹ hb', A.time_point,
            transport_point B A hd.symm b⁻¹ hb', A.time_point, A.deck_point, mul_assoc]
      · funext x
        cases x with
        | inl x =>
          obtain ⟨t,z,rfl⟩ := A.covers x
          change Sum.inl (A.time (transport B A b⁻¹ (transport A B b (A.point t z)))) = _
          rw [transport_point A B hd b hb, transport_point B A hd.symm b⁻¹ hb',
            mul_inv_cancel_right]
          rfl
        | inr y =>
          obtain ⟨t,z,rfl⟩ := B.covers y
          change Sum.inr (transport A B b (A.time (transport B A b⁻¹ (B.point t z)))) = _
          rw [transport_point B A hd.symm b⁻¹ hb', A.time_point,
            transport_point A B hd b hb, inv_mul_cancel_right, jointTime, Sum.map_inr, B.time_point]

end Charts

open EssentialWordRealization FiniteWindowTableCriterion FixedBlockRigidity
open FixedBlockRigidity.BlockCoordinates OrderedGroupChainHistories
open CountedGroupOverlap (GroupMat Path)

section Actual
variable {H : Type u} [Group H] {n : ℕ} (C : GroupMat H n n) (p₀ p₁ : Path C)

/-- Every original expanded numbered-edge history over either signed base orbit. -/
def OrbitUnion := {x : History (expandedGraph C) //
  (∃ t : ℤ, forgetHistory x = translate (baseGraph C) t p₀) ∨
  (∃ t : ℤ, forgetHistory x = translate (baseGraph C) t p₁)}

/-- The restriction of the original history shift. -/
def unionShift : OrbitUnion C p₀ p₁ → OrbitUnion C p₀ p₁ := fun x =>
  ⟨shift (expandedGraph C) x.val, by
    have step : ∀ (p : Path C) (t : ℤ), forgetHistory x.val = translate (baseGraph C) t p →
        forgetHistory (shift (expandedGraph C) x.val) = translate (baseGraph C) (t+1) p := by
      intro p t ht
      change shift (baseGraph C) (forgetHistory x.val) = _
      rw [ht]
      apply Subtype.ext
      funext i
      simp [shift,translate,add_comm,add_left_comm]
    rcases x.property with ⟨t,ht⟩ | ⟨t,ht⟩
    · exact Or.inl ⟨t+1,step p₀ t ht⟩
    · exact Or.inr ⟨t+1,step p₁ t ht⟩⟩

/-- The original left deck action, restricted to the full union. -/
def unionDeck (a : H) : OrbitUnion C p₀ p₁ → OrbitUnion C p₀ p₁ := fun x =>
  ⟨groupHistory C a x.val,x.property⟩

theorem signed_phase (p : Path C) (d : ℕ) (hd : 0 < d)
    (hmin : Function.minimalPeriod (CountedGroupOverlap.shift C) p = d)
    (x : History (expandedGraph C)) :
    (∃ t : ℤ, forgetHistory x = translate (baseGraph C) t p) ↔
      ∃ q : Fin d, forgetHistory x = (CountedGroupOverlap.shift C)^[q.val] p := by
  constructor
  · rintro ⟨t,ht⟩
    obtain ⟨q,hq⟩ := ((actualAtlas C p d hd hmin).point t 1).property
    exact ⟨q,ht.trans hq⟩
  · rintro ⟨q,hq⟩
    exact ⟨q.val,hq.trans (shift_iterate_translate (baseGraph C) q.val p)⟩

variable {d₀ d₁ : ℕ} (hd₀ : 0 < d₀) (hd₁ : 0 < d₁)
  (hm₀ : Function.minimalPeriod (CountedGroupOverlap.shift C) p₀ = d₀)
  (hm₁ : Function.minimalPeriod (CountedGroupOverlap.shift C) p₁ = d₁)
  (hdis : ∀ t : ℤ, translate (baseGraph C) t p₀ ≠ p₁)

include hdis in
theorem disjoint_lifts (x : History (expandedGraph C))
    (h₀ : ∃ q : Fin d₀, forgetHistory x = (CountedGroupOverlap.shift C)^[q.val] p₀)
    (h₁ : ∃ q : Fin d₁, forgetHistory x = (CountedGroupOverlap.shift C)^[q.val] p₁) : False := by
  obtain ⟨q,hq⟩ := h₀
  obtain ⟨r,hr⟩ := h₁
  change forgetHistory x = (shift (baseGraph C))^[q.val] p₀ at hq
  change forgetHistory x = (shift (baseGraph C))^[r.val] p₁ at hr
  rw [shift_iterate_translate] at hq hr
  apply hdis ((q.val:ℤ)-r.val)
  apply Subtype.ext
  funext i
  have hi := congrArg (fun p : Path C => p.val (i-r.val)) (hq.symm.trans hr)
  simpa [translate,sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using hi

private def join : LiftOrbit C p₀ d₀ ⊕ LiftOrbit C p₁ d₁ → OrbitUnion C p₀ p₁ :=
  Sum.elim (fun x => ⟨x.val,Or.inl (by
    obtain ⟨q,hq⟩ := x.property
    exact ⟨q.val,hq.trans (shift_iterate_translate (baseGraph C) q.val p₀)⟩)⟩)
    (fun x => ⟨x.val,Or.inr (by
    obtain ⟨q,hq⟩ := x.property
    exact ⟨q.val,hq.trans (shift_iterate_translate (baseGraph C) q.val p₁)⟩)⟩)

private def unionEquiv : LiftOrbit C p₀ d₀ ⊕ LiftOrbit C p₁ d₁ ≃ OrbitUnion C p₀ p₁ :=
  Equiv.ofBijective (join C p₀ p₁) (by
    constructor
    · intro x y h
      cases x with
      | inl x =>
        cases y with
        | inl y =>
          have he : x.val = y.val := congrArg (fun z : OrbitUnion C p₀ p₁ => z.val) h
          exact congrArg Sum.inl (Subtype.ext he)
        | inr y =>
          have he : x.val = y.val := congrArg Subtype.val h
          exact (disjoint_lifts C p₀ p₁ hdis x.val x.property (he.symm ▸ y.property)).elim
      | inr x =>
        cases y with
        | inl y =>
          have he : x.val = y.val := congrArg Subtype.val h
          exact (disjoint_lifts C p₀ p₁ hdis x.val (he.symm ▸ y.property) x.property).elim
        | inr y =>
          have he : x.val = y.val := congrArg (fun z : OrbitUnion C p₀ p₁ => z.val) h
          exact congrArg Sum.inr (Subtype.ext he)
    · intro x
      rcases x.property with h₀ | h₁
      · exact ⟨.inl ⟨x.val,(signed_phase C p₀ d₀ hd₀ hm₀ x.val).1 h₀⟩,Subtype.ext rfl⟩
      · exact ⟨.inr ⟨x.val,(signed_phase C p₁ d₁ hd₁ hm₁ x.val).1 h₁⟩,Subtype.ext rfl⟩)

include hd₀ hd₁ hm₀ hm₁ hdis in
/-- A square root on the full original-history union either preserves both joint
components, or exchanges equal-period components with conjugate ordered holonomies. -/
theorem square_root_criterion :
    (∃ R : OrbitUnion C p₀ p₁ → OrbitUnion C p₀ p₁,
      (∀ a x, R (unionDeck C p₀ p₁ a x) = unionDeck C p₀ p₁ a (R x)) ∧
      R^[2] = unionShift C p₀ p₁) ↔
    (((∃ s : Fin d₀, ∃ m : ℤ, ∃ b : H, Commute b (orbitHolonomy C p₀ d₀) ∧
        (2:ℤ)*(s.val:ℤ) = 1 + (d₀:ℤ)*m ∧ b^2*(orbitHolonomy C p₀ d₀)^m = 1) ∧
      (∃ s : Fin d₁, ∃ m : ℤ, ∃ b : H, Commute b (orbitHolonomy C p₁ d₁) ∧
        (2:ℤ)*(s.val:ℤ) = 1 + (d₁:ℤ)*m ∧ b^2*(orbitHolonomy C p₁ d₁)^m = 1)) ∨
      (d₀ = d₁ ∧ ∃ b : H, b*orbitHolonomy C p₁ d₁ = orbitHolonomy C p₀ d₀*b)) := by
  let A := actualAtlas C p₀ d₀ hd₀ hm₀
  let B := actualAtlas C p₁ d₁ hd₁ hm₁
  let e := unionEquiv C p₀ p₁ hd₀ hd₁ hm₀ hm₁ hdis
  have et : ∀ x, e (jointTime A B x) = unionShift C p₀ p₁ (e x) := by
    intro x; cases x <;> exact Subtype.ext rfl
  have ed : ∀ a x, e (jointDeck A B a x) = unionDeck C p₀ p₁ a (e x) := by
    intro a x; cases x <;> exact Subtype.ext rfl
  have eit : ∀ x, e.symm (unionShift C p₀ p₁ x) = jointTime A B (e.symm x) := by
    intro x
    apply e.injective
    rw [e.apply_symm_apply,et,e.apply_symm_apply]
  have eid : ∀ a x, e.symm (unionDeck C p₀ p₁ a x) = jointDeck A B a (e.symm x) := by
    intro a x
    apply e.injective
    rw [e.apply_symm_apply,ed,e.apply_symm_apply]
  change _ ↔ ((Local A ∧ Local B) ∨
    (A.period = B.period ∧ ∃ b : H, b * B.holonomy = A.holonomy * b))
  rw [← chart_criterion A B]
  constructor
  · rintro ⟨R,hR,hS⟩
    refine ⟨fun x => e.symm (R (e x)), ?_, ?_⟩
    · intro a x
      change e.symm (R (e (jointDeck A B a x))) = _
      rw [ed,hR,eid]
    · funext x
      change e.symm (R (e (e.symm (R (e x))))) = jointTime A B x
      rw [e.apply_symm_apply]
      have hs : R (R (e x)) = unionShift C p₀ p₁ (e x) := congrFun hS (e x)
      rw [hs,eit,e.symm_apply_apply]
  · rintro ⟨r,hr,hs⟩
    refine ⟨fun x => e (r (e.symm x)), ?_, ?_⟩
    · intro a x
      change e (r (e.symm (unionDeck C p₀ p₁ a x))) = _
      rw [eid,hr,ed]
    · funext x
      change e (r (e.symm (e (r (e.symm x))))) = unionShift C p₀ p₁ x
      rw [e.symm_apply_apply]
      have ht : r (r (e.symm x)) = jointTime A B (e.symm x) := congrFun hs (e.symm x)
      rw [ht,et,e.apply_symm_apply]

end Actual
end D5.S3.ConceptDynamics.Coding.PrimitiveLifts.TwoOrbitSquareRootCriterion
