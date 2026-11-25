/- GID: D5/S3/ConceptDynamics/Attribution/CoordinateFibreCounts
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/CoordinateFibreCounts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Output orbit fibre sizes and coordinate fixed counts obey a sharp parity criterion. -/

import D5.S3.ConceptDynamics.Attribution.CoordinateColourOrbit
import Mathlib.Algebra.Group.Action.Sigma
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.Algebra.Group.Action.Sum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.GroupTheory.PGroup

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.CoordinateFibreCounts

open Finset
open CoordinateFlagCoupling

open scoped Classical

noncomputable section

variable {I : Type*} [Fintype I]

private abbrev Label (r q : ℕ) := Fin r ⊕ (Fin q × ZMod 2)

private def shiftLabel {r q : ℕ} (v : I → ℕ) (g : Acting I) : Label r q → Label r q
  | .inl s => .inl s
  | .inr (j, b) => .inr (j, shift (fun i => decide (j.val < v i)) g.toAdd + b)

@[instance_reducible] private def labelAction {r q : ℕ} (v : I → ℕ) : MulAction (Acting I) (Label r q) where
  smul := shiftLabel v
  one_smul x := by
    rcases x with j | ⟨j, b⟩
    · rfl
    · change Sum.inr (j, shift (fun i => decide (j.val < v i)) 0 + b) = Sum.inr (j, b)
      simp [shift]
  mul_smul g h x := by
    rcases x with j | ⟨j, b⟩
    · rfl
    · change Sum.inr (j, shift (fun i => decide (j.val < v i)) (g.toAdd + h.toAdd) + b) =
        Sum.inr (j, shift (fun i => decide (j.val < v i)) g.toAdd +
          (shift (fun i => decide (j.val < v i)) h.toAdd + b))
      rw [shift_add, add_assoc]

private theorem label_fixed {r q : ℕ} (v : I → ℕ) (i : I) (j : Fin q) (b : ZMod 2) :
    shiftLabel v (generator i) (Sum.inr (j, b) : Label r q) = Sum.inr (j, b) ↔ j.val < v i := by
  simp only [shiftLabel]
  rw [show (generator i : Acting I).toAdd = Pi.single i 1 from rfl]
  rw [CoordinateColourOrbit.eval_single]
  by_cases hj : j.val < v i <;> simp [hj]

private theorem realize_coordinate_fixed_counts (m : ℕ) (z : I → ℕ)
    (bounds : ∀ i, z i ≤ m) (parity : ∀ i, z i % 2 = m % 2) :
    ∃ (S : Type) (_ : Fintype S) (_ : MulAction (Acting I) S), Fintype.card S = m ∧
      ∀ i, Nat.card {s : S // generator i • s = s} = z i := by
  classical
  let r := m % 2
  let q := m / 2
  let v (i : I) := z i / 2
  let S := Label r q
  letI : MulAction (Acting I) S := labelAction v
  refine ⟨S, inferInstance, inferInstance, ?_, ?_⟩
  · change Fintype.card (Fin r ⊕ (Fin q × ZMod 2)) = m
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, ZMod.card]
    dsimp [r, q]
    omega
  · intro i
    rw [Nat.card_eq_fintype_card]
    let e : {s : S // generator i • s = s} ≃ Fin r ⊕ ({j : Fin q // j.val < v i} × ZMod 2) :=
      { toFun := fun s => match hs : s.val with
          | .inl j => .inl j
          | .inr (j, b) => .inr (⟨j, (label_fixed v i j b).mp (by
            have h : shiftLabel v (generator i) s.val = s.val := s.property
            simpa only [hs] using h)⟩, b)
        invFun := fun s => match s with
          | .inl j => ⟨.inl j, rfl⟩
          | .inr (j, b) => ⟨.inr (j.val, b), (label_fixed v i j.val b).mpr j.property⟩
        left_inv := by
          rintro ⟨j | ⟨j, b⟩, h⟩ <;> rfl
        right_inv := by
          rintro (j | ⟨j, b⟩) <;> rfl }
    rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, ZMod.card,
      Fintype.card_fin_lt_of_le (show v i ≤ q from Nat.div_le_div_right (bounds i))]
    have hp := parity i
    dsimp [r, v]
    omega

private theorem generator_square (i : I) : (generator i : Acting I) ^ 2 = 1 := by
  rw [pow_two]
  let v := (generator i : Acting I).toAdd
  change v + v = (0 : I → ZMod 2)
  funext j
  change v j + v j = 0
  rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]

private theorem realize_uniform_point_fibres {T : Type} [Fintype T] [MulAction (Acting I) T]
    (m : ℕ) (z : I → ℕ)
    (bounds : ∀ i, z i ≤ m) (parity : ∀ i, z i % 2 = m % 2) :
    ∃ (S : Type) (_ : Fintype S) (_ : MulAction (Acting I) S) (f : S → T),
      (∀ (g : Acting I) s, f (g • s) = g • f s) ∧
      (∀ t, Nat.card {s : S // f s = t} = m) ∧
      ∀ i t, Nat.card {s : S // f s = t ∧ generator i • s = s} =
        if generator i • t = t then z i else 0 := by
  classical
  obtain ⟨L, _, _, size, counts⟩ := realize_coordinate_fixed_counts m z bounds parity
  refine ⟨T × L, inferInstance, inferInstance, Prod.fst, fun _ _ => rfl, ?_, ?_⟩
  · intro t
    let e : {s : T × L // s.1 = t} ≃ L :=
      { toFun := fun s => s.val.2
        invFun := fun l => ⟨(t, l), rfl⟩
        left_inv := by rintro ⟨⟨_, _⟩, rfl⟩; rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, size]
  · intro i t
    by_cases target_fixed : generator i • t = t
    · rw [ite_eq_left target_fixed]
      let e : {s : T × L // s.1 = t ∧ generator i • s = s} ≃ {l : L // generator i • l = l} :=
        { toFun := fun s => ⟨s.val.2, congrArg Prod.snd s.property.2⟩
          invFun := fun l => ⟨(t, l.val), rfl, Prod.ext target_fixed l.property⟩
          left_inv := by rintro ⟨⟨_, _⟩, rfl, _⟩; rfl
          right_inv := fun _ => rfl }
      exact (Nat.card_congr e).trans (counts i)
    · rw [ite_eq_right target_fixed]
      haveI : IsEmpty {s : T × L // s.1 = t ∧ generator i • s = s} :=
        ⟨fun s => by
          have eq : generator i • s.val.1 = s.val.1 := congrArg Prod.fst s.property.2
          rw [s.property.1] at eq
          exact target_fixed eq⟩
      simp [Nat.card_eq_fintype_card]

private theorem fixed_fibre_card_parity {S T : Type*} [Finite S]
    [MulAction (Acting I) S] [MulAction (Acting I) T]
    (f : S → T) (equivariant : ∀ (g : Acting I) s, f (g • s) = g • f s)
    (i : I) (t : T) (target_fixed : generator i • t = t) :
    Nat.card {s : S // f s = t ∧ generator i • s = s} ≡ Nat.card {s : S // f s = t} [MOD 2] := by
  classical
  let H := Subgroup.zpowers (generator i)
  let F : SubMulAction H S := {
    carrier := {s | f s = t}
    smul_mem' := by
      intro h s hs
      have hfix : (h : Acting I) • t = t := by
        have hsub : H ≤ MulAction.stabilizer (Acting I) t := by
          dsimp only [H]
          rwa [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
        exact hsub h.property
      change f s = t at hs
      change f ((h : Acting I) • s) = t
      rw [equivariant, hs, hfix] }
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have power : IsPGroup 2 H := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    change Nat.card (Subgroup.zpowers (generator i)) ∣ 2 ^ 1
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (generator_square i)
  let g : H := ⟨generator i, Subgroup.mem_zpowers _⟩
  have subgroup_gen : Subgroup.zpowers g = ⊤ := by
    apply top_unique
    intro h _
    obtain ⟨n, hn⟩ := h.property
    exact ⟨n, Subtype.ext hn⟩
  have readout (s : F) : s ∈ MulAction.fixedPoints H F ↔ generator i • s.val = s.val := by
    have equiv : (∀ h : H, h • s = s) ↔ g • s = s := by
      have fixesTop : (∀ h : H, h • s = s) ↔ (⊤ : Subgroup H) ≤ MulAction.stabilizer H s :=
        ⟨fun all h _ => all h, fun h g => h (Subgroup.mem_top g)⟩
      rw [fixesTop, ← subgroup_gen, Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
    exact MulAction.mem_fixedPoints.trans (equiv.trans Subtype.ext_iff)
  let e : (MulAction.fixedPoints H F) ≃ {s : S // f s = t ∧ generator i • s = s} :=
    { toFun := fun s => ⟨s.val.val, s.val.property, (readout s.val).mp s.property⟩
      invFun := fun s => ⟨⟨s.val, s.property.1⟩, (readout _).mpr s.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e]
  exact (power.card_modEq_card_fixedPoints F).symm

open MulAction

private theorem realize_orbit_point_fibres {T : Type} [Fintype T] [MulAction (Acting I) T]
    (m : orbitRel.Quotient (Acting I) T → ℕ)
    (z : orbitRel.Quotient (Acting I) T → I → ℕ)
    (bounds : ∀ o i, z o i ≤ m o) (parity : ∀ o i, z o i % 2 = m o % 2) :
    ∃ (S : Type) (_ : Fintype S) (_ : MulAction (Acting I) S) (f : S → T),
      (∀ (g : Acting I) s, f (g • s) = g • f s) ∧
      (∀ t, Nat.card {s : S // f s = t} = m (Quotient.mk'' t)) ∧
      ∀ i t, Nat.card {s : S // f s = t ∧ generator i • s = s} =
        if generator i • t = t then z (Quotient.mk'' t) i else 0 := by
  classical
  let Q := orbitRel.Quotient (Acting I) T
  let Tₒ (o : Q) : SubMulAction (Acting I) T :=
    { carrier := o.orbit
      smul_mem' := by
        intro g t ht
        exact orbitRel.Quotient.mem_orbit.mpr
          (orbitRel.Quotient.quotient_smul_eq.trans (orbitRel.Quotient.mem_orbit.mp ht)) }
  let _ : Fintype Q := Fintype.ofFinite Q
  let _ (o : Q) : Fintype (Tₒ o) := Fintype.ofFinite _
  have chooseOne (o : Q) := realize_uniform_point_fibres (T := Tₒ o) (m o) (z o)
    (bounds o) (parity o)
  choose L finiteL actionL f equiv totals fixed using chooseOne
  let _ (o : Q) : Fintype (L o) := finiteL o
  let _ (o : Q) : MulAction (Acting I) (L o) := actionL o
  let whole := (Σ o : Q, L o)
  let readout (s : whole) : T := (f s.1 s.2).val
  have equivariance (g : Acting I) (s : whole) : readout (g • s) = g • readout s := by
    cases s with
    | mk o l => exact congrArg Subtype.val (equiv o g l)
  have readoutOrbit (s : whole) : Quotient.mk'' (readout s) = s.1 :=
    orbitRel.Quotient.mem_orbit.mp (f s.1 s.2).property
  refine ⟨whole, inferInstance, inferInstance, readout, equivariance, ?_, ?_⟩
  · intro t
    let o : Q := Quotient.mk'' t
    let tₒ : Tₒ o := ⟨t, orbitRel.Quotient.mem_orbit.mpr rfl⟩
    let e : {s : whole // readout s = t} ≃ {l : L o // f o l = tₒ} :=
      { toFun := fun s => by
          obtain ⟨⟨q, l⟩, hl⟩ := s
          have eq : q = o := (readoutOrbit ⟨q, l⟩).symm.trans (congrArg Quotient.mk'' hl)
          subst q
          exact ⟨l, Subtype.ext hl⟩
        invFun := fun l => ⟨⟨o, l.val⟩, congrArg Subtype.val l.property⟩
        left_inv := by
          rintro ⟨⟨q, l⟩, hl⟩
          have eq : q = o := (readoutOrbit ⟨q, l⟩).symm.trans (congrArg Quotient.mk'' hl)
          subst q
          rfl
        right_inv := by rintro ⟨l,hl⟩; rfl }
    exact (Nat.card_congr e).trans (totals o tₒ)
  · intro i t
    let o : Q := Quotient.mk'' t
    let tₒ : Tₒ o := ⟨t, orbitRel.Quotient.mem_orbit.mpr rfl⟩
    let e : {s : whole // readout s = t ∧ generator i • s = s} ≃
        {l : L o // f o l = tₒ ∧ generator i • l = l} :=
      { toFun := fun s => by
          obtain ⟨⟨q, l⟩, hl,hs⟩ := s
          have eq : q = o := (readoutOrbit ⟨q, l⟩).symm.trans (congrArg Quotient.mk'' hl)
          subst q
          exact ⟨l, Subtype.ext hl, eq_of_heq (Sigma.mk.inj_iff.mp hs).2⟩
        invFun := fun l => ⟨⟨o, l.val⟩, congrArg Subtype.val l.property.1,
          congrArg (Sigma.mk o) l.property.2⟩
        left_inv := by
          rintro ⟨⟨q, l⟩, hl,hs⟩
          have eq : q = o := (readoutOrbit ⟨q, l⟩).symm.trans (congrArg Quotient.mk'' hl)
          subst q
          rfl
        right_inv := by rintro ⟨l, hl, hs⟩; rfl }
    rw [Nat.card_congr e, fixed o i tₒ]
    have hit : generator i • tₒ = tₒ ↔ generator i • t = t := Subtype.ext_iff
    simp only [hit, o]

private theorem fixed_is_preserved_by_action {X : Type*} [MulAction (Acting I) X]
    (i : I) (g : Acting I) (x : X) :
    generator i • (g • x) = g • x ↔ generator i • x = x := by
  rw [smul_comm (generator i) g]
  exact (MulAction.toPerm g).injective.eq_iff

/-- An equivariant finite readout has constant fibre size on each output orbit. Each
coordinate that fixes an output point sees a fixed-seed count of the same parity in its fibre. -/
theorem orbit_fixed_fibre_counts {S T : Type*} [Finite S]
    [MulAction (Acting I) S] [MulAction (Acting I) T]
    (f : S → T) (equivariant : ∀ (g : Acting I) s, f (g • s) = g • f s) :
    ∃ (m : orbitRel.Quotient (Acting I) T → ℕ)
      (z : orbitRel.Quotient (Acting I) T → I → ℕ),
      (∀ o i, z o i ≤ m o) ∧ (∀ o i, z o i % 2 = m o % 2) ∧
      (∀ t, Nat.card {s : S // f s = t} = m (Quotient.mk'' t)) ∧
      ∀ i t, Nat.card {s : S // f s = t ∧ generator i • s = s} =
        if generator i • t = t then z (Quotient.mk'' t) i else 0 := by
  classical
  let Q := orbitRel.Quotient (Acting I) T
  let count (t : T) := Nat.card {s : S // f s = t}
  let fixed (i : I) (t : T) := Nat.card {s : S // f s = t ∧ generator i • s = s}
  have countInvariant (t : T) (g : Acting I) : count (g • t) = count t := by
    let e : {s : S // f s = g • t} ≃ {s : S // f s = t} :=
      { toFun := fun s => ⟨g⁻¹ • s.val, by rw [equivariant, s.property, inv_smul_smul]⟩
        invFun := fun s => ⟨g • s.val, by rw [equivariant, s.property]⟩
        left_inv := fun s => Subtype.ext (smul_inv_smul g s.val)
        right_inv := fun s => Subtype.ext (inv_smul_smul g s.val) }
    exact Nat.card_congr e
  have fixedInvariant (i : I) (t : T) (g : Acting I) : fixed i (g • t) = fixed i t := by
    let e : {s : S // f s = g • t ∧ generator i • s = s} ≃
        {s : S // f s = t ∧ generator i • s = s} :=
      { toFun := fun s => ⟨g⁻¹ • s.val,
          by rw [equivariant, s.property.1, inv_smul_smul],
          (fixed_is_preserved_by_action i g⁻¹ s.val).mpr s.property.2⟩
        invFun := fun s => ⟨g • s.val, by rw [equivariant, s.property.1],
          (fixed_is_preserved_by_action i g s.val).mpr s.property.2⟩
        left_inv := fun s => Subtype.ext (smul_inv_smul g s.val)
        right_inv := fun s => Subtype.ext (inv_smul_smul g s.val) }
    exact Nat.card_congr e
  let m (o : Q) := count o.out
  let z (o : Q) (i : I) := if generator i • o.out = o.out then fixed i o.out else m o
  refine ⟨m, z, ?_, ?_, ?_, ?_⟩
  · intro o i
    dsimp only [z]
    split
    · exact Nat.card_le_card_of_injective
        (fun s : {s : S // f s = o.out ∧ generator i • s = s} =>
          (⟨s.val, s.property.1⟩ : {s : S // f s = o.out}))
        (fun _ _ h => Subtype.ext (congrArg (fun s : {s : S // f s = o.out} => s.val) h))
    · exact le_rfl
  · intro o i
    dsimp only [z]
    split
    · rename_i h
      exact fixed_fibre_card_parity f equivariant i o.out h
    · rfl
  · intro t
    obtain ⟨g, hg⟩ := Quotient.exact (Quotient.out_eq (Quotient.mk'' t : Q))
    change g • t = (Quotient.mk'' t : Q).out at hg
    change count t = count (Quotient.mk'' t : Q).out
    rw [← hg, countInvariant]
  · intro i t
    let o : Q := Quotient.mk'' t
    obtain ⟨g, hg⟩ := Quotient.exact (Quotient.out_eq o)
    change g • t = o.out at hg
    change fixed i t = if generator i • t = t then z o i else 0
    by_cases h : generator i • t = t
    · have outFix : generator i • o.out = o.out := hg ▸ (fixed_is_preserved_by_action i g t).2 h
      simp only [z, ite_eq_left h, ite_eq_left outFix, ← hg, fixedInvariant]
    · rw [ite_eq_right h]
      have empty : IsEmpty {s : S // f s = t ∧ generator i • s = s} := by
        refine ⟨fun s => h ?_⟩
        have eq := (equivariant (generator i) s.val).symm.trans (congrArg f s.property.2)
        rwa [s.property.1] at eq
      simp [fixed]

/-- Prescribed orbit fibre sizes and coordinate fixed counts admit a common equivariant
realization exactly when each fixed-point fibre satisfies the size bound and parity constraint. -/
theorem exact_orbit_fibre_counts {T : Type} [Fintype T] [MulAction (Acting I) T]
    (m : orbitRel.Quotient (Acting I) T → ℕ) (z : orbitRel.Quotient (Acting I) T → I → ℕ) :
    (∃ (S : Type) (_ : Fintype S) (_ : MulAction (Acting I) S) (f : S → T),
      (∀ (g : Acting I) s, f (g • s) = g • f s) ∧
      (∀ t, Nat.card {s : S // f s = t} = m (Quotient.mk'' t)) ∧
      ∀ i t, Nat.card {s : S // f s = t ∧ generator i • s = s} =
        if generator i • t = t then z (Quotient.mk'' t) i else 0) ↔
    ∀ (t : T) (i : I), generator i • t = t →
      z (Quotient.mk'' t) i ≤ m (Quotient.mk'' t) ∧
        z (Quotient.mk'' t) i % 2 = m (Quotient.mk'' t) % 2 := by
  classical
  constructor
  · rintro ⟨S, _, _, f, equiv, totals, fixed⟩ t i ht
    have fixedCount := fixed i t
    rw [ite_eq_left ht] at fixedCount
    rw [← fixedCount, ← totals t]
    exact ⟨Nat.card_le_card_of_injective
      (fun s : {s : S // f s = t ∧ generator i • s = s} =>
        (⟨s.val, s.property.1⟩ : {s : S // f s = t}))
      (fun _ _ h => Subtype.ext (congrArg (fun s : {s : S // f s = t} => s.val) h)),
      fixed_fibre_card_parity f equiv i t ht⟩
  · intro conditions
    let Q := orbitRel.Quotient (Acting I) T
    let a (o : Q) (i : I) := if generator i • o.out = o.out then z o i else m o
    have bounds (o : Q) (i : I) : a o i ≤ m o := by
      by_cases h : generator i • o.out = o.out
      · simpa [a, h, Quotient.out_eq] using (conditions o.out i h).1
      · simp [a, h]
    have parity (o : Q) (i : I) : a o i % 2 = m o % 2 := by
      by_cases h : generator i • o.out = o.out
      · simpa [a, h, Quotient.out_eq] using (conditions o.out i h).2
      · simp [a, h]
    obtain ⟨S, _, _, f, equiv, totals, fixed⟩ := realize_orbit_point_fibres m a bounds parity
    refine ⟨S, inferInstance, inferInstance, f, equiv, totals, fun i t => ?_⟩
    rw [fixed]
    by_cases ht : generator i • t = t
    · let o : Q := Quotient.mk'' t
      obtain ⟨g, hg⟩ := Quotient.exact (Quotient.out_eq o)
      change g • t = o.out at hg
      have oh : generator i • o.out = o.out :=
        hg ▸ (fixed_is_preserved_by_action i g t).mpr ht
      change (if generator i • t = t then a o i else 0) =
        (if generator i • t = t then z o i else 0)
      simp [a, ht, oh]
    · simp [ht]

end


end D5.S3.ConceptDynamics.Attribution.CoordinateFibreCounts
