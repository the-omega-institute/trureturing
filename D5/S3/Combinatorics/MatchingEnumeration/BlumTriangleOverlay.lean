/- GID: D5/S3/Combinatorics/MatchingEnumeration/BlumTriangleOverlay
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MatchingEnumeration/BlumTriangleOverlay
   mirror-E: none(waiver:reflection-component-switch)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.Cycle.Basic]
   utility: none
   digest: Switching an axis component is an involution on the fixed triangle matchings. -/

import Mathlib.GroupTheory.Perm.Cycle.Basic
import D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleSwitching

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleOverlay

open BlumTriangleDefs BlumTriangleSwitching Equiv.Perm

open Classical in
/-- The component containing a reflection-fixed vertex can be switched without changing
the uncolored overlay. Repeating this construction gives the original matching. -/
theorem axis_component_switch (n : ℕ) (a : Vertex n) (ha : reflection n a = a) :
    ∃ S : Equiv.Perm (PerfectMatching n), Function.Involutive S ∧
      (∀ P v w,
        (w = (S P).1 v ∨ w = reflection n ((S P).1 (reflection n v))) ↔
          (w = P.1 v ∨ w = reflection n (P.1 (reflection n v)))) ∧
      ∀ P v, (S P).1 v = if Relation.EqvGen
          (fun u w => w = P.1 u ∨ w = reflection n (P.1 (reflection n u))) a v
        then reflection n (P.1 (reflection n v)) else P.1 v := by
  classical
  let rho : Vertex n → Vertex n := reflection n
  have rr (v : Vertex n) : rho (rho v) = v := (reflection n).left_inv v
  have ra : rho a = a := ha
  let blue : PerfectMatching n → Vertex n → Vertex n := fun P v => rho (P.1 (rho v))
  let edge : PerfectMatching n → Vertex n → Vertex n → Prop :=
    fun P v w => w = P.1 v ∨ w = blue P v
  let conn := fun P => Relation.EqvGen (edge P)
  have bb (P : PerfectMatching n) (v : Vertex n) : blue P (blue P v) = v := by
    dsimp [blue]
    rw [rr, (P.2 (rho v)).1, rr]
  have bn (P : PerfectMatching n) (v : Vertex n) : blue P v ≠ v := by
    intro h
    have h' := congrArg rho h
    dsimp [blue] at h'
    rw [rr] at h'
    exact (P.2 (rho v)).2.1 h'
  have ba (P : PerfectMatching n) (v : Vertex n) : Adj v (blue P v) := by
    have h := (reflection n).map_rel_iff.mpr (P.2 (rho v)).2.2
    change Adj (rho (rho v)) (blue P v) at h
    simpa only [rr] using h
  have reflect (P : PerfectMatching n) {v w : Vertex n} (h : conn P v w) :
      conn P (rho v) (rho w) := by
    induction h with
    | rel v w h =>
      apply Relation.EqvGen.rel
      rcases h with h | h
      · right
        dsimp [blue]
        rw [rr, h]
      · left
        rw [h]
        dsimp [blue]
        rw [rr]
    | refl v => exact Relation.EqvGen.refl _
    | symm v w _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans v w z _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'
  have reflect_component (P : PerfectMatching n) (v : Vertex n) :
      conn P a (rho v) ↔ conn P a v := by
    constructor
    · intro h
      have h' := reflect P h
      simpa only [ra, rr] using h'
    · intro h
      simpa only [ra] using reflect P h
  have red_component (P : PerfectMatching n) (v : Vertex n) :
      conn P a (P.1 v) ↔ conn P a v := by
    have h : conn P v (P.1 v) := Relation.EqvGen.rel _ _ (Or.inl rfl)
    exact ⟨fun h' => Relation.EqvGen.trans _ _ _ h' (Relation.EqvGen.symm _ _ h),
      fun h' => Relation.EqvGen.trans _ _ _ h' h⟩
  have blue_component (P : PerfectMatching n) (v : Vertex n) :
      conn P a (blue P v) ↔ conn P a v := by
    have h : conn P v (blue P v) := Relation.EqvGen.rel _ _ (Or.inr rfl)
    exact ⟨fun h' => Relation.EqvGen.trans _ _ _ h' (Relation.EqvGen.symm _ _ h),
      fun h' => Relation.EqvGen.trans _ _ _ h' h⟩
  let switch : PerfectMatching n → PerfectMatching n := fun P =>
    ⟨fun v => if conn P a v then blue P v else P.1 v, by
      intro v
      by_cases h : conn P a v
      · have hb : conn P a (blue P v) := (blue_component P v).mpr h
        simp only [if_pos h, if_pos hb]
        exact ⟨bb P v, bn P v, ba P v⟩
      · have hp : ¬ conn P a (P.1 v) := fun hp => h ((red_component P v).mp hp)
        simp only [if_neg h, if_neg hp]
        exact P.2 v⟩
  have new_blue (P : PerfectMatching n) (v : Vertex n) :
      blue (switch P) v = if conn P a v then P.1 v else blue P v := by
    change rho (if conn P a (rho v) then blue P (rho v) else P.1 (rho v)) = _
    by_cases h : conn P a v
    · rw [if_pos ((reflect_component P v).mpr h), if_pos h]
      dsimp [blue]
      rw [rr, rr]
    · rw [if_neg (fun h' => h ((reflect_component P v).mp h')), if_neg h]
  have same_edges (P : PerfectMatching n) : edge (switch P) = edge P := by
    funext v w
    apply propext
    dsimp [edge]
    rw [new_blue]
    change (w = (if conn P a v then blue P v else P.1 v) ∨
      w = (if conn P a v then P.1 v else blue P v)) ↔ _
    by_cases h : conn P a v
    · simp only [if_pos h]
      exact or_comm
    · simp only [if_neg h]
  have twice (P : PerfectMatching n) : switch (switch P) = P := by
    apply Subtype.ext
    funext v
    have hc : conn (switch P) a v ↔ conn P a v := by
      dsimp [conn]
      rw [same_edges]
    change (if conn (switch P) a v then blue (switch P) v else (switch P).1 v) = P.1 v
    rw [new_blue]
    by_cases h : conn P a v
    · rw [if_pos (hc.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (hc.mp h'))]
      change (if conn P a v then blue P v else P.1 v) = P.1 v
      rw [if_neg h]
  refine ⟨⟨switch, switch, twice, twice⟩, twice, ?_, ?_⟩
  · intro P v w
    change edge (switch P) v w ↔ edge P v w
    rw [same_edges]
  · intro P v
    rfl

/-- The overlay component through an axis vertex contains exactly one other axis
vertex. Rotation coordinates give uniqueness; two restricted involutions give existence. -/
theorem axis_component_pair (n : ℕ) (P : PerfectMatching n)
    (a : Vertex n) (ha : reflection n a = a) :
    ∃! v : Vertex n, v ≠ a ∧ reflection n v = v ∧ Relation.EqvGen
      (fun u z => z = P.1 u ∨ z = reflection n (P.1 (reflection n u))) a v := by
  classical
  have unique (v w : Vertex n) (hv : reflection n v = v) (hw : reflection n w = w)
      (hva : v ≠ a) (hwa : w ≠ a)
      (hc : Relation.EqvGen
        (fun u z => z = P.1 u ∨ z = reflection n (P.1 (reflection n u))) a v)
      (hc' : Relation.EqvGen
        (fun u z => z = P.1 u ∨ z = reflection n (P.1 (reflection n u))) a w) :
      v = w := by
    classical
    let r : Equiv.Perm (Vertex n) := (reflection n).toEquiv
    let p : Equiv.Perm (Vertex n) :=
      ⟨P.1, P.1, fun u => (P.2 u).1, fun u => (P.2 u).1⟩
    let t : Equiv.Perm (Vertex n) := p * r
    have ri : r⁻¹ = r := rfl
    have pi : p⁻¹ = p := rfl
    have rr (u : Vertex n) : r (r u) = u := r.left_inv u
    have pp (u : Vertex n) : p (p u) = u := p.left_inv u
    have rrs : r * r = 1 := by
      calc
        r * r = r⁻¹ * r := congrArg (fun e => e * r) ri.symm
        _ = 1 := inv_mul_cancel r
    have ra : r a = a := ha
    have rt : r * t * r⁻¹ = t⁻¹ := by
      simp [t, mul_inv_rev, ri, pi, mul_assoc, rrs]
    have reflected {u : Vertex n} (h : t.SameCycle a u) : t.SameCycle a (r u) := by
      have h' := h.conj (g := r)
      rw [rt, ra] at h'
      exact h'.of_inv
    have red {u : Vertex n} (h : t.SameCycle a u) : t.SameCycle a (p u) := by
      have h' := (reflected h).apply_right
      change t.SameCycle a (p (r (r u))) at h'
      simpa only [rr] using h'
    have blue {u : Vertex n} (h : t.SameCycle a u) :
        t.SameCycle a (r (p (r u))) := by
      have h' := (reflected h).symm_apply_right
      exact h'
    have in_orbit {u : Vertex n} (h : Relation.EqvGen
        (fun u z => z = p u ∨ z = r (p (r u))) a u) : t.SameCycle a u := by
      have carry {x y : Vertex n} (hxy : Relation.EqvGen
          (fun u z => z = p u ∨ z = r (p (r u))) x y) :
          t.SameCycle a x ↔ t.SameCycle a y := by
        induction hxy with
        | rel x y h =>
          rcases h with rfl | rfl
          · exact ⟨red, fun h => by simpa only [pp] using red h⟩
          · refine ⟨blue, fun h => ?_⟩
            simpa only [rr, pp] using blue h
        | refl => rfl
        | symm _ _ _ ih => exact ih.symm
        | trans _ _ _ _ _ ih ih' => exact ih.trans ih'
      exact (carry h).mp (SameCycle.refl t a)
    let d := Function.minimalPeriod (t : Vertex n → Vertex n) a
    have dpos : 0 < d := Function.minimalPeriod_pos_of_mem_periodicPts
      (t.injective.mem_periodicPts a)
    have coordinate {u : Vertex n} (h : t.SameCycle a u) :
        ∃ i : ℕ, i < d ∧ (t ^ i) a = u := by
      obtain ⟨i, hi⟩ := h.exists_nat_pow_eq
      refine ⟨i % d, Nat.mod_lt _ dpos, ?_⟩
      have hmod := Function.iterate_mod_minimalPeriod_eq
        (f := (t : Vertex n → Vertex n)) (x := a) (n := i)
      simpa only [← Equiv.Perm.coe_pow] using hmod.trans hi
    have half {u : Vertex n} (hu : r u = u) (hne : u ≠ a)
        (i : ℕ) (hi : i < d) (he : (t ^ i) a = u) : 2 * i = d := by
      have conjugated : r * t ^ i * r⁻¹ = t⁻¹ ^ i := by
        rw [← conj_pow, rt]
      have flip : r ((t ^ i) a) = (t⁻¹ ^ i) a := by
        have h := congrArg (fun e : Equiv.Perm (Vertex n) => e a) conjugated
        simpa only [mul_apply, ri, ra] using h
      have equal : (t⁻¹ ^ i) a = (t ^ i) a := by
        rw [← flip, he, hu]
      have periodic : (t ^ (2 * i)) a = a := by
        have h := congrArg (fun u => (t ^ i) u) equal
        simpa only [← mul_apply, ← pow_add, mul_inv_rev, inv_pow, mul_inv_cancel,
          one_apply, two_mul] using h.symm
      have div : d ∣ 2 * i := by
        apply Function.IsPeriodicPt.minimalPeriod_dvd
        change (t : Vertex n → Vertex n)^[2 * i] a = a
        simpa only [Equiv.Perm.coe_pow] using periodic
      have ipos : 0 < i := by
        by_contra hn
        have iz : i = 0 := by omega
        rw [iz, pow_zero, one_apply] at he
        exact hne he.symm
      exact Nat.eq_of_dvd_of_lt_two_mul (by omega) div (by omega)
    have hc0 : Relation.EqvGen (fun u z => z = p u ∨ z = r (p (r u))) a v := hc
    have hc1 : Relation.EqvGen (fun u z => z = p u ∨ z = r (p (r u))) a w := hc'
    obtain ⟨i, hi, he⟩ := coordinate (in_orbit hc0)
    obtain ⟨j, hj, hj'⟩ := coordinate (in_orbit hc1)
    have ih := half hv hva i hi he
    have jh := half hw hwa j hj hj'
    have ij : i = j := by omega
    rw [← he, ← hj', ij]
  -- The component is even; deleting its only hypothetical fixed vertex makes it odd.
  let r : Vertex n → Vertex n := reflection n
  let conn := Relation.EqvGen
    (fun u z => z = P.1 u ∨ z = r (P.1 (r u)))
  have rr (u : Vertex n) : r (r u) = u := (reflection n).left_inv u
  have ra : r a = a := ha
  have reflect {v w : Vertex n} (h : conn v w) : conn (r v) (r w) := by
    induction h with
    | rel v w h =>
      apply Relation.EqvGen.rel
      rcases h with h | h
      · right
        rw [rr, h]
      · left
        rw [h, rr]
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'
  have reflect_a {v : Vertex n} (h : conn a v) : conn a (r v) := by
    simpa only [ra] using reflect h
  have red_a {v : Vertex n} (h : conn a v) : conn a (P.1 v) :=
    Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.rel _ _ (Or.inl rfl))
  let C := {v : Vertex n // conn a v}
  let : Fintype C := Fintype.ofFinite _
  let ac : C := ⟨a, Relation.EqvGen.refl _⟩
  let red : C → C := fun v => ⟨P.1 v.1, red_a v.2⟩
  have red_invol : Function.Involutive red := by
    intro v
    apply Subtype.ext
    exact (P.2 v.1).1
  have red_free (v : C) : red v ≠ v := by
    intro h
    exact (P.2 v.1).2.1 (congrArg Subtype.val h)
  have ceven := D5.S3.PrimeForms.Crossing.GlideCrossingParity.glide_crossing_count_even
    red red_invol red_free
  have exists_other : ∃ v : Vertex n, v ≠ a ∧ r v = v ∧ conn a v := by
    by_contra hn
    let D := {v : C // v ≠ ac}
    let : Fintype D := Fintype.ofFinite _
    let flip : D → D := fun v => ⟨⟨r v.1.1, reflect_a v.1.2⟩, by
      intro h
      have h' := congrArg (fun v : C => r v.1) h
      change r (r v.1.1) = r a at h'
      rw [rr, ra] at h'
      exact v.2 (Subtype.ext h')⟩
    have flip_invol : Function.Involutive flip := by
      intro v
      apply Subtype.ext
      apply Subtype.ext
      exact rr v.1.1
    have flip_free (v : D) : flip v ≠ v := by
      intro h
      have fixed := congrArg (fun v : D => v.1.1) h
      apply hn
      refine ⟨v.1.1, ?_, fixed, v.1.2⟩
      intro h'
      exact v.2 (Subtype.ext h')
    have deven :=
      D5.S3.PrimeForms.Crossing.GlideCrossingParity.glide_crossing_count_even
        flip flip_invol flip_free
    have cd : Fintype.card D = Fintype.card C - 1 := by
      change Fintype.card {v : C // ¬ v = ac} = _
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    have cp : 0 < Fintype.card C := Fintype.card_pos_iff.mpr ⟨ac⟩
    obtain ⟨c, hc⟩ := ceven
    obtain ⟨d, hd⟩ := deven
    omega
  obtain ⟨v, hva, hv, hc⟩ := exists_other
  refine ⟨v, ⟨hva, hv, hc⟩, ?_⟩
  rintro w ⟨hwa, hw, hc'⟩
  exact unique w v hw hv hwa hva hc' hc


/-- Independent marked components give equally sized side-choice fibers. The proof
constructs their equivalences by induction on the coordinates to be switched. -/
theorem reflection_choice_count (n k : ℕ) (axis : Fin k → Vertex n)
    (haxis : ∀ i, reflection n (axis i) = axis i) (side : Vertex n → Bool)
    (hside : ∀ (P : PerfectMatching n) i,
      side (reflection n (P.1 (axis i))) = !(side (P.1 (axis i))))
    (hseparate : ∀ (P : PerfectMatching n) i j, Relation.EqvGen
      (fun u z => z = P.1 u ∨ z = reflection n (P.1 (reflection n u)))
        (axis i) (axis j) → i = j) :
    M n = 2 ^ k * Nat.card {P : PerfectMatching n //
      ∀ i, side (P.1 (axis i)) = false} := by
  classical
  let choice : PerfectMatching n → Fin k → Bool := fun P i => side (P.1 (axis i))
  have switches (i : Fin k) := axis_component_switch n (axis i) (haxis i)
  choose S hS hEdges hFormula using switches
  have toggle (P : PerfectMatching n) (i j : Fin k) :
      choice (S i P) j = if j = i then !(choice P j) else choice P j := by
    dsimp [choice]
    rw [hFormula]
    by_cases hji : j = i
    · subst j
      rw [if_pos (Relation.EqvGen.refl _), haxis, hside, if_pos rfl]
    · have hn : ¬ Relation.EqvGen
          (fun u z => z = P.1 u ∨ z = reflection n (P.1 (reflection n u)))
            (axis i) (axis j) := fun h => hji (hseparate P i j h).symm
      rw [if_neg hn, if_neg hji]
  let Fiber := fun s : Finset (Fin k) =>
    {P : PerfectMatching n // choice P = fun i => decide (i ∈ s)}
  have normalize (s : Finset (Fin k)) : Nonempty (Fiber s ≃ Fiber ∅) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨Equiv.refl _⟩
    | @insert i s hi ih =>
      obtain ⟨e⟩ := ih
      have forward (P : Fiber (insert i s)) :
          choice (S i P.1) = fun j => decide (j ∈ s) := by
        funext j
        rw [toggle, congrFun P.2 j]
        by_cases hji : j = i
        · subst j
          simp [hi]
        · simp [hji]
      have backward (P : Fiber s) :
          choice (S i P.1) = fun j => decide (j ∈ insert i s) := by
        funext j
        rw [toggle, congrFun P.2 j]
        by_cases hji : j = i
        · subst j
          simp [hi]
        · simp [hji]
      let step : Fiber (insert i s) ≃ Fiber s :=
        { toFun := fun P => ⟨S i P.1, forward P⟩
          invFun := fun P => ⟨S i P.1, backward P⟩
          left_inv := fun P => Subtype.ext (hS i P.1)
          right_inv := fun P => Subtype.ext (hS i P.1) }
      exact ⟨step.trans e⟩
  let Zero := {P : PerfectMatching n // ∀ i, choice P i = false}
  let : Fintype Zero := Fintype.ofFinite _
  let empty_equiv : Fiber ∅ ≃ Zero :=
    { toFun := fun P => ⟨P.1, fun i => by
        have h := congrFun P.2 i
        simpa using h⟩
      invFun := fun P => ⟨P.1, funext (fun i => by simpa using P.2 i)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let : ∀ b : Fin k → Bool, Fintype {P : PerfectMatching n // choice P = b} :=
    fun _ => Fintype.ofFinite _
  have equal_fibers (b : Fin k → Bool) :
      Fintype.card {P : PerfectMatching n // choice P = b} = Fintype.card Zero := by
    let s := Finset.univ.filter (fun i => b i = true)
    have mask : (fun i => decide (i ∈ s)) = b := by
      funext i
      cases hb : b i <;> simp [s, hb]
    obtain ⟨e⟩ := normalize s
    have cast_fiber : {P : PerfectMatching n // choice P = b} ≃ Fiber s :=
      Equiv.subtypeEquivProp (by rw [mask])
    exact Fintype.card_congr ((cast_fiber.trans e).trans empty_equiv)
  have total := Fintype.card_congr (Equiv.sigmaFiberEquiv choice).symm
  rw [Fintype.card_sigma] at total
  simp_rw [equal_fibers] at total
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi_const, Fintype.card_bool,
    nsmul_eq_mul] at total
  change Fintype.card (PerfectMatching n) = 2 ^ k * Nat.card Zero
  rw [Nat.card_eq_fintype_card]
  exact total

end D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleOverlay
