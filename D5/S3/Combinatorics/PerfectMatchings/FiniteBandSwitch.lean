/- GID: D5/S3/Combinatorics/PerfectMatchings/FiniteBandSwitch
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/FiniteBandSwitch
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.Cycle.Factors]
   utility: none
   digest: Band surgery exchanges good and regular and yields equal finite means. -/
import D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing
import D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PerfectMatchings.FiniteBandSwitch
attribute [local instance] Classical.propDecidable
open D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing



set_option autoImplicit false

namespace FourEndpoint

open Equiv

/-- The original two matching edges. -/
def J0 : Perm (Fin 4) := swap 0 2 * swap 1 3

/-- The switched two matching edges. -/
def J1 : Perm (Fin 4) := swap 0 3 * swap 1 2

def Good (P J : Perm (Fin 4)) : Prop := (P * J).SameCycle 0 1

/-- The bad endpoint is J(0), which is 2 before switching and 3 afterward. -/
def Bad (P J : Perm (Fin 4)) : Prop := (P * J).SameCycle (J 0) 1

def Regular (P J : Perm (Fin 4)) : Prop := ¬ Good P J ∧ ¬ Bad P J

private def thirdPairing : Perm (Fin 4) := swap 0 1 * swap 2 3

/-- The three forms follow structurally from the pairing axioms. -/
private theorem pairing_three_forms (P : Perm (Fin 4))
    (hP : Function.Involutive P) (hfree : ∀ x, P x ≠ x) :
    P = J0 ∨ P = thirdPairing ∨ P = J1 := by
  generalize h0 : P (0 : Fin 4) = z
  fin_cases z
  · exact False.elim (hfree 0 h0)
  · have h1 : P 1 = 0 := by simpa [h0] using hP 0
    have h2 : P 2 = 3 := by
      have h2inv := hP (2 : Fin 4)
      have h2free := hfree (2 : Fin 4)
      generalize hv : P (2 : Fin 4) = v
      fin_cases v <;> simp_all
    have h3 : P 3 = 2 := by simpa only [h2] using hP 2
    right
    left
    ext i
    fin_cases i <;> simp [thirdPairing, Perm.mul_apply, swap_apply_def, h0, h1, h2, h3]
  · have h2 : P 2 = 0 := by simpa [h0] using hP 0
    have h1 : P 1 = 3 := by
      have h1inv := hP (1 : Fin 4)
      have h1free := hfree (1 : Fin 4)
      generalize hv : P (1 : Fin 4) = v
      fin_cases v <;> simp_all
    have h3 : P 3 = 1 := by simpa only [h1] using hP 1
    left
    ext i
    fin_cases i <;> simp [J0, Perm.mul_apply, swap_apply_def, h0, h1, h2, h3]
  · have h3 : P 3 = 0 := by simpa [h0] using hP 0
    have h1 : P 1 = 2 := by
      have h1inv := hP (1 : Fin 4)
      have h1free := hfree (1 : Fin 4)
      generalize hv : P (1 : Fin 4) = v
      fin_cases v <;> simp_all
    have h2 : P 2 = 1 := by simpa only [h1] using hP 1
    right
    right
    ext i
    fin_cases i <;> simp [J1, Perm.mul_apply, swap_apply_def, h0, h1, h2, h3]

/-- Every orbit of an involution consists of a point and its partner.
The proof is a natural-power induction, rather than finite orbit enumeration. -/
private theorem same_cycle_involutive_iff {Y : Type*} [Finite Y]
    (p : Perm Y) (hp : Function.Involutive p) (x y : Y) :
    p.SameCycle x y ↔ x = y ∨ p x = y := by
  constructor
  · intro hxy
    obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
    have hpower : ∀ k : Nat, (p ^ k) x = x ∨ (p ^ k) x = p x := by
      intro k
      induction k with
      | zero => exact Or.inl rfl
      | succ k ih =>
          simp only [pow_succ', Perm.mul_apply]
          rcases ih with h | h
          · exact Or.inr (congrArg p h)
          · exact Or.inl ((congrArg p h).trans (hp x))
    rcases hpower n with h | h
    · exact Or.inl (h.symm.trans hn)
    · exact Or.inr (h.symm.trans hn)
  · rintro (h | h)
    · subst y
      exact Perm.SameCycle.refl p x
    · exact ⟨1, by simpa only [zpow_one] using h⟩

/-- Four-point normalization for the endpoint-pairing
and permutation-orbit argument. -/
private theorem four_endpoint_classification :
    ∀ P : Perm (Fin 4),
      Function.Involutive P → (∀ x, P x ≠ x) →
      (Good P J1 ↔ Regular P J0) ∧
      (Bad P J1 ↔ Bad P J0) ∧
      (Regular P J1 ↔ Good P J0) := by
  intro P hP hfree
  have h0 : Function.Involutive J0 := by intro i; fin_cases i <;> rfl
  have h1 : Function.Involutive J1 := by intro i; fin_cases i <;> rfl
  have hK : Function.Involutive thirdPairing := by intro i; fin_cases i <;> rfl
  have h00 : J0 * J0 = 1 := by ext i; fin_cases i <;> rfl
  have h11 : J1 * J1 = 1 := by ext i; fin_cases i <;> rfl
  have h01 : J0 * J1 = thirdPairing := by ext i; fin_cases i <;> rfl
  have h10 : J1 * J0 = thirdPairing := by ext i; fin_cases i <;> rfl
  have hK0 : thirdPairing * J0 = J1 := by ext i; fin_cases i <;> rfl
  have hK1 : thirdPairing * J1 = J0 := by ext i; fin_cases i <;> rfl
  have cyc0 := same_cycle_involutive_iff J0 h0
  have cyc1 := same_cycle_involutive_iff J1 h1
  have cycK := same_cycle_involutive_iff thirdPairing hK
  rcases pairing_three_forms P hP hfree with rfl | rfl | rfl
  all_goals
    simp only [Good, Bad, Regular, h00, h11, h01, h10, hK0, hK1,
      cyc0, cyc1, cycK, Perm.sameCycle_one]
    simp [J0, J1, thirdPairing, Perm.mul_apply, swap_apply_def, Fin.ext_iff]

end FourEndpoint

set_option autoImplicit false
open Equiv
variable {X Y : Type*} [Finite X]

omit [Finite X] in
private theorem same_cycle_perm_congr (e : X ≃ Y) (p : Perm X) (x y : X) :
    (e.permCongr p).SameCycle (e x) (e y) ↔ p.SameCycle x y := by
  have hp (n : ℤ) : e.permCongr (p ^ n) = (e.permCongr p) ^ n :=
    map_zpow e.permCongrHom p n
  simp only [Perm.SameCycle, ← hp, Equiv.permCongr_apply,
    Equiv.symm_apply_apply, e.injective.eq_iff]

/-- Three categories expressed directly in the original flag carrier. -/
def GoodAt (s t : Perm X) (a b : X) : Prop := (s * t).SameCycle a b
def BadAt (s t : Perm X) (a b : X) : Prop := (s * t).SameCycle (s a) b
def RegularAt (s t : Perm X) (a b : X) : Prop := ¬GoodAt s t a b ∧ ¬BadAt s t a b

noncomputable def closeBoundary (r : Perm X) (J : Perm {z // r z = z}) : Perm X :=
  r * J.ofSubtype

omit [Finite X] in
private theorem bad_at_boundary_iff (s r : Perm X)
    (J : Perm {z // r z = z}) (hJ : Function.Involutive J)
    (a b : {z // r z = z}) :
    BadAt s (closeBoundary r J) a b ↔
      (s * closeBoundary r J).SameCycle (J a) b := by
  have hstep : (s * closeBoundary r J) (J a) = s a := by
    simp only [closeBoundary, Perm.mul_apply, Perm.ofSubtype_apply_coe, hJ a,
      a.property]
  rw [BadAt, ← hstep, Perm.sameCycle_apply_left]

/-- A labelled four-endpoint closure, with the internal path pairing derived
from the finite cut matching system. -/
private theorem cut_good_regular_exchange (s r : Perm X)
    (hs : Function.Involutive s) (hr : Function.Involutive r)
    (hsfree : ∀ x, s x ≠ x) (e : Fin 4 ≃ {z // r z = z}) :
    let J0 := e.permCongr FourEndpoint.J0
    let J1 := e.permCongr FourEndpoint.J1
    (GoodAt s (closeBoundary r J1) (e 0) (e 1) ↔
      RegularAt s (closeBoundary r J0) (e 0) (e 1)) ∧
    (BadAt s (closeBoundary r J1) (e 0) (e 1) ↔
      BadAt s (closeBoundary r J0) (e 0) (e 1)) ∧
    (RegularAt s (closeBoundary r J1) (e 0) (e 1) ↔
      GoodAt s (closeBoundary r J0) (e 0) (e 1)) := by
  classical
  let P : Perm {z // r z = z} := endpointPairing s r hs hr
  let Q : Perm (Fin 4) := e.symm.permCongr P
  have hQ : Function.Involutive Q := by
    intro i
    simpa only [Q, Equiv.permCongr_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply, Equiv.symm_apply_apply] using
      congrArg e.symm (endpoint_pairing_involutive s r hs hr (e i))
  have hQfree : ∀ i, Q i ≠ i := by
    intro i hi
    apply endpoint_pairing_fixed_point_free s r hs hr hsfree (e i)
    simpa only [Q, Equiv.permCongr_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply] using congrArg e hi
  have hrestore : e.permCongr Q = P := by
    exact e.permCongr.apply_symm_apply P
  have hcycles (J : Perm (Fin 4)) (i j : Fin 4) :
      (s * closeBoundary r (e.permCongr J)).SameCycle (e i) (e j) ↔
        (Q * J).SameCycle i j := by
    rw [closeBoundary, endpoint_pairing_reattach_same_cycle s r hs hr]
    change (P * e.permCongr J).SameCycle (e i) (e j) ↔ _
    rw [← hrestore, ← e.permCongr_mul]
    exact same_cycle_perm_congr e (Q * J) i j
  have good (J : Perm (Fin 4)) :
      GoodAt s (closeBoundary r (e.permCongr J)) (e 0) (e 1) ↔
        FourEndpoint.Good Q J := hcycles J 0 1
  have bad (J : Perm (Fin 4)) (hj : Function.Involutive J) :
      BadAt s (closeBoundary r (e.permCongr J)) (e 0) (e 1) ↔
        FourEndpoint.Bad Q J := by
    have heJ : Function.Involutive (e.permCongr J) := by
      intro x
      have hJJ (i : Fin 4) : J (J i) = i := hj i
      simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, hJJ,
        Equiv.apply_symm_apply]
    rw [bad_at_boundary_iff s r (e.permCongr J) heJ]
    simpa only [FourEndpoint.Bad, Equiv.permCongr_apply, Equiv.symm_apply_apply]
      using hcycles J (J 0) 1
  have h0 : Function.Involutive FourEndpoint.J0 := by intro i; fin_cases i <;> rfl
  have h1 : Function.Involutive FourEndpoint.J1 := by intro i; fin_cases i <;> rfl
  obtain ⟨hg, hb, hr⟩ := FourEndpoint.four_endpoint_classification Q hQ hQfree
  dsimp only
  simpa only [RegularAt, good, bad _ h0, bad _ h1, FourEndpoint.Regular] using
    And.intro hg (And.intro hb hr)





set_option autoImplicit false

namespace OriginalCut


open Equiv
open FourEndpoint

variable {X : Type*}

def boundaryLabel (t : Perm X) (a b : X) : Fin 4 → X := ![a, b, t a, t b]

def boundary (t : Perm X) (a b : X) : Set X := Set.range (boundaryLabel t a b)

private theorem boundary_label_mem (t : Perm X) (a b : X) (i : Fin 4) :
    boundaryLabel t a b i ∈ boundary t a b := ⟨i, rfl⟩

private theorem t_boundary_label (t : Perm X) (ht : Function.Involutive t)
    (a b : X) (i : Fin 4) :
    t (boundaryLabel t a b i) = boundaryLabel t a b (J0 i) := by
  fin_cases i <;> simp [boundaryLabel, J0, Perm.mul_apply, swap_apply_def, ht a, ht b]

private theorem boundary_t_mem (t : Perm X) (ht : Function.Involutive t)
    (a b : X) {x : X} (hx : x ∈ boundary t a b) :
    t x ∈ boundary t a b := by
  rcases hx with ⟨i, rfl⟩
  exact ⟨J0 i, (t_boundary_label t ht a b i).symm⟩

private theorem boundary_t_iff (t : Perm X) (ht : Function.Involutive t)
    (a b x : X) : t x ∈ boundary t a b ↔ x ∈ boundary t a b := by
  constructor
  · intro hx
    simpa only [ht x] using boundary_t_mem t ht a b hx
  · exact boundary_t_mem t ht a b

/-- Delete precisely the two selected t-pairs by fixing their four endpoints. -/
noncomputable def cutFun (t : Perm X) (a b x : X) : X :=
  if x ∈ boundary t a b then x else t x

private theorem cut_fun_involutive (t : Perm X) (ht : Function.Involutive t)
    (a b : X) : Function.Involutive (cutFun t a b) := by
  intro x
  by_cases hx : x ∈ boundary t a b
  · simp only [cutFun, if_pos hx]
  · have htx : t x ∉ boundary t a b :=
      fun h => hx ((boundary_t_iff t ht a b x).mp h)
    simp only [cutFun, if_neg hx, if_neg htx, ht x]

noncomputable def cutPerm (t : Perm X) (ht : Function.Involutive t)
    (a b : X) : Perm X where
  toFun := cutFun t a b
  invFun := cutFun t a b
  left_inv := cut_fun_involutive t ht a b
  right_inv := cut_fun_involutive t ht a b

private theorem cut_perm_involutive (t : Perm X) (ht : Function.Involutive t)
    (a b : X) : Function.Involutive (cutPerm t ht a b) :=
  cut_fun_involutive t ht a b

private theorem cut_perm_apply_of_mem (t : Perm X) (ht : Function.Involutive t)
    (a b : X) {x : X} (hx : x ∈ boundary t a b) :
    cutPerm t ht a b x = x := by
  change cutFun t a b x = x
  simp only [cutFun, if_pos hx]

private theorem cut_perm_apply_of_not_mem (t : Perm X) (ht : Function.Involutive t)
    (a b : X) {x : X} (hx : x ∉ boundary t a b) :
    cutPerm t ht a b x = t x := by
  change cutFun t a b x = t x
  simp only [cutFun, if_neg hx]

private theorem cut_perm_fixed_iff (t : Perm X) (ht : Function.Involutive t)
    (htfree : ∀ x, t x ≠ x) (a b x : X) :
    cutPerm t ht a b x = x ↔ x ∈ boundary t a b := by
  by_cases hx : x ∈ boundary t a b
  · simp only [cut_perm_apply_of_mem t ht a b hx, hx]
  · rw [cut_perm_apply_of_not_mem t ht a b hx]
    simp only [htfree x, hx]

noncomputable def cutLabel (t : Perm X) (ht : Function.Involutive t)
    (a b : X) (i : Fin 4) : {x // cutPerm t ht a b x = x} :=
  ⟨boundaryLabel t a b i,
    cut_perm_apply_of_mem t ht a b (boundary_label_mem t a b i)⟩

private theorem cut_label_bijective (t : Perm X) (ht : Function.Involutive t)
    (htfree : ∀ x, t x ≠ x) (a b : X)
    (hinj : Function.Injective (boundaryLabel t a b)) :
    Function.Bijective (cutLabel t ht a b) := by
  constructor
  · intro i j hij
    exact hinj (congrArg Subtype.val hij)
  · intro x
    obtain ⟨i, hi⟩ := (cut_perm_fixed_iff t ht htfree a b x).mp x.property
    exact ⟨i, Subtype.ext hi⟩

noncomputable def cutEquiv (t : Perm X) (ht : Function.Involutive t)
    (htfree : ∀ x, t x ≠ x) (a b : X)
    (hinj : Function.Injective (boundaryLabel t a b)) :
    Fin 4 ≃ {x // cutPerm t ht a b x = x} :=
  Equiv.ofBijective (cutLabel t ht a b) (cut_label_bijective t ht htfree a b hinj)

/-- A generic extensional closure lemma; both hypotheses are verified below
for the original and switched matching, rather than supplied by the caller. -/
private theorem closure_eq_of_actions (r f : Perm X) (e : Fin 4 ≃ {x // r x = x})
    (J : Perm (Fin 4))
    (hboundary : ∀ i, f (e i) = (e (J i) : X))
    (houtside : ∀ x, r x ≠ x → f x = r x) :
    f = r * (e.permCongr J).ofSubtype := by
  ext x
  by_cases hx : r x = x
  · obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
    have hix : (e i : X) = x := congrArg Subtype.val hi
    rw [← hix, Perm.mul_apply, Perm.ofSubtype_apply_coe,
      Equiv.permCongr_apply, e.symm_apply_apply]
    exact (hboundary i).trans (e (J i)).property.symm
  · rw [Perm.mul_apply,
      Perm.ofSubtype_apply_of_not_mem (p := fun z => r z = z) (e.permCongr J) hx]
    exact houtside x hx

noncomputable def switchSwap (t : Perm X) (a b : X) : Perm X := swap (t a) (t b)

def indexSwitch : Perm (Fin 4) := swap 2 3

private theorem switch_swap_boundary_label (t : Perm X) (a b : X)
    (hinj : Function.Injective (boundaryLabel t a b)) (i : Fin 4) :
    switchSwap t a b (boundaryLabel t a b i) =
      boundaryLabel t a b (indexSwitch i) := by
  simpa [switchSwap, indexSwitch, boundaryLabel] using
    hinj.swap_apply (2 : Fin 4) (3 : Fin 4) i

private theorem index_switch_j0_index_switch (i : Fin 4) :
    indexSwitch (J0 (indexSwitch i)) = J1 i := by
  fin_cases i <;> simp [indexSwitch, J0, J1, Perm.mul_apply, swap_apply_def]

private theorem switched_boundary_label (t : Perm X) (ht : Function.Involutive t)
    (a b : X) (hinj : Function.Injective (boundaryLabel t a b)) (i : Fin 4) :
    (switchSwap t a b * t * switchSwap t a b) (boundaryLabel t a b i) =
      boundaryLabel t a b (J1 i) := by
  simp only [Perm.mul_apply, switch_swap_boundary_label t a b hinj,
    t_boundary_label t ht a b, index_switch_j0_index_switch]

private theorem switch_swap_apply_of_not_mem (t : Perm X) (a b : X)
    {x : X} (hx : x ∉ boundary t a b) : switchSwap t a b x = x := by
  apply swap_apply_of_ne_of_ne
  · intro h
    exact hx ⟨2, by simpa [boundaryLabel] using h.symm⟩
  · intro h
    exact hx ⟨3, by simpa [boundaryLabel] using h.symm⟩

private theorem original_cut_factorizations (t : Perm X) (ht : Function.Involutive t)
    (htfree : ∀ x, t x ≠ x) (a b : X)
    (hinj : Function.Injective (boundaryLabel t a b)) :
    let r := cutPerm t ht a b
    let e := cutEquiv t ht htfree a b hinj
    t = r * (e.permCongr J0).ofSubtype ∧
      switchSwap t a b * t * switchSwap t a b = r * (e.permCongr J1).ofSubtype := by
  let r := cutPerm t ht a b
  let e := cutEquiv t ht htfree a b hinj
  change t = r * (e.permCongr J0).ofSubtype ∧
    switchSwap t a b * t * switchSwap t a b = r * (e.permCongr J1).ofSubtype
  constructor
  · apply closure_eq_of_actions r t e J0
    · intro i
      exact t_boundary_label t ht a b i
    · intro x hx
      have hnot : x ∉ boundary t a b :=
        fun h => hx (cut_perm_apply_of_mem t ht a b h)
      exact (cut_perm_apply_of_not_mem t ht a b hnot).symm
  · apply closure_eq_of_actions r (switchSwap t a b * t * switchSwap t a b) e J1
    · intro i
      exact switched_boundary_label t ht a b hinj i
    · intro x hx
      have hnot : x ∉ boundary t a b :=
        fun h => hx (cut_perm_apply_of_mem t ht a b h)
      have htnot : t x ∉ boundary t a b :=
        fun h => hnot ((boundary_t_iff t ht a b x).mp h)
      rw [Perm.mul_apply, Perm.mul_apply,
        switch_swap_apply_of_not_mem t a b hnot,
        switch_swap_apply_of_not_mem t a b htnot]
      exact (cut_perm_apply_of_not_mem t ht a b hnot).symm

/-- The full source-model bridge supplies an actual cut involution, its
four-point coordinate equivalence, and both verified closure identities. -/
private theorem original_cut_adapter (t : Perm X) (ht : Function.Involutive t)
    (htfree : ∀ x, t x ≠ x) (a b : X)
    (hinj : Function.Injective (boundaryLabel t a b)) :
    ∃ r : Perm X, ∃ e : Fin 4 ≃ {x // r x = x},
      Function.Involutive r ∧
      (∀ i, (e i : X) = boundaryLabel t a b i) ∧
      t = r * (e.permCongr J0).ofSubtype ∧
      switchSwap t a b * t * switchSwap t a b = r * (e.permCongr J1).ofSubtype := by
  refine ⟨cutPerm t ht a b, cutEquiv t ht htfree a b hinj,
    cut_perm_involutive t ht a b, ?_, ?_⟩
  · intro i
    rfl
  · exact original_cut_factorizations t ht htfree a b hinj

end OriginalCut

set_option autoImplicit false
open Equiv
variable {X : Type*} [Finite X]

/-- Regularity means genuinely different combinatorial boundary components. -/
def PhysicalRegularAt (s t : Perm X) (a b : X) : Prop :=
  ¬ D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.Connected s t a b

omit [Finite X] in
private theorem regular_at_iff_physical (s t : Perm X)
    (hs : Function.Involutive s) (ht : Function.Involutive t) (a b : X) :
    RegularAt s t a b ↔ PhysicalRegularAt s t a b := by
  rw [RegularAt, GoodAt, BadAt, PhysicalRegularAt,
    D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.connected_iff_rotation_orbits
      s t hs ht, not_or]



set_option autoImplicit false
open Equiv
open scoped BigOperators
variable {X : Type*} [Finite X]

/-- Switching the two specified band pairs exchanges good and regular
categories and preserves bad singularity, for every finite flag carrier. -/
theorem band_switch (s t : Perm X)
    (hs : Function.Involutive s) (ht : Function.Involutive t)
    (hsfree : ∀ x, s x ≠ x) (htfree : ∀ x, t x ≠ x)
    (a b : X) (hinj : Function.Injective (OriginalCut.boundaryLabel t a b)) :
    let u := OriginalCut.switchSwap t a b
    (GoodAt s (u * t * u) a b ↔ RegularAt s t a b) ∧
    (BadAt s (u * t * u) a b ↔ BadAt s t a b) ∧
    (RegularAt s (u * t * u) a b ↔ GoodAt s t a b) := by
  obtain ⟨r, e, hr, he, h0, h1⟩ :=
    OriginalCut.original_cut_adapter t ht htfree a b hinj
  have ha : (e 0 : X) = a := by
    simpa [OriginalCut.boundaryLabel] using he 0
  have hb : (e 1 : X) = b := by
    simpa [OriginalCut.boundaryLabel] using he 1
  have h := cut_good_regular_exchange s r hs hr hsfree e
  simpa only [closeBoundary, ← h0, ← h1, ha, hb] using h

/-- The state map changes the actual band matching. Classifier transport is
proved by band_switch; it is not a premise of the expectation theorem. -/
theorem twist_invariant_uniform_expectation {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (s : Perm X) (t : Ω → Perm X) (τ : Ω ≃ Ω)
    (hs : Function.Involutive s) (hsfree : ∀ x, s x ≠ x)
    (ht : ∀ ω, Function.Involutive (t ω)) (htfree : ∀ ω x, t ω x ≠ x)
    (a b : X) (hinj : ∀ ω, Function.Injective (OriginalCut.boundaryLabel (t ω) a b))
    (htwist : ∀ ω, t (τ ω) =
      OriginalCut.switchSwap (t ω) a b * t ω * OriginalCut.switchSwap (t ω) a b) :
    (∑ ω, if GoodAt s (t ω) a b then (1 : ℚ) else 0) / Fintype.card Ω =
      (∑ ω, if PhysicalRegularAt s (t ω) a b then (1 : ℚ) else 0) / Fintype.card Ω := by
  congr 1
  symm
  apply Fintype.sum_equiv τ
  intro ω
  have h := (band_switch s (t ω) hs (ht ω) hsfree (htfree ω) a b (hinj ω)).1
  rw [htwist ω]
  rw [h, regular_at_iff_physical s (t ω) hs (ht ω) a b]


#print axioms band_switch
#print axioms twist_invariant_uniform_expectation
end D5.S3.Combinatorics.PerfectMatchings.FiniteBandSwitch
