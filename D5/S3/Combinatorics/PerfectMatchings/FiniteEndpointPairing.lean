/- GID: D5/S3/Combinatorics/PerfectMatchings/FiniteEndpointPairing
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/FiniteEndpointPairing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.Cycle.Factors]
   utility: none
   digest: Finite path pairings determine reattached endpoint orbits. -/
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing
attribute [local instance] Classical.propDecidable

set_option autoImplicit false

open Equiv
variable {X : Type*} [Finite X]

/-- A first positive visit to a marked subset under a permutation. -/
def FirstVisit (q : Perm X) (S : Set X) (x : X) (n : ℕ) : Prop :=
  0 < n ∧ (q ^ n) x ∈ S ∧ ∀ k, 0 < k → k < n → (q ^ k) x ∉ S

private theorem return_exists (q : Perm X) (S : Set X) (x : X) (hx : x ∈ S) :
    ∃ n : ℕ, 0 < n ∧ (q ^ n) x ∈ S := by
  refine ⟨orderOf q, orderOf_pos q, ?_⟩
  simpa only [pow_orderOf_eq_one, Perm.one_apply] using hx

private noncomputable def visitTime (q : Perm X) (S : Set X) (x : X) (hx : x ∈ S) : ℕ :=
  Nat.find (return_exists q S x hx)

private theorem first_visit_visit_time (q : Perm X) (S : Set X) (x : X) (hx : x ∈ S) :
    FirstVisit q S x (visitTime q S x hx) := by
  classical
  unfold visitTime
  obtain ⟨hp, hs⟩ := Nat.find_spec (return_exists q S x hx)
  refine ⟨hp, hs, ?_⟩
  intro k hk hkn hmem
  exact Nat.find_min (return_exists q S x hx) hkn ⟨hk, hmem⟩

omit [Finite X] in
private theorem FirstVisit.unique {q : Perm X} {S : Set X} {x : X} {m n : ℕ}
    (hm : FirstVisit q S x m) (hn : FirstVisit q S x n) : m = n := by
  rcases hm with ⟨hmp, hms, hmi⟩
  rcases hn with ⟨hnp, hns, hni⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hni m hmp h hms
  · exact hmi n hnp h hns

/-- The actual next marked point, not a supplied boundary pairing. -/
private noncomputable def nextVisit (q : Perm X) (S : Set X) (x : S) : S :=
  ⟨(q ^ visitTime q S x x.property) x,
    (first_visit_visit_time q S x x.property).2.1⟩






set_option autoImplicit false


open Equiv

variable {X : Type*} [Finite X]

omit [Finite X] in
private theorem square_of_involutive (p : Perm X)
    (hp : Function.Involutive p) : p * p = 1 := by
  ext x
  exact hp x

omit [Finite X] in
/-- The alternating walk is reversed by the cut matching. -/
private theorem cut_palindrome (s r : Perm X)
    (hs : Function.Involutive s) (hr : Function.Involutive r) (k : Nat) :
    (s * r) ^ k * r * (s * r) ^ k = r := by
  let q : Perm X := s * r
  have hbase : q * r * q = r := by
    change (s * r) * r * (s * r) = r
    calc
      (s * r) * r * (s * r) = (s * (r * r) * s) * r := by group
      _ = r := by
        rw [square_of_involutive r hr, mul_one, square_of_involutive s hs,
          one_mul]
  change q ^ k * r * q ^ k = r
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        q ^ (k + 1) * r * q ^ (k + 1) =
            (q ^ k * q) * r * (q * q ^ k) :=
          congrArg₂ (fun u v : Perm X => u * r * v)
            (pow_succ q k) (pow_succ' q k)
        _ = q ^ k * (q * r * q) * q ^ k := by simp only [mul_assoc]
        _ = q ^ k * r * q ^ k := by rw [hbase]
        _ = r := ih

omit [Finite X] in
/-- If a positive alternating segment starts and ends at exposed endpoints,
the same number of rotation steps returns to its start. -/
private theorem cut_segment_returns (s r : Perm X)
    (hs : Function.Involutive s) (hr : Function.Involutive r)
    (x : X) (hx : r x = x) (n : Nat)
    (hy : r (((s * r) ^ n) x) = ((s * r) ^ n) x) :
    ((s * r) ^ n) (((s * r) ^ n) x) = x := by
  have h := congrArg (fun p : Perm X => p x) (cut_palindrome s r hs hr n)
  simpa only [Perm.mul_apply, hy, hx] using h

omit [Finite X] in
/-- Reversal preserves not only the endpoints but also the first-visit time.
This is a minimality argument, not an assumption about path components. -/
private theorem FirstVisit.reverse_cut {s r : Perm X}
    (hs : Function.Involutive s) (hr : Function.Involutive r)
    {x : X} (hx : r x = x) {n : Nat}
    (hn : FirstVisit (s * r) {z | r z = z} x n) :
    FirstVisit (s * r) {z | r z = z} (((s * r) ^ n) x) n := by
  let q : Perm X := s * r
  change FirstVisit q {z | r z = z} x n at hn
  change FirstVisit q {z | r z = z} ((q ^ n) x) n
  have hy : r ((q ^ n) x) = (q ^ n) x := hn.2.1
  have hreturn : (q ^ n) ((q ^ n) x) = x :=
    cut_segment_returns s r hs hr x hx n hy
  refine ⟨hn.1, ?_, ?_⟩
  · change r ((q ^ n) ((q ^ n) x)) = (q ^ n) ((q ^ n) x)
    simpa only [hreturn] using hx
  · intro k hk hkn hmem
    have hz : r ((q ^ k) ((q ^ n) x)) = (q ^ k) ((q ^ n) x) := hmem
    have hback : (q ^ k) ((q ^ k) ((q ^ n) x)) = (q ^ n) x :=
      cut_segment_returns s r hs hr ((q ^ n) x) hy k hz
    have hsum : k + (n - k) = n := by omega
    have hforward : (q ^ k) ((q ^ (n - k)) x) = (q ^ n) x := by
      rw [← Perm.mul_apply, ← pow_add, hsum]
    have heq : (q ^ (n - k)) x = (q ^ k) ((q ^ n) x) :=
      (q ^ k).injective (hforward.trans hback.symm)
    apply hn.2.2 (n - k) (by omega) (by omega)
    change r ((q ^ (n - k)) x) = (q ^ (n - k)) x
    simpa only [heq] using hz

private theorem next_visit_eq_of_first_visit {q : Perm X} {S : Set X}
    (x : S) {n : Nat} (hn : FirstVisit q S x n) :
    (nextVisit q S x : X) = (q ^ n) x := by
  change (q ^ visitTime q S x x.property) x = (q ^ n) x
  rw [(first_visit_visit_time q S x x.property).unique hn]

/-- The endpoint successor obtained from actual finite recurrence is an
involution. The first-return permutation has not been postulated. -/
private theorem next_visit_involutive_cut (s r : Perm X)
    (hs : Function.Involutive s) (hr : Function.Involutive r) :
    Function.Involutive (nextVisit (s * r) {z | r z = z}) := by
  intro x
  let q : Perm X := s * r
  let E : Set X := {z | r z = z}
  let n : Nat := visitTime q E x x.property
  let y : E := nextVisit q E x
  have hn : FirstVisit q E x n := first_visit_visit_time q E x x.property
  have hxy : (y : X) = (q ^ n) x := rfl
  have hrev : FirstVisit q E y n := by
    rw [hxy]
    exact hn.reverse_cut hs hr x.property
  have hyx : (nextVisit q E y : X) = (q ^ n) y :=
    next_visit_eq_of_first_visit y hrev
  apply Subtype.ext
  change (nextVisit q E y : X) = (x : X)
  rw [hyx, hxy]
  exact cut_segment_returns s r hs hr x x.property n hn.2.1

/-- A first return cannot return to its own exposed endpoint. An even return
would expose an earlier midpoint; an odd return would fix an s-vertex. -/
private theorem next_visit_ne_self_cut (s r : Perm X)
    (hs : Function.Involutive s) (hr : Function.Involutive r)
    (hsfree : ∀ z, s z ≠ z) (x : {z // r z = z}) :
    nextVisit (s * r) {z | r z = z} x ≠ x := by
  intro hfixed
  let q : Perm X := s * r
  let E : Set X := {z | r z = z}
  let n : Nat := visitTime q E x x.property
  have hn : FirstVisit q E x n := first_visit_visit_time q E x x.property
  have hnpos : 0 < n := hn.1
  have hperiod : (q ^ n) x = (x : X) := congrArg Subtype.val hfixed
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · have hsum : k + k = n := by omega
    have hp : (q ^ k) (r ((q ^ k) x)) = (x : X) := by
      have h := congrArg (fun p : Perm X => p (x : X))
        (cut_palindrome s r hs hr k)
      simpa only [Perm.mul_apply, x.property] using h
    have hmid : (q ^ k) ((q ^ k) x) = (x : X) := by
      rw [← Perm.mul_apply, ← pow_add, hsum]
      exact hperiod
    have hendpoint : r ((q ^ k) x) = (q ^ k) x :=
      (q ^ k).injective (hp.trans hmid.symm)
    exact hn.2.2 k (by omega) (by omega) hendpoint
  · have hsum : k + (k + 1) = n := by omega
    have hsq : s * q = r := by
      change s * (s * r) = r
      rw [← mul_assoc, square_of_involutive s hs, one_mul]
    have hodd : q ^ k * s * q ^ (k + 1) = r := by
      calc
        q ^ k * s * q ^ (k + 1) = q ^ k * s * (q * q ^ k) :=
          congrArg (fun p : Perm X => q ^ k * s * p) (pow_succ' q k)
        _ = q ^ k * (s * q) * q ^ k := by simp only [mul_assoc]
        _ = q ^ k * r * q ^ k := by rw [hsq]
        _ = r := cut_palindrome s r hs hr k
    have hp : (q ^ k) (s ((q ^ (k + 1)) x)) = (x : X) := by
      have h := congrArg (fun p : Perm X => p (x : X)) hodd
      simpa only [Perm.mul_apply, x.property] using h
    have hmid : (q ^ k) ((q ^ (k + 1)) x) = (x : X) := by
      rw [← Perm.mul_apply, ← pow_add, hsum]
      exact hperiod
    exact hsfree ((q ^ (k + 1)) x) ((q ^ k).injective (hp.trans hmid.symm))

/-- The genuine endpoint pairing of the cut alternating matching system. -/
noncomputable def endpointPairing (s r : Perm X)
    (hs : Function.Involutive s) (hr : Function.Involutive r) :
    Perm {z // r z = z} where
  toFun := nextVisit (s * r) {z | r z = z}
  invFun := nextVisit (s * r) {z | r z = z}
  left_inv := next_visit_involutive_cut s r hs hr
  right_inv := next_visit_involutive_cut s r hs hr

theorem endpoint_pairing_involutive (s r : Perm X)
    (hs : Function.Involutive s) (hr : Function.Involutive r) :
    Function.Involutive (endpointPairing s r hs hr) :=
  next_visit_involutive_cut s r hs hr

theorem endpoint_pairing_fixed_point_free (s r : Perm X)
    (hs : Function.Involutive s) (hr : Function.Involutive r)
    (hsfree : ∀ z, s z ≠ z) :
    ∀ x, endpointPairing s r hs hr x ≠ x :=
  next_visit_ne_self_cut s r hs hr hsfree




set_option autoImplicit false
open Equiv
variable {X : Type*} [Finite X]

omit [Finite X] in
/-- Reattaching marked endpoints leaves every interior step unchanged. -/
private theorem first_visit_reattach (q : Perm X) (S : Set X)
    [DecidablePred (· ∈ S)] (J : Perm S) (x : S) (n : ℕ)
    (hn : FirstVisit q S (J x) n) :
    FirstVisit (q * J.ofSubtype) S x n ∧
      ((q * J.ofSubtype) ^ n) x = (q ^ n) (J x) := by
  have hsegment : ∀ k, 0 < k → k ≤ n →
      ((q * J.ofSubtype) ^ k) x = (q ^ k) (J x) := by
    intro k
    induction k with
    | zero => intro hk; omega
    | succ k ih =>
      intro hk hkn
      by_cases hk0 : k = 0
      · subst k
        simp only [zero_add, pow_one, Perm.mul_apply, Perm.ofSubtype_apply_coe]
      · have hkp : 0 < k := Nat.pos_of_ne_zero hk0
        rw [pow_succ', Perm.mul_apply, Perm.mul_apply,
          ih hkp (by omega), Perm.ofSubtype_apply_of_not_mem J (hn.2.2 k hkp (by omega))]
        rw [← Perm.mul_apply, ← pow_succ']
  refine ⟨⟨hn.1, ?_, ?_⟩, hsegment n hn.1 le_rfl⟩
  · rw [hsegment n hn.1 le_rfl]
    exact hn.2.1
  · intro k hk hkn
    rw [hsegment k hk (by omega)]
    exact hn.2.2 k hk hkn

/-- A permutation's cycles restricted to a marked subset are exactly the
cycles of a proved first-return permutation. -/
private theorem same_cycle_of_first_visit (f : Perm X) (S : Set X) (H : Perm S)
    (jump : ∀ x : S, ∃ n : ℕ, FirstVisit f S x n ∧ (f ^ n) x = H x)
    (x y : S) : f.SameCycle x y ↔ H.SameCycle x y := by
  classical
  let := Fintype.ofFinite X
  constructor
  · intro hxy
    obtain ⟨n, _, _, hn⟩ := Perm.SameCycle.exists_pow_eq f hxy
    have hreach : ∀ k : ℕ, ∀ z w : S, (f ^ k) z = w → H.SameCycle z w := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
        intro z w hkw
        by_cases hk : k = 0
        · subst k
          have hzw : z = w := Subtype.ext (by simpa using hkw)
          subst w
          exact Perm.SameCycle.refl _ _
        obtain ⟨m, hm, hstep⟩ := jump z
        have hmk : m ≤ k := by
          by_contra hh
          have hlt : k < m := by omega
          exact hm.2.2 k (by omega) hlt (by rw [hkw]; exact w.property)
        have htail : (f ^ (k - m)) (H z : X) = w := by
          rw [← hstep, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hmk]
          exact hkw
        have hmp : 0 < m := hm.1
        have hind := ih (k - m) (by omega) (H z) w htail
        exact (Perm.SameCycle.refl H z).apply_right.trans hind
    exact hreach n x y hn
  · intro hxy
    obtain ⟨n, _, _, hn⟩ := Perm.SameCycle.exists_pow_eq H hxy
    have hreach : ∀ k : ℕ, ∀ z : S, f.SameCycle z ((H ^ k) z : S) := by
      intro k
      induction k with
      | zero => intro z; simpa using Perm.SameCycle.refl f (z : X)
      | succ k ih =>
        intro z
        rw [pow_succ', Perm.mul_apply]
        obtain ⟨m, _, hm⟩ := jump ((H ^ k) z)
        apply (ih z).trans
        refine ⟨(m : ℤ), ?_⟩
        simpa only [zpow_natCast] using hm
    simpa only [hn] using hreach n x



set_option autoImplicit false
open Equiv
variable {X : Type*} [Finite X]

/-- Closing the exposed endpoints changes the induced return permutation
from the constructed path pairing P to P*J. -/
theorem endpoint_pairing_reattach_same_cycle (s r : Perm X)
    (hs : Function.Involutive s) (hr : Function.Involutive r)
    (J : Perm {z // r z = z})
    (x y : {z // r z = z}) :
    (s * (r * J.ofSubtype)).SameCycle x y ↔
      (endpointPairing s r hs hr * J).SameCycle x y := by
  classical
  let E : Set X := {z | r z = z}
  let q : Perm X := s * r
  let P := endpointPairing s r hs hr
  have hjump : ∀ z : E, ∃ n : Nat,
      FirstVisit (q * J.ofSubtype) E z n ∧
        ((q * J.ofSubtype) ^ n) z = (P * J) z := by
    intro z
    let n := visitTime q E (J z) (J z).property
    have hn : FirstVisit q E (J z) n :=
      first_visit_visit_time q E (J z) (J z).property
    obtain ⟨hfirst, hend⟩ := first_visit_reattach q E J z n hn
    refine ⟨n, hfirst, ?_⟩
    exact hend
  simpa only [q, P, mul_assoc] using
    (same_cycle_of_first_visit (q * J.ofSubtype) E (P * J) hjump x y)



#print axioms endpoint_pairing_fixed_point_free
#print axioms endpoint_pairing_reattach_same_cycle
end D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing
