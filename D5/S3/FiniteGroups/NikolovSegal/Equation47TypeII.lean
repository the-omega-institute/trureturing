/- GID: D5/S3/FiniteGroups/NikolovSegal/Equation47TypeII
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Equation47TypeII
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-group coordinate, extraction or product mathematics. -/

import D5.S3.FiniteGroups.NikolovSegal.Equation47Forest
import Mathlib.GroupTheory.Perm.Cycle.Basic

set_option autoImplicit false

/-!
Nikolov--Segal Part I, Proposition 9.1, printed pp. 223--226.
The cycle constraints below are the actual constraints (H_{i,Delta}).
The group action convention here is the forward coordinate law used by
`Equation47Forest`: a value at sigma(i) is c(sigma(i))^-1 * alpha(i)(c(i)).
Consequently the ordered cycle accumulator transports the preceding word
before adding the next value.  It must not be replaced by an unordered product.

The Part II twisted PRODUCT theorem and the quantitative balanced-word
extraction are not asserted by this file.
-/
namespace NikolovSegal.Equation47TypeII
universe u
variable {S : Type u} [Group S] {I : Type u}

/-- The constrained value word on a genuine directed permutation cycle. -/
def valueBoundary (sigma : Equiv.Perm I) (alpha : I → MulAut S)
    (a : I) (x : I → S) : ℕ → S
  | 0 => 1
  | n+1 => x (sigma^[n+1] a) * alpha (sigma^[n] a)
      (valueBoundary sigma alpha a x n)

/-- Solve (40) in its actual forward coordinate order. -/
private def recover (sigma : Equiv.Perm I) (alpha : I → MulAut S)
    (a : I) (x : I → S) (u : S) : ℕ → S
  | 0 => u
  | n+1 => alpha (sigma^[n] a) (recover sigma alpha a x u n) *
      (x (sigma^[n+1] a))⁻¹

private theorem recover_boundary (sigma : Equiv.Perm I) (alpha : I → MulAut S)
    (a : I) (x : I → S) (u : S) (n : ℕ) :
    (recover sigma alpha a x u n)⁻¹ *
        cycleComponent (fun (_ : Fin 1) => alpha) (fun _ => sigma) 0 a n u =
      valueBoundary sigma alpha a x n := by
  induction n with
  | zero => simp [recover, valueBoundary, cycleComponent]
  | succ n ih =>
    simp [recover, valueBoundary, cycleComponent, map_mul, map_inv,
      MulAut.mul_apply, mul_assoc, ← ih]

private theorem boundary_of_values (sigma : Equiv.Perm I) (alpha : I → MulAut S)
    (a : I) (c x : I → S)
    (hx : ∀ n, x (sigma^[n+1] a) =
      (c (sigma^[n+1] a))⁻¹ * alpha (sigma^[n] a) (c (sigma^[n] a)))
    (n : ℕ) :
    valueBoundary sigma alpha a x n = (c (sigma^[n] a))⁻¹ *
      cycleComponent (fun (_ : Fin 1) => alpha) (fun _ => sigma) 0 a n (c a) := by
  induction n with
  | zero => simp [valueBoundary, cycleComponent]
  | succ n ih =>
    rw [valueBoundary,hx n,ih]
    simp [cycleComponent, map_mul, map_inv,
      MulAut.mul_apply, mul_assoc]

/-- The precise local necessity AND sufficiency of (H_{i,Delta}).  The
remaining cycle values are free, but their ordered boundary must be one
actual scalar commutator value.  This is not whole-block coverage. -/
theorem cycle_value_with_witness_iff (sigma : Equiv.Perm I) (alpha : I → MulAut S)
    (a : I) (x : I → S)
    (hp : a ∈ Function.periodicPts sigma) (u : S) :
    (∃ c : I → S, c a = u ∧ ∀ n : ℕ,
      x (sigma^[n+1] a) = (c (sigma^[n+1] a))⁻¹ *
        alpha (sigma^[n] a) (c (sigma^[n] a))) ↔
    valueBoundary sigma alpha a x (Function.minimalPeriod sigma a) =
      u⁻¹ * cycleComponent (fun (_ : Fin 1) => alpha) (fun _ => sigma) 0 a
        (Function.minimalPeriod sigma a) u := by
  classical
  let e := Function.minimalPeriod sigma a
  have he : 0 < e := Function.minimalPeriod_pos_of_mem_periodicPts hp
  have hreturn : sigma^[e] a = a := Function.iterate_minimalPeriod (f := sigma) (x := a)
  constructor
  · rintro ⟨c,hca,hc⟩
    simpa only [hreturn,hca] using boundary_of_values sigma alpha a c x hc e
  · intro hu
    let f : Fin e → I := fun n => sigma^[n.val] a
    have hf : Function.Injective f := by
      intro n k h
      exact Fin.ext ((Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
        n.isLt k.isLt).mp h)
    let c : I → S := Function.extend f (fun n => recover sigma alpha a x u n.val) (fun _ => 1)
    have hc : ∀ n : Fin e, c (sigma^[n.val] a) = recover sigma alpha a x u n.val :=
      fun n => hf.extend_apply _ _ n
    have hend : recover sigma alpha a x u e = u := by
      have hb := recover_boundary sigma alpha a x u e
      rw [hu] at hb
      exact inv_injective (mul_right_cancel hb)
    have hcmod : ∀ n : ℕ, c (sigma^[n] a) = recover sigma alpha a x u (n % e) := by
      intro n
      rw [← Function.iterate_mod_minimalPeriod_eq (f := sigma) (x := a) (n := n)]
      exact hc ⟨n % e, Nat.mod_lt n he⟩
    refine ⟨c, ?_, ?_⟩
    · simpa [recover] using hc ⟨0,he⟩
    intro n
    let k := n % e
    have hk : k < e := Nat.mod_lt n he
    have hn : sigma^[n] a = sigma^[k] a :=
      (Function.iterate_mod_minimalPeriod_eq (f := sigma) (x := a) (n := n)).symm
    have hnext : sigma^[n+1] a = sigma^[k+1] a := by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hn]
    rw [hn, hnext]
    have hck : c (sigma^[k] a) = recover sigma alpha a x u k := hc ⟨k,hk⟩
    have hcknext : c (sigma^[k+1] a) = recover sigma alpha a x u (k+1) := by
      by_cases hlt : k+1 < e
      · exact hc ⟨k+1,hlt⟩
      · have hke : k+1 = e := by omega
        rw [hke,hreturn,hend]
        simpa [recover] using hc ⟨0,he⟩
    rw [hck,hcknext,recover]
    simp [mul_assoc]

/-- Existential form of the same genuine cycle constraint.  The stronger
theorem above retains the prescribed scalar parameter u as the root witness,
which is needed when the paper treats the u(i,Delta) as independent parameters. -/
theorem cycle_value_iff (sigma : Equiv.Perm I) (alpha : I → MulAut S)
    (a : I) (x : I → S) (hp : a ∈ Function.periodicPts sigma) :
    (∃ c : I → S, ∀ n : ℕ,
      x (sigma^[n+1] a) = (c (sigma^[n+1] a))⁻¹ *
        alpha (sigma^[n] a) (c (sigma^[n] a))) ↔
    ∃ u : S, valueBoundary sigma alpha a x (Function.minimalPeriod sigma a) =
      u⁻¹ * cycleComponent (fun (_ : Fin 1) => alpha) (fun _ => sigma) 0 a
        (Function.minimalPeriod sigma a) u := by
  constructor
  · rintro ⟨c,hc⟩
    exact ⟨c a,(cycle_value_with_witness_iff sigma alpha a x hp (c a)).mp ⟨c,rfl,hc⟩⟩
  · rintro ⟨u,hu⟩
    obtain ⟨c,hca,hc⟩ := (cycle_value_with_witness_iff sigma alpha a x hp u).mpr hu
    exact ⟨c,hc⟩

private theorem permutation_periodic [Finite I] (sigma : Equiv.Perm I) (a : I) :
    a ∈ Function.periodicPts sigma := by
  apply Function.mk_mem_periodicPts (orderOf_pos sigma)
  change sigma^[orderOf sigma] a = a
  rw [← Equiv.Perm.coe_pow, pow_orderOf_eq_one]
  rfl

private theorem boundary_update_before_return [DecidableEq I]
    (sigma : Equiv.Perm I) (alpha : I → MulAut S) (a : I) (x : I → S)
    (s : S) (n : ℕ) (hn : n < Function.minimalPeriod sigma a) :
    valueBoundary sigma alpha a (Function.update x a s) n =
      valueBoundary sigma alpha a x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hne : sigma^[n+1] a ≠ a := by
      intro heq
      have hh : Function.IsPeriodicPt sigma (n+1) a := heq
      have hz := hh.eq_zero_of_lt_minimalPeriod hn
      omega
    rw [valueBoundary,Function.update_of_ne hne,ih (by omega),valueBoundary]

/-- Construct the actual cycle-base VALUE substitution (50), retaining all
other cycle coordinates verbatim and the freely prescribed scalar witness u.
The corrected cycle automorphism is not replaced by an exponent divisor. -/
theorem cycle_base_value_substitution [DecidableEq I]
    (sigma : Equiv.Perm I) (alpha : I → MulAut S) (a : I)
    (hp : a ∈ Function.periodicPts sigma) (x : I → S) (u : S) :
    let e := Function.minimalPeriod sigma a
    let beta := cycleComponent (fun (_ : Fin 1) => alpha) (fun _ => sigma) 0 a e
    let tail := alpha (sigma^[e-1] a) (valueBoundary sigma alpha a x (e-1))
    let xb := u⁻¹ * beta u * tail⁻¹
    ∃ c : I → S, c a = u ∧ ∀ n : ℕ,
      (Function.update x a xb) (sigma^[n+1] a) =
        (c (sigma^[n+1] a))⁻¹ * alpha (sigma^[n] a) (c (sigma^[n] a)) := by
  dsimp only
  apply (cycle_value_with_witness_iff sigma alpha a _ hp u).mpr
  let e := Function.minimalPeriod sigma a
  have he : 0 < e := Function.minimalPeriod_pos_of_mem_periodicPts hp
  have heq : e = (e-1)+1 := by omega
  have hb := boundary_update_before_return sigma alpha a x
    (u⁻¹ * cycleComponent (fun (_ : Fin 1) => alpha) (fun _ => sigma) 0 a e u *
      (alpha (sigma^[e-1] a) (valueBoundary sigma alpha a x (e-1)))⁻¹)
    (e-1) (by omega)
  change valueBoundary sigma alpha a _ e = _
  nth_rw 1 [heq]
  rw [valueBoundary,hb]
  rw [show sigma^[(e-1)+1] a = a by
    rw [← heq]; exact Function.iterate_minimalPeriod]
  simp [e,mul_assoc]

abbrev ActualCycle (sigma : Equiv.Perm I) :=
  Quotient (Equiv.Perm.SameCycle.setoid sigma)

/-- Exactly ONE constraint and ONE independently prescribed scalar parameter
per actual permutation cycle.  The constructed factor tuple retains each
u(j,Delta) at Delta's actual chosen representative; nonroot witnesses are
solved by (40).  No coverage hypothesis occurs in either direction. -/
theorem value_tuple_with_parameters_iff [Finite I] {m : ℕ}
    (g : Fin m → MulAut (I → S)) (sigma : Fin m → Equiv.Perm I)
    (alpha : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, g j z (sigma j i) = alpha j i (z i))
    (x : Fin m → I → S) (u : ∀ j, ActualCycle (sigma j) → S) :
    (∃ c : Fin m → I → S,
      (∀ j (C : ActualCycle (sigma j)), c j C.out = u j C) ∧
      ∀ j i, x j i = (c j i)⁻¹ * (g j (c j)) i) ↔
    ∀ j (C : ActualCycle (sigma j)),
      valueBoundary (sigma j) (alpha j) C.out (x j)
        (Function.minimalPeriod (sigma j) C.out) =
      (u j C)⁻¹ * cycleComponent alpha sigma j C.out
        (Function.minimalPeriod (sigma j) C.out) (u j C) := by
  classical
  have hcomponent : ∀ j a n,
      cycleComponent (fun (_ : Fin 1) => alpha j) (fun _ => sigma j) 0 a n =
        cycleComponent alpha sigma j a n := by
    intro j a n
    induction n with
    | zero => rfl
    | succ n ih => simp only [cycleComponent,ih]
  constructor
  · rintro ⟨c,hroot,hc⟩ j C
    have hsteps : ∀ n, x j ((sigma j)^[n+1] C.out) =
        (c j ((sigma j)^[n+1] C.out))⁻¹ * alpha j ((sigma j)^[n] C.out)
          (c j ((sigma j)^[n] C.out)) := by
      intro n
      rw [hc]
      have hh := hcoord j (c j) ((sigma j)^[n] C.out)
      rw [← Function.iterate_succ_apply' (sigma j) n C.out] at hh
      rw [hh]
    have hh := (cycle_value_with_witness_iff (sigma j) (alpha j) C.out (x j)
      (permutation_periodic _ _) (u j C)).mp ⟨c j,hroot j C,hsteps⟩
    simpa only [hcomponent] using hh
  · intro h
    have hlocal : ∀ j (C : ActualCycle (sigma j)), ∃ c : I → S,
        c C.out = u j C ∧ ∀ n,
          x j ((sigma j)^[n+1] C.out) = (c ((sigma j)^[n+1] C.out))⁻¹ *
            alpha j ((sigma j)^[n] C.out) (c ((sigma j)^[n] C.out)) := by
      intro j C
      apply (cycle_value_with_witness_iff (sigma j) (alpha j) C.out (x j)
        (permutation_periodic _ _) (u j C)).mpr
      simpa only [hcomponent] using h j C
    choose c hc using hlocal
    let Q : ∀ j, I → ActualCycle (sigma j) := fun j i => Quotient.mk _ i
    let z : Fin m → I → S := fun j i => c j (Q j i) i
    refine ⟨z,?_,?_⟩
    · intro j C
      change c j (Quotient.mk _ C.out) C.out = u j C
      rw [C.out_eq]
      exact (hc j C).1
    · intro j i
      let b := (sigma j).symm i
      have hb : sigma j b = i := Equiv.apply_symm_apply _ i
      have hQ : Q j (sigma j b) = Q j b :=
        Quotient.sound (Equiv.Perm.SameCycle.refl (sigma j) b).apply_left
      have hsame : (sigma j).SameCycle (Q j b).out b := by
        apply @Quotient.exact I (Equiv.Perm.SameCycle.setoid (sigma j))
        exact (Q j b).out_eq
      obtain ⟨n,hn⟩ := hsame.exists_nat_pow_eq
      have hn' : (sigma j)^[n] (Q j b).out = b := by
        simpa only [Equiv.Perm.coe_pow] using hn
      have hnnext : (sigma j)^[n+1] (Q j b).out = i := by
        rw [Function.iterate_succ_apply',hn',hb]
      have hh := (hc j (Q j b)).2 n
      rw [hn',hnnext] at hh
      rw [← hb,hcoord]
      change x j (sigma j b) = (c j (Q j (sigma j b)) (sigma j b))⁻¹ *
        alpha j b (c j (Q j b) b)
      rw [hQ,hb]
      exact hh

private noncomputable def cycleRoot (sigma : Equiv.Perm I) (a : I) : I :=
  (Quotient.mk (Equiv.Perm.SameCycle.setoid sigma) a).out

private theorem cycleRoot_same (sigma : Equiv.Perm I) (a : I) :
    sigma.SameCycle (cycleRoot sigma a) a := by
  apply @Quotient.exact I (Equiv.Perm.SameCycle.setoid sigma)
  exact Quotient.out_eq (Quotient.mk (Equiv.Perm.SameCycle.setoid sigma) a)

private theorem cycleRoot_apply (sigma : Equiv.Perm I) (a : I) :
    cycleRoot sigma (sigma a) = cycleRoot sigma a := by
  apply congrArg Quotient.out
  exact Quotient.sound (Equiv.Perm.SameCycle.refl sigma a).apply_left

/-- All actual cycle constraints, glued without changing any component
automorphism.  This is the first reduction of Proposition 9.1: arbitrary
coordinate VALUE data are realizable precisely when their genuine ordered
cycle words are scalar commutator values.  No surjectivity is assumed. -/
theorem value_tuple_iff [Finite I] {m : ℕ}
    (g : Fin m → MulAut (I → S)) (sigma : Fin m → Equiv.Perm I)
    (alpha : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, g j z (sigma j i) = alpha j i (z i))
    (x : Fin m → I → S) :
    (∃ c : Fin m → I → S, ∀ j i, x j i = (c j i)⁻¹ * (g j (c j)) i) ↔
    ∀ j a, ∃ u : S,
      valueBoundary (sigma j) (alpha j) a (x j) (Function.minimalPeriod (sigma j) a) =
        u⁻¹ * cycleComponent alpha sigma j a (Function.minimalPeriod (sigma j) a) u := by
  classical
  have hcomponent : ∀ j a n,
      cycleComponent (fun (_ : Fin 1) => alpha j) (fun _ => sigma j) 0 a n =
        cycleComponent alpha sigma j a n := by
    intro j a n
    induction n with
    | zero => rfl
    | succ n ih => simp only [cycleComponent,ih]
  constructor
  · rintro ⟨c,hc⟩ j a
    have hh : ∀ n : ℕ, x j ((sigma j)^[n+1] a) =
        (c j ((sigma j)^[n+1] a))⁻¹ *
          alpha j ((sigma j)^[n] a) (c j ((sigma j)^[n] a)) := by
      intro n
      rw [hc]
      have hn := hcoord j (c j) ((sigma j)^[n] a)
      rw [← Function.iterate_succ_apply' (sigma j) n a] at hn
      rw [hn]
    obtain ⟨u,hu⟩ := (cycle_value_iff (sigma j) (alpha j) a (x j)
      (permutation_periodic _ _)).mp ⟨c j,hh⟩
    exact ⟨u,by simpa only [hcomponent] using hu⟩
  · intro h
    have hlocal : ∀ j a, ∃ c : I → S, ∀ n : ℕ,
        x j ((sigma j)^[n+1] a) = (c ((sigma j)^[n+1] a))⁻¹ *
          alpha j ((sigma j)^[n] a) (c ((sigma j)^[n] a)) := by
      intro j a
      apply (cycle_value_iff (sigma j) (alpha j) a (x j)
        (permutation_periodic _ _)).mpr
      obtain ⟨u,hu⟩ := h j a
      exact ⟨u,by simpa only [hcomponent] using hu⟩
    choose c hc using hlocal
    let z : Fin m → I → S := fun j i => c j (cycleRoot (sigma j) i) i
    refine ⟨z,?_⟩
    intro j i
    let b := (sigma j).symm i
    have hb : sigma j b = i := Equiv.apply_symm_apply _ i
    have hr : cycleRoot (sigma j) i = cycleRoot (sigma j) b := by
      rw [← hb,cycleRoot_apply]
    obtain ⟨n,hn⟩ := (cycleRoot_same (sigma j) b).exists_nat_pow_eq
    have hn' : (sigma j)^[n] (cycleRoot (sigma j) b) = b := by
      simpa only [Equiv.Perm.coe_pow] using hn
    have hnnext : (sigma j)^[n+1] (cycleRoot (sigma j) b) = i := by
      rw [Function.iterate_succ_apply',hn',hb]
    have hh := hc j (cycleRoot (sigma j) b) n
    rw [hn',hnnext] at hh
    rw [← hb,hcoord]
    change x j (sigma j b) =
      (c j (cycleRoot (sigma j) (sigma j b)) (sigma j b))⁻¹ *
      alpha j b (c j (cycleRoot (sigma j) b) b)
    rw [cycleRoot_apply,hb]
    exact hh

/-- Instantiate the actual constraints with the accepted q-power component
bridge and the ONE already fixed global correction tuple.  The cycle periods
here are periods of sigma^q, not periods of the original transitive action. -/
theorem corrected_value_tuple_iff [Finite I] {m q : ℕ}
    (k : Fin m → MulAut (I → S)) (sigma : Fin m → Equiv.Perm I)
    (beta : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, k j z (sigma j i) = beta j i (z i))
    (y x : Fin m → I → S) :
    (∃ c : Fin m → I → S, ∀ j i, x j i = (c j i)⁻¹ *
      (((k j * MulAut.conj (y j)⁻¹)^q) (c j)) i) ↔
    ∀ j a, ∃ u : S,
      valueBoundary (sigma j ^ q)
        (fun i => correctedCycleComponent beta sigma y j i q) a (x j)
        (Function.minimalPeriod (sigma j ^ q) a) =
      u⁻¹ * cycleComponent
        (fun j i => correctedCycleComponent beta sigma y j i q)
        (fun j => sigma j ^ q) j a
        (Function.minimalPeriod (sigma j ^ q) a) u := by
  apply value_tuple_iff
    (fun j => (k j * MulAut.conj (y j)⁻¹)^q)
    (fun j => sigma j ^ q)
    (fun j i => correctedCycleComponent beta sigma y j i q)
  intro j z i
  simpa only [Equiv.Perm.coe_pow] using
    actual_corrected_q_power_coordinate k sigma beta hcoord y j i q z

/-- The same actual q-powered specialization retaining the paper's chosen
scalar parameters at ONE representative of EACH powered-generator cycle.
The original cycles used by Hall selection are not conflated with these. -/
theorem corrected_value_tuple_with_parameters_iff [Finite I] {m q : ℕ}
    (k : Fin m → MulAut (I → S)) (sigma : Fin m → Equiv.Perm I)
    (beta : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, k j z (sigma j i) = beta j i (z i))
    (y x : Fin m → I → S) (u : ∀ j, ActualCycle (sigma j ^ q) → S) :
    (∃ c : Fin m → I → S,
      (∀ j (C : ActualCycle (sigma j ^ q)), c j C.out = u j C) ∧
      ∀ j i, x j i = (c j i)⁻¹ * (((k j * MulAut.conj (y j)⁻¹)^q) (c j)) i) ↔
    ∀ j (C : ActualCycle (sigma j ^ q)),
      valueBoundary (sigma j ^ q)
        (fun i => correctedCycleComponent beta sigma y j i q) C.out (x j)
        (Function.minimalPeriod (sigma j ^ q) C.out) =
      (u j C)⁻¹ * cycleComponent
        (fun j i => correctedCycleComponent beta sigma y j i q)
        (fun j => sigma j ^ q) j C.out
        (Function.minimalPeriod (sigma j ^ q) C.out) (u j C) := by
  apply value_tuple_with_parameters_iff
    (fun j => (k j * MulAut.conj (y j)⁻¹)^q) (fun j => sigma j ^ q)
    (fun j i => correctedCycleComponent beta sigma y j i q)
  intro j z i
  simpa only [Equiv.Perm.coe_pow] using
    actual_corrected_q_power_coordinate k sigma beta hcoord y j i q z

end NikolovSegal.Equation47TypeII
