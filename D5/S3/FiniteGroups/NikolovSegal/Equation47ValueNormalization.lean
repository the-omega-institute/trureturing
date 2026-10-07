/- GID: D5/S3/FiniteGroups/NikolovSegal/Equation47ValueNormalization
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Equation47ValueNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-group coordinate, extraction or product mathematics. -/

import D5.S3.FiniteGroups.NikolovSegal.Equation47WordCoupling
import D5.S3.FiniteGroups.NikolovSegal.Equation47TypeIIBounds

set_option autoImplicit false

/-!
Part I, Proposition 9.1, printed pp. 223--225: the actual VALUE system
after (H) and the cycle-base substitution (50).  The variables in this
system are nonbase VALUES, not commutator witnesses.  Scalar cycle witnesses
are retained as parameters.  All transports and all products are ordered.
-/
namespace NikolovSegal.Equation47ValueNormalization
open Equation47 Equation47TypeII Equation47WordCoupling
universe u
variable {S I : Type u} [Group S] [Finite I] [DecidableEq I] {m : ℕ}

noncomputable def cycleClass (tau : Equiv.Perm I) (v : I) : ActualCycle tau :=
  Quotient.mk _ v

noncomputable def base (tau : Equiv.Perm I) (v : I) : I :=
  (cycleClass tau v).out

private theorem class_base (tau : Equiv.Perm I) (v : I) :
    cycleClass tau (base tau v) = cycleClass tau v := Quotient.out_eq _

private theorem base_base (tau : Equiv.Perm I) (v : I) :
    base tau (base tau v) = base tau v := congrArg Quotient.out (class_base tau v)

private theorem class_iterate (tau : Equiv.Perm I) (v : I) (n : ℕ) :
    cycleClass tau (tau^[n] v) = cycleClass tau v := by
  apply Quotient.sound
  change tau.SameCycle (tau^[n] v) v
  simpa only [Equiv.Perm.coe_pow] using
    (Equiv.Perm.SameCycle.refl tau v).pow_left (n := n)

private theorem periodic (tau : Equiv.Perm I) (v : I) :
    v ∈ Function.periodicPts tau := by
  apply Function.mk_mem_periodicPts (orderOf_pos tau)
  change tau^[orderOf tau] v = v
  rw [← Equiv.Perm.coe_pow,pow_orderOf_eq_one]
  rfl

/-- The literal transported boundary word.  Its last factor is on the left,
as required by our forward-coordinate convention in the accepted (H) proof. -/
def boundaryWord (tau : Fin m → Equiv.Perm I)
    (alpha : Fin m → I → MulAut S) (j : Fin m) (a : I) :
    ℕ → List (Letter (Arc m I) S)
  | 0 => []
  | n+1 => [.var (j,(tau j)^[n+1] a) 1 false] ++
      twist (alpha j ((tau j)^[n] a)) (boundaryWord tau alpha j a n)

private theorem boundaryWord_value (tau : Fin m → Equiv.Perm I)
    (alpha : Fin m → I → MulAut S) (j : Fin m) (a : I)
    (z : Arc m I → S) (n : ℕ) :
    wordValue (boundaryWord tau alpha j a n) z =
      valueBoundary (tau j) (alpha j) a (fun v => z (j,v)) n := by
  induction n with
  | zero => simp [boundaryWord,wordValue,valueBoundary]
  | succ n ih =>
    simp only [boundaryWord,value_append,value_var,Bool.false_eq_true,↓reduceIte,
      MulAut.one_apply,value_twist,ih,valueBoundary]

/-- Equation (50), as a literal word with the true cycle-base scalar
parameter.  No witness variables are counted as nonbase VALUE variables. -/
noncomputable def baseValueWord (tau : Fin m → Equiv.Perm I)
    (alpha : Fin m → I → MulAut S)
    (u : ∀ j, ActualCycle (tau j) → S) (j : Fin m) (v : I) :
    List (Letter (Arc m I) S) :=
  let a := base (tau j) v
  let e := Function.minimalPeriod (tau j) a
  [.constant ((u j (cycleClass (tau j) v))⁻¹ *
    cycleComponent alpha tau j a e (u j (cycleClass (tau j) v)))] ++
  inverseWord (twist (alpha j ((tau j)^[e-1] a))
    (boundaryWord tau alpha j a (e-1)))

noncomputable def normalizedFactorWord (tau : Fin m → Equiv.Perm I)
    (alpha : Fin m → I → MulAut S)
    (u : ∀ j, ActualCycle (tau j) → S) (j : Fin m) (v : I) :
    List (Letter (Arc m I) S) :=
  if v = base (tau j) v then baseValueWord tau alpha u j v
  else [.var (j,v) 1 false]

noncomputable def normalizedVertexWord (tau : Fin m → Equiv.Perm I)
    (alpha : Fin m → I → MulAut S)
    (u : ∀ j, ActualCycle (tau j) → S) (v : I) :
    List (Letter (Arc m I) S) :=
  (List.ofFn (fun j => normalizedFactorWord tau alpha u j v)).flatten

/-- Actual coordinate VALUES determined by the free nonbase assignment z.
Base values are determined by (50); every nonbase value is left untouched. -/
noncomputable def normalizedValues (tau : Fin m → Equiv.Perm I)
    (alpha : Fin m → I → MulAut S)
    (u : ∀ j, ActualCycle (tau j) → S) (z : Arc m I → S) : Fin m → I → S :=
  fun j v => wordValue (normalizedFactorWord tau alpha u j v) z

theorem normalizedValues_nonbase (tau : Fin m → Equiv.Perm I)
    (alpha : Fin m → I → MulAut S)
    (u : ∀ j, ActualCycle (tau j) → S) (z : Arc m I → S)
    (j : Fin m) (v : I) (hv : v ≠ base (tau j) v) :
    normalizedValues tau alpha u z j v = z (j,v) := by
  simp [normalizedValues,normalizedFactorWord,hv]

private theorem normalizedValues_base (tau : Fin m → Equiv.Perm I)
    (alpha : Fin m → I → MulAut S)
    (u : ∀ j, ActualCycle (tau j) → S) (z : Arc m I → S)
    (j : Fin m) (C : ActualCycle (tau j)) :
    normalizedValues tau alpha u z j C.out =
      (u j C)⁻¹ * cycleComponent alpha tau j C.out
        (Function.minimalPeriod (tau j) C.out) (u j C) *
      (alpha j ((tau j)^[Function.minimalPeriod (tau j) C.out-1] C.out)
        (valueBoundary (tau j) (alpha j) C.out (fun v => z (j,v))
          (Function.minimalPeriod (tau j) C.out-1)))⁻¹ := by
  have hc : cycleClass (tau j) C.out = C := C.out_eq
  have hb : base (tau j) C.out = C.out := congrArg Quotient.out hc
  simp only [normalizedValues,normalizedFactorWord,hb,ite_true,
    baseValueWord,hc,value_append,value_constant,value_inverse,value_twist,
    boundaryWord_value]

private theorem boundary_congr (tau : Equiv.Perm I) (alpha : I → MulAut S)
    (a : I) (x z : I → S) (n : ℕ)
    (h : ∀ k, 0 < k → k ≤ n → x (tau^[k] a) = z (tau^[k] a)) :
    valueBoundary tau alpha a x n = valueBoundary tau alpha a z n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [valueBoundary,valueBoundary,h (n+1) (by omega) (by omega),
      ih (fun k hk hkn => h k hk (by omega))]

/-- All normalized VALUE tuples satisfy all genuine cycle constraints (H),
with the prescribed scalar parameters.  This is constructive normalization,
not an assumption of tuple coverage. -/
theorem normalizedValues_cycle_constraints (tau : Fin m → Equiv.Perm I)
    (alpha : Fin m → I → MulAut S)
    (u : ∀ j, ActualCycle (tau j) → S) (z : Arc m I → S)
    (j : Fin m) (C : ActualCycle (tau j)) :
    valueBoundary (tau j) (alpha j) C.out (normalizedValues tau alpha u z j)
        (Function.minimalPeriod (tau j) C.out) =
      (u j C)⁻¹ * cycleComponent alpha tau j C.out
        (Function.minimalPeriod (tau j) C.out) (u j C) := by
  let e := Function.minimalPeriod (tau j) C.out
  have he : 0 < e := Function.minimalPeriod_pos_of_mem_periodicPts (periodic _ _)
  have htail : valueBoundary (tau j) (alpha j) C.out
      (normalizedValues tau alpha u z j) (e-1) =
      valueBoundary (tau j) (alpha j) C.out (fun v => z (j,v)) (e-1) := by
    apply boundary_congr
    intro n hn hne
    apply normalizedValues_nonbase
    have hb : base (tau j) ((tau j)^[n] C.out) = C.out := by
      unfold base
      rw [class_iterate]
      exact congrArg Quotient.out C.out_eq
    rw [hb]
    intro hh
    have hz := (show Function.IsPeriodicPt (tau j) n C.out from hh).eq_zero_of_lt_minimalPeriod
      (by dsimp [e] at hne; omega)
    omega
  have hreturn : (tau j)^[e] C.out = C.out := Function.iterate_minimalPeriod
  have heq : e = (e-1)+1 := by omega
  change valueBoundary _ _ _ _ e = _
  nth_rw 1 [heq]
  rw [valueBoundary,← heq,hreturn,normalizedValues_base,htail]
  simp [e,mul_assoc]

/-- Evaluate the literal normalized right-hand side in generator order. -/
theorem normalizedVertexWord_value (tau : Fin m → Equiv.Perm I)
    (alpha : Fin m → I → MulAut S)
    (u : ∀ j, ActualCycle (tau j) → S) (z : Arc m I → S) (v : I) :
    wordValue (normalizedVertexWord tau alpha u v) z =
      orderedProduct (normalizedValues tau alpha u z · v) := by
  simp [normalizedVertexWord,value_flatten,List.map_ofFn,orderedProduct,
    normalizedValues,Function.comp_def]

private theorem normalize_constrained_values (tau : Fin m → Equiv.Perm I)
    (alpha : Fin m → I → MulAut S)
    (u : ∀ j, ActualCycle (tau j) → S) (x : Fin m → I → S)
    (h : ∀ j (C : ActualCycle (tau j)),
      valueBoundary (tau j) (alpha j) C.out (x j)
        (Function.minimalPeriod (tau j) C.out) =
      (u j C)⁻¹ * cycleComponent alpha tau j C.out
        (Function.minimalPeriod (tau j) C.out) (u j C)) :
    normalizedValues tau alpha u (fun a => x a.1 a.2) = x := by
  funext j v
  by_cases hv : v = base (tau j) v
  · let C := cycleClass (tau j) v
    have hv' : v = C.out := hv
    rw [hv',normalizedValues_base]
    let e := Function.minimalPeriod (tau j) C.out
    have he : 0 < e := Function.minimalPeriod_pos_of_mem_periodicPts (periodic _ _)
    have heq : e = (e-1)+1 := by omega
    have hh := h j C
    change valueBoundary _ _ _ _ e = _ at hh
    nth_rw 1 [heq] at hh
    rw [valueBoundary,← heq,Function.iterate_minimalPeriod] at hh
    change _ * _⁻¹ = _
    rw [← hh]
    simp [e,mul_assoc]
  · exact normalizedValues_nonbase tau alpha u _ j v hv

/-- The actual normalized VALUE equations are equivalent to the original
commutator equations, retaining all true cycle-base witness parameters.
The only existential choice here is free nonbase VALUES. -/
theorem normalized_system_iff_actual [Fintype I]
    (g : Fin m → MulAut (I → S)) (tau : Fin m → Equiv.Perm I)
    (alpha : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, g j z (tau j i) = alpha j i (z i))
    (u : ∀ j, ActualCycle (tau j) → S) (kappa : I → S) :
    (∃ z : Arc m I → S, ∀ v,
      wordValue (normalizedVertexWord tau alpha u v) z = kappa v) ↔
    (∃ c : Fin m → I → S,
      (∀ j (C : ActualCycle (tau j)), c j C.out = u j C) ∧
      ∀ v, orderedProduct (fun j => (c j v)⁻¹ * g j (c j) v) = kappa v) := by
  constructor
  · rintro ⟨z,hz⟩
    obtain ⟨c,hc,hx⟩ := (value_tuple_with_parameters_iff g tau alpha hcoord
      (normalizedValues tau alpha u z) u).mpr
        (normalizedValues_cycle_constraints tau alpha u z)
    refine ⟨c,hc,?_⟩
    intro v
    rw [← hz v,normalizedVertexWord_value]
    congr 1
    funext j
    exact (hx j v).symm
  · rintro ⟨c,hc,hk⟩
    let x := fun j v => (c j v)⁻¹ * g j (c j) v
    have hx := (value_tuple_with_parameters_iff g tau alpha hcoord x u).mp
      ⟨c,hc,fun _ _ => rfl⟩
    refine ⟨fun a => x a.1 a.2,?_⟩
    intro v
    rw [normalizedVertexWord_value,normalize_constrained_values tau alpha u x hx]
    exact hk v

/-- Consume this normalization on the REAL corrected q-powered action.
The ONE global y remains fixed before target kappa and before the scalar
cycle parameters.  No powered connectivity or coverage is assumed here. -/
theorem corrected_normalized_system_iff [Fintype I] {q : ℕ}
    (k : Fin m → MulAut (I → S)) (sigma : Fin m → Equiv.Perm I)
    (beta : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, k j z (sigma j i) = beta j i (z i))
    (y : Fin m → I → S)
    (u : ∀ j, ActualCycle (sigma j ^ q) → S) (kappa : I → S) :
    (∃ z : Arc m I → S, ∀ v,
      wordValue (normalizedVertexWord (fun j => sigma j ^ q)
        (fun j i => correctedCycleComponent beta sigma y j i q) u v) z = kappa v) ↔
    (∃ c : Fin m → I → S,
      (∀ j (C : ActualCycle (sigma j ^ q)), c j C.out = u j C) ∧
      ∀ v, orderedProduct (fun j => (c j v)⁻¹ *
        (((k j * MulAut.conj (y j)⁻¹)^q) (c j)) v) = kappa v) := by
  apply normalized_system_iff_actual
  intro j z i
  simpa only [Equiv.Perm.coe_pow] using
    actual_corrected_q_power_coordinate k sigma beta hcoord y j i q z

end NikolovSegal.Equation47ValueNormalization
