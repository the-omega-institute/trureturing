/- GID: D5/S3/VertexAlgebra/PolynomialFockChargedStateField
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/PolynomialFockChargedStateField
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual charged Fock fields have finite positional-deletion coefficients. -/

/-
proof_shape: charged_statefield_coefficients: content
escape_witness: Induction on every ordered word expands the two actual
  normal-product branches on arbitrary input states into independent positional
  masks. Raw and individual transformed supports give common finite bounds;
  successor images and insertion of the first position give the exact weights
  and integer shifts. The monomial basis extends this calculation to every state.
admission_basis: escape-witness
utility: none; the result is a universal algebraic coefficient identity, not a
  numerical reduction, enumeration, checker or certified finite instance.
-/

import D5.S3.VertexAlgebra.PolynomialFockStateField
import D5.S3.VertexAlgebra.PolynomialFockChargedIrreducibility
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.List.FinRange

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.PolynomialFockChargedStateField

open MvPolynomial PolynomialFockSugawaraSupport PolynomialFockStateField
open FieldNormalProduct PolynomialFockChargedIrreducibility
open scoped VertexOperator

/-- The actual current plus the charge at Laurent power minus one. -/
noncomputable def chargedCurrent (lambda : ℂ) : VertexOperator ℂ Fock :=
  current + VertexOperator.of_coeff
    (fun power => if power = -1 then lambda • LinearMap.id else 0) (by
      intro v
      refine ⟨-1, ?_⟩
      intro power hp
      by_contra hn
      exact hp (by simp [show power ≠ -1 by omega]))

/-- Ordered right-nested divided derivatives of the charged current. -/
noncomputable def chargedWordField (lambda : ℂ) : List ℕ → VertexOperator ℂ Fock
  | [] => identityField
  | j :: w => (normalMinusOne (dividedDerivative j (chargedCurrent lambda))
      (chargedWordField lambda w)).1

/-- Complex linear extension along the existing monomial occurrence basis. -/
noncomputable def chargedY (lambda : ℂ) : Fock →ₗ[ℂ] VertexOperator ℂ Fock :=
  (basisMonomials ℕ ℂ).constr ℂ
    (fun e => chargedWordField lambda (occurrences e))

set_option backward.isDefEq.respectTransparency false in
/-- Every charged state-field coefficient is the finite positional-deletion sum. -/
theorem charged_statefield_coefficients (lambda : ℂ) (u v : Fock) (n : ℤ) :
    let keep := fun (w : List ℕ) (R : Finset (Fin w.length)) =>
      ((List.finRange w.length).filter (fun i => i ∉ R)).map w.get
    let shift := fun (w : List ℕ) (R : Finset (Fin w.length)) =>
      ∑ i ∈ R, ((w.get i : ℤ) + 1)
    let weight := fun (w : List ℕ) (R : Finset (Fin w.length)) =>
      ∏ i ∈ R, ((-1 : ℂ) ^ w.get i * lambda)
    ((chargedY lambda u) [[n]]) v =
      ∑ e ∈ u.support,
        ∑ R ∈ (Finset.univ : Finset (Fin (occurrences e).length)).powerset,
          (AddMonoidAlgebra.coeff u e * weight (occurrences e) R) •
            ((wordField (keep (occurrences e) R)) [[n - shift (occurrences e) R]]) v := by
  classical
  let keep (w : List ℕ) (R : Finset (Fin w.length)) :=
    ((List.finRange w.length).filter (fun i => i ∉ R)).map w.get
  let shift (w : List ℕ) (R : Finset (Fin w.length)) : ℤ :=
    ∑ i ∈ R, ((w.get i : ℤ) + 1)
  let weight (w : List ℕ) (R : Finset (Fin w.length)) : ℂ :=
    ∏ i ∈ R, ((-1 : ℂ) ^ w.get i * lambda)
  have currentModes (m : ℤ) : (current [[m]]) = mode m := by
    rw [current, VertexOperator.ncoeff_of_coeff]
    rw [show -(-m - 1) - 1 = m by omega]
  have chargedModes (m : ℤ) : (chargedCurrent lambda [[m]]) = chargedMode lambda m := by
    simp only [chargedCurrent, map_add, Pi.add_apply, VertexOperator.ncoeff_of_coeff,
      currentModes]
    by_cases hm : m = 0
    · subst m
      simp [chargedMode, mode]
    · simp [chargedMode, hm, show -m - 1 ≠ -1 by omega]
  have derivativeModes (j : ℕ) (A : VertexOperator ℂ Fock) (m : ℤ) (x : Fock) :
      (dividedDerivative j A [[m]]) x =
        ((Ring.choose (-m - 1 + j) j : ℤ) : ℂ) • (A [[m-j]]) x := by
    change Ring.choose (-m - 1 + j) j • HVertexOperator.coeff A (-m - 1 + j) x = _
    rw [VertexOperator.coeff_eq_ncoeff]
    rw [show -(-m - 1 + j) - 1 = m - j by omega]
    simp only [Int.cast_smul_eq_zsmul]
  have chargeDifference (j : ℕ) (m : ℤ) :
      (dividedDerivative j (chargedCurrent lambda) [[m]]) =
        (dividedDerivative j current [[m]]) +
          if m = (j : ℤ) then (((-1 : ℂ)^j)*lambda) • LinearMap.id else 0 := by
    apply LinearMap.ext
    intro x
    rw [LinearMap.add_apply, derivativeModes, derivativeModes, chargedModes]
    by_cases hm : m = (j : ℤ)
    · subst m
      rw [show -(j : ℤ) - 1 + j = -1 by omega]
      simp only [sub_self, chargedMode, currentModes, mode, LinearMap.zero_apply,
        smul_zero, zero_add]
      rw [show (-1 : ℤ) = -(1 : ℤ) by rfl, Ring.choose_neg]
      simp [Ring.choose_natCast, Int.coe_negOnePow_natCast, Units.smul_def, smul_smul]
    · rw [chargedMode, if_neg (show m - (j : ℤ) ≠ 0 by omega), if_neg hm, currentModes]
      simp
  have forwardFinite (A B : VertexOperator ℂ Fock) (m : ℤ) (x : Fock) :
      Function.HasFiniteSupport
        (fun k : ℕ => (A [[-(k : ℤ)-1]]) ((B [[m+k]]) x)) := by
    refine BddAbove.finite (bddAbove_def.mpr ?_)
    refine ⟨(-((HahnModule.of ℂ).symm (B x)).order - m).toNat, ?_⟩
    intro k hk
    contrapose! hk
    have hz : (B [[m+k]]) x = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      omega
    simp [hz]
  have reverseFinite (A B : VertexOperator ℂ Fock) (m : ℤ) (x : Fock) :
      Function.HasFiniteSupport
        (fun k : ℕ => (B [[m-k-1]]) ((A [[k]]) x)) := by
    refine BddAbove.finite (bddAbove_def.mpr ?_)
    refine ⟨(-((HahnModule.of ℂ).symm (A x)).order - 1).toNat, ?_⟩
    intro k hk
    contrapose! hk
    have hz : (A [[k]]) x = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      omega
    simp [hz]
  -- A common finite set contains the raw support and each separate mask support.
  have exchange (ι : Type) (masks : Finset ι) (f : ℕ → Fock) (g : ℕ → ι → Fock)
      (raw : Function.HasFiniteSupport f)
      (each : ∀ r ∈ masks, Function.HasFiniteSupport (fun k => g k r))
      (heq : ∀ k, f k = ∑ r ∈ masks, g k r) :
      (∑ᶠ k, f k) = ∑ r ∈ masks, ∑ᶠ k, g k r := by
    let T : Set ℕ := Function.support f ∪ ⋃ r ∈ masks, Function.support (fun k => g k r)
    have finite : T.Finite := raw.union (masks.finite_toSet.biUnion each)
    have hf : Function.support f ⊆ finite.toFinset := by
      rw [Set.Finite.coe_toFinset]
      exact Set.subset_union_left
    have hg (r : ι) (hr : r ∈ masks) :
        Function.support (fun k => g k r) ⊆ finite.toFinset := by
      rw [Set.Finite.coe_toFinset]
      intro k hk
      exact Or.inr (by simp only [Set.mem_iUnion]; exact ⟨r, hr, hk⟩)
    rw [finsum_eq_sum_of_support_subset _ hf]
    simp_rw [heq]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    exact (finsum_eq_sum_of_support_subset _ (hg r hr)).symm
  have splitFinite (f g h : ℕ → Fock) (hf : Function.HasFiniteSupport f)
      (hg : Function.HasFiniteSupport g) (hh : Function.HasFiniteSupport h)
      (heq : ∀ k, f k = g k + h k) :
      (∑ᶠ k, f k) = (∑ᶠ k, g k) + (∑ᶠ k, h k) := by
    let T : Set ℕ := Function.support f ∪ (Function.support g ∪ Function.support h)
    have finite : T.Finite := hf.union (hg.union hh)
    have first : Function.support f ⊆ finite.toFinset := by
      rw [Set.Finite.coe_toFinset]; exact Set.subset_union_left
    have second : Function.support g ⊆ finite.toFinset := by
      rw [Set.Finite.coe_toFinset]
      exact Set.Subset.trans Set.subset_union_left Set.subset_union_right
    have third : Function.support h ⊆ finite.toFinset := by
      rw [Set.Finite.coe_toFinset]
      exact Set.Subset.trans Set.subset_union_right Set.subset_union_right
    rw [finsum_eq_sum_of_support_subset _ first]
    simp_rw [heq]
    rw [Finset.sum_add_distrib, ← finsum_eq_sum_of_support_subset _ second,
      ← finsum_eq_sum_of_support_subset _ third]
  have normalCharge (j : ℕ) (B : VertexOperator ℂ Fock) (m : ℤ) (x : Fock) :
      ((normalMinusOne (dividedDerivative j (chargedCurrent lambda)) B).1 [[m]]) x =
        ((normalMinusOne (dividedDerivative j current) B).1 [[m]]) x +
          (((-1 : ℂ)^j)*lambda) • (B [[m - j - 1]]) x := by
    let A := dividedDerivative j (chargedCurrent lambda)
    let A0 := dividedDerivative j current
    let correction (k : ℕ) : Fock :=
      if k = j then (((-1 : ℂ)^j)*lambda) • (B [[m-j-1]]) x else 0
    have rawForward := forwardFinite A B m x
    have rawReverse := reverseFinite A B m x
    have baseForward := forwardFinite A0 B m x
    have baseReverse := reverseFinite A0 B m x
    have correctionFinite : Function.HasFiniteSupport correction := by
      refine (Set.finite_singleton j).subset ?_
      intro k hk
      by_contra hn
      exact hk (by simp [correction, show k ≠ j by simpa using hn])
    have leftEquality (k : ℕ) : (A [[-(k : ℤ)-1]]) ((B [[m+k]]) x) =
        (A0 [[-(k : ℤ)-1]]) ((B [[m+k]]) x) := by
      simp [A, A0, chargeDifference, show -(k : ℤ) - 1 ≠ (j : ℤ) by omega]
    have rightEquality (k : ℕ) : (B [[m-k-1]]) ((A [[k]]) x) =
        (B [[m-k-1]]) ((A0 [[k]]) x) + correction k := by
      simp only [A, A0, chargeDifference, LinearMap.add_apply, map_add]
      by_cases hk : k = j
      · subst k
        simp [correction, map_smul]
      · simp [correction, hk, show (k : ℤ) ≠ (j : ℤ) by exact_mod_cast hk]
    rw [(normalMinusOne A B).2, (normalMinusOne A0 B).2]
    rw [exchange Unit {()} _ (fun k _ => (A0 [[-(k : ℤ)-1]]) ((B [[m+k]]) x))
      rawForward (by intro r hr; exact baseForward) (by intro k; simpa using leftEquality k)]
    simp only [Finset.sum_singleton]
    rw [splitFinite _ _ correction rawReverse baseReverse correctionFinite rightEquality]
    rw [finsum_eq_single correction j (by intro k hk; simp [correction, hk])]
    simp only [correction, if_pos rfl]
    abel
  have wordFormula (w : List ℕ) (x : Fock) (m : ℤ) :
      (chargedWordField lambda w [[m]]) x =
        ∑ R ∈ (Finset.univ : Finset (Fin w.length)).powerset,
          weight w R • ((wordField (keep w R)) [[m-shift w R]]) x := by
    induction w generalizing x m with
    | nil => simp [chargedWordField, keep, shift, weight, wordField]
    | cons j w ih =>
      let masks := (Finset.univ : Finset (Fin w.length)).powerset
      let A := dividedDerivative j (chargedCurrent lambda)
      let lift (R : Finset (Fin w.length)) : Finset (Fin (j::w).length) :=
        R.image Fin.succ
      have nz (R : Finset (Fin w.length)) : (0 : Fin (j::w).length) ∉ lift R := by
        simp [lift]
      have keepLift (R : Finset (Fin w.length)) : keep (j::w) (lift R) = j :: keep w R := by
        simp [keep, lift, List.finRange_succ, List.filter_map, List.map_map, Function.comp_def]
      have keepInsert (R : Finset (Fin w.length)) :
          keep (j::w) (insert 0 (lift R)) = keep w R := by
        simp [keep, lift, List.finRange_succ, List.filter_map, List.map_map, Function.comp_def]
      have shiftLift (R : Finset (Fin w.length)) : shift (j::w) (lift R) = shift w R := by
        simp only [shift, lift]
        calc
          _ = ∑ i ∈ R, (((j::w).get i.succ : ℤ)+1) :=
            Finset.sum_image (f := fun i : Fin (j::w).length => ((j::w).get i : ℤ) + 1)
              (g := Fin.succ) (Fin.succ_injective w.length).injOn
          _ = _ := by simp
      have shiftInsert (R : Finset (Fin w.length)) :
          shift (j::w) (insert 0 (lift R)) = (j : ℤ) + 1 + shift w R := by
        simp only [shift]
        rw [Finset.sum_insert (nz R)]
        change (j : ℤ) + 1 + shift (j::w) (lift R) = (j : ℤ)+1+shift w R
        rw [shiftLift]
      have weightLift (R : Finset (Fin w.length)) : weight (j::w) (lift R) = weight w R := by
        simp only [weight, lift]
        calc
          _ = ∏ i ∈ R, ((-1 : ℂ)^((j::w).get i.succ)*lambda) :=
            Finset.prod_image (Fin.succ_injective w.length).injOn
          _ = _ := by simp
      have weightInsert (R : Finset (Fin w.length)) :
          weight (j::w) (insert 0 (lift R)) = ((-1 : ℂ)^j * lambda) * weight w R := by
        change (∏ i ∈ insert 0 (lift R), ((-1 : ℂ)^((j::w).get i)*lambda)) = _
        rw [Finset.prod_insert (nz R)]
        change ((-1 : ℂ)^j * lambda) * weight (j::w) (lift R) = _
        rw [weightLift]
      have maskSplit (f : Finset (Fin (j::w).length) → Fock) :
          (∑ R ∈ (Finset.univ : Finset (Fin (j::w).length)).powerset, f R) =
          (∑ R ∈ masks, f (lift R)) + (∑ R ∈ masks, f (insert 0 (lift R))) := by
        have hu : (Finset.univ : Finset (Fin (j::w).length)) =
            insert 0 ((Finset.univ : Finset (Fin w.length)).image Fin.succ) := by
          ext i
          refine Fin.cases ?_ (fun k => ?_) i <;> simp
        rw [hu, Finset.sum_powerset_insert (by simp)]
        simp only [Finset.powerset_image]
        congr 1
        · exact Finset.sum_image (Finset.image_injective (Fin.succ_injective w.length)).injOn
        · exact Finset.sum_image (Finset.image_injective (Fin.succ_injective w.length)).injOn
      -- Both bounds are statewise, before the coefficient expansions and exchanges.
      have rawForward := forwardFinite A (chargedWordField lambda w) m x
      have rawReverse := reverseFinite A (chargedWordField lambda w) m x
      have transformedForward (R : Finset (Fin w.length)) : Function.HasFiniteSupport
          (fun k : ℕ => weight w R •
            (A [[-(k : ℤ)-1]]) (((wordField (keep w R)) [[(m-shift w R)+k]]) x)) :=
        (forwardFinite A (wordField (keep w R)) (m-shift w R) x).smul_right
          (fun _ => weight w R)
      have transformedReverse (R : Finset (Fin w.length)) : Function.HasFiniteSupport
          (fun k : ℕ => weight w R •
            ((wordField (keep w R)) [[(m-shift w R)-k-1]]) ((A [[k]]) x)) :=
        (reverseFinite A (wordField (keep w R)) (m-shift w R) x).smul_right
          (fun _ => weight w R)
      have leftExpansion (k : ℕ) :
          (A [[-(k : ℤ)-1]]) ((chargedWordField lambda w [[m+k]]) x) =
          ∑ R ∈ masks, weight w R •
            (A [[-(k : ℤ)-1]]) (((wordField (keep w R)) [[(m-shift w R)+k]]) x) := by
        rw [ih]
        simp only [map_sum, map_smul]
        apply Finset.sum_congr rfl
        intro R hR
        rw [show m + (k : ℤ) - shift w R = (m-shift w R)+k by omega]
      -- The induction hypothesis is used on the actual intermediate charged-mode state.
      have rightExpansion (k : ℕ) :
          (chargedWordField lambda w [[m-k-1]]) ((A [[k]]) x) =
          ∑ R ∈ masks, weight w R •
            ((wordField (keep w R)) [[(m-shift w R)-k-1]]) ((A [[k]]) x) := by
        rw [ih]
        apply Finset.sum_congr rfl
        intro R hR
        rw [show m - (k : ℤ) - 1 - shift w R = (m-shift w R)-k-1 by omega]
      rw [chargedWordField, (normalMinusOne A (chargedWordField lambda w)).2]
      rw [exchange _ masks _ _ rawForward (by intro R hR; exact transformedForward R)
        leftExpansion]
      rw [exchange _ masks _ _ rawReverse (by intro R hR; exact transformedReverse R)
        rightExpansion]
      rw [← Finset.sum_add_distrib, maskSplit, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro R hR
      rw [← smul_finsum' (weight w R)
          (forwardFinite A (wordField (keep w R)) (m-shift w R) x),
        ← smul_finsum' (weight w R)
          (reverseFinite A (wordField (keep w R)) (m-shift w R) x),
        ← smul_add, ← (normalMinusOne A (wordField (keep w R))).2]
      rw [normalCharge, keepLift, keepInsert, shiftLift, shiftInsert, weightLift, weightInsert]
      simp only [wordField, smul_add, smul_smul]
      rw [show m - shift w R - (j : ℤ) - 1 = m - ((j : ℤ)+1+shift w R) by omega]
      rw [mul_comm (weight w R)]
  change ((chargedY lambda u) [[n]]) v =
    ∑ e ∈ u.support, ∑ R ∈ (Finset.univ : Finset (Fin (occurrences e).length)).powerset,
      (AddMonoidAlgebra.coeff u e * weight (occurrences e) R) •
        ((wordField (keep (occurrences e) R)) [[n-shift (occurrences e) R]]) v
  -- Basis coordinates are the actual polynomial coefficients.
  rw [chargedY, (MvPolynomial.basisMonomials ℕ ℂ).constr_apply]
  change ((∑ e ∈ u.support,
    AddMonoidAlgebra.coeff u e • chargedWordField lambda (occurrences e)) [[n]]) v = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, LinearMap.sum_apply,
    LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro e he
  rw [wordFormula, Finset.smul_sum]
  simp only [smul_smul]

end D5.S3.VertexAlgebra.PolynomialFockChargedStateField
