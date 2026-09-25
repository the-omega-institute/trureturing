/- GID: D5/S3/Combinatorics/Posets/GradedGamma/OrdinalSumWShift
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Posets/GradedGamma/OrdinalSumWShift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.WellKnown]
   utility: none
   digest: A strict ordinal join shifts the full weak-join descent enumerator by one. -/

import D5.S3.Combinatorics.Posets.GradedGamma.OrdinalSumProduct

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Posets.GradedGamma

open D5.S3.Combinatorics.Posets.PPartitions
noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β]
    [PartialOrder α] [PartialOrder β]

/-- A strict ordinal join contributes exactly one descent relative to the
weak join, measured over all extensions rather than a chosen extension. -/
theorem strictSum_W_eq_X_mul_weakSum_W [Nonempty α] [Nonempty β]
    (ω : α → ℕ) (ν : β → ℕ)
    (hω : Function.Injective ω) (hν : Function.Injective ν)
    (hbω : ∀ x, ω x < Fintype.card α)
    (hbν : ∀ y, ν y < Fintype.card β) :
    WPolynomial (strictSumLabel ω ν) =
      Polynomial.X * WPolynomial (weakSumLabel ω ν) := by
  classical
  have hweak : Function.Injective (weakSumLabel ω ν) := by
    intro x y heq
    induction x using Lex.rec with
    | h sx =>
      induction y using Lex.rec with
      | h sy =>
        cases sx with
        | inl x =>
          cases sy with
          | inl y =>
              exact congrArg (fun t : α => toLex (Sum.inl t))
                (hω (by simpa [weakSumLabel] using heq))
          | inr y =>
              have h := hbω x
              have hn : ω x = Fintype.card α + ν y := by
                simpa [weakSumLabel] using heq
              omega
        | inr x =>
          cases sy with
          | inl y =>
              have h := hbω y
              have hn : Fintype.card α + ν x = ω y := by
                simpa [weakSumLabel] using heq
              omega
          | inr y =>
              exact congrArg (fun t : β => toLex (Sum.inr t))
                (hν (by simpa [weakSumLabel] using heq))
  have hstrict : Function.Injective (strictSumLabel ω ν) := by
    intro x y heq
    induction x using Lex.rec with
    | h sx =>
      induction y using Lex.rec with
      | h sy =>
        cases sx with
        | inl x =>
          cases sy with
          | inl y =>
              exact congrArg (fun t : α => toLex (Sum.inl t))
                (hω (by simpa [strictSumLabel] using heq))
          | inr y =>
              have h := hbν y
              have hn : Fintype.card β + ω x = ν y := by
                simpa [strictSumLabel] using heq
              omega
        | inr x =>
          cases sy with
          | inl y =>
              have h := hbν x
              have hn : ν x = Fintype.card β + ω y := by
                simpa [strictSumLabel] using heq
              omega
          | inr y =>
              exact congrArg (fun t : β => toLex (Sum.inr t))
                (hν (by simpa [strictSumLabel] using heq))
  let U := (PowerSeries.invOneSubPow ℤ
    (Fintype.card (α ⊕ₗ β) + 1)).val
  have hcount (q : ℕ) :
      Fintype.card (PPartition (strictSumLabel ω ν) (q + 1)) =
      Fintype.card (PPartition (weakSumLabel ω ν) q) :=
    Fintype.card_congr (strictWeakPartitionEquiv ω ν hbω hbν q)
  have hzero : Fintype.card (PPartition (weakSumLabel ω ν) 0) = 0 := by
    let x : α ⊕ₗ β := toLex (.inl (Classical.choice inferInstance))
    have hempty : IsEmpty (PPartition (weakSumLabel ω ν) 0) :=
      ⟨fun p => (p.1 x).elim0⟩
    exact Fintype.card_eq_zero
  have hseries : PowerSeries.X *
      ((WPolynomial (weakSumLabel ω ν) : PowerSeries ℤ) * U) =
      (WPolynomial (strictSumLabel ω ν) : PowerSeries ℤ) * U := by
    rw [← pPartition_series (weakSumLabel ω ν) hweak,
      ← pPartition_series (strictSumLabel ω ν) hstrict]
    ext q
    rw [← pow_one (PowerSeries.X : PowerSeries ℤ),
      PowerSeries.coeff_X_pow_mul']
    cases q with
    | zero =>
        simp [hcount 0, hzero]
    | succ q =>
        simp only [Nat.one_le_iff_ne_zero, Nat.succ_ne_zero, if_true,
          Nat.succ_sub_one, PowerSeries.coeff_mk]
        exact congrArg (fun k : ℕ => (k : ℤ)) (hcount (q + 1)) |>.symm
  have hcancel : PowerSeries.X *
      (WPolynomial (weakSumLabel ω ν) : PowerSeries ℤ) =
      (WPolynomial (strictSumLabel ω ν) : PowerSeries ℤ) := by
    have h := congrArg (fun p : PowerSeries ℤ =>
      p * (PowerSeries.invOneSubPow ℤ
        (Fintype.card (α ⊕ₗ β) + 1)).inv) hseries
    simpa only [mul_assoc, U, (PowerSeries.invOneSubPow ℤ
      (Fintype.card (α ⊕ₗ β) + 1)).val_inv, mul_one] using h
  apply Polynomial.ext
  intro k
  have hk := congrArg (PowerSeries.coeff k) hcancel
  have hcast :
      ((Polynomial.X * WPolynomial (weakSumLabel ω ν) : Polynomial ℤ) :
        PowerSeries ℤ) =
      PowerSeries.X * (WPolynomial (weakSumLabel ω ν) : PowerSeries ℤ) := by
    simp
  rw [← hcast] at hk
  simpa only [Polynomial.coeff_coe] using hk.symm

private def adjacentIndexEquiv (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    Fin (n + m - 1) ≃ (Fin (n - 1) ⊕ Fin 1) ⊕ Fin (m - 1) :=
  (finCongr (show n + m - 1 = (n - 1 + 1) + (m - 1) by omega)).trans <|
    finSumFinEquiv.symm.trans <|
      Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl _)

/-- Internal descents of an ordinal join are exactly the descents of the
two constituent extensions; the weak join itself has no descent. -/
theorem ordinalAppendExtension_descentCard [Nonempty α] [Nonempty β]
    (ω : α → ℕ) (ν : β → ℕ)
    (u : EnumeratingExtension α) (v : EnumeratingExtension β)
    (hboundary : ω (u ⟨Fintype.card α - 1, by
        have h : 0 < Fintype.card α := Fintype.card_pos
        omega⟩) < ν (v ⟨0, Fintype.card_pos⟩)) :
    descentCard (directSumLabel ω ν) (ordinalAppendExtension u v) =
      descentCard ω u + descentCard ν v := by
  classical
  let n := Fintype.card α
  let m := Fintype.card β
  have hn : 0 < n := Fintype.card_pos
  have hm : 0 < m := Fintype.card_pos
  have hc : Fintype.card (α ⊕ₗ β) = n + m := by
    exact (Fintype.card_congr (ofLex : α ⊕ₗ β ≃ α ⊕ β)).trans Fintype.card_sum
  let e := ordinalAppendExtension u v
  let E : Fin (Fintype.card (α ⊕ₗ β) - 1) ≃
      (Fin (n - 1) ⊕ Fin 1) ⊕ Fin (m - 1) :=
    (finCongr (congrArg (· - 1) hc)).trans (adjacentIndexEquiv n m hn hm)
  have hleft_index (i : Fin (n - 1)) :
      (E.symm (Sum.inl (Sum.inl i))).val = i.val := by
    change i.val = i.val
    rfl
  have hmiddle_index (i : Fin 1) :
      (E.symm (Sum.inl (Sum.inr i))).val = n - 1 := by
    change n - 1 + i.val = n - 1
    have hi : i.val = 0 := by omega
    omega
  have hright_index (i : Fin (m - 1)) :
      (E.symm (Sum.inr i)).val = n + i.val := by
    change n - 1 + 1 + i.val = n + i.val
    omega
  have hleft_value (i : Fin n) :
      e ((finCongr hc).symm (Fin.castAdd m i)) =
        toLex (.inl (u i)) := by
    change ((finCongr hc).trans
      (finSumFinEquiv.symm.trans ((Equiv.sumCongr u.1 v.1).trans toLex)))
        ((finCongr hc).symm (Fin.castAdd m i)) = _
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply,
      finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply]
    rfl
  have hright_value (i : Fin m) :
      e ((finCongr hc).symm (Fin.natAdd n i)) =
        toLex (.inr (v i)) := by
    change ((finCongr hc).trans
      (finSumFinEquiv.symm.trans ((Equiv.sumCongr u.1 v.1).trans toLex)))
        ((finCongr hc).symm (Fin.natAdd n i)) = _
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply,
      finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply]
    rfl
  have hleft (i : Fin (n - 1)) :
      descent (directSumLabel ω ν) e (E.symm (Sum.inl (Sum.inl i))) ↔
      descent ω u i := by
    unfold descent
    have hi := hleft_index i
    have h0 : e ⟨(E.symm (Sum.inl (Sum.inl i))).val, by omega⟩ =
        toLex (.inl (u ⟨i.val, by omega⟩)) := by
      have hk : (⟨(E.symm (Sum.inl (Sum.inl i))).val, by omega⟩ :
          Fin (Fintype.card (α ⊕ₗ β))) =
          (finCongr hc).symm (Fin.castAdd m (⟨i.val, by omega⟩ : Fin n)) :=
        Fin.ext hi
      rw [hk]
      exact hleft_value _
    have h1 : e ⟨(E.symm (Sum.inl (Sum.inl i))).val + 1, by omega⟩ =
        toLex (.inl (u ⟨i.val + 1, by omega⟩)) := by
      have hk : (⟨(E.symm (Sum.inl (Sum.inl i))).val + 1, by omega⟩ :
          Fin (Fintype.card (α ⊕ₗ β))) =
          (finCongr hc).symm (Fin.castAdd m (⟨i.val + 1, by omega⟩ : Fin n)) :=
        Fin.ext (by
          change (E.symm (Sum.inl (Sum.inl i))).val + 1 = i.val + 1
          omega)
      rw [hk]
      exact hleft_value _
    rw [h0, h1]
    rfl
  have hmiddle (i : Fin 1) :
      ¬ descent (directSumLabel ω ν) e (E.symm (Sum.inl (Sum.inr i))) := by
    have hi := hmiddle_index i
    have h0 : e ⟨(E.symm (Sum.inl (Sum.inr i))).val, by omega⟩ =
        toLex (.inl (u ⟨n - 1, by omega⟩)) := by
      have hk : (⟨(E.symm (Sum.inl (Sum.inr i))).val, by omega⟩ :
          Fin (Fintype.card (α ⊕ₗ β))) =
          (finCongr hc).symm
            (Fin.castAdd m (⟨n - 1, by omega⟩ : Fin n)) := Fin.ext hi
      rw [hk]
      exact hleft_value _
    have h1 : e ⟨(E.symm (Sum.inl (Sum.inr i))).val + 1, by omega⟩ =
        toLex (.inr (v ⟨0, hm⟩)) := by
      have hk : (⟨(E.symm (Sum.inl (Sum.inr i))).val + 1, by omega⟩ :
          Fin (Fintype.card (α ⊕ₗ β))) =
          (finCongr hc).symm (Fin.natAdd n (⟨0, hm⟩ : Fin m)) :=
        Fin.ext (by
          change (E.symm (Sum.inl (Sum.inr i))).val + 1 = n
          omega)
      rw [hk]
      exact hright_value _
    unfold descent
    rw [h0, h1]
    change ¬ ω (u ⟨n - 1, by omega⟩) > ν (v ⟨0, hm⟩)
    have hb : ω (u ⟨n - 1, by omega⟩) < ν (v ⟨0, hm⟩) := hboundary
    omega
  have hright (i : Fin (m - 1)) :
      descent (directSumLabel ω ν) e (E.symm (Sum.inr i)) ↔
      descent ν v i := by
    unfold descent
    have hi := hright_index i
    have h0 : e ⟨(E.symm (Sum.inr i)).val, by omega⟩ =
        toLex (.inr (v ⟨i.val, by omega⟩)) := by
      have hk : (⟨(E.symm (Sum.inr i)).val, by omega⟩ :
          Fin (Fintype.card (α ⊕ₗ β))) =
          (finCongr hc).symm
            (Fin.natAdd n (⟨i.val, by omega⟩ : Fin m)) := Fin.ext hi
      rw [hk]
      exact hright_value _
    have h1 : e ⟨(E.symm (Sum.inr i)).val + 1, by omega⟩ =
        toLex (.inr (v ⟨i.val + 1, by omega⟩)) := by
      have hk : (⟨(E.symm (Sum.inr i)).val + 1, by omega⟩ :
          Fin (Fintype.card (α ⊕ₗ β))) =
          (finCongr hc).symm
            (Fin.natAdd n (⟨i.val + 1, by omega⟩ : Fin m)) :=
        Fin.ext (by
          change (E.symm (Sum.inr i)).val + 1 = n + (i.val + 1)
          omega)
      rw [hk]
      exact hright_value _
    rw [h0, h1]
    rfl
  have hsum :
      (∑ i : Fin (Fintype.card (α ⊕ₗ β) - 1),
        if descent (directSumLabel ω ν) e i then 1 else 0) =
      (∑ i : Fin (n - 1), if descent ω u i then 1 else 0) +
      (∑ i : Fin (m - 1), if descent ν v i then 1 else 0) := by
    calc
      (∑ i : Fin (Fintype.card (α ⊕ₗ β) - 1),
        if descent (directSumLabel ω ν) e i then 1 else 0) =
        ∑ t : (Fin (n - 1) ⊕ Fin 1) ⊕ Fin (m - 1),
          if descent (directSumLabel ω ν) e (E.symm t) then 1 else 0 := by
          exact (Equiv.sum_comp E.symm _).symm
      _ = (∑ i : Fin (n - 1), if descent ω u i then 1 else 0) +
          (∑ i : Fin (m - 1), if descent ν v i then 1 else 0) := by
            rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
            simp only [hleft, hright, hmiddle, ite_false]
            simp
  calc
    descentCard (directSumLabel ω ν) (ordinalAppendExtension u v) =
        ∑ i : Fin (Fintype.card (α ⊕ₗ β) - 1),
          if descent (directSumLabel ω ν) e i then 1 else 0 := by
            simpa [descentCard, descentFinset, e] using
              (Finset.sum_boole (descent (directSumLabel ω ν) e) Finset.univ :
                (∑ i : Fin (Fintype.card (α ⊕ₗ β) - 1),
                  if descent (directSumLabel ω ν) e i then 1 else 0) =
                (Finset.univ.filter (descent (directSumLabel ω ν) e)).card).symm
    _ = (∑ i : Fin (n - 1), if descent ω u i then 1 else 0) +
        (∑ i : Fin (m - 1), if descent ν v i then 1 else 0) := hsum
    _ = descentCard ω u + descentCard ν v := by
      simp only [Finset.sum_boole]
      rfl

/-- The complete descent enumerator of a weak ordinal join factors over its
two nonempty blocks. -/
theorem weakSum_W_mul [Nonempty α] [Nonempty β]
    (ω : α → ℕ) (ν : β → ℕ)
    (hbω : ∀ x, ω x < Fintype.card α) :
    WPolynomial (weakSumLabel ω ν) = WPolynomial ω * WPolynomial ν := by
  classical
  have hdescent (u : EnumeratingExtension α) (v : EnumeratingExtension β) :
      descentCard (weakSumLabel ω ν) (ordinalAppendExtension u v) =
        descentCard ω u + descentCard ν v := by
    have hb : ω (u ⟨Fintype.card α - 1, by
        have h : 0 < Fintype.card α := Fintype.card_pos
        omega⟩) < Fintype.card α + ν (v ⟨0, Fintype.card_pos⟩) := by
      have h := hbω (u ⟨Fintype.card α - 1, by
        have h : 0 < Fintype.card α := Fintype.card_pos
        omega⟩)
      omega
    have h := ordinalAppendExtension_descentCard ω
      (fun y => Fintype.card α + ν y) u v hb
    change descentCard (weakSumLabel ω ν) (ordinalAppendExtension u v) =
      descentCard ω u + descentCard (fun y => Fintype.card α + ν y) v at h
    have hr : descentCard (fun y => Fintype.card α + ν y) v =
        descentCard ν v := by
      unfold descentCard descentFinset
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, descent]
      omega
    rw [hr] at h
    exact h
  have hsum :
      (∑ e : EnumeratingExtension (α ⊕ₗ β),
        (Polynomial.X : Polynomial ℤ) ^
          descentCard (weakSumLabel ω ν) e) =
      ∑ p : EnumeratingExtension α × EnumeratingExtension β,
        (Polynomial.X : Polynomial ℤ) ^
          descentCard (weakSumLabel ω ν)
            (ordinalAppendExtension p.1 p.2) := by
    symm
    apply Fintype.sum_equiv ordinalExtensionEquiv.symm
    intro p
    rfl
  unfold WPolynomial
  rw [hsum]
  simp only [Fintype.sum_prod_type]
  simp_rw [hdescent, pow_add]
  rw [Fintype.sum_mul_sum]

end
end D5.S3.Combinatorics.Posets.GradedGamma
