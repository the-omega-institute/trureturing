import OmegaMath.NumberTheory.GRH.Lib.DiscreteSeries.FlenstedJensen.FlenstedJensenInvariance
import OmegaMath.NumberTheory.GRH.Lib.DiscreteSeries.Theta.JointHarmonicUnique
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! One general lemma (a derivation applied to a product of determinants), then joint harmonics for
`FockDualPair`.

Part of: Theta correspondence of discrete series for real unitary dual pairs; joint harmonics (known
result; see Lib.DiscreteSeries.Theta.LocalThetaCorrespondence).

This file: Products of minors are joint harmonics; existence for matched parameters. -/


open Matrix MvPolynomial Finset Units Function Fischer
variable {L} [Fintype L] {I : L → Type} [∀ t, Fintype (I t)] {R C} [Fintype R] [Fintype C] {ε ε' ι}
  [Fintype ι] (T : @FockDualPair R C ε ε' ι) (l ν : HCParam ε) {l' ν'} (ρ κ : ∀ t, I t → _)

omit [Fintype R] in
lemma derivation_prod_det (D : Derivation ℂ (MvPolynomial R ℂ) _) (N M : ∀ t, Matrix (I t) _ _)
    (h : ∀ t i k, D (M t k i) = ∑ j, N t i j • M t k j) :
    D (∏ t, det (M t)) = (∑ t, ∑ i, N t i i) * ∏ t, det (M t) := by
  have {t} : D (M t).det = ∑ i, N t i i • (M t).det := by
    have {s f} : D (s.prod f) = ∑ i ∈ s, s.prod (update f (i : I t) (D (f i))) := by
      induction s using cons_induction <;> simp_all [mul_sum, prod_update_of_notMem]
      grind [sum_congr]
    simp_all [det_apply', updateCol, ↓← det_updateCol_sum, update_apply, mul_sum, @sum_comm (I t)]
  induction @univ L _ using cons_induction <;> simp_all [← sum_mul]; ring

/-- Finitely many layers of paired rows ρ_t (distinct) and columns κ_t, with one column sign on
layers sharing a row, rows closed under moving outwards in l, and total weight ν. -/
structure IsLayering where
  injective t : Injective (ρ t)
  sign_eq t u i j k m : ρ t i = ρ u j → ε' (κ t k) = ε' (κ u m)
  closed t i r : ε r = ε (ρ t i) → 0 < T.varSign (ρ t i, κ t i) * (l r - l (ρ t i)) → ∃ j, ρ t j = r
  weight_eq r : ν r = T.vacuumWeight (ε r) + ∑ t, ∑ i with ρ t i = r, (T.varSign (r, κ t i)).1

attribute [local grind] pairSign IsLayering int_unit_val_eq_one_or_neg_one IsMatch HasGap
  sum_eq_zero val_mul Units.val_neg
variable {T l ν ρ κ} (H : IsLayering T l ν ρ κ) (hm : IsMatch T l l')
include H

omit [Fintype ι] in
lemma IsLayering.isKHighest_and_isHarmonic {P} (hP : P = ∏ t, det (of fun i j ↦
  X (T.varEquiv (ρ t i, κ t j)))ᵀ) : l.IsKHighest T.oscRows ν P ∧ T.swap.IsHarmonic P := by
  simp +contextual [-pairSign, ← C_mul', oscRows_E_eq_polarisation_sub, polarisation,
    (by simpa [-sum_boole, -pairSign] using (fun a b (s : ℤˣ) (_ : a = b ∨ ε a = ε b ∧ s * l b < s *
    l a) ↦ hP ▸ derivation_prod_det (.mk' (∑ c with T.varSign (b, c) = s, @X ℂ _ _ (T.varEquiv (a,
    c)) • (pderiv (T.varEquiv (b, c))).1) (by simp [mul_sum, ← sum_add_distrib]; grind))
    (fun t i j ↦ ite (ρ t i = b ∧ ρ t j = a ∧ T.varSign (b,
    κ t i) = s) 1 0) _ (by obtain ⟨_, rfl⟩ | _ := em <| ∃ j, ρ · j = a <;> simp [(H.1 _).eq_iff] <;>
    grind) :)), H.4, ← sub_mul, ← add_mul, ← sum_sub_distrib, -sum_boole, add_comm, sum_filter]
  use ⟨fun _ ↦ .inl (by congr!; split_ifs <;> simp_all), by grind⟩
  grind [_root_.pderiv_comm, units_ne_neg_self (R := ℤ), show ∀ x,
    (∀ t i j, (ρ t i, κ t j) ≠ x) → pderiv (T.varEquiv x) P = 0 by
    simp_all [derivation_prod_det _ 0]]

omit [Fintype ι] in
/-- If (ρ, κ) are layers as in `IsLayering` for the rows and (κ, ρ) for the columns, the product of
the minors on (ρ_t, κ_t) is nonzero, highest of weight ν for rows and ν' for columns, and
satisfies `IsHarmonic` both ways. -/
lemma IsLayering.joint_highest_prod_det {ν'} (H' : IsLayering T.swap l' ν' κ ρ) {P} (hP : P =
  ∏ t, det (of fun i j ↦ X (T.varEquiv (ρ t i, κ t j)))) : T.IsJointHighest l l' P ν ν' :=
  ⟨by simpa [*, prod_eq_zero_iff, det_apply] using (fun t ↦ (rename_injective _
  (T.varEquiv.injective.comp ((H.1 t).prodMap (H'.1 t)))).ne (det_mvPolynomialX_ne_zero _ ℂ)),
  and_assoc.1 ⟨H'.isKHighest_and_isHarmonic hP, H.isKHighest_and_isHarmonic (by simpa)⟩⟩

omit H
include hm

/-- For matching parameters λ, λ', rows and columns of the matched pairs (r, c) form layers
(`IsLayering`) of total weight Λ, one layer for each m < |Λ_r − v_r| (v the vacuum weight) and
each pair of signs, relabelled by the permutation s. -/
lemma IsMatch.isLayering (s : Equiv.Perm _) {w} (hw : w = (fun (r, c) ↦ ite (T.IsMatchedPair l l' r
  c) (T.relWeight l r).natAbs 0) ∘ T.varEquiv.symm) : IsLayering T l l.lowestKType (fun (t :
  Fin (univ.sup w) × _) (x : {x // t.1 < w x ∧ s ((T.varEquiv.symm x).map ε ε') = t.2}) ↦
  (T.varEquiv.symm x).1) fun _ x ↦ (T.varEquiv.symm x).2 := by
  have := hm.1.isKDominant_lowestKType; simp_all [IsKDominant]
  have {r} : T.relWeight l r ≠ 0 → ∃ c, T.IsMatchedPair l l' r c ∧ T.varSign (r, c) = (T.relWeight l
    r).sign := by grind [by simpa using And.intro (hm.sign_mul_lowestKType_sub_nonneg r 1)
                              (hm.sign_mul_lowestKType_sub_nonneg r (-1))]
  constructor; rotate_right; intro r
  rw [sum_sigma', sum_of_injOn (·.1.1.1), sum_const (T.relWeight l r).sign,
    card_range (T.relWeight l r).natAbs]
  all_goals simp [*, reindex_equiv T.varEquiv, Injective, Set.InjOn, Set.MapsTo,
    Fin.exists_iff, Sigma.forall, Sigma.subtype_ext_iff]; grind [Units.ext, s.injective]

/-- If the parameters l, l' match for T (`IsMatch`), then there is a joint harmonic polynomial Φ in
the sense of `IsJointHarmonic`: nonzero and highest for both lowest K-types Λ and Λ'.

Known result: Theta correspondence of discrete series for real unitary dual pairs; joint
harmonics. -/
lemma IsMatch.exists_isJointHarmonic : ∃ Φ, IsJointHarmonic T l l' Φ :=
  ⟨_, hm, (hm.isLayering 1 rfl).joint_highest_prod_det
  (hm.swap.isLayering (.prodComm ..) (by grind [lowestKType_sub_vacuumWeight_eq_neg])) rfl⟩
