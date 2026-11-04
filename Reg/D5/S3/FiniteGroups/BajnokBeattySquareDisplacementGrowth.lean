import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattySquareDisplacementGrowth
import Reg.Support.DependentFamily

set_option maxRecDepth 4000

namespace Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementGrowth

open _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementGrowth
open _root_.D5.S3.FiniteGroups.BajnokBeattyExtremalGrowth
open _root_.D5.S3.FiniteGroups.NearSquareLatticeRigidity
open _root_.D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

/- All-odd-q Reg source attempt. The complete original theorem
is retained as the Law; only the two actual ball-cardinality readouts vary.
issue25856: raw source-selection coordinates, exact occurrence reconstruction
and the State=Nat source tie remain unencoded/unverified. The Contract entry
below intentionally supplies no sourceSelection or escapeFrom certificate.
Neither this source attempt nor the new entry is declared_validated. -/

abbrev squareGrowthSignature : Signature where
  Params := Σ _p : ℤ, Σ _q : ℤ, ℤ
  State _ := ℕ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def squareGrowthOne (p q t : ℤ) (r : ℕ) : ℕ :=
    let m : ℤ := 2*q*t-1
    let D : ℤ := (m^2-q^2)/2
    let H := ZMod p.natAbs × ZMod (p*D).natAbs
    let v11 : Plane := ![p*(m-1)/2, p*(m+1)/2]
    let v21 : Plane := ![p*(m-q^2)/2, -(p*(m+q^2)/2)]
    let v1q : Plane := ![p*(m-q)/2, p*(m+q)/2]
    let v2q : Plane := ![p*(m-q)/2, -(p*(m+q)/2)]
    let K1 : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v11, v21])
    let Kq : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v1q, v2q])
    let G1 := Plane ⧸ K1
    let Gq := Plane ⧸ Kq
    let F1 : Plane →+ G1 := K1.mkQ.toAddMonoidHom
    let Fq : Plane →+ Gq := Kq.mkQ.toAddMonoidHom
    let E : Plane ≃ₗ[ℤ] (ℤ × ℤ) := LinearEquiv.finTwoArrow ℤ ℤ
    let f1 : (ℤ × ℤ) →+ G1 := F1.comp E.symm.toLinearMap.toAddMonoidHom
    let fq : (ℤ × ℤ) →+ Gq := Fq.comp E.symm.toLinearMap.toAddMonoidHom
    let s : ℕ := ((p*m-1)/2).toNat
    let c1 : ℕ → ℕ := fun r => ((leeDiamond r).image f1).card
    let cq : ℕ → ℕ := fun r => ((leeDiamond r).image fq).card
    let gap : ℕ → ℤ := fun r => (c1 r : ℤ)-(cq r : ℤ)
    let M : ℤ := (q-1)^2*p^2/2-(q-1)*p+1
    c1 r

noncomputable def squareGrowthEqual (p q t : ℤ) (r : ℕ) : ℕ :=
    let m : ℤ := 2*q*t-1
    let D : ℤ := (m^2-q^2)/2
    let H := ZMod p.natAbs × ZMod (p*D).natAbs
    let v11 : Plane := ![p*(m-1)/2, p*(m+1)/2]
    let v21 : Plane := ![p*(m-q^2)/2, -(p*(m+q^2)/2)]
    let v1q : Plane := ![p*(m-q)/2, p*(m+q)/2]
    let v2q : Plane := ![p*(m-q)/2, -(p*(m+q)/2)]
    let K1 : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v11, v21])
    let Kq : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v1q, v2q])
    let G1 := Plane ⧸ K1
    let Gq := Plane ⧸ Kq
    let F1 : Plane →+ G1 := K1.mkQ.toAddMonoidHom
    let Fq : Plane →+ Gq := Kq.mkQ.toAddMonoidHom
    let E : Plane ≃ₗ[ℤ] (ℤ × ℤ) := LinearEquiv.finTwoArrow ℤ ℤ
    let f1 : (ℤ × ℤ) →+ G1 := F1.comp E.symm.toLinearMap.toAddMonoidHom
    let fq : (ℤ × ℤ) →+ Gq := Fq.comp E.symm.toLinearMap.toAddMonoidHom
    let s : ℕ := ((p*m-1)/2).toNat
    let c1 : ℕ → ℕ := fun r => ((leeDiamond r).image f1).card
    let cq : ℕ → ℕ := fun r => ((leeDiamond r).image fq).card
    let gap : ℕ → ℤ := fun r => (c1 r : ℤ)-(cq r : ℤ)
    let M : ℤ := (q-1)^2*p^2/2-(q-1)*p+1
    cq r

noncomputable def squareActual : Realization squareGrowthSignature :=
  realize squareGrowthSignature
    (fun i pqt r => if i = 0 then squareGrowthOne pqt.1 pqt.2.1 pqt.2.2 r
      else squareGrowthEqual pqt.1 pqt.2.1 pqt.2.2 r)
    (fun e => nomatch e)

noncomputable def squareRejected (i : Fin 2) : Realization squareGrowthSignature :=
  realize squareGrowthSignature
    (fun j pqt r => if j = i then 0 else squareActual.readout j pqt r)
    (fun e => nomatch e)

abbrev squareGrowthArena : Arena where
  signature := squareGrowthSignature
  Law R := ∀ (p q t : ℤ)
    (hp3 : 3 ≤ p) (hpo : Odd p) (hq3 : 3 ≤ q) (hqo : Odd q)
    (ht : q+1 ≤ 2*t),
    let m : ℤ := 2*q*t-1
    let D : ℤ := (m^2-q^2)/2
    let H := ZMod p.natAbs × ZMod (p*D).natAbs
    let v11 : Plane := ![p*(m-1)/2, p*(m+1)/2]
    let v21 : Plane := ![p*(m-q^2)/2, -(p*(m+q^2)/2)]
    let v1q : Plane := ![p*(m-q)/2, p*(m+q)/2]
    let v2q : Plane := ![p*(m-q)/2, -(p*(m+q)/2)]
    let K1 : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v11, v21])
    let Kq : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v1q, v2q])
    let G1 := Plane ⧸ K1
    let Gq := Plane ⧸ Kq
    let F1 : Plane →+ G1 := K1.mkQ.toAddMonoidHom
    let Fq : Plane →+ Gq := Kq.mkQ.toAddMonoidHom
    let E : Plane ≃ₗ[ℤ] (ℤ × ℤ) := LinearEquiv.finTwoArrow ℤ ℤ
    let f1 : (ℤ × ℤ) →+ G1 := F1.comp E.symm.toLinearMap.toAddMonoidHom
    let fq : (ℤ × ℤ) →+ Gq := Fq.comp E.symm.toLinearMap.toAddMonoidHom
    let s : ℕ := ((p*m-1)/2).toNat
    let c1 : ℕ → ℕ := fun r => R.readout 0 ⟨p,q,t⟩ r
    let cq : ℕ → ℕ := fun r => R.readout 1 ⟨p,q,t⟩ r
    let gap : ℕ → ℤ := fun r => (c1 r : ℤ)-(cq r : ℤ)
    let M : ℤ := (q-1)^2*p^2/2-(q-1)*p+1
    ∃ (e1 : G1 ≃+ H) (eq : Gq ≃+ H),
      (∀ z : Plane, e1 (F1 z) =
        (((-z 0+z 1 : ℤ) : ZMod p.natAbs),
          ((-(q*t)*z 0+(q*t-1)*z 1 : ℤ) : ZMod (p*D).natAbs))) ∧
      (∀ z : Plane, eq (Fq z) =
        ((((-2*t-1)*z 0+(2*t-1)*z 1 : ℤ) : ZMod p.natAbs),
          ((-(q*t+(q-1)/2)*z 0+(q*t-(q+1)/2)*z 1 : ℤ) :
            ZMod (p*D).natAbs))) ∧
      ¬ IsAddCyclic H ∧
      (∀ R : ℕ, LeeCovers F1 (R : ℤ) ↔ s ≤ R) ∧
      (∀ R : ℕ, LeeCovers Fq (R : ℤ) ↔ s ≤ R) ∧
      (∀ r : ℕ, cq r ≤ c1 r ∧
        (cq r < c1 r ↔ p*(m-q)/2 ≤ (r : ℤ) ∧ r < s)) ∧
      (∀ r : ℕ, r ≤ s →
        let δ : ℤ := p*m-(2*(r : ℤ)+1)
        0 ≤ δ ∧ Even δ ∧
          (q*p ≤ δ → gap r = 0) ∧
          (p ≤ δ → δ < q*p → 2*gap r = (q*p-δ)^2+1) ∧
          (δ < p → 2*gap r = (q-1)^2*p*δ)) ∧
      (∀ r : ℕ, s ≤ r →
        (c1 r : ℤ) = p^2*D ∧ (cq r : ℤ) = p^2*D) ∧
      (∀ r : ℕ, gap r ≤ M) ∧
      (∀ r : ℕ, gap r = M ↔ (r : ℤ) = p*(m-1)/2-1) ∧
      (0 ≤ p*(m-1)/2-1) ∧
      (∃! r : ℕ, gap r = M) ∧
      gap (s-1) = (q-1)^2*p ∧
      ¬ ∃ e : G1 ≃+ Gq,
        e (F1 ![1, 0]) = Fq ![1, 0] ∧
        e (F1 ![0, 1]) = Fq ![0, 1]

private theorem square_peak_positive (p q : ℤ) (hqo : Odd q) :
    0 < (q-1)^2*p^2/2-(q-1)*p+1 := by
  let A : ℤ := (q-1)*p
  have hAeven : Even A := (hqo.sub_odd odd_one).mul_right p
  have hsquare : (q-1)^2*p^2 = A^2 := by dsimp only [A]; ring
  have hhalf : 2*(A^2/2) = A^2 := by
    have hd : (2 : ℤ) ∣ A^2 := by
      simpa only [pow_two] using (hAeven.mul_right A).two_dvd
    simpa only [mul_comm] using Int.ediv_mul_cancel hd
  rw [hsquare]
  change 0 < A^2/2-A+1
  nlinarith only [hhalf, sq_nonneg (A-1)]

private theorem square_actual_law : squareGrowthArena.Law squareActual := by
  exact same_group_square_displacement_growth

-- Every admissible fiber gives the two honest interventions, not a sampled Law.
private theorem square_rejected_law_at (i : Fin 2) (p q t : ℤ)
    (hp3 : 3 ≤ p) (hpo : Odd p) (hq3 : 3 ≤ q) (hqo : Odd q)
    (ht : q+1 ≤ 2*t) : ¬ squareGrowthArena.Law (squareRejected i) := by
  intro h
  obtain ⟨e1, eq, he1, heq, hn, hd1, hdq, ho, hreg, hfull,
    hbound, hpeak, hpeakNonneg, hunique, hpen, hmarked⟩ :=
      h p q t hp3 hpo hq3 hqo ht
  have hMpos := square_peak_positive p q hqo
  fin_cases i
  · obtain ⟨r, hr, _⟩ := hunique
    have he : -(squareGrowthEqual p q t r : ℤ) =
        (q-1)^2*p^2/2-(q-1)*p+1 := by
      simpa [squareRejected, squareActual, realize] using hr
    have hc : 0 ≤ (squareGrowthEqual p q t r : ℤ) := Int.natCast_nonneg _
    omega
  · have ht2 : 2 ≤ t := by omega
    have hmq : 1 ≤ (2*q*t-1)-q := by
      have hprod := mul_nonneg (show 0 ≤ q-3 by omega) (show 0 ≤ 2*t-2 by omega)
      nlinarith only [hq3, ht2, hprod]
    have hlarge : q*p ≤ p*(2*q*t-1)-(2*(0 : ℤ)+1) := by
      have hprod := mul_le_mul_of_nonneg_left hmq (show 0 ≤ p by omega)
      nlinarith only [hp3, hprod]
    have hz := (hreg 0 (Nat.zero_le _)).2.2.1 hlarge
    have hz' : (squareGrowthOne p q t 0 : ℤ) = 0 := by
      simpa [squareRejected, squareActual, realize] using hz
    have hactual0 : squareGrowthOne p q t 0 = 1 := by
      simp [squareGrowthOne, leeDiamond, Finset.filter_singleton]
    omega

private theorem square_rejected_law (i : Fin 2) :
    ¬ squareGrowthArena.Law (squareRejected i) :=
  square_rejected_law_at i 3 3 2 (by norm_num) (by decide)
    (by norm_num) (by decide) (by norm_num)

-- Both actual readouts vary between radius zero and the actual diameter,
-- for every admissible p,q,t, including odd composite parameters.
private theorem square_dependence_at (p q t : ℤ)
    (hp3 : 3 ≤ p) (hpo : Odd p) (hq3 : 3 ≤ q) (hqo : Odd q)
    (ht : q+1 ≤ 2*t) (i : Fin 2) :
    squareActual.readout i ⟨p,q,t⟩ 0 ≠
      squareActual.readout i ⟨p,q,t⟩ (((p*(2*q*t-1)-1)/2).toNat) := by
  let m : ℤ := 2*q*t-1
  let D : ℤ := (m^2-q^2)/2
  let s : ℕ := ((p*m-1)/2).toNat
  obtain ⟨e1, eq, he1, heq, hn, hd1, hdq, ho, hreg, hfull,
    hbound, hpeak, hpeakNonneg, hunique, hpen, hmarked⟩ :=
      same_group_square_displacement_growth p q t hp3 hpo hq3 hqo ht
  have hballs := hfull s le_rfl
  have hmo : Odd m := ⟨q*t-1, by dsimp only [m]; ring⟩
  have hD2 : 2*D = m^2-q^2 := by
    have hd : (2 : ℤ) ∣ m^2-q^2 := by
      simpa only [pow_two] using ((hmo.mul hmo).sub_odd (hqo.mul hqo)).two_dvd
    simpa only [mul_comm] using Int.ediv_mul_cancel hd
  have hqm : q < m := by
    have hprod := mul_nonneg (show 0 ≤ q by omega) (show 0 ≤ 2*t-q-1 by omega)
    have hsq : q < q^2 := by nlinarith only [hq3, sq_nonneg (q-1)]
    dsimp only [m]
    nlinarith only [hprod, hq3, hsq]
  have hDpos : 0 < D := by
    have hprod := mul_pos (sub_pos.mpr hqm) (show 0 < m+q by omega)
    nlinarith only [hD2, hprod]
  have horder : 1 < p^2*D := by
    have hprod := mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ D by omega) (sq_nonneg p)
    nlinarith only [hprod, hp3, sq_nonneg (p-3)]
  fin_cases i
  · have hzero : squareGrowthOne p q t 0 = 1 := by
      simp [squareGrowthOne, leeDiamond, Finset.filter_singleton]
    have hsfull : (squareGrowthOne p q t s : ℤ) = p^2*D := hballs.1
    change squareGrowthOne p q t 0 ≠ squareGrowthOne p q t s
    omega
  · have hzero : squareGrowthEqual p q t 0 = 1 := by
      simp [squareGrowthEqual, leeDiamond, Finset.filter_singleton]
    have hsfull : (squareGrowthEqual p q t s : ℤ) = p^2*D := hballs.2
    change squareGrowthEqual p q t 0 ≠ squareGrowthEqual p q t s
    omega

noncomputable def squareGrowthSource : Registration squareGrowthArena
    (type_of% (@same_group_square_displacement_growth)) where
  actual := squareActual
  bridge := Iff.rfl
  variation := ⟨square_actual_law, squareRejected 0, square_rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨squareRejected i, ?_, rfl, square_rejected_law i⟩
      intro j hj
      funext pqt r
      simp [squareRejected, realize, hj]
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨3,3,2⟩, 0, 16, ?_⟩
    exact square_dependence_at 3 3 2 (by norm_num) (by decide)
      (by norm_num) (by decide) (by norm_num) i

-- Faithful mathematical family record above; deliberately incomplete source
-- binding below. issue25856 owns the missing exact raw occurrence selection,
-- inverse reconstruction, and source State=Nat correspondence evidence.
noncomputable def squareGrowthRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@same_group_square_displacement_growth)
      (Realization squareGrowthSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattySquareDisplacementGrowth.same_group_square_displacement_growth.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementGrowth.squareGrowthSource
  realizationSource := none
  generated := false
  arena := .source ⟨squareGrowthArena⟩
  objectArena := .source ⟨squareGrowthArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source squareGrowthArena ⟨squareGrowthSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize squareGrowthSignature
    (fun i pqt r => if i = 0 then squareGrowthOne pqt.1 pqt.2.1 pqt.2.2 r
      else squareGrowthEqual pqt.1 pqt.2.1 pqt.2.2 r)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementGrowth
