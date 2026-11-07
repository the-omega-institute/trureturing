/- GID: D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyLaws
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyLaws
   mirror-E: none(waiver:algebraic-original-brst-cohomology)
   anchors: []
   utility: none
   digest: The original critical BRST quotient inherits vacuum, creation, translation, parity and signed locality. -/

/- Original tensor-state BRST cohomology. The supplier chain retains the
Bakalov--Kac lattice, Scott Carnahan field and residue calculus, Kalle Kytölä
Sugawara and Mathlib attribution. No literature novelty is asserted. -/

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyField

/-! Vacuum, translation, parity and signed locality on the actual quotient. -/

set_option autoImplicit false

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.LatticeBRSTCohomologyField

open LatticeGeneratingFieldLocality (LatticeData)
open LatticeMatterGhostCoupling (State)
open FieldNormalProductLocality (delta)
open private identity_modes delta_evaluate from
  D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostStateField
open D5.S3.Quantum.Fermionic.CountableOccupationFock (parity_ket)

noncomputable section

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (h26 : D.rank = 26)
  (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
  (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)

private theorem charge_vacuum :
    LatticeBRST.totalCharge D H (LatticeMatterGhostStateField.vacuum D) = 0 := by
  rw [← LatticeMatterGhostStateField.current_zero_mode D H]
  exact (LatticeMatterGhostStateField.stateField_vacuum_creation D).2.2.1
    (LatticeMatterGhostStateField.Jtot D H) 0 (by omega)

def cycleVacuum : cycles D H :=
  ⟨LatticeMatterGhostStateField.vacuum D, charge_vacuum D H⟩

def vacuum : Cohomology D H h26 hHG hGH :=
  classOf D H h26 hHG hGH (cycleVacuum D H)

private theorem charge_translation (x : State D) :
    LatticeBRST.totalCharge D H (LatticeMatterGhostStateField.translation D x) =
      LatticeMatterGhostStateField.translation D (LatticeBRST.totalCharge D H x) := by
  have h := LatticeMatterGhostStateField.stateField_covariance D
    (LatticeMatterGhostStateField.Jtot D H) 0
  rw [LatticeMatterGhostStateField.current_zero_mode] at h
  have e : LatticeMatterGhostStateField.translation D * LatticeBRST.totalCharge D H =
      LatticeBRST.totalCharge D H * LatticeMatterGhostStateField.translation D := by
    simpa only [Int.cast_zero, neg_zero, zero_smul, sub_eq_zero] using h
  exact (LinearMap.congr_fun e x).symm

def cycleTranslation : Module.End ℂ (cycles D H) where
  toFun a := ⟨LatticeMatterGhostStateField.translation D a, by
    change LatticeBRST.totalCharge D H
      (LatticeMatterGhostStateField.translation D (a : State D)) = 0
    rw [charge_translation, show LatticeBRST.totalCharge D H a = 0 from a.property,
      map_zero]⟩
  map_add' a b := Subtype.ext
    (map_add (LatticeMatterGhostStateField.translation D) (a : State D) (b : State D))
  map_smul' z a := Subtype.ext
    (map_smul (LatticeMatterGhostStateField.translation D) z (a : State D))

private theorem translation_boundary (a : cycles D H)
    (ha : a ∈ boundaries D H h26 hHG hGH) :
    cycleTranslation D H a ∈ boundaries D H h26 hHG hGH := by
  obtain ⟨x, hx⟩ := (mem_boundaries D H h26 hHG hGH a).mp ha
  apply (mem_boundaries D H h26 hHG hGH _).mpr
  refine ⟨LatticeMatterGhostStateField.translation D x, ?_⟩
  change LatticeBRST.totalCharge D H (LatticeMatterGhostStateField.translation D x) =
    LatticeMatterGhostStateField.translation D (a : State D)
  rw [charge_translation, hx]

def translation : Module.End ℂ (Cohomology D H h26 hHG hGH) :=
  (boundaries D H h26 hHG hGH).mapQ (boundaries D H h26 hHG hGH)
    (cycleTranslation D H) (translation_boundary D H h26 hHG hGH)

@[simp] theorem translation_classOf (a : cycles D H) :
    translation D H h26 hHG hGH (classOf D H h26 hHG hGH a) =
      classOf D H h26 hHG hGH (cycleTranslation D H a) := rfl

theorem vacuum_mode (n : ℤ) (a : Cohomology D H h26 hHG hGH) :
    mode D H h26 hHG hGH n (vacuum D H h26 hHG hGH) a =
      if n = -1 then a else 0 := by
  obtain ⟨x, rfl⟩ := classOf_surjective D H h26 hHG hGH a
  rw [vacuum, mode_classOf]
  have e : cycleMode D H n (cycleVacuum D H) x = if n = -1 then x else 0 := by
    apply Subtype.ext
    change ((LatticeMatterGhostStateField.Y D
      (LatticeMatterGhostStateField.vacuum D))[[n]]) x = _
    rw [(LatticeMatterGhostStateField.stateField_vacuum_creation D).1, identity_modes]
    split_ifs <;> rfl
  rw [e]
  split_ifs <;> simp

theorem vacuum_field :
    Y D H h26 hHG hGH (vacuum D H h26 hHG hGH) =
      FieldNormalProduct.identityField := by
  apply HVertexOperator.coeff_inj (Γ := ℤ) (R := ℂ)
    (V := Cohomology D H h26 hHG hGH) (W := Cohomology D H h26 hHG hGH)
  funext power
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff,
    Y_modes, identity_modes]
  apply LinearMap.ext; intro a
  rw [vacuum_mode]
  split_ifs <;> rfl

theorem creation (a : Cohomology D H h26 hHG hGH) :
    ((Y D H h26 hHG hGH a)[[-1]]) (vacuum D H h26 hHG hGH) = a := by
  obtain ⟨x, rfl⟩ := classOf_surjective D H h26 hHG hGH a
  rw [Y_modes, vacuum, mode_classOf]
  apply congrArg (classOf D H h26 hHG hGH)
  apply Subtype.ext
  exact (LatticeMatterGhostStateField.stateField_vacuum_creation D).2.1 x

theorem creativity (a : Cohomology D H h26 hHG hGH) (n : ℤ) (hn : 0 ≤ n) :
    ((Y D H h26 hHG hGH a)[[n]]) (vacuum D H h26 hHG hGH) = 0 := by
  obtain ⟨x, rfl⟩ := classOf_surjective D H h26 hHG hGH a
  rw [Y_modes, vacuum, mode_classOf]
  have e : cycleMode D H n x (cycleVacuum D H) = 0 :=
    Subtype.ext ((LatticeMatterGhostStateField.stateField_vacuum_creation D).2.2.1 x n hn)
  rw [e, map_zero]

theorem translation_vacuum :
    translation D H h26 hHG hGH (vacuum D H h26 hHG hGH) = 0 := by
  rw [vacuum, translation_classOf]
  have e : cycleTranslation D H (cycleVacuum D H) = 0 :=
    Subtype.ext (LatticeMatterGhostStateField.stateField_vacuum_creation D).2.2.2
  rw [e, map_zero]

theorem covariance (a : Cohomology D H h26 hHG hGH) (n : ℤ) :
    translation D H h26 hHG hGH * ((Y D H h26 hHG hGH a)[[n]]) -
      ((Y D H h26 hHG hGH a)[[n]]) * translation D H h26 hHG hGH =
        -(n : ℂ) • ((Y D H h26 hHG hGH a)[[n - 1]]) := by
  obtain ⟨s, rfl⟩ := classOf_surjective D H h26 hHG hGH a
  apply LinearMap.ext; intro b
  obtain ⟨x, rfl⟩ := classOf_surjective D H h26 hHG hGH b
  simp only [Y_modes, Module.End.mul_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, mode_classOf, translation_classOf]
  rw [← map_sub, ← map_smul]
  apply congrArg (classOf D H h26 hHG hGH)
  apply Subtype.ext
  exact LinearMap.congr_fun (LatticeMatterGhostStateField.stateField_covariance D s n) x

theorem translation_as_minusTwo (a : Cohomology D H h26 hHG hGH) :
    translation D H h26 hHG hGH a =
      ((Y D H h26 hHG hGH a)[[-2]]) (vacuum D H h26 hHG hGH) := by
  have h := LinearMap.congr_fun (covariance D H h26 hHG hGH a (-1))
    (vacuum D H h26 hHG hGH)
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    creation, translation_vacuum, map_zero, sub_zero,
    Int.cast_neg, Int.cast_one, neg_neg, one_smul,
    show (-1 : ℤ) - 1 = -2 by norm_num] using h

theorem parity_vacuum :
    parity D H h26 hHG hGH (vacuum D H h26 hHG hGH) = vacuum D H h26 hHG hGH := by
  rw [vacuum, parity_classOf]
  apply congrArg (classOf D H h26 hHG hGH)
  apply Subtype.ext
  change LatticeMatterGhostStateField.parity D
    (LatticeMatterGhostStateField.vacuum D) = LatticeMatterGhostStateField.vacuum D
  simp only [LatticeMatterGhostStateField.vacuum,
    LatticeMatterGhostStateField.parity, TensorProduct.map_tmul, LinearMap.id_apply,
    D5.S3.Quantum.Fermionic.CountableOccupationFock.vacuum, parity_ket,
    Finset.card_empty, pow_zero, one_smul]

theorem field_parity (a : Cohomology D H h26 hHG hGH) (n : ℤ) :
    parity D H h26 hHG hGH * ((Y D H h26 hHG hGH a)[[n]]) =
      ((Y D H h26 hHG hGH (parity D H h26 hHG hGH a))[[n]]) *
        parity D H h26 hHG hGH := by
  obtain ⟨s, rfl⟩ := classOf_surjective D H h26 hHG hGH a
  apply LinearMap.ext; intro b
  obtain ⟨x, rfl⟩ := classOf_surjective D H h26 hHG hGH b
  simp only [Y_modes, Module.End.mul_apply, mode_classOf, parity_classOf]
  apply congrArg (classOf D H h26 hHG hGH)
  apply Subtype.ext
  exact LinearMap.congr_fun (LatticeMatterGhostStateField.stateField_parity D s n) x

private theorem cycle_delta_val
    (f : ℤ → ℤ → Module.End ℂ (cycles D H)) (N : ℕ) (r s : ℤ) (x : cycles D H) :
    (((delta^[N] f) r s) x : State D) =
      (delta^[N] (fun i j => (f i j x : State D))) r s := by
  induction N generalizing r s with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change (((delta^[N] f) (r + 1) s) x : State D) -
      (((delta^[N] f) r (s + 1)) x : State D) = _
    rw [ih, ih]
    rfl

private theorem delta_class
    (f : ℤ → ℤ → Module.End ℂ (cycles D H))
    (g : ℤ → ℤ → Module.End ℂ (Cohomology D H h26 hHG hGH))
    (h : ∀ r s x, g r s (classOf D H h26 hHG hGH x) =
      classOf D H h26 hHG hGH (f r s x))
    (N : ℕ) (r s : ℤ) (x : cycles D H) :
    (delta^[N] g) r s (classOf D H h26 hHG hGH x) =
      classOf D H h26 hHG hGH ((delta^[N] f) r s x) := by
  induction N generalizing r s with
  | zero => exact h r s x
  | succ N ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    simp only [delta, LinearMap.sub_apply]
    rw [ih, ih, ← map_sub]

/-- Signed locality on the true quotient. The exponent is uniform in all INPUT
classes. Homogeneous field classes are lifted by the proved cycle projections. -/
theorem locality (a b : Cohomology D H h26 hHG hGH) (p q : ℕ)
    (ha : parity D H h26 hHG hGH a = (-1 : ℂ)^p • a)
    (hb : parity D H h26 hHG hGH b = (-1 : ℂ)^q • b) :
    ∃ N : ℕ, delta^[N] (fun r s =>
      ((Y D H h26 hHG hGH a)[[r]]) * ((Y D H h26 hHG hGH b)[[s]]) -
        (-1 : ℂ)^(p*q) •
          (((Y D H h26 hHG hGH b)[[s]]) * ((Y D H h26 hHG hGH a)[[r]]))) = 0 := by
  obtain ⟨u, hu, up⟩ := homogeneous_cycle_lift D H h26 hHG hGH a p ha
  obtain ⟨v, hv, vp⟩ := homogeneous_cycle_lift D H h26 hHG hGH b q hb
  obtain ⟨N, hN⟩ := LatticeMatterGhostStateField.stateField_locality D u v p q up vp
  let f : ℤ → ℤ → Module.End ℂ (cycles D H) := fun r s =>
    cycleMode D H r u * cycleMode D H s v -
      (-1 : ℂ)^(p*q) • (cycleMode D H s v * cycleMode D H r u)
  let g : ℤ → ℤ → Module.End ℂ (Cohomology D H h26 hHG hGH) := fun r s =>
    mode D H h26 hHG hGH r (classOf D H h26 hHG hGH u) *
      mode D H h26 hHG hGH s (classOf D H h26 hHG hGH v) -
        (-1 : ℂ)^(p*q) •
          (mode D H h26 hHG hGH s (classOf D H h26 hHG hGH v) *
            mode D H h26 hHG hGH r (classOf D H h26 hHG hGH u))
  have fzero : delta^[N] f = 0 := by
    funext r s
    apply LinearMap.ext; intro x
    apply Subtype.ext
    rw [cycle_delta_val]
    change (delta^[N] (fun i j =>
      ((((LatticeMatterGhostStateField.Y D u)[[i]]) *
        ((LatticeMatterGhostStateField.Y D v)[[j]]) -
          (-1 : ℂ)^(p*q) •
            (((LatticeMatterGhostStateField.Y D v)[[j]]) *
              ((LatticeMatterGhostStateField.Y D u)[[i]]))) (x : State D)))) r s = 0
    rw [delta_evaluate, hN]
    rfl
  have intertwine : ∀ r s x, g r s (classOf D H h26 hHG hGH x) =
      classOf D H h26 hHG hGH (f r s x) := by
    intro r s x
    simp only [f, g, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      mode_classOf, map_sub, map_smul]
  refine ⟨N, ?_⟩
  rw [← hu, ← hv]
  simp only [Y_modes]
  change delta^[N] g = 0
  funext r s
  apply LinearMap.ext; intro x
  obtain ⟨w, rfl⟩ := classOf_surjective D H h26 hHG hGH x
  simpa only [fzero, Pi.zero_apply, LinearMap.zero_apply, map_zero] using
    delta_class D H h26 hHG hGH f g intertwine N r s w

/-- Exact nonvacuity criterion for the ACTUAL vacuum, without an added assumption. -/
theorem vacuum_eq_zero_iff_boundary : vacuum D H h26 hHG hGH = 0 ↔
    ∃ x : State D, LatticeBRST.totalCharge D H x = LatticeMatterGhostStateField.vacuum D :=
  classOf_eq_zero D H h26 hHG hGH (cycleVacuum D H)

/-- For these descended fields, vacuum non-exactness is necessary AND sufficient
for nontriviality. The independent covector consumer discharges it. -/
theorem nontrivial_iff_vacuum_not_boundary :
    Nontrivial (Cohomology D H h26 hHG hGH) ↔
      ¬ ∃ x : State D,
        LatticeBRST.totalCharge D H x = LatticeMatterGhostStateField.vacuum D := by
  rw [← vacuum_eq_zero_iff_boundary D H h26 hHG hGH]
  constructor
  · intro hn hv
    letI := hn
    have allzero (a : Cohomology D H h26 hHG hGH) : a = 0 := by
      have h := vacuum_mode D H h26 hHG hGH (-1) a
      simpa only [hv, map_zero, LinearMap.zero_apply, if_pos rfl, ite_true] using h.symm
    obtain ⟨a, ha⟩ := exists_ne (0 : Cohomology D H h26 hHG hGH)
    exact ha (allzero a)
  · intro hv
    exact ⟨⟨vacuum D H h26 hHG hGH, 0, hv⟩⟩

end
end D5.S3.VertexAlgebra.LatticeBRSTCohomologyField
