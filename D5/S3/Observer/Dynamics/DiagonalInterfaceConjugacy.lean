/- GID: D5/S3/Observer/Dynamics/DiagonalInterfaceConjugacy
   generality: G
   mirror-B: D5/B/S3/Observer/Dynamics/DiagonalInterfaceConjugacy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Diagonal-interface-preserving similarity exactly recovers finite map conjugacy. -/

import D5.S3.ObserverMemory.InverseLimits.DiagonalCornerReconstruction
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.LinearAlgebra.Dimension.Constructions

/- Library-search audit trail (2026-08-20):
   * The repository exact hit `diagonal_corner_reconstruction` constructs the
     source transfer from its state map and proves its nonzero coordinate-corner
     criterion. It is applied in both directions of the final reconstruction.
   * Pinned Mathlib exact hits `Finsupp.mapDomain.linearEquiv`,
     `Finsupp.mapDomain_single`, and `Finsupp.mapDomain_equiv_apply` transport
     coordinate functions through a state equivalence and are applied below.
   * Pinned Mathlib exact hits `LinearEquiv.conj`, `LinearEquiv.finrank_eq`,
     `Module.finrank_finsupp_self`, `Fintype.bijective_iff_injective_and_card`,
     and `Equiv.ofBijective` supply operator conjugation and the finite-cardinal
     reconstruction step; they are applied below.
   * Repository and pinned-Mathlib shape searches found no theorem packaging
     the full equivalence or characterizing this diagonal normalizer directly. -/

noncomputable section

namespace D5.S3.Observer.Dynamics.DiagonalInterfaceConjugacy

open D5.S3.ObserverMemory.InverseLimits.TraceRankCombinatorics
open D5.S3.ObserverMemory.InverseLimits.DiagonalCornerReconstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Multiplication by a coordinate function, constructed pointwise on the
finite-state coordinate space. -/
def diagonalOperator {Y : Type*} (f : Finsupp Y Complex) :
    Module.End Complex (Finsupp Y Complex) where
  toFun v := f * v
  map_add' v w := by
    ext z
    simp [Finsupp.mul_apply, mul_add]
  map_smul' c v := by
    ext z
    change f z * (c * v z) = c * (f z * v z)
    ring

/-- The complete interface of coordinatewise multiplication operators. -/
def diagonalInterface (Y : Type*) :
    Set (Module.End Complex (Finsupp Y Complex)) :=
  Set.range diagonalOperator

private theorem coordinate_projection_eq_diagonal {Y : Type*} (y : Y) :
    coordinateProjection y = diagonalOperator (Finsupp.single y 1) := by
  classical
  ext v z
  by_cases hz : z = y
  · subst z
    simp [coordinateProjection, diagonalOperator]
  · simp [coordinateProjection, diagonalOperator, hz]

private theorem basis_vector_ne_zero {Y : Type*} (y : Y) :
    basisVector y ≠ 0 := by
  simp [basisVector]

private theorem conjugate_apply_image {Y Z : Type*}
    (U : Finsupp Y Complex ≃ₗ[Complex] Finsupp Z Complex)
    (A : Module.End Complex (Finsupp Y Complex))
    (v : Finsupp Y Complex) :
    U.conj A (U v) = U (A v) := by
  simp [LinearEquiv.conj_apply]

private theorem conjugate_comp {Y Z : Type*}
    (U : Finsupp Y Complex ≃ₗ[Complex] Finsupp Z Complex)
    (A B : Module.End Complex (Finsupp Y Complex)) :
    U.conj (A.comp B) = (U.conj A).comp (U.conj B) := by
  ext v
  simp [LinearEquiv.conj_apply, LinearMap.comp_apply]

private theorem map_domain_conjugates_transfer {Y Z : Type*}
    (tau : Y -> Y) (sigma : Z -> Z) (phi : Y ≃ Z)
    (hphi : ∀ y, phi (tau y) = sigma (phi y)) :
    let U := Finsupp.mapDomain.linearEquiv Complex Complex phi
    U.conj (transferOperator tau) = transferOperator sigma := by
  dsimp
  ext v z
  simp [LinearEquiv.conj_apply, Finsupp.mapDomain.linearEquiv,
    transferOperator, Finsupp.mapDomain_single, hphi]

private theorem map_domain_conjugates_diagonal {Y Z : Type*}
    (phi : Y ≃ Z) (f : Finsupp Y Complex) :
    let U := Finsupp.mapDomain.linearEquiv Complex Complex phi
    U.conj (diagonalOperator f) = diagonalOperator (Finsupp.mapDomain phi f) := by
  dsimp
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro z
  simp [LinearEquiv.conj_apply, diagonalOperator,
    Finsupp.mapDomain_equiv_apply, Finsupp.mul_apply]

/-- Finite state maps are conjugate by a bijection exactly when their transfer
operators are linearly conjugate by an equivalence that carries the full
coordinate-multiplication interface onto the target interface. -/
theorem diagonal_interface_conjugacy
    {Y Z : Type*} [Finite Y] [Finite Z]
    (tau : Y -> Y) (sigma : Z -> Z) :
    (∃ phi : Y ≃ Z, ∀ y, phi (tau y) = sigma (phi y)) ↔
      ∃ U : Finsupp Y Complex ≃ₗ[Complex] Finsupp Z Complex,
        U.conj (transferOperator tau) = transferOperator sigma ∧
        Set.image U.conj (diagonalInterface Y) = diagonalInterface Z := by
  classical
  letI := Fintype.ofFinite Y
  letI := Fintype.ofFinite Z
  constructor
  · rintro ⟨phi, hphi⟩
    let U := Finsupp.mapDomain.linearEquiv Complex Complex phi
    refine ⟨U, map_domain_conjugates_transfer tau sigma phi hphi, ?_⟩
    ext A
    constructor
    · rintro ⟨B, ⟨f, rfl⟩, rfl⟩
      exact ⟨Finsupp.mapDomain phi f, (map_domain_conjugates_diagonal phi f).symm⟩
    · rintro ⟨g, rfl⟩
      let f := Finsupp.mapDomain phi.symm g
      refine ⟨diagonalOperator f, ⟨f, rfl⟩, ?_⟩
      rw [map_domain_conjugates_diagonal]
      congr
      exact (Finsupp.mapDomain.linearEquiv Complex Complex phi).apply_symm_apply g
  · rintro ⟨U, htransfer, hdiagonal⟩
    have himage_ne : ∀ y : Y, U (basisVector y) ≠ 0 := fun y => by
      simpa only [map_zero] using U.injective.ne (basis_vector_ne_zero y)
    have hsupport : ∀ y : Y, (U (basisVector y)).support.Nonempty := fun y =>
      Finsupp.support_nonempty_iff.mpr (himage_ne y)
    let pick : Y -> Z := fun y => Classical.choose (hsupport y)
    have hpick : ∀ y : Y, U (basisVector y) (pick y) ≠ 0 := fun y =>
      Finsupp.mem_support_iff.mp (Classical.choose_spec (hsupport y))
    have hprojection_mem : ∀ y : Y,
        U.conj (coordinateProjection y) ∈ diagonalInterface Z := by
      intro y
      rw [← hdiagonal]
      exact ⟨coordinateProjection y,
        ⟨Finsupp.single y 1, (coordinate_projection_eq_diagonal y).symm⟩, rfl⟩
    choose weight hweight using hprojection_mem
    have hweight_one : ∀ y : Y, weight y (pick y) = 1 := by
      intro y
      have haction := conjugate_apply_image U (coordinateProjection y) (basisVector y)
      have hsame : coordinateProjection y (basisVector y) = basisVector y := by
        ext z
        simp [coordinateProjection, basisVector, Finsupp.single_apply]
      rw [hsame, ← hweight y] at haction
      have hcoordinate := congrArg (fun v : Finsupp Z Complex => v (pick y)) haction
      simp only [diagonalOperator] at hcoordinate
      exact (mul_right_cancel₀ (hpick y)) (by simpa using hcoordinate)
    have hweight_zero : ∀ {y k : Y}, y ≠ k -> weight y (pick k) = 0 := by
      intro y k hyk
      have haction := conjugate_apply_image U (coordinateProjection y) (basisVector k)
      have hzero : coordinateProjection y (basisVector k) = 0 := by
        ext z
        simp [coordinateProjection, basisVector, hyk]
      rw [hzero, map_zero, ← hweight y] at haction
      have hcoordinate := congrArg (fun v : Finsupp Z Complex => v (pick k)) haction
      simp only [diagonalOperator, Finsupp.zero_apply] at hcoordinate
      exact (mul_eq_zero.mp hcoordinate).resolve_right (hpick k)
    have hpick_injective : Function.Injective pick := by
      intro y k hyk
      by_contra hne
      have hone := hweight_one y
      have hzero := hweight_zero hne
      rw [hyk] at hone
      rw [hone] at hzero
      exact one_ne_zero hzero
    have hcard : Fintype.card Y = Fintype.card Z := by
      rw [← Module.finrank_finsupp_self Complex, ← Module.finrank_finsupp_self Complex]
      exact U.finrank_eq
    have hpick_bijective : Function.Bijective pick :=
      (Fintype.bijective_iff_injective_and_card pick).mpr ⟨hpick_injective, hcard⟩
    let phi : Y ≃ Z := Equiv.ofBijective pick hpick_bijective
    have hphi_apply : ∀ y : Y, phi y = pick y := fun _ => rfl
    have hprojection : ∀ y : Y,
        U.conj (coordinateProjection y) = coordinateProjection (phi y) := by
      intro y
      rw [← hweight y, coordinate_projection_eq_diagonal]
      congr 1
      apply Finsupp.ext
      intro z
      let k := phi.symm z
      have hzk : phi k = z := phi.apply_symm_apply z
      by_cases hky : k = y
      · rw [← hzk, hky, hphi_apply, hweight_one]
        simp
      · have hyk : y ≠ k := fun hyk => hky hyk.symm
        have hzweight := hweight_zero (y := y) (k := k) hyk
        have hzpick : pick k = z := by
          rw [← hphi_apply, hzk]
        rw [hzpick] at hzweight
        rw [hzweight]
        have hzne : z ≠ phi y := by
          intro hz
          apply hky
          exact phi.injective (hzk.trans hz)
        simp [hzne]
    refine ⟨phi, ?_⟩
    intro y
    have hsource : diagonalCorner (tau y) tau y ≠ 0 :=
      (diagonal_corner_reconstruction tau y (tau y)).1.2 rfl
    have hconjugate : U.conj (diagonalCorner (tau y) tau y) ≠ 0 := by
      simpa only [map_zero] using U.conj.injective.ne hsource
    have hcorner :
        U.conj (diagonalCorner (tau y) tau y) =
          diagonalCorner (phi (tau y)) sigma (phi y) := by
      rw [diagonalCorner, diagonalCorner]
      rw [conjugate_comp, conjugate_comp, hprojection, htransfer, hprojection]
    rw [hcorner] at hconjugate
    exact (diagonal_corner_reconstruction sigma (phi y) (phi (tau y))).1.1 hconjugate

/-- A singleton state space inhabits both sides of the equivalence. -/
example :
    ∃ U : Finsupp (Fin 1) Complex ≃ₗ[Complex] Finsupp (Fin 1) Complex,
      U.conj (transferOperator (id : Fin 1 -> Fin 1)) = transferOperator id ∧
      Set.image U.conj (diagonalInterface (Fin 1)) = diagonalInterface (Fin 1) := by
  apply (diagonal_interface_conjugacy (id : Fin 1 -> Fin 1) id).mp
  exact ⟨Equiv.refl _, fun _ => rfl⟩

#print axioms diagonal_interface_conjugacy

end D5.S3.Observer.Dynamics.DiagonalInterfaceConjugacy
