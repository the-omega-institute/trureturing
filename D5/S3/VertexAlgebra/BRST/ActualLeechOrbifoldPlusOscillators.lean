/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldPlusOscillators
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldPlusOscillators
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual Virasoro and quartet support on the plus-null oscillator sector. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLightCone

/-! Plus-null polynomial states in the original plane and ghost carriers.
The Sugawara commutator preserves this matter support at nonnegative modes.
The quartet homotopy removes the single extra c mode from this support. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.PlusOscillators

open ActualLeechOrbifoldMatter (Orbifold mode)
open ActualLeechOrbifoldCriticalMatter (Matter hyperbolicPlane hyperbolicMatter matter)
open LatticeGeneratingFieldLocality (Carrier Charge Oscillator)
open LatticeSugawaraCurrents (gramComplex sugawaraMode)
open LatticeLightConeCoordinates (NullFrame a a_single polynomialCurrent_zero)
open LatticeLightConeCoordinates.NullFrame (plus minus)
open LatticeQuartetContraction
open MvPolynomial
open D5.S3.Quantum.Fermionic.CountableOccupationFock (Fock ket create_ket annihilate_ket)
open D5.S3.Quantum.Fermionic.BcGhostFock (b c ghost_mixed_car)
open D5.S3.Quantum.Fermionic.BcGhostQuartetCount
  (c1vac c1vac_eq b_positive c_negative c_positive_ge_two)
open D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus
  (inverseNumber diagonal_basis)

open private grouped_coordinate_d grouped_coordinate_R
  from D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction
open private sugawaraMode_a_commutator
  from D5.S3.VertexAlgebra.Lattice.LatticeRelativeBRSTGround
open private plane_inverse
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldCriticalMatter
open private matter_mode_tmul
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLightCone

private abbrev Plane := Carrier hyperbolicPlane
private abbrev Poly := MvPolynomial ℕ ℂ
private abbrev H := gramComplex hyperbolicPlane

variable (F : NullFrame hyperbolicPlane) (B : Module.Basis (Fin 0) ℂ F.K)
variable (p : Charge hyperbolicPlane)

/-- Variable r is the plus oscillator of frequency r+1. -/
def plusVariable (r : ℕ) : Variables 0 := (plus 0, r)

private theorem plusVariable_injective : Function.Injective plusVariable :=
  fun _ _ h => congrArg Prod.snd h

private theorem pderiv_minus_rename (r : ℕ) (P : Poly) :
    pderiv (minus 0, r) (rename plusVariable P) = 0 := by
  classical
  induction P using MvPolynomial.induction_on with
  | C z => simp
  | add P T hP hT => simp only [map_add, hP, hT, add_zero]
  | mul_X P s ih =>
    have hne : (minus 0, r) ≠ plusVariable s := by simp [plusVariable, minus, plus]
    simp [map_mul, Derivation.leibniz, pderiv_X, Ne.symm hne, ih]

/-- Insertion into the original all-charge plane with exactly the plus variables at p. -/
def planeInsert : Poly →ₗ[ℂ] Plane :=
  (Finsupp.lsingle p).comp ((F.coordinateEquiv B).symm.toLinearEquiv.toLinearMap.comp
    (rename (R := ℂ) plusVariable).toLinearMap)

@[simp] theorem planeInsert_one :
    planeInsert F B p 1 = Finsupp.single p (1 : Oscillator hyperbolicPlane) := by
  change Finsupp.single p ((F.coordinateEquiv B).symm (rename plusVariable 1)) = _
  simp only [map_one]

private theorem a_plus_negative (r : ℕ) (P : Poly) :
    a F.ePlus (-(r : ℤ)-1) (planeInsert F B p P) =
      planeInsert F B p (P * X r) := by
  change a F.ePlus (-(r : ℤ)-1)
    (Finsupp.single p ((F.coordinateEquiv B).symm (rename plusVariable P))) =
    Finsupp.single p ((F.coordinateEquiv B).symm (rename plusVariable (P * X r)))
  rw [a_single]
  apply congrArg (Finsupp.single p)
  apply (F.coordinateEquiv B).injective
  simp only [F.creation_plus B, AlgEquiv.apply_symm_apply, map_mul, rename_X]
  exact mul_comm _ _

private theorem a_plus_zero (P : Poly) :
    a F.ePlus 0 (planeInsert F B p P) = F.pPlus p • planeInsert F B p P := by
  change a F.ePlus 0 (Finsupp.single p ((F.coordinateEquiv B).symm (rename plusVariable P))) =
    F.pPlus p • Finsupp.single p ((F.coordinateEquiv B).symm (rename plusVariable P))
  simp only [a_single, polynomialCurrent_zero, Finsupp.smul_single, NullFrame.pPlus]

private theorem a_plus_positive (r : ℕ) (P : Poly) :
    a F.ePlus ((r : ℤ)+1) (planeInsert F B p P) = 0 := by
  change a F.ePlus ((r : ℤ)+1)
    (Finsupp.single p ((F.coordinateEquiv B).symm (rename plusVariable P))) = 0
  rw [a_single, ← Finsupp.single_zero p]
  apply congrArg (Finsupp.single p)
  apply (F.coordinateEquiv B).injective
  rw [F.annihilation_plus B, AlgEquiv.apply_symm_apply, pderiv_minus_rename,
    smul_zero, map_zero]

private theorem a_plus_mem (n : ℤ) {u : Plane}
    (hu : u ∈ LinearMap.range (planeInsert F B p)) :
    a F.ePlus n u ∈ LinearMap.range (planeInsert F B p) := by
  obtain ⟨P, rfl⟩ := LinearMap.mem_range.mp hu
  cases n with
  | ofNat n =>
    cases n with
    | zero =>
      change a F.ePlus 0 (planeInsert F B p P) ∈ _
      rw [a_plus_zero]
      exact (LinearMap.range (planeInsert F B p)).smul_mem _
        (LinearMap.mem_range_self _ P)
    | succ r =>
      rw [show Int.ofNat (r+1) = (r : ℤ)+1 by simp, a_plus_positive]
      exact (LinearMap.range (planeInsert F B p)).zero_mem
  | negSucc r =>
    rw [show Int.negSucc r = -(r : ℤ)-1 by omega, a_plus_negative]
    exact LinearMap.mem_range_self _ _

/-- The actual nonnegative plane Virasoro modes preserve plus-null matter support.
The generator step uses the original current commutator with coefficient r+1. -/
theorem plane_mode_mem (n : ℤ) (hn : 0 ≤ n) (P : Poly) :
    hyperbolicMatter.mode n (planeInsert F B p P) ∈
      LinearMap.range (planeInsert F B p) := by
  change sugawaraMode hyperbolicPlane H n (planeInsert F B p P) ∈ _
  induction P using MvPolynomial.induction_on with
  | C z =>
    have hC : (C z : Poly) = z • (1 : Poly) := by simp [MvPolynomial.smul_eq_C_mul]
    rw [hC, map_smul, map_smul]
    apply (LinearMap.range (planeInsert F B p)).smul_mem
    by_cases hz : n = 0
    · rw [hz, planeInsert_one, LatticeSugawaraVirasoro.sugawaraMode_ground_zero,
        ← planeInsert_one F B p]
      exact (LinearMap.range (planeInsert F B p)).smul_mem _
        (LinearMap.mem_range_self _ 1)
    · rw [planeInsert_one,
        LatticeSugawaraVirasoro.sugawaraMode_ground_positive _ _ _ _ (by omega)]
      exact (LinearMap.range (planeInsert F B p)).zero_mem
  | add P T hP hT =>
    rw [map_add, map_add]
    exact (LinearMap.range (planeInsert F B p)).add_mem hP hT
  | mul_X P r ih =>
    rw [← a_plus_negative F B p]
    have hc := LinearMap.congr_fun
      (sugawaraMode_a_commutator hyperbolicPlane H plane_inverse plane_inverse
        F.ePlus n (-(r : ℤ)-1)) (planeInsert F B p P)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at hc
    rw [sub_eq_iff_eq_add.mp hc]
    exact (LinearMap.range (planeInsert F B p)).add_mem
      ((LinearMap.range (planeInsert F B p)).smul_mem _
        (a_plus_mem F B p _ (LinearMap.mem_range_self _ P)))
      (a_plus_mem F B p _ ih)

/-- Span of orbifold states tensored with fixed-momentum plus-null plane states. -/
def plusMatter : Submodule ℂ Matter :=
  Submodule.span ℂ {φ | ∃ (v : Orbifold) (P : Poly), φ = v ⊗ₜ[ℂ] planeInsert F B p P}

theorem tmul_mem_plusMatter (v : Orbifold) (P : Poly) :
    v ⊗ₜ[ℂ] planeInsert F B p P ∈ plusMatter F B p :=
  Submodule.subset_span ⟨v, P, rfl⟩

/-- The original orbifold-plane matter Virasoro modes of index n ≥ 0
preserve the fixed-momentum plus-null matter submodule. -/
theorem matter_mode_mem (n : ℤ) (hn : 0 ≤ n) {φ : Matter}
    (hφ : φ ∈ plusMatter F B p) :
    matter.mode n φ ∈ plusMatter F B p := by
  have hle : plusMatter F B p ≤ (plusMatter F B p).comap (matter.mode n) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, P, rfl⟩
    change matter.mode n (v ⊗ₜ[ℂ] planeInsert F B p P) ∈ plusMatter F B p
    rw [matter_mode_tmul]
    obtain ⟨T, hT⟩ := LinearMap.mem_range.mp (plane_mode_mem F B p n hn P)
    rw [← hT]
    exact (plusMatter F B p).add_mem (tmul_mem_plusMatter F B p (mode n v) P)
      (tmul_mem_plusMatter F B p v T)
  exact hle hφ

private def sectorInsert (w : Fock) : Poly →ₗ[ℂ] State hyperbolicPlane :=
  ((TensorProduct.mk ℂ Plane Fock).flip w).comp (planeInsert F B p)

/-- The fixed-ghost sector of plus-null oscillators at momentum p. -/
def plusSector (w : Fock) : Submodule ℂ (State hyperbolicPlane) :=
  LinearMap.range (sectorInsert F B p w)

theorem mem_plusSector_iff (w : Fock) (y : State hyperbolicPlane) :
    y ∈ plusSector F B p w ↔ ∃ P : Poly, planeInsert F B p P ⊗ₜ[ℂ] w = y :=
  Iff.rfl

private theorem sector_mem (w : Fock) (P : Poly) :
    sector F B p (rename plusVariable P) w ∈ plusSector F B p w :=
  LinearMap.mem_range_self (sectorInsert F B p w) P

/-- Support with a single additional c mode, including the possible c(0) site. -/
def extraCSector : Submodule ℂ (State hyperbolicPlane) :=
  ⨆ n : ℕ, plusSector F B p (c (-(n : ℤ)) c1vac)

private theorem dTerm_mem (r : ℕ) (P : Poly) :
    dTerm F r (sector F B p (rename plusVariable P) c1vac) ∈ extraCSector F B p := by
  have hc : c ((r : ℤ)+1) c1vac = 0 := by
    cases r with
    | zero =>
      rw [show ((0 : ℕ) : ℤ)+1 = 1 by simp, c1vac_eq,
        D5.S3.Quantum.Fermionic.BcGhostQuartetCount.c_positive_one, create_ket]
      simp
    | succ r =>
      rw [show ((r+1 : ℕ) : ℤ)+1 = ((r+2 : ℕ) : ℤ) by omega,
        c_positive_ge_two (r+2) (by omega), c1vac_eq, annihilate_ket]
      have hsite : 2 * (r + 2 - 2) ∉ ({1} : Finset ℕ) := by
        simp only [Finset.mem_singleton]
        omega
      rw [ite_eq_right hsite]
  rw [grouped_coordinate_d F B, hc]
  simp only [sector, TensorProduct.tmul_zero, add_zero]
  change (r+1 : ℂ) •
    sector F B p (pderiv (plusVariable r) (rename plusVariable P))
      (c (-((r : ℤ)+1)) c1vac) ∈ _
  rw [pderiv_rename plusVariable_injective,
    show (r : ℤ)+1 = ((r+1 : ℕ) : ℤ) by omega]
  exact (extraCSector F B p).smul_mem _
    (le_iSup (fun n : ℕ => plusSector F B p (c (-(n : ℤ)) c1vac)) (r+1)
      (sector_mem F B p _ (pderiv r P)))

/-- The actual quartet differential produces only one extra nonzero-frequency
c excitation from plus-null matter and c1vac. -/
theorem d0_mem_extraCSector {y : State hyperbolicPlane}
    (hy : y ∈ plusSector F B p c1vac) : d0 F p y ∈ extraCSector F B p := by
  obtain ⟨P, rfl⟩ := LinearMap.mem_range.mp hy
  let y := sector F B p (rename plusVariable P) c1vac
  change F.pPlus p • (dFamily F).total y ∈ extraCSector F B p
  rw [(dFamily F).total_eq_sum y _ le_rfl]
  exact (extraCSector F B p).smul_mem _
    ((extraCSector F B p).sum_mem fun r _ => dTerm_mem F B p r P)

private theorem b_extra (r n : ℕ) :
    b ((r : ℤ)+1) (c (-(n : ℤ)) c1vac) =
      if r+1 = n then c1vac else 0 := by
  have hb : b ((r : ℤ)+1) c1vac = 0 := by
    rw [← Nat.cast_succ, b_positive, c1vac_eq, annihilate_ket]
    have hsite : 2 * (r+1) + 3 ∉ ({1} : Finset ℕ) := by
      simp only [Finset.mem_singleton]
      omega
    rw [ite_eq_right hsite]
  have h := LinearMap.congr_fun (ghost_mixed_car ((r : ℤ)+1) (-(n : ℤ))) c1vac
  have he : (r : ℤ)+1 + -(n : ℤ) = 0 ↔ r+1 = n := by omega
  by_cases hr : r+1 = n
  · simpa only [he, ite_eq_left hr, LinearMap.add_apply, Module.End.mul_apply,
      hb, map_zero, add_zero, Module.End.one_apply] using h
  · simpa only [he, ite_eq_right hr, LinearMap.add_apply, Module.End.mul_apply,
      hb, map_zero, add_zero, LinearMap.zero_apply] using h

private theorem sector_zero_poly (w : Fock) : sector F B p 0 w = 0 := by
  simp [sector]

private theorem rTerm_mem (r n : ℕ) (P : Poly) :
    rTerm F r (sector F B p (rename plusVariable P) (c (-(n : ℤ)) c1vac)) ∈
      plusSector F B p c1vac := by
  rw [grouped_coordinate_R F B, pderiv_minus_rename, sector_zero_poly, add_zero, b_extra]
  split_ifs
  · change (r+1 : ℂ)⁻¹ • sector F B p (X (plusVariable r) * rename plusVariable P) c1vac ∈ _
    have hrename : rename plusVariable (X r * P) =
        X (plusVariable r) * rename plusVariable P := by
      simp only [map_mul, rename_X]
    rw [← hrename]
    exact (plusSector F B p c1vac).smul_mem ((r+1 : ℂ)⁻¹)
      (sector_mem F B p c1vac (X r * P))
  · simp [sector]

private theorem R_mem (n : ℕ) {y : State hyperbolicPlane}
    (hy : y ∈ plusSector F B p (c (-(n : ℤ)) c1vac)) :
    R F p y ∈ plusSector F B p c1vac := by
  obtain ⟨P, rfl⟩ := LinearMap.mem_range.mp hy
  let y := sector F B p (rename plusVariable P) (c (-(n : ℤ)) c1vac)
  change (F.pPlus p)⁻¹ • (rFamily F).total y ∈ plusSector F B p c1vac
  rw [(rFamily F).total_eq_sum y _ le_rfl]
  exact (plusSector F B p c1vac).smul_mem _
    ((plusSector F B p c1vac).sum_mem fun r _ => rTerm_mem F B p r n P)

private theorem invM_mem_ket (S : Finset ℕ) (P : Poly) :
    invM F B (sectorInsert F B p (ket S) P) ∈ plusSector F B p (ket S) := by
  classical
  have hsum := congrArg ((invM F B).comp (sectorInsert F B p (ket S)))
    (MvPolynomial.as_sum P)
  simp only [LinearMap.comp_apply, map_sum] at hsum
  rw [hsum]
  apply (plusSector F B p (ket S)).sum_mem
  intro m hm
  have hmon : monomial m (P.coeff m) = P.coeff m • (monomial m 1 : Poly) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hmon, map_smul, map_smul]
  apply (plusSector F B p (ket S)).smul_mem
  let i : StateIndex hyperbolicPlane 0 := (⟨p, m.mapDomain plusVariable⟩, S)
  have hb : sectorInsert F B p (ket S) (monomial m 1) = actualBasis F B i := by
    change sector F B p (rename plusVariable (monomial m 1)) (ket S) =
      actualBasis F B (⟨p, m.mapDomain plusVariable⟩, S)
    rw [rename_monomial, actualBasis_apply]
  rw [hb, invM, inverseNumber, diagonal_basis]
  apply (plusSector F B p (ket S)).smul_mem
  rw [← hb]
  exact LinearMap.mem_range_self (sectorInsert F B p (ket S)) (monomial m 1)

private theorem extra_c_eq (n : ℕ) :
    c (-(n : ℤ)) c1vac = -ket (insert (2*n+3) {1}) := by
  rw [c_negative, c1vac_eq, create_ket]
  have hs : 1 < 2*n+3 := by omega
  have hf : 2*n+3 ∉ ({1} : Finset ℕ) := by
    simp only [Finset.mem_singleton]
    omega
  have hl : D5.S3.Quantum.Fermionic.CountableOccupationFock.lowerCount (2*n+3) {1} = 1 := by
    simp [D5.S3.Quantum.Fermionic.CountableOccupationFock.lowerCount, Finset.filter_singleton, hs]
  simp only [ite_eq_right hf, D5.S3.Quantum.Fermionic.CountableOccupationFock.phase,
    hl, pow_one, neg_one_smul]

private theorem plusSector_neg (w : Fock) :
    plusSector F B p (-w) = plusSector F B p w := by
  ext y
  constructor
  · intro hy
    obtain ⟨P, rfl⟩ := (mem_plusSector_iff F B p (-w) y).mp hy
    rw [TensorProduct.tmul_neg]
    exact (plusSector F B p w).neg_mem ((mem_plusSector_iff F B p w _).mpr ⟨P, rfl⟩)
  · intro hy
    obtain ⟨P, rfl⟩ := (mem_plusSector_iff F B p w y).mp hy
    have hP : planeInsert F B p P ⊗ₜ[ℂ] (-w) ∈ plusSector F B p (-w) :=
      (mem_plusSector_iff F B p (-w) _).mpr ⟨P, rfl⟩
    rw [TensorProduct.tmul_neg] at hP
    exact (plusSector F B p (-w)).neg_mem_iff.mp hP

private theorem invM_mem (n : ℕ) {y : State hyperbolicPlane}
    (hy : y ∈ plusSector F B p (c (-(n : ℤ)) c1vac)) :
    invM F B y ∈ plusSector F B p (c (-(n : ℤ)) c1vac) := by
  rw [extra_c_eq, plusSector_neg] at hy ⊢
  obtain ⟨P, rfl⟩ := LinearMap.mem_range.mp hy
  exact invM_mem_ket F B p _ P

/-- The original inverse-count homotopy maps the plus-null sector with one
extra c excitation into the same matter sector with ghost factor c1vac. -/
theorem h_mem_plusSector {y : State hyperbolicPlane}
    (hy : y ∈ extraCSector F B p) :
    h F B p y ∈ plusSector F B p c1vac := by
  have hle : extraCSector F B p ≤ (plusSector F B p c1vac).comap (h F B p) :=
    iSup_le fun n z hz => R_mem F B p n (invM_mem F B p n hz)
  exact hle hy

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.PlusOscillators
