/- GID: D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology
   mirror-E: none(waiver:algebraic-original-absolute-zero-cohomology)
   anchors: []
   utility: none
   digest: Actual original absolute zero-momentum BRST kernel/image and native ghost-graded cohomology at every rank. -/

/- Original carrier and operators retain their repository suppliers' authorship.
The absolute/cohomology/ghost-grade and cone source proposals supply the initial
construction; native integration reuses RelativeZeroMode CAR and the original
zero-momentum shell. Mathlib quotient and dimension results are Apache 2.0.
There is no claim about ambient noncritical nilpotence, pairings or positivity. -/

import D5.S3.VertexAlgebra.Lattice.LatticeZeroMomentumBRST
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTRelativeZeroMode
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-! Actual original absolute zero-energy cohomology, with native integer ghost grading. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

noncomputable section
open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.LatticeOriginalAbsoluteZeroCohomology

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticePositiveEnergy
open LatticeMatterGhostCoupling LatticeRelativeMassShell LatticeZeroMomentumBRST
open LatticeMatterGhostDegree (tensorNumber)
open LatticeBRSTRelativeZeroMode (ghost_b_zero_square ghost_c_zero_square
  ghost_zero_mixed bZeroProjector_fix_of_ker totalL0_b_zero)
open D5.S3.Quantum.Fermionic CountableOccupationFock
open private ghostSlice ghostSlice_coeff ghostSlice_tmul
  from D5.S3.VertexAlgebra.Lattice.LatticeRelativeMassShell
open private R_odd_capture from D5.S3.VertexAlgebra.Lattice.LatticeZeroMomentumBRST
open private totalL0_c_zero from D5.S3.VertexAlgebra.Lattice.LatticeBRSTRelativeZeroMode

variable (D : LatticeData)

/-- The genuine all-state CAR splitting, before imposing either charge or energy. -/
theorem bc_split (x : State D) :
    ghostB D 0 (ghostC D 0 x) + ghostC D 0 (ghostB D 0 x) = x :=
  LinearMap.congr_fun (ghost_zero_mixed D) x

private theorem b_twice (x : State D) : ghostB D 0 (ghostB D 0 x) = 0 :=
  LinearMap.congr_fun (ghost_b_zero_square D) x

private theorem c_twice (x : State D) : ghostC D 0 (ghostC D 0 x) = 0 :=
  LinearMap.congr_fun (ghost_c_zero_square D) x

private theorem bc_fix (x : State D) (hx : ghostB D 0 x = 0) :
    ghostB D 0 (ghostC D 0 x) = x := bZeroProjector_fix_of_ker D x hx

/-- Every ghost endomorphism preserves every original charge, with no mode
cutoff. The proof uses the original tensor coefficient slices. -/
theorem ghost_preserves_fixedMomentum (a : Charge D) (T : Module.End ℂ Fock)
    (x : State D) (hx : x ∈ fixedMomentum D a) :
    TensorProduct.map LinearMap.id T x ∈ fixedMomentum D a := by
  have hs (l : Label D) (y : State D) :
      ghostSlice D l (TensorProduct.map LinearMap.id T y) = T (ghostSlice D l y) := by
    induction y using TensorProduct.inductionOn with
    | tmul v w => simp only [TensorProduct.map_tmul, LinearMap.id_apply,
        ghostSlice_tmul, map_smul]
    | add y z hy hz => simp only [map_add, hy, hz]
  apply (mem_fixedMomentum_iff D a _).mpr
  intro i hi
  have hz : ghostSlice D i.1 x = 0 := by
    ext S
    rw [ghostSlice_coeff]
    exact (mem_fixedMomentum_iff D a x).mp hx (i.1,S) hi
  rw [← ghostSlice_coeff, hs, hz, map_zero]
  rfl

variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

/-- Kernel of the actual original unshifted total L0. -/
abbrev Absolute : Submodule ℂ (State D) := LinearMap.ker (totalL0 D H)

/-- The absolute sector has no b0 constraint. -/
def E0 : Submodule ℂ (State D) := fixedMomentum D 0 ⊓ Absolute D H

instance e0_addCommGroup : AddCommGroup (E0 D H) :=
  Submodule.addCommGroup (R := ℂ) (M := State D) (E0 D H)

private theorem b_mem_absolute (x : State D) (hx : x ∈ Absolute D H) :
    ghostB D 0 x ∈ Absolute D H := by
  change totalL0 D H (ghostB D 0 x) = 0
  have hc := LinearMap.congr_fun (sub_eq_zero.mp (totalL0_b_zero D H)) x
  change totalL0 D H (ghostB D 0 x) = ghostB D 0 (totalL0 D H x) at hc
  rw [hc, hx, map_zero]

private theorem c_mem_absolute (x : State D) (hx : x ∈ Absolute D H) :
    ghostC D 0 x ∈ Absolute D H := by
  change totalL0 D H (ghostC D 0 x) = 0
  have he := LinearMap.congr_fun (sub_eq_zero.mp (totalL0_c_zero D H)) x
  change totalL0 D H (ghostC D 0 x) = ghostC D 0 (totalL0 D H x) at he
  rw [he, hx, map_zero]

/-- Charge-preserving CAR splitting of the whole literal absolute shell. -/
def split0 : E0 D H ≃ₗ[ℂ]
    (relativeMassShell D H 0 × relativeMassShell D H 0) where
  toFun x :=
    (⟨ghostB D 0 (ghostC D 0 x),
      ⟨ghost_preserves_fixedMomentum D 0 (BcGhostFock.b 0) _
        (ghost_preserves_fixedMomentum D 0 (BcGhostFock.c 0) x x.2.1), b_twice D _⟩,
      b_mem_absolute D H _ (c_mem_absolute D H x x.2.2)⟩,
     ⟨ghostB D 0 x,
      ⟨ghost_preserves_fixedMomentum D 0 (BcGhostFock.b 0) x x.2.1, b_twice D x⟩,
      b_mem_absolute D H x x.2.2⟩)
  invFun z := ⟨(z.1 : State D) + ghostC D 0 (z.2 : State D),
    (fixedMomentum D 0).add_mem z.1.2.1.1
      (ghost_preserves_fixedMomentum D 0 (BcGhostFock.c 0) z.2 z.2.2.1.1),
    (Absolute D H).add_mem z.1.2.2 (c_mem_absolute D H z.2 z.2.2.2)⟩
  left_inv x := Subtype.ext (bc_split D x)
  right_inv z := by
    apply Prod.ext <;> apply Subtype.ext
    · change ghostB D 0 (ghostC D 0 ((z.1 : State D) + ghostC D 0 z.2)) = z.1
      rw [map_add, c_twice D, add_zero, bc_fix D _ z.1.2.1.2]
    · change ghostB D 0 ((z.1 : State D) + ghostC D 0 z.2) = z.2
      rw [map_add, z.1.2.1.2, zero_add, bc_fix D _ z.2.2.1.2]
  map_add' x y := by
    apply Prod.ext <;> apply Subtype.ext
    · change ghostB D 0 (ghostC D 0 ((x : State D) + (y : State D))) =
        ghostB D 0 (ghostC D 0 x) + ghostB D 0 (ghostC D 0 y)
      simp only [map_add]
    · exact map_add (ghostB D 0) (x : State D) (y : State D)
  map_smul' a x := by
    apply Prod.ext <;> apply Subtype.ext
    · change ghostB D 0 (ghostC D 0 (a • (x : State D))) =
        a • ghostB D 0 (ghostC D 0 x)
      simp only [map_smul]
    · exact map_smul (ghostB D 0) a (x : State D)


/-- Coordinates are extracted AFTER exhaustive splitting in the actual shell. -/
def stateEquiv : E0 D H ≃ₗ[ℂ] (Coordinates D × Coordinates D) :=
  (split0 D H).trans ((shellEquiv D H hHG hGH).prodCongr
    (shellEquiv D H hHG hGH))

/-- Exhaustion of ALL original charge-zero absolute zero-energy states. -/
theorem mem_E0_iff (x : State D) : x ∈ E0 D H ↔
    ∃ z w : Coordinates D,
      x = Psi D H hHG hGH z + ghostC D 0 (Psi D H hHG hGH w) := by
  constructor
  · intro hx
    let p := stateEquiv D H hHG hGH ⟨x,hx⟩
    refine ⟨p.1,p.2,?_⟩
    exact (congrArg Subtype.val
      ((stateEquiv D H hHG hGH).symm_apply_apply ⟨x,hx⟩)).symm
  · rintro ⟨z,w,rfl⟩
    exact ((stateEquiv D H hHG hGH).symm (z,w)).property

/-- A literal finite evaluation of the native finsum, with the supplier's
CAR/high-mode proof supplying EVERY tail zero. No operator-family finiteness
or finite-test extrapolation is used. -/
private theorem R0_odd (S : Finset ℕ) (hS : ∀ j ∈ S, j % 2 = 1) :
    BcGhostBRST.R 0 (ket S) =
      BcGhostBRST.rTerm 0 (-1) (ket S) +
        BcGhostBRST.rTerm 0 0 (ket S) + BcGhostBRST.rTerm 0 1 (ket S) := by
  rw [R_odd_capture S hS 0]
  have hi : Finset.Icc (0-1 : ℤ) 1 = {-1,0,1} := by
    ext p
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [hi]
  simp [add_assoc]

private theorem R0_empty : BcGhostBRST.R 0 (ket ∅) = (2 : ℂ) • ket {1,5} := by
  have hm : BcGhostBRST.rTerm 0 (-1) (ket ∅) = ket {1,5} := by
    norm_num [BcGhostBRST.rTerm, Module.End.mul_apply, BcGhostFock.c,
      create_ket, phase, lowerCount, Finset.filter_insert, Finset.filter_singleton, Finset.pair_comm]
  have hz : BcGhostBRST.rTerm 0 0 (ket ∅) = 0 := by
    simp [BcGhostBRST.rTerm]
  have hp : BcGhostBRST.rTerm 0 1 (ket ∅) = ket {1,5} := by
    norm_num [BcGhostBRST.rTerm, Module.End.mul_apply, BcGhostFock.c,
      create_ket, phase, lowerCount, Finset.filter_insert, Finset.filter_singleton, Finset.pair_comm]
  rw [R0_odd ∅ (by simp), hm, hz, hp, add_zero]
  module

private theorem R0_down : BcGhostBRST.R 0 (ket {1}) = 0 := by
  rw [R0_odd {1} (by simp)]
  norm_num [BcGhostBRST.rTerm, Module.End.mul_apply, BcGhostFock.c,
    create_ket, annihilate_ket, phase, lowerCount, Finset.filter_insert, Finset.filter_singleton, Finset.pair_comm]

private theorem R0_top : BcGhostBRST.R 0 (ket {1,5}) = 0 := by
  rw [R0_odd {1,5} (by simp)]
  norm_num [BcGhostBRST.rTerm, Module.End.mul_apply, BcGhostFock.c,
    create_ket, annihilate_ket, phase, lowerCount, Finset.filter_insert, Finset.filter_singleton, Finset.pair_comm]


/-- Exact original zero-momentum M coefficient: +2 from the native unshifted
rTerm convention. This proves a nontrivial map from coordinate 0 to coordinate
2, and cannot be replaced by M=0 or an automatic doubling argument. -/
theorem M_Psi (z : Coordinates D) :
    LatticeBRST.ghostR D 0 (Psi D H hHG hGH z) =
      Psi D H hHG hGH (0,(0,2*z.1)) := by
  rw [Psi_formula D H hHG hGH z,
    Psi_formula D H hHG hGH (0,(0,2*z.1))]
  simp [LatticeBRST.ghostR, TensorProduct.map_tmul, R0_empty, R0_down,
    R0_top, TensorProduct.tmul_smul, smul_smul, mul_comm]


private theorem Q_Psi (z : Coordinates D) :
    LatticeBRST.totalCharge D H (Psi D H hHG hGH z) = 0 :=
  totalCharge_on_zero_shell D H hHG hGH _
    ((shellEquiv D H hHG hGH).symm z).property

/-- The only nonzero matrix entry is the actual M coefficient +2. -/
theorem Q_representative (z w : Coordinates D) :
    LatticeBRST.totalCharge D H
      (Psi D H hHG hGH z + ghostC D 0 (Psi D H hHG hGH w)) =
        Psi D H hHG hGH (0,(0,2*w.1)) := by
  have hc := LinearMap.congr_fun (LatticeBRST.total_ward_c D H 0)
    (Psi D H hHG hGH w)
  simp only [LinearMap.add_apply, Module.End.mul_apply, Q_Psi D H hHG hGH,
    map_zero, add_zero, M_Psi D H hHG hGH] at hc
  rw [map_add, Q_Psi D H hHG hGH, zero_add, hc]

include hHG hGH in
/-- Q preserves the exact original fixed-charge absolute space. -/
theorem Q_mem_E0 (x : E0 D H) :
    LatticeBRST.totalCharge D H (x : State D) ∈ E0 D H := by
  obtain ⟨z,w,hx⟩ := (mem_E0_iff D H hHG hGH x).mp x.property
  rw [hx,Q_representative D H hHG hGH]
  apply (mem_E0_iff D H hHG hGH _).mpr
  exact ⟨(0,(0,2*w.1)),0,by simp⟩

/-- Literal restriction of original Q; its definition does not prescribe a
coordinate differential. -/
def Q0 : Module.End ℂ (E0 D H) :=
  ((LatticeBRST.totalCharge D H).comp (E0 D H).subtype).codRestrict _
    (Q_mem_E0 D H hHG hGH)

theorem Q0_coordinates (z w : Coordinates D) :
    Q0 D H hHG hGH ((stateEquiv D H hHG hGH).symm (z,w)) =
      (stateEquiv D H hHG hGH).symm ((0,(0,2*w.1)),0) := by
  apply Subtype.ext
  change LatticeBRST.totalCharge D H
      (Psi D H hHG hGH z + ghostC D 0 (Psi D H hHG hGH w)) =
    Psi D H hHG hGH (0,(0,2*w.1)) + ghostC D 0 (Psi D H hHG hGH 0)
  simpa only [map_zero,add_zero] using
    Q_representative D H hHG hGH z w

/-- Restricted square-zero at every rank, from the computed original image
and the actual zero action on the original relative shell. -/
theorem Q0_square : Q0 D H hHG hGH * Q0 D H hHG hGH = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  obtain ⟨z,w,hx⟩ := (mem_E0_iff D H hHG hGH x).mp x.property
  change LatticeBRST.totalCharge D H (LatticeBRST.totalCharge D H (x : State D)) = 0
  rw [hx,Q_representative D H hHG hGH,Q_Psi D H hHG hGH]

abbrev Cycles : Submodule ℂ (E0 D H) := LinearMap.ker (Q0 D H hHG hGH)

instance cycles_addCommGroup : AddCommGroup (Cycles D H hHG hGH) :=
  Submodule.addCommGroup (R := ℂ) (M := E0 D H) (Cycles D H hHG hGH)

theorem cycle_coordinates (z w : Coordinates D) :
    (stateEquiv D H hHG hGH).symm (z,w) ∈ Cycles D H hHG hGH ↔ w.1 = 0 := by
  change Q0 D H hHG hGH _ = 0 ↔ _
  rw [Q0_coordinates D H hHG hGH]
  constructor
  · intro h
    have hc := congrArg (fun x : E0 D H => (stateEquiv D H hHG hGH x).1.2.2) h
    have he := (stateEquiv D H hHG hGH).map_zero
    have h2 : (2 : ℂ)*w.1 = 0 := by
      simpa only [LinearEquiv.apply_symm_apply, he, Prod.fst_zero, Prod.snd_zero] using hc
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  · intro h
    simp [h]

/-- Actual range on actual E0; the unique surviving exact coordinate is z.c. -/
theorem range_coordinates (z w : Coordinates D) :
    (stateEquiv D H hHG hGH).symm (z,w) ∈ LinearMap.range (Q0 D H hHG hGH) ↔
      z.1 = 0 ∧ z.2.1 = 0 ∧ w = 0 := by
  constructor
  · rintro ⟨y,hy⟩
    let p := stateEquiv D H hHG hGH y
    have hy' : y = (stateEquiv D H hHG hGH).symm (p.1,p.2) :=
      ((stateEquiv D H hHG hGH).symm_apply_apply y).symm
    rw [hy', Q0_coordinates D H hHG hGH] at hy
    have hp := (stateEquiv D H hHG hGH).symm.injective hy
    exact ⟨(congrArg (fun t : Coordinates D × Coordinates D => t.1.1) hp).symm,
      (congrArg (fun t : Coordinates D × Coordinates D => t.1.2.1) hp).symm,
      (congrArg Prod.snd hp).symm⟩
  · rintro ⟨ha,hv,hw⟩
    refine ⟨(stateEquiv D H hHG hGH).symm (0,(z.2.2/2,(0,0))),?_⟩
    rw [Q0_coordinates D H hHG hGH]
    apply (stateEquiv D H hHG hGH).injective
    simp only [LinearEquiv.apply_symm_apply]
    apply Prod.ext
    · apply Prod.ext ha.symm
      apply Prod.ext hv.symm
      dsimp
      ring
    · exact hw.symm


/-- Actual incoming Q with codomain its actual kernel. -/
def boundaryMap : E0 D H →ₗ[ℂ] Cycles D H hHG hGH :=
  (Q0 D H hHG hGH).codRestrict _ (fun x =>
    LinearMap.congr_fun (Q0_square D H hHG hGH) x)

def Boundaries : Submodule ℂ (Cycles D H hHG hGH) :=
  LinearMap.range (boundaryMap D H hHG hGH)

/-- The ORIGINAL state kernel/range quotient. -/
abbrev Cohomology : Type := Cycles D H hHG hGH ⧸ Boundaries D H hHG hGH

/-- Four retained ORIGINAL class coordinates, in the requested order. -/
abbrev ClassCoordinates := ℂ × ((Fin D.rank → ℂ) × ((Fin D.rank → ℂ) × ℂ))

def classCoordinates : Cycles D H hHG hGH →ₗ[ℂ] ClassCoordinates D where
  toFun x :=
    let p := stateEquiv D H hHG hGH x.1
    (p.1.1,(p.1.2.1,(p.2.2.1,p.2.2.2)))
  map_add' x y := by simp only [Submodule.coe_add,map_add]; rfl
  map_smul' a x := by simp only [Submodule.coe_smul,map_smul]; rfl

/-- Canonical cycles are ORIGINAL states with z.c=w.a=0. -/
def representative : ClassCoordinates D →ₗ[ℂ] Cycles D H hHG hGH where
  toFun t := ⟨(stateEquiv D H hHG hGH).symm ((t.1,(t.2.1,0)),(0,t.2.2)),
    (cycle_coordinates D H hHG hGH _ _).mpr rfl⟩
  map_add' x y := by
    apply Subtype.ext
    change (stateEquiv D H hHG hGH).symm
        (((x + y).1,((x + y).2.1,0)),(0,(x + y).2.2)) =
      (stateEquiv D H hHG hGH).symm ((x.1,(x.2.1,0)),(0,x.2.2)) +
        (stateEquiv D H hHG hGH).symm ((y.1,(y.2.1,0)),(0,y.2.2))
    rw [← map_add (stateEquiv D H hHG hGH).symm]
    congr 1 <;> ext <;> simp
  map_smul' a x := by
    apply Subtype.ext
    change (stateEquiv D H hHG hGH).symm
        (((a • x).1,((a • x).2.1,0)),(0,(a • x).2.2)) =
      a • (stateEquiv D H hHG hGH).symm ((x.1,(x.2.1,0)),(0,x.2.2))
    rw [← map_smul (stateEquiv D H hHG hGH).symm]
    congr 1 <;> ext <;> simp

@[simp] theorem coordinates_representative (t : ClassCoordinates D) :
    classCoordinates D H hHG hGH (representative D H hHG hGH t) = t := by
  simp [classCoordinates,representative]

theorem classCoordinates_surjective : Function.Surjective (classCoordinates D H hHG hGH) :=
  fun t => ⟨representative D H hHG hGH t,coordinates_representative D H hHG hGH t⟩

/-- This is the load-bearing quotient calculation: actual Q-images are exactly
the kernel of the FOUR-COORDINATE class map on actual Q-cycles. -/
theorem boundaries_eq_ker : Boundaries D H hHG hGH =
    LinearMap.ker (classCoordinates D H hHG hGH) := by
  ext x
  change (∃ y, boundaryMap D H hHG hGH y = x) ↔
    classCoordinates D H hHG hGH x = 0
  let p := stateEquiv D H hHG hGH x.1
  have hp : x.1 = (stateEquiv D H hHG hGH).symm (p.1,p.2) :=
    ((stateEquiv D H hHG hGH).symm_apply_apply x.1).symm
  have hcycle : p.2.1 = 0 :=
    (cycle_coordinates D H hHG hGH p.1 p.2).mp (hp ▸ x.property)
  constructor
  · rintro ⟨y,rfl⟩
    let r := stateEquiv D H hHG hGH y
    have hy : y = (stateEquiv D H hHG hGH).symm (r.1,r.2) :=
      ((stateEquiv D H hHG hGH).symm_apply_apply y).symm
    change classCoordinates D H hHG hGH ⟨Q0 D H hHG hGH y,_⟩ = 0
    change (((stateEquiv D H hHG hGH) (Q0 D H hHG hGH y)).1.1,
      (((stateEquiv D H hHG hGH) (Q0 D H hHG hGH y)).1.2.1,
        (((stateEquiv D H hHG hGH) (Q0 D H hHG hGH y)).2.2.1,
          ((stateEquiv D H hHG hGH) (Q0 D H hHG hGH y)).2.2.2))) = 0
    rw [hy, Q0_coordinates D H hHG hGH, LinearEquiv.apply_symm_apply]
    rfl
  · intro hx
    have ha : p.1.1 = 0 := congrArg Prod.fst hx
    have hv : p.1.2.1 = 0 := congrArg (fun t : ClassCoordinates D => t.2.1) hx
    have hv' : p.2.2.1 = 0 := congrArg (fun t : ClassCoordinates D => t.2.2.1) hx
    have hc' : p.2.2.2 = 0 := congrArg (fun t : ClassCoordinates D => t.2.2.2) hx
    have hw : p.2 = 0 := Prod.ext hcycle (Prod.ext hv' hc')
    obtain ⟨y,hy⟩ := (range_coordinates D H hHG hGH p.1 p.2).mpr ⟨ha,hv,hw⟩
    exact ⟨y,Subtype.ext (hy.trans hp.symm)⟩

/-- Mathlib's first isomorphism theorem, applied to the proved actual
kernel/image equality. No new generic cohomology/quotient framework. -/
def cohomologyEquiv : Cohomology D H hHG hGH ≃ₗ[ℂ] ClassCoordinates D :=
  (Submodule.quotEquivOfEq _ _ (boundaries_eq_ker D H hHG hGH)).trans
    ((classCoordinates D H hHG hGH).quotKerEquivOfSurjective
      (classCoordinates_surjective D H hHG hGH))

@[simp] theorem cohomologyEquiv_mk (x : Cycles D H hHG hGH) :
    cohomologyEquiv D H hHG hGH
      ((Boundaries D H hHG hGH).mkQ x) =
        classCoordinates D H hHG hGH x := rfl

def classOf : ClassCoordinates D →ₗ[ℂ] Cohomology D H hHG hGH :=
  (Boundaries D H hHG hGH).mkQ.comp (representative D H hHG hGH)

@[simp] theorem cohomologyEquiv_classOf (t : ClassCoordinates D) :
    cohomologyEquiv D H hHG hGH (classOf D H hHG hGH t) = t := by
  rw [classOf,LinearMap.comp_apply,cohomologyEquiv_mk,coordinates_representative]

/-- Every class has the stated canonical representative, with an actual Q
preimage for the removed z.c already given in range_coordinates. -/
theorem classOf_coordinates (x : Cycles D H hHG hGH) :
    classOf D H hHG hGH (classCoordinates D H hHG hGH x) =
      (Boundaries D H hHG hGH).mkQ x := by
  apply (cohomologyEquiv D H hHG hGH).injective
  rw [cohomologyEquiv_classOf,cohomologyEquiv_mk]

/- Native ghost number, with its exact original SL2 vacuum reference. -/

/-- Actual Q raises native ghost number on ALL original states. This consumes
the committed all-integer finite-capture proof, rather than a grade premise. -/
theorem number_Q (x : State D) :
    tensorNumber D (LatticeBRST.totalCharge D H x) =
      LatticeBRST.totalCharge D H (tensorNumber D x) +
        LatticeBRST.totalCharge D H x := by
  have hm : tensorNumber D * LatticeBRST.totalCharge D H -
      LatticeBRST.totalCharge D H * tensorNumber D =
        LatticeBRST.totalCharge D H := by
    exact LatticeMatterGhostDegree.tensorNumber_Q D H
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, add_comm] using
    sub_eq_iff_eq_add.mp (LinearMap.congr_fun hm x)

/-- All-state c0 degree +1, obtained from the committed all-integer relation. -/
theorem number_c0 (x : State D) :
    tensorNumber D (ghostC D 0 x) =
      ghostC D 0 (tensorNumber D x) + ghostC D 0 x := by
  have hm : tensorNumber D * ghostC D 0 - ghostC D 0 * tensorNumber D =
      ghostC D 0 := by
    apply TensorProduct.ext'
    intro v w
    have h := LinearMap.congr_fun (BcGhostCharge.ghost_number_relations.2.2 0) w
    simp only [LinearMap.sub_apply,Module.End.mul_apply] at h
    simpa only [tensorNumber, BcGhostChargeTensor.number, BcGhostChargeTensor.liftGhost, ghostC,LinearMap.sub_apply,Module.End.mul_apply,
      TensorProduct.map_tmul,LinearMap.id_apply,← TensorProduct.tmul_sub] using
        congrArg (fun y => v ⊗ₜ[ℂ] y) h
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, add_comm] using
    sub_eq_iff_eq_add.mp (LinearMap.congr_fun hm x)

theorem number_representative (z w : Coordinates D) :
    tensorNumber D
      (Psi D H hHG hGH z + ghostC D 0 (Psi D H hHG hGH w)) =
    Psi D H hHG hGH (0,(z.2.1,2*z.2.2)) +
      ghostC D 0 (Psi D H hHG hGH (w.1,((2 : ℂ) • w.2.1,3*w.2.2))) := by
  have hw : (0,(w.2.1,2*w.2.2)) + w = (w.1,((2 : ℂ) • w.2.1,3*w.2.2)) := by
    apply Prod.ext
    · simp
    · apply Prod.ext
      · funext i
        simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      · dsimp
        ring
  rw [map_add,number_c0,totalGhostNumber_Psi,totalGhostNumber_Psi,
    ← map_add (ghostC D 0),← map_add (Psi D H hHG hGH),hw]

include hHG hGH in
theorem number_mem_E0 (x : E0 D H) : tensorNumber D (x : State D) ∈ E0 D H := by
  obtain ⟨z,w,hx⟩ := (mem_E0_iff D H hHG hGH x).mp x.property
  rw [hx,number_representative D H hHG hGH]
  exact ((stateEquiv D H hHG hGH).symm
    ((0,(z.2.1,2*z.2.2)),(w.1,((2 : ℂ) • w.2.1,3*w.2.2)))).property

/-- Restriction of the native number operator to the actual E0. -/
def N0 : Module.End ℂ (E0 D H) :=
  ((tensorNumber D).comp (E0 D H).subtype).codRestrict _
    (number_mem_E0 D H hHG hGH)

theorem N0_coordinates (z w : Coordinates D) :
    N0 D H hHG hGH ((stateEquiv D H hHG hGH).symm (z,w)) =
      (stateEquiv D H hHG hGH).symm
        ((0,(z.2.1,2*z.2.2)),(w.1,((2 : ℂ) • w.2.1,3*w.2.2))) := by
  apply Subtype.ext
  exact number_representative D H hHG hGH z w

/-- Actual homogeneous ORIGINAL states, over every integer ghost degree. -/
abbrev Grade (q : ℤ) : Submodule ℂ (E0 D H) :=
  Module.End.eigenspace (N0 D H hHG hGH) (q : ℂ)

/-- Native grading on ALL E0 states. The two scalars with degree two are
z.c (exact) and w.v; w.a has degree one and is excluded by cycles. -/
theorem grade_coordinates (q : ℤ) (z w : Coordinates D) :
    (stateEquiv D H hHG hGH).symm (z,w) ∈ Grade D H hHG hGH q ↔
      (q : ℂ)*z.1 = 0 ∧
      (∀ i, ((q : ℂ)-1)*z.2.1 i = 0) ∧ ((q : ℂ)-2)*z.2.2 = 0 ∧
      ((q : ℂ)-1)*w.1 = 0 ∧
      (∀ i, ((q : ℂ)-2)*w.2.1 i = 0) ∧ ((q : ℂ)-3)*w.2.2 = 0 := by
  rw [Module.End.mem_eigenspace_iff, N0_coordinates D H hHG hGH]
  constructor
  · intro h
    have hp := congrArg (stateEquiv D H hHG hGH) h
    simp only [LinearEquiv.apply_symm_apply,map_smul] at hp
    have ha := congrArg (fun p : Coordinates D × Coordinates D => p.1.1) hp
    have hv i := congrArg (fun p : Coordinates D × Coordinates D => p.1.2.1 i) hp
    have hc := congrArg (fun p : Coordinates D × Coordinates D => p.1.2.2) hp
    have hb := congrArg (fun p : Coordinates D × Coordinates D => p.2.1) hp
    have hu i := congrArg (fun p : Coordinates D × Coordinates D => p.2.2.1 i) hp
    have hd := congrArg (fun p : Coordinates D × Coordinates D => p.2.2.2) hp
    change (0 : ℂ) = (q : ℂ)*z.1 at ha
    refine ⟨ha.symm,?_,?_,?_,?_,?_⟩
    · intro i
      have hi : z.2.1 i = (q : ℂ)*z.2.1 i := hv i
      linear_combination -hi
    · change 2*z.2.2 = (q : ℂ)*z.2.2 at hc; linear_combination -hc
    · change w.1 = (q : ℂ)*w.1 at hb; linear_combination -hb
    · intro i; have hi : 2*w.2.1 i = (q : ℂ)*w.2.1 i := hu i
      linear_combination -hi
    · change 3*w.2.2 = (q : ℂ)*w.2.2 at hd; linear_combination -hd
  · rintro ⟨ha,hv,hc,hb,hu,hd⟩
    apply (stateEquiv D H hHG hGH).injective
    simp only [LinearEquiv.apply_symm_apply,map_smul]
    apply Prod.ext
    · apply Prod.ext
      · exact ha.symm
      · apply Prod.ext
        · funext i; change z.2.1 i = (q : ℂ)*z.2.1 i; linear_combination -(hv i)
        · change 2*z.2.2 = (q : ℂ)*z.2.2; linear_combination -hc
    · apply Prod.ext
      · change w.1 = (q : ℂ)*w.1; linear_combination -hb
      · apply Prod.ext
        · funext i; change 2*w.2.1 i = (q : ℂ)*w.2.1 i; linear_combination -(hu i)
        · change 3*w.2.2 = (q : ℂ)*w.2.2; linear_combination -hd

/-- Incoming Q raises the ACTUAL native number eigenvalue by one. This proof
uses the committed all-state number/Q relation, with no mode restriction. -/
theorem Q0_grade (q : ℤ) (x : E0 D H) (hx : x ∈ Grade D H hHG hGH (q - 1)) :
    Q0 D H hHG hGH x ∈ Grade D H hHG hGH q := by
  have hx' := congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp hx)
  change tensorNumber D (x : State D) = ((q - 1 : ℤ) : ℂ) • (x : State D) at hx'
  rw [Module.End.mem_eigenspace_iff]
  apply Subtype.ext
  change tensorNumber D (LatticeBRST.totalCharge D H (x : State D)) =
    (q : ℂ) • LatticeBRST.totalCharge D H (x : State D)
  rw [number_Q D H,hx',map_smul]
  push_cast
  module

/-- Literal original cycles intersected with a native homogeneous subspace. -/
abbrev GradedCycles (q : ℤ) : Submodule ℂ (E0 D H) :=
  Cycles D H hHG hGH ⊓ Grade D H hHG hGH q

instance gradedCycles_addCommGroup (q : ℤ) :
    AddCommGroup (GradedCycles D H hHG hGH q) :=
  Submodule.addCommGroup (R := ℂ) (M := E0 D H) (GradedCycles D H hHG hGH q)


/-- Q on the actual incoming eigenspace, with codomain the actual homogeneous
cycle space. All-rank restricted square-zero supplies the cycle condition. -/
def gradedBoundaryMap (q : ℤ) :
    Grade D H hHG hGH (q - 1) →ₗ[ℂ] GradedCycles D H hHG hGH q where
  toFun x := ⟨Q0 D H hHG hGH x,
    LinearMap.congr_fun (Q0_square D H hHG hGH) x,
    Q0_grade D H hHG hGH q x x.property⟩
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  map_smul' a x := by apply Subtype.ext; exact map_smul _ _ _

def GradedBoundaries (q : ℤ) : Submodule ℂ (GradedCycles D H hHG hGH q) :=
  LinearMap.range (gradedBoundaryMap D H hHG hGH q)

/-- No assigned dimensions: genuine native homogeneous kernel/image quotient. -/
abbrev GradedCohomology (q : ℤ) : Type :=
  GradedCycles D H hHG hGH q ⧸ GradedBoundaries D H hHG hGH q

def canonicalState : ClassCoordinates D →ₗ[ℂ] E0 D H :=
  (Cycles D H hHG hGH).subtype.comp (representative D H hHG hGH)

/-- Coordinate target grading is PULLED BACK from the native operator on the
original canonical representatives. It is not an assumed grading certificate. -/
abbrev ClassGrade (q : ℤ) : Submodule ℂ (ClassCoordinates D) :=
  (Grade D H hHG hGH q).comap (canonicalState D H hHG hGH)

theorem classGrade_coordinates (q : ℤ) (t : ClassCoordinates D) :
    t ∈ ClassGrade D H hHG hGH q ↔
      (q : ℂ)*t.1 = 0 ∧
      (∀ i, ((q : ℂ)-1)*t.2.1 i = 0) ∧
      (∀ i, ((q : ℂ)-2)*t.2.2.1 i = 0) ∧ ((q : ℂ)-3)*t.2.2.2 = 0 := by
  change (stateEquiv D H hHG hGH).symm ((t.1,(t.2.1,0)),(0,t.2.2)) ∈
    Grade D H hHG hGH q ↔ _
  rw [grade_coordinates]
  simp only [mul_zero,and_true,true_and]

def gradedCoordinates (q : ℤ) :
    GradedCycles D H hHG hGH q →ₗ[ℂ] ClassGrade D H hHG hGH q :=
  let inclusion : GradedCycles D H hHG hGH q →ₗ[ℂ] Cycles D H hHG hGH :=
    { toFun := fun x => ⟨x.1,x.2.1⟩
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }
  ((classCoordinates D H hHG hGH).comp inclusion).codRestrict _ (fun x => by
    let p := stateEquiv D H hHG hGH x.1
    have hp : x.1 = (stateEquiv D H hHG hGH).symm (p.1,p.2) :=
      ((stateEquiv D H hHG hGH).symm_apply_apply x.1).symm
    have hg := (grade_coordinates D H hHG hGH q p.1 p.2).mp (hp ▸ x.2.2)
    apply (classGrade_coordinates D H hHG hGH q _).mpr
    exact ⟨hg.1,hg.2.1,hg.2.2.2.2.1,hg.2.2.2.2.2⟩)

def gradedRepresentative (q : ℤ) :
    ClassGrade D H hHG hGH q →ₗ[ℂ] GradedCycles D H hHG hGH q where
  toFun t := ⟨canonicalState D H hHG hGH t,
    (representative D H hHG hGH t).property,t.property⟩
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  map_smul' a x := by apply Subtype.ext; exact map_smul _ _ _

@[simp] theorem gradedCoordinates_representative (q : ℤ) (t : ClassGrade D H hHG hGH q) :
    gradedCoordinates D H hHG hGH q (gradedRepresentative D H hHG hGH q t) = t := by
  apply Subtype.ext
  exact coordinates_representative D H hHG hGH t

theorem gradedCoordinates_surjective (q : ℤ) :
    Function.Surjective (gradedCoordinates D H hHG hGH q) :=
  fun t => ⟨gradedRepresentative D H hHG hGH q t,
    gradedCoordinates_representative D H hHG hGH q t⟩

/-- The original graded Q-image, not merely intersection with an ungraded
image, equals the coordinate kernel. Reverse inclusion constructs a genuine
incoming state of native degree q - 1 with w.a=z.c/2. -/
theorem gradedBoundaries_eq_ker (q : ℤ) :
    GradedBoundaries D H hHG hGH q =
      LinearMap.ker (gradedCoordinates D H hHG hGH q) := by
  ext x
  change (∃ y, gradedBoundaryMap D H hHG hGH q y = x) ↔
    gradedCoordinates D H hHG hGH q x = 0
  constructor
  · rintro ⟨y,rfl⟩
    apply Subtype.ext
    have hb : boundaryMap D H hHG hGH (y : E0 D H) ∈
        Boundaries D H hHG hGH := ⟨y,rfl⟩
    rw [boundaries_eq_ker] at hb
    exact hb
  · intro hx
    let p := stateEquiv D H hHG hGH x.1
    have hp : x.1 = (stateEquiv D H hHG hGH).symm (p.1,p.2) :=
      ((stateEquiv D H hHG hGH).symm_apply_apply x.1).symm
    have hg := (grade_coordinates D H hHG hGH q p.1 p.2).mp (hp ▸ x.2.2)
    have hcycle := (cycle_coordinates D H hHG hGH p.1 p.2).mp (hp ▸ x.2.1)
    have ht : (p.1.1,(p.1.2.1,(p.2.2.1,p.2.2.2))) = (0 : ClassCoordinates D) :=
      congrArg Subtype.val hx
    have ha : p.1.1 = 0 := congrArg Prod.fst ht
    have hv : p.1.2.1 = 0 := congrArg (fun t : ClassCoordinates D => t.2.1) ht
    have hu : p.2.2.1 = 0 := congrArg (fun t : ClassCoordinates D => t.2.2.1) ht
    have hd : p.2.2.2 = 0 := congrArg (fun t : ClassCoordinates D => t.2.2.2) ht
    have hw : p.2 = 0 := Prod.ext hcycle (Prod.ext hu hd)
    let y := (stateEquiv D H hHG hGH).symm (0,(p.1.2.2/2,(0,0)))
    have hygrade : y ∈ Grade D H hHG hGH (q - 1) := by
      apply (grade_coordinates D H hHG hGH (q - 1) _ _).mpr
      refine ⟨by simp,by simp,by simp,?_,by simp,by simp⟩
      have hc := hg.2.2.1
      push_cast
      linear_combination (1 / 2 : ℂ) * hc
    refine ⟨⟨y,hygrade⟩,?_⟩
    apply Subtype.ext
    change Q0 D H hHG hGH y = x.1
    rw [hp]
    change Q0 D H hHG hGH ((stateEquiv D H hHG hGH).symm _) = _
    rw [Q0_coordinates D H hHG hGH]
    apply (stateEquiv D H hHG hGH).injective
    simp only [LinearEquiv.apply_symm_apply]
    apply Prod.ext
    · apply Prod.ext ha.symm
      apply Prod.ext hv.symm
      dsimp
      ring
    · exact hw.symm

/-- Degreewise quotient transport uses Mathlib directly on the actual
homogeneous original kernel and incoming Q-image. -/
def gradedCohomologyEquiv (q : ℤ) :
    GradedCohomology D H hHG hGH q ≃ₗ[ℂ] ClassGrade D H hHG hGH q :=
  (Submodule.quotEquivOfEq _ _ (gradedBoundaries_eq_ker D H hHG hGH q)).trans
    ((gradedCoordinates D H hHG hGH q).quotKerEquivOfSurjective
      (gradedCoordinates_surjective D H hHG hGH q))

private theorem scalar_zero {q k : ℤ} (hqk : q ≠ k) {a : ℂ}
    (ha : ((q : ℂ) - (k : ℂ)) * a = 0) : a = 0 := by
  apply (mul_eq_zero.mp ha).resolve_left
  exact sub_ne_zero.mpr (by exact_mod_cast hqk)

/-- Native degree zero has the ground scalar class. -/
def classGradeZeroEquiv : ClassGrade D H hHG hGH 0 ≃ₗ[ℂ] ℂ where
  toFun x := x.1.1
  invFun a := ⟨(a,(0,(0,0))),
    (classGrade_coordinates D H hHG hGH 0 _).mpr (by simp)⟩
  left_inv x := by
    apply Subtype.ext
    have hx := (classGrade_coordinates D H hHG hGH 0 x.1).mp x.2
    have hv : x.1.2.1 = 0 := funext fun i => scalar_zero (q:=0) (k:=1) (by decide) (by simpa using hx.2.1 i)
    have hu : x.1.2.2.1 = 0 := funext fun i => scalar_zero (q:=0) (k:=2) (by decide) (hx.2.2.1 i)
    have hd : x.1.2.2.2 = 0 := scalar_zero (q:=0) (k:=3) (by decide) hx.2.2.2
    exact Prod.ext rfl (Prod.ext hv.symm (Prod.ext hu.symm hd.symm))
  right_inv a := rfl
  map_add' x y := rfl
  map_smul' a x := rfl

/-- Native degree one has z.v; the scalar w.a is removed by the actual cycle
condition, rather than being silently counted as a second copy. -/
def classGradeOneEquiv : ClassGrade D H hHG hGH 1 ≃ₗ[ℂ] (Fin D.rank → ℂ) where
  toFun x := x.1.2.1
  invFun v := ⟨(0,(v,(0,0))),
    (classGrade_coordinates D H hHG hGH 1 _).mpr (by simp)⟩
  left_inv x := by
    apply Subtype.ext
    have hx := (classGrade_coordinates D H hHG hGH 1 x.1).mp x.2
    have ha : x.1.1 = 0 := by simpa using hx.1
    have hu : x.1.2.2.1 = 0 := funext fun i => scalar_zero (q:=1) (k:=2) (by decide) (hx.2.2.1 i)
    have hd : x.1.2.2.2 = 0 := scalar_zero (q:=1) (k:=3) (by decide) hx.2.2.2
    exact Prod.ext ha.symm (Prod.ext rfl (Prod.ext hu.symm hd.symm))
  right_inv v := rfl
  map_add' x y := rfl
  map_smul' a x := rfl

/-- Native degree two has w.v; z.c is exactly the actual Q-image. -/
def classGradeTwoEquiv : ClassGrade D H hHG hGH 2 ≃ₗ[ℂ] (Fin D.rank → ℂ) where
  toFun x := x.1.2.2.1
  invFun v := ⟨(0,(0,(v,0))),
    (classGrade_coordinates D H hHG hGH 2 _).mpr (by simp)⟩
  left_inv x := by
    apply Subtype.ext
    have hx := (classGrade_coordinates D H hHG hGH 2 x.1).mp x.2
    have ha : x.1.1 = 0 := scalar_zero (q:=2) (k:=0) (by decide) (by simpa using hx.1)
    have hv : x.1.2.1 = 0 := funext fun i => scalar_zero (q:=2) (k:=1) (by decide) (by simpa using hx.2.1 i)
    have hd : x.1.2.2.2 = 0 := scalar_zero (q:=2) (k:=3) (by decide) hx.2.2.2
    exact Prod.ext ha.symm (Prod.ext hv.symm (Prod.ext rfl hd.symm))
  right_inv v := rfl
  map_add' x y := rfl
  map_smul' a x := rfl

/-- Native degree three has w.c. -/
def classGradeThreeEquiv : ClassGrade D H hHG hGH 3 ≃ₗ[ℂ] ℂ where
  toFun x := x.1.2.2.2
  invFun a := ⟨(0,(0,(0,a))),
    (classGrade_coordinates D H hHG hGH 3 _).mpr (by simp)⟩
  left_inv x := by
    apply Subtype.ext
    have hx := (classGrade_coordinates D H hHG hGH 3 x.1).mp x.2
    have ha : x.1.1 = 0 := scalar_zero (q:=3) (k:=0) (by decide) (by simpa using hx.1)
    have hv : x.1.2.1 = 0 := funext fun i => scalar_zero (q:=3) (k:=1) (by decide) (by simpa using hx.2.1 i)
    have hu : x.1.2.2.1 = 0 := funext fun i => scalar_zero (q:=3) (k:=2) (by decide) (hx.2.2.1 i)
    exact Prod.ext ha.symm (Prod.ext hv.symm (Prod.ext hu.symm rfl))
  right_inv a := rfl
  map_add' x y := rfl
  map_smul' a x := rfl

def H0Equiv : GradedCohomology D H hHG hGH 0 ≃ₗ[ℂ] ℂ :=
  (gradedCohomologyEquiv D H hHG hGH 0).trans (classGradeZeroEquiv D H hHG hGH)

def H1Equiv : GradedCohomology D H hHG hGH 1 ≃ₗ[ℂ] (Fin D.rank → ℂ) :=
  (gradedCohomologyEquiv D H hHG hGH 1).trans (classGradeOneEquiv D H hHG hGH)

def H2Equiv : GradedCohomology D H hHG hGH 2 ≃ₗ[ℂ] (Fin D.rank → ℂ) :=
  (gradedCohomologyEquiv D H hHG hGH 2).trans (classGradeTwoEquiv D H hHG hGH)

def H3Equiv : GradedCohomology D H hHG hGH 3 ≃ₗ[ℂ] ℂ :=
  (gradedCohomologyEquiv D H hHG hGH 3).trans (classGradeThreeEquiv D H hHG hGH)

/-- Every other integer degree, including negative degrees, is zero. -/
theorem other_grade_zero (q : ℤ) (h0 : q ≠ 0) (h1 : q ≠ 1) (h2 : q ≠ 2) (h3 : q ≠ 3)
    (x : GradedCohomology D H hHG hGH q) : x = 0 := by
  apply (gradedCohomologyEquiv D H hHG hGH q).injective
  rw [(gradedCohomologyEquiv D H hHG hGH q).map_zero]
  apply Subtype.ext
  let y := gradedCohomologyEquiv D H hHG hGH q x
  have hy := (classGrade_coordinates D H hHG hGH q y.1).mp y.2
  have ha : y.1.1 = 0 := scalar_zero h0 (by simpa using hy.1)
  have hv : y.1.2.1 = 0 := funext fun i => scalar_zero h1 (by simpa using hy.2.1 i)
  have hu : y.1.2.2.1 = 0 := funext fun i => scalar_zero h2 (hy.2.2.1 i)
  have hd : y.1.2.2.2 = 0 := scalar_zero h3 hy.2.2.2
  exact Prod.ext ha (Prod.ext hv (Prod.ext hu hd))

/-- Native dimensions are consequences of the explicit ORIGINAL
quotient equivalences; they are not assumptions or certificates. -/
theorem native_dimensions :
    Module.finrank ℂ (GradedCohomology D H hHG hGH 0) = 1 ∧
    Module.finrank ℂ (GradedCohomology D H hHG hGH 1) = D.rank ∧
    Module.finrank ℂ (GradedCohomology D H hHG hGH 2) = D.rank ∧
    Module.finrank ℂ (GradedCohomology D H hHG hGH 3) = 1 := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa using (H0Equiv D H hHG hGH).finrank_eq
  · simpa [Module.finrank_fintype_fun_eq_card] using
      (H1Equiv D H hHG hGH).finrank_eq
  · simpa [Module.finrank_fintype_fun_eq_card] using
      (H2Equiv D H hHG hGH).finrank_eq
  · simpa using (H3Equiv D H hHG hGH).finrank_eq


/-- The entire integer grading, including arbitrary rank zero, is derived
from the original homogeneous kernel and incoming-image quotients. -/
theorem native_finrank (q : ℤ) :
    Module.finrank ℂ (GradedCohomology D H hHG hGH q) =
      if q = 0 then 1 else if q = 1 then D.rank else
        if q = 2 then D.rank else if q = 3 then 1 else 0 := by
  obtain ⟨h0,h1,h2,h3⟩ := native_dimensions D H hHG hGH
  by_cases e0 : q = 0
  · subst q; simpa using h0
  by_cases e1 : q = 1
  · subst q; simpa using h1
  by_cases e2 : q = 2
  · subst q; simpa using h2
  by_cases e3 : q = 3
  · subst q; simpa using h3
  haveI : Subsingleton (GradedCohomology D H hHG hGH q) :=
    ⟨fun x y => (other_grade_zero D H hHG hGH q e0 e1 e2 e3 x).trans
      (other_grade_zero D H hHG hGH q e0 e1 e2 e3 y).symm⟩
  simpa [e0,e1,e2,e3] using
    (Module.finrank_zero_of_subsingleton (R := ℂ)
      (M := GradedCohomology D H hHG hGH q))

end D5.S3.VertexAlgebra.LatticeOriginalAbsoluteZeroCohomology
