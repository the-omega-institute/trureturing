/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldClosedSemirelative
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldClosedSemirelative
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native closed semirelative BRST complex and level-matched difference zero modes. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldClosedRelativeKunneth
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Batteries.Tactic.OpenPrivate

/-!
# The native original-orbifold closed semirelative complex

The closed charge acts on the tensor of two original critical-matter and bc-ghost
states. The difference antighost and Virasoro zero modes define the semirelative
carrier. On the level-matched carrier the conjugate ghost zero mode gives two
semirelative coordinates with a connection term in the differential.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.OriginalOrbifoldClosedSemirelative

open D5.S3.Quantum.Fermionic
open D5.S3.HomologicalAlgebra.FinitePerturbation (Boundaries Cohomology)
open OriginalOrbifoldCriticalMatter (Matter State Q b matterDatum Q_squared Q_ward_b)
open OriginalOrbifoldBRSTSignedLocality (parity)
open OriginalOrbifoldBRSTDescent (relativeStates relativeDifferential)
open OriginalOrbifoldClosedRelativeKunneth
  (ClosedRelativeState ClosedRelativeCohomology chiralComplex closedDifferential
    closedDifferential_tmul relativeParity_val)

open private parity_square Q_parity b_zero_parity b_square from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTDescent
open private cycleMap cohomologyMap cohomologyMap_mk from
  D5.S3.HomologicalAlgebra.FinitePerturbationCohomology

noncomputable section

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

abbrev ClosedState := State ⊗[ℂ] State

private abbrev b0 : Module.End ℂ State := b 0
private abbrev c0 : Module.End ℂ State := VirasoroBRST.ghostC matterDatum 0
private abbrev L0 : Module.End ℂ State := VirasoroBRST.Ltotal matterDatum 0

/-- The left ghost parity implements the right-hand Koszul action. -/
def closedQ : Module.End ℂ ClosedState :=
  TensorProduct.map Q LinearMap.id + TensorProduct.map parity Q

def bMinus : Module.End ℂ ClosedState :=
  TensorProduct.map b0 LinearMap.id - TensorProduct.map parity b0

def LMinus : Module.End ℂ ClosedState :=
  TensorProduct.map L0 LinearMap.id - TensorProduct.map LinearMap.id L0

theorem closedQ_tmul (x y : State) :
    closedQ (x ⊗ₜ[ℂ] y) = Q x ⊗ₜ[ℂ] y + parity x ⊗ₜ[ℂ] Q y := by
  simp only [closedQ, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply]

theorem bMinus_tmul (x y : State) :
    bMinus (x ⊗ₜ[ℂ] y) = b0 x ⊗ₜ[ℂ] y - parity x ⊗ₜ[ℂ] b0 y := by
  simp only [bMinus, LinearMap.sub_apply, TensorProduct.map_tmul, LinearMap.id_apply]

theorem LMinus_tmul (x y : State) :
    LMinus (x ⊗ₜ[ℂ] y) = L0 x ⊗ₜ[ℂ] y - x ⊗ₜ[ℂ] L0 y := by
  simp only [LMinus, LinearMap.sub_apply, TensorProduct.map_tmul, LinearMap.id_apply]

private theorem chiralQ_twice (x : State) : Q (Q x) = 0 := by
  simpa only [pow_two, Module.End.mul_apply, LinearMap.zero_apply] using
    LinearMap.congr_fun Q_squared x

private theorem chiralWard (x : State) : Q (b0 x) + b0 (Q x) = L0 x :=
  LinearMap.congr_fun (Q_ward_b 0) x

theorem closedQ_square : closedQ * closedQ = 0 := by
  apply TensorProduct.ext'
  intro x y
  simp only [Module.End.mul_apply, closedQ_tmul, map_add, chiralQ_twice,
    Q_parity, parity_square, TensorProduct.zero_tmul, TensorProduct.tmul_zero,
    TensorProduct.neg_tmul, LinearMap.zero_apply]
  abel

theorem bMinus_square : bMinus * bMinus = 0 := by
  apply TensorProduct.ext'
  intro x y
  simp only [Module.End.mul_apply, bMinus_tmul, map_sub, b_square,
    b_zero_parity, parity_square, TensorProduct.zero_tmul, TensorProduct.tmul_zero,
    TensorProduct.neg_tmul, LinearMap.zero_apply]
  abel

/-- The mixed left/right terms cancel. The right chiral Ward term has a minus sign. -/
theorem closed_ward : closedQ * bMinus + bMinus * closedQ = LMinus := by
  apply TensorProduct.ext'
  intro x y
  change closedQ (bMinus (x ⊗ₜ[ℂ] y)) + bMinus (closedQ (x ⊗ₜ[ℂ] y)) =
    LMinus (x ⊗ₜ[ℂ] y)
  simp only [closedQ_tmul, bMinus_tmul, LMinus_tmul, map_add, map_sub, Q_parity,
    b_zero_parity, parity_square, TensorProduct.neg_tmul]
  calc
    _ = (Q (b0 x) + b0 (Q x)) ⊗ₜ[ℂ] y -
        x ⊗ₜ[ℂ] (Q (b0 y) + b0 (Q y)) := by
      simp only [TensorProduct.add_tmul, TensorProduct.tmul_add]
      abel
    _ = _ := by rw [chiralWard, chiralWard]

theorem LMinus_closedQ : LMinus * closedQ = closedQ * LMinus := by
  rw [← closed_ward, add_mul, mul_add, mul_assoc bMinus closedQ closedQ,
    ← mul_assoc closedQ closedQ bMinus, closedQ_square, mul_zero, zero_mul,
    add_zero, zero_add, mul_assoc]

theorem LMinus_bMinus : LMinus * bMinus = bMinus * LMinus := by
  rw [← closed_ward, add_mul, mul_add, mul_assoc closedQ bMinus bMinus,
    ← mul_assoc bMinus bMinus closedQ, bMinus_square, mul_zero, zero_mul,
    zero_add, add_zero, mul_assoc]

/-- Level matching keeps the common value of the two energies unrestricted. -/
abbrev levelMatched : Submodule ℂ ClosedState := LinearMap.ker LMinus

def levelMatchedDifferential : Module.End ℂ levelMatched :=
  closedQ.restrict (fun x hx => by
    change LMinus x = 0 at hx
    change LMinus (closedQ x) = 0
    simpa only [Module.End.mul_apply, hx, map_zero] using
      LinearMap.congr_fun LMinus_closedQ x)

theorem levelMatchedDifferential_square :
    levelMatchedDifferential * levelMatchedDifferential = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun closedQ_square (x : ClosedState)

def semirelativeStates : Submodule ℂ ClosedState :=
  LinearMap.ker bMinus ⊓ LinearMap.ker LMinus

theorem mem_semirelativeStates (x : ClosedState) :
    x ∈ semirelativeStates ↔ bMinus x = 0 ∧ LMinus x = 0 :=
  Iff.rfl

theorem closedQ_mem_semirelativeStates (x : ClosedState) (hx : x ∈ semirelativeStates) :
    closedQ x ∈ semirelativeStates := by
  rcases (mem_semirelativeStates x).mp hx with ⟨hb, hL⟩
  apply (mem_semirelativeStates _).mpr
  constructor
  · simpa only [Module.End.mul_apply, LinearMap.add_apply, hb, hL, map_zero, zero_add]
      using LinearMap.congr_fun closed_ward x
  · simpa only [Module.End.mul_apply, hL, map_zero]
      using LinearMap.congr_fun LMinus_closedQ x

def semirelativeDifferential : Module.End ℂ semirelativeStates :=
  closedQ.restrict closedQ_mem_semirelativeStates

theorem semirelativeDifferential_square :
    semirelativeDifferential * semirelativeDifferential = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun closedQ_square (x : ClosedState)

abbrev SemirelativeCohomology :=
  Cohomology semirelativeDifferential semirelativeDifferential_square

abbrev DoubleRelativeState := ClosedRelativeState

abbrev doubleRelativeDifferential : Module.End ℂ DoubleRelativeState := closedDifferential

local notation "doubleRelativeSquare" =>
  D5.S3.HomologicalAlgebra.ParityOddKunneth.closedDifferential_square chiralComplex chiralComplex

private def relativeTensorInclusion : DoubleRelativeState →ₗ[ℂ] ClosedState :=
  TensorProduct.map relativeStates.subtype relativeStates.subtype

private theorem relativeTensorInclusion_mem (z : DoubleRelativeState) :
    relativeTensorInclusion z ∈ semirelativeStates := by
  have hb : bMinus.comp relativeTensorInclusion = 0 := by
    apply TensorProduct.ext'
    intro x y
    have hx : b0 (x : State) = 0 := x.property.1
    have hy : b0 (y : State) = 0 := y.property.1
    simp only [LinearMap.comp_apply, relativeTensorInclusion, TensorProduct.map_tmul,
      Submodule.subtype_apply, bMinus_tmul, hx, hy, TensorProduct.zero_tmul,
      TensorProduct.tmul_zero, sub_zero, LinearMap.zero_apply]
  have hL : LMinus.comp relativeTensorInclusion = 0 := by
    apply TensorProduct.ext'
    intro x y
    have hx : L0 (x : State) = 0 := x.property.2
    have hy : L0 (y : State) = 0 := y.property.2
    simp only [LinearMap.comp_apply, relativeTensorInclusion, TensorProduct.map_tmul,
      Submodule.subtype_apply, LMinus_tmul, hx, hy, TensorProduct.zero_tmul,
      TensorProduct.tmul_zero, sub_zero, LinearMap.zero_apply]
  exact (mem_semirelativeStates _).mpr
    ⟨LinearMap.congr_fun hb z, LinearMap.congr_fun hL z⟩

/-- Tensor the native subtype maps and restrict the codomain by the difference constraints. -/
def doubleRelativeInclusion : DoubleRelativeState →ₗ[ℂ] semirelativeStates :=
  relativeTensorInclusion.codRestrict _ relativeTensorInclusion_mem

theorem doubleRelativeInclusion_tmul (x y : relativeStates) :
    (doubleRelativeInclusion (x ⊗ₜ[ℂ] y) : ClosedState) =
      (x : State) ⊗ₜ[ℂ] (y : State) :=
  TensorProduct.map_tmul relativeStates.subtype relativeStates.subtype x y

theorem doubleRelativeInclusion_injective : Function.Injective doubleRelativeInclusion := by
  have hi : Function.Injective relativeTensorInclusion :=
    TensorProduct.map_injective_of_flat_flat _ _
      relativeStates.subtype_injective relativeStates.subtype_injective
  intro x y h
  exact hi (congrArg (fun z : semirelativeStates => (z : ClosedState)) h)

theorem doubleRelativeInclusion_chain :
    doubleRelativeInclusion.comp doubleRelativeDifferential =
      semirelativeDifferential.comp doubleRelativeInclusion := by
  apply TensorProduct.ext'
  intro x y
  apply Subtype.ext
  change (doubleRelativeInclusion (doubleRelativeDifferential (x ⊗ₜ[ℂ] y)) : ClosedState) =
    closedQ (doubleRelativeInclusion (x ⊗ₜ[ℂ] y) : ClosedState)
  have hQ (v : relativeStates) : (relativeDifferential v : State) = Q (v : State) := rfl
  simp only [doubleRelativeDifferential, closedDifferential_tmul, map_add, Submodule.coe_add,
    doubleRelativeInclusion_tmul, hQ, relativeParity_val, closedQ_tmul]

abbrev DoubleRelativeCohomology := ClosedRelativeCohomology

/-- The induced map sends the class of a cycle to the class of the same ambient state. -/
def doubleRelativeToSemirelativeCohomology :
    DoubleRelativeCohomology →ₗ[ℂ] SemirelativeCohomology :=
  cohomologyMap _ _ doubleRelativeSquare semirelativeDifferential_square
    doubleRelativeInclusion doubleRelativeInclusion_chain

def doubleRelativeCycleInclusion :
    LinearMap.ker doubleRelativeDifferential →ₗ[ℂ] LinearMap.ker semirelativeDifferential :=
  cycleMap _ _ doubleRelativeInclusion doubleRelativeInclusion_chain

theorem doubleRelativeToSemirelativeCohomology_class
    (z : LinearMap.ker doubleRelativeDifferential) :
    doubleRelativeToSemirelativeCohomology
        ((Boundaries doubleRelativeDifferential doubleRelativeSquare).mkQ z) =
      (Boundaries semirelativeDifferential semirelativeDifferential_square).mkQ
        (doubleRelativeCycleInclusion z) :=
  cohomologyMap_mk _ _ doubleRelativeSquare semirelativeDifferential_square
    doubleRelativeInclusion doubleRelativeInclusion_chain z

/-!
## The antighost zero mode and its conjugate

The normalized difference of the native c zero modes pairs with `bMinus`.
On the level-matched complex this gives coordinates `z = u + cMinus v`
with both coordinates semirelative. The matrix for the differential in these
coordinates uses the generally present term `{closedQ, cMinus}`.
-/

private theorem c_zero_parity (x : State) : c0 (parity x) = -parity (c0 x) := by
  have h : c0 * parity + parity * c0 = 0 := by
    apply TensorProduct.ext'
    intro v w
    have e := LinearMap.congr_fun (BcGhostFock.ghost_parity 0).2 w
    change CountableOccupationFock.parity (BcGhostFock.c 0 w) +
      BcGhostFock.c 0 (CountableOccupationFock.parity w) = 0 at e
    simp only [c0, VirasoroBRST.ghostC, BcGhostChargeTensor.C, BcGhostChargeTensor.liftGhost,
      parity, LinearMap.add_apply, Module.End.mul_apply, TensorProduct.map_tmul,
      LinearMap.id_apply, LinearMap.zero_apply]
    rw [← TensorProduct.tmul_add, add_comm, e, TensorProduct.tmul_zero]
  have e : c0 (parity x) + parity (c0 x) = 0 := LinearMap.congr_fun h x
  calc
    c0 (parity x) = (c0 (parity x) + parity (c0 x)) - parity (c0 x) := by abel
    _ = -parity (c0 x) := by rw [e, zero_sub]

private theorem chiralMixed (x : State) : b0 (c0 x) + c0 (b0 x) = x := by
  have h : b0 * c0 + c0 * b0 = 1 := by
    apply TensorProduct.ext'
    intro v w
    have e := LinearMap.congr_fun (BcGhostFock.ghost_mixed_car 0 0) w
    change BcGhostFock.b 0 (BcGhostFock.c 0 w) +
      BcGhostFock.c 0 (BcGhostFock.b 0 w) = w at e
    simp only [b0, b, c0, VirasoroBRST.ghostB, VirasoroBRST.ghostC, BcGhostChargeTensor.B,
      BcGhostChargeTensor.C, BcGhostChargeTensor.liftGhost, Module.End.mul_apply,
      LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply, Module.End.one_apply]
    rw [← TensorProduct.tmul_add, e]
  exact LinearMap.congr_fun h x

def cMinus : Module.End ℂ ClosedState :=
  (1 / 2 : ℂ) • (TensorProduct.map c0 LinearMap.id - TensorProduct.map parity c0)

theorem cMinus_tmul (x y : State) :
    cMinus (x ⊗ₜ[ℂ] y) = (1 / 2 : ℂ) • (c0 x ⊗ₜ[ℂ] y - parity x ⊗ₜ[ℂ] c0 y) := by
  simp only [cMinus, LinearMap.smul_apply, LinearMap.sub_apply,
    TensorProduct.map_tmul, LinearMap.id_apply]

theorem bMinus_cMinus : bMinus * cMinus + cMinus * bMinus = 1 := by
  apply TensorProduct.ext'
  intro x y
  simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply,
    cMinus_tmul, bMinus_tmul, map_smul, map_sub, b_zero_parity, c_zero_parity,
    parity_square, TensorProduct.neg_tmul, ← smul_sub, ← smul_add]
  calc
    _ = (1 / 2 : ℂ) • ((b0 (c0 x) + c0 (b0 x)) ⊗ₜ[ℂ] y +
          x ⊗ₜ[ℂ] (b0 (c0 y) + c0 (b0 y))) := by
      simp only [TensorProduct.add_tmul, TensorProduct.tmul_add]
      congr 1
      abel
    _ = _ := by
      rw [chiralMixed, chiralMixed, smul_add, ← add_smul]
      norm_num

private theorem chiralL0_c (x : State) : L0 (c0 x) = c0 (L0 x) := by
  have hc (w : CountableOccupationFock.Fock) :
      BcGhostVirasoro.L 0 (BcGhostFock.c 0 w) =
        BcGhostFock.c 0 (BcGhostVirasoro.L 0 w) := by
    apply sub_eq_zero.mp
    simpa using LinearMap.congr_fun (BcGhostVirasoro.ward_c 0 0) w
  have h : L0 * c0 = c0 * L0 := by
    apply TensorProduct.ext'
    intro v w
    simp only [L0, c0, VirasoroBRST.Ltotal, VirasoroBRST.ghostC,
      VirasoroBRST.matterMode, VirasoroBRST.ghostVirasoro, BcGhostChargeTensor.C,
      BcGhostChargeTensor.liftGhost, Module.End.mul_apply, LinearMap.add_apply,
      TensorProduct.map_tmul, LinearMap.id_apply, map_add, hc]
  exact LinearMap.congr_fun h x

private theorem chiralL0_parity (x : State) : L0 (parity x) = parity (L0 x) := by
  calc
    L0 (parity x) = Q (b0 (parity x)) + b0 (Q (parity x)) := (chiralWard (parity x)).symm
    _ = parity (Q (b0 x) + b0 (Q x)) := by
      simp only [b_zero_parity, Q_parity, map_neg, neg_neg, map_add]
    _ = parity (L0 x) := by rw [chiralWard]

theorem LMinus_cMinus : LMinus * cMinus = cMinus * LMinus := by
  apply TensorProduct.ext'
  intro x y
  simp only [Module.End.mul_apply, cMinus_tmul, LMinus_tmul, map_smul, map_sub,
    chiralL0_c, chiralL0_parity]
  module

/-- The zero-mode connecting operator for the level-matched splitting. -/
def connectionTerm : Module.End ℂ ClosedState := closedQ * cMinus + cMinus * closedQ

private theorem LMinus_connectionTerm :
    LMinus * connectionTerm = connectionTerm * LMinus := by
  unfold connectionTerm
  calc
    _ = (LMinus * closedQ) * cMinus + (LMinus * cMinus) * closedQ := by noncomm_ring
    _ = (closedQ * LMinus) * cMinus + (cMinus * LMinus) * closedQ := by
      rw [LMinus_closedQ, LMinus_cMinus]
    _ = closedQ * (LMinus * cMinus) + cMinus * (LMinus * closedQ) := by noncomm_ring
    _ = closedQ * (cMinus * LMinus) + cMinus * (closedQ * LMinus) := by
      rw [LMinus_cMinus, LMinus_closedQ]
    _ = _ := by noncomm_ring

private theorem bMinus_connectionTerm :
    bMinus * connectionTerm = connectionTerm * bMinus := by
  have hQB : bMinus * closedQ + closedQ * bMinus = LMinus :=
    (add_comm _ _).trans closed_ward
  unfold connectionTerm
  calc
    _ = (bMinus * closedQ + closedQ * bMinus) * cMinus -
        closedQ * (bMinus * cMinus + cMinus * bMinus) +
        (bMinus * cMinus + cMinus * bMinus) * closedQ -
        cMinus * (bMinus * closedQ + closedQ * bMinus) +
        (closedQ * cMinus + cMinus * closedQ) * bMinus := by noncomm_ring
    _ = _ := by
      rw [hQB, bMinus_cMinus, LMinus_cMinus, mul_one, one_mul]
      abel

theorem connectionTerm_commutes :
    connectionTerm * closedQ = closedQ * connectionTerm := by
  rw [connectionTerm, add_mul, mul_add, mul_assoc cMinus closedQ closedQ,
    ← mul_assoc closedQ closedQ cMinus, closedQ_square, mul_zero, zero_mul,
    add_zero, zero_add, mul_assoc]

theorem connectionTerm_mem_semirelativeStates (v : semirelativeStates) :
    connectionTerm (v : ClosedState) ∈ semirelativeStates := by
  rcases (mem_semirelativeStates _).mp v.property with ⟨hb, hL⟩
  refine (mem_semirelativeStates _).mpr ⟨?_, ?_⟩
  · simpa only [Module.End.mul_apply, hb, map_zero] using
      LinearMap.congr_fun bMinus_connectionTerm (v : ClosedState)
  · simpa only [Module.End.mul_apply, hL, map_zero] using
      LinearMap.congr_fun LMinus_connectionTerm (v : ClosedState)

private theorem bMinus_cMinus_apply (z : ClosedState) :
    bMinus (cMinus z) + cMinus (bMinus z) = z :=
  LinearMap.congr_fun bMinus_cMinus z

/-- The two semirelative coordinates of an arbitrary level-matched state. -/
theorem zeroMode_split (z : levelMatched) :
    bMinus (z : ClosedState) ∈ semirelativeStates ∧
    (z : ClosedState) - cMinus (bMinus z) ∈ semirelativeStates ∧
    ((z : ClosedState) - cMinus (bMinus z)) + cMinus (bMinus z) = z := by
  have hb : bMinus (bMinus z) = 0 := LinearMap.congr_fun bMinus_square (z : ClosedState)
  have hL : LMinus (z : ClosedState) = 0 := z.property
  have hbL : LMinus (bMinus z) = 0 := by
    simpa only [Module.End.mul_apply, hL, map_zero] using
      LinearMap.congr_fun LMinus_bMinus (z : ClosedState)
  have hbc : bMinus (cMinus (bMinus z)) = bMinus z := by
    simpa only [hb, map_zero, add_zero] using bMinus_cMinus_apply (bMinus z)
  have hcL : LMinus (cMinus (bMinus z)) = 0 := by
    simpa only [Module.End.mul_apply, hbL, map_zero] using
      LinearMap.congr_fun LMinus_cMinus (bMinus z)
  refine ⟨(mem_semirelativeStates _).mpr ⟨hb, hbL⟩,
    (mem_semirelativeStates _).mpr ⟨?_, ?_⟩, sub_add_cancel _ _⟩
  · rw [map_sub, hbc, sub_self]
  · rw [map_sub, hL, hcL, sub_zero]

/-- Recover the coordinates of every sum of the indicated form. -/
theorem zeroMode_coordinates (u v : semirelativeStates) :
    LMinus ((u : ClosedState) + cMinus v) = 0 ∧
    bMinus ((u : ClosedState) + cMinus v) = (v : ClosedState) ∧
    (u : ClosedState) + cMinus v - cMinus (bMinus ((u : ClosedState) + cMinus v)) =
      (u : ClosedState) := by
  rcases (mem_semirelativeStates _).mp u.property with ⟨hbu, hLu⟩
  rcases (mem_semirelativeStates _).mp v.property with ⟨hbv, hLv⟩
  have hbc : bMinus (cMinus v) = (v : ClosedState) := by
    simpa only [hbv, map_zero, add_zero] using bMinus_cMinus_apply (v : ClosedState)
  have hcL : LMinus (cMinus v) = 0 := by
    simpa only [Module.End.mul_apply, hLv, map_zero] using
      LinearMap.congr_fun LMinus_cMinus (v : ClosedState)
  have hB : bMinus ((u : ClosedState) + cMinus v) = (v : ClosedState) := by
    rw [map_add, hbu, hbc, zero_add]
  exact ⟨by rw [map_add, hLu, hcL, add_zero], hB, by rw [hB, add_sub_cancel_right]⟩

/-- In zero-mode coordinates the matched differential is
`(u,v) ↦ (Q u + {Q,cMinus} v, -Q v)`. -/
theorem zeroMode_differential (u v : semirelativeStates) :
    closedQ ((u : ClosedState) + cMinus v) =
      ((semirelativeDifferential u : semirelativeStates) : ClosedState) +
        connectionTerm v + cMinus (-(semirelativeDifferential v : ClosedState)) := by
  change closedQ ((u : ClosedState) + cMinus v) =
    closedQ u + connectionTerm v + cMinus (-closedQ v)
  simp only [map_add, connectionTerm, LinearMap.add_apply, Module.End.mul_apply, map_neg]
  abel

#print axioms closedQ_square
#print axioms closed_ward
#print axioms levelMatchedDifferential_square
#print axioms semirelativeDifferential_square
#print axioms doubleRelativeInclusion_injective
#print axioms doubleRelativeInclusion_chain
#print axioms doubleRelativeToSemirelativeCohomology_class
#print axioms bMinus_cMinus
#print axioms LMinus_cMinus
#print axioms connectionTerm_commutes
#print axioms connectionTerm_mem_semirelativeStates
#print axioms zeroMode_split
#print axioms zeroMode_coordinates
#print axioms zeroMode_differential

end
end D5.S3.VertexAlgebra.OriginalOrbifoldClosedSemirelative
