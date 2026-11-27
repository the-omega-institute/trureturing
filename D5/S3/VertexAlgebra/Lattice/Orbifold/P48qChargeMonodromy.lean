/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qChargeMonodromy
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cover rotation of the P48q ground charge operators at momentum p/3. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedChargeAction
import Mathlib.Algebra.Module.Torsion.Field

/-!
The ground charge part of Bakalov–Kac, arXiv:math/0402315v3, (4.30).
For the cover coordinate `x = z^(1/3)`, the branch change is `x ↦ ζ x`,
where `ζ = exp(2πi/3)`. The momentum index `p` represents `p / 3`.
-/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargeMonodromy

open LatticeGeneratingFieldLocality (Charge bilinear)
open P48qTwistedChargeAction (lattice g g_apply liftPhase Momentum Ground U
  U_comp_single U_difference_single)

noncomputable section

local notation "ζ" => ThirdTwistedChargeCocycle.zeta
local notation "c₃" => ThirdTwistedChargeCocycle.c lattice g

/-- The exact charge relation on the momentum single at `p / 3`. -/
theorem U_monodromy_single (a : Charge lattice) (p : Momentum) (z : ℂ) :
    (↑((liftPhase.eta a)⁻¹) : ℂ) • U (g a) (Finsupp.single p z) =
      (ζ : ℂ) ^ (ThirdTwistedChargeAction.q lattice g a + bilinear lattice a p.1) •
        U a (Finsupp.single p z) := by
  let d : Charge lattice := a - g a
  let exponent : ℤ := ThirdTwistedChargeAction.q lattice g a + bilinear lattice a p.1
  let cocycle : ℂ := ↑(c₃ (g a) d)
  let etaInv : ℂ := ↑((liftPhase.eta a)⁻¹)
  have hadd : g a + d = a := by
    change g a + (a - g a) = a
    rw [add_comm (g a), sub_add_cancel]
  have hcomp : U (g a) (U d (Finsupp.single p z)) = cocycle • U a (Finsupp.single p z) := by
    rw [U_comp_single, hadd]
  have hmove : U d (Finsupp.single p z) =
      (cocycle * ((ζ : ℂ) ^ (-exponent) * etaInv)) • Finsupp.single p z := by
    let a48 : Fin 48 → ℤ := fun i => a i
    have hg48 : (fun i : Fin 48 => g a i) =
        Matrix.vecMul (m := Fin 48) (n := Fin 48) a48
          P48qFixedRankCertificateDraft.nebeOrderThree := g_apply a
    have hdiff : a48 - (fun i : Fin 48 => g a i) =
        Matrix.vecMul (m := Fin 48) (n := Fin 48) a48
          ((1 : Matrix (Fin 48) (Fin 48) ℤ) - P48qFixedRankCertificateDraft.nebeOrderThree) := by
      rw [Matrix.vecMul_sub, Matrix.vecMul_one]
      exact congrArg (fun b : Fin 48 → ℤ => a48 - b) hg48
    change d = Matrix.vecMul (m := Fin 48) (n := Fin 48) a
      ((1 : Matrix (Fin 48) (Fin 48) ℤ) - P48qFixedRankCertificateDraft.nebeOrderThree) at hdiff
    have h := (congrArg (fun b : Charge lattice => U b (Finsupp.single p z)) hdiff).trans
      (U_difference_single a p z)
    refine h.trans ?_
    apply congrArg (fun s : ℂ => s • Finsupp.single p z)
    simp only [cocycle, etaInv, exponent, Units.val_mul, Units.val_zpow_eq_zpow_val,
      neg_add, zpow_add₀ (Units.ne_zero ζ)]
    ac_rfl
  have hcancel :
      (ζ : ℂ) ^ (-exponent) • (etaInv • U (g a) (Finsupp.single p z)) =
        U a (Finsupp.single p z) := by
    have hne : cocycle ≠ 0 := Units.ne_zero (c₃ (g a) d)
    apply smul_right_injective Ground hne
    simpa only [hmove, map_smul, smul_smul] using hcomp
  have hroot : (ζ : ℂ) ^ exponent * (ζ : ℂ) ^ (-exponent) = 1 := by
    rw [← zpow_add₀ (Units.ne_zero ζ), add_neg_cancel, zpow_zero]
  calc
    _ = ((ζ : ℂ) ^ exponent * (ζ : ℂ) ^ (-exponent)) •
          (etaInv • U (g a) (Finsupp.single p z)) := by rw [hroot, one_smul]
    _ = (ζ : ℂ) ^ exponent • U a (Finsupp.single p z) := by rw [← smul_smul, hcancel]

/-- The branch change on the factor `x^(q(a) + (a,p))` of the charged field. -/
def momentumMonodromy (a : Charge lattice) : Module.End ℂ Ground :=
  Finsupp.lsum ℂ fun p =>
    (ζ : ℂ) ^ (ThirdTwistedChargeAction.q lattice g a + bilinear lattice a p.1) •
      Finsupp.lsingle p

theorem momentumMonodromy_single (a : Charge lattice) (p : Momentum) (z : ℂ) :
    momentumMonodromy a (Finsupp.single p z) =
      (ζ : ℂ) ^ (ThirdTwistedChargeAction.q lattice g a + bilinear lattice a p.1) •
        Finsupp.single p z := by
  simp only [momentumMonodromy, Finsupp.lsum_single, LinearMap.smul_apply, Finsupp.lsingle_apply]

/-- Apply the branch phase at the input momentum before shifting it by the charge. -/
theorem U_monodromy (a : Charge lattice) :
    (↑((liftPhase.eta a)⁻¹) : ℂ) • U (g a) = (U a).comp (momentumMonodromy a) := by
  apply Finsupp.lhom_ext
  intro p z
  simpa only [LinearMap.smul_apply, LinearMap.comp_apply, momentumMonodromy_single, map_smul]
    using U_monodromy_single a p z

#print axioms U_monodromy_single
#print axioms U_monodromy

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargeMonodromy
