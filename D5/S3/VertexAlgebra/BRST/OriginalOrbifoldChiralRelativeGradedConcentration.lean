/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldChiralRelativeGradedConcentration
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldChiralRelativeGradedConcentration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native relative BRST cycles at nonzero momentum concentrate in ghost number one. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeQuartet
import Batteries.Tactic.OpenPrivate

/-! Ghost-number concentration on the native chiral relative shell at nonzero momentum. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.OriginalOrbifoldRelativeQuartet

open OriginalOrbifoldCriticalMatter (Matter State hyperbolicData)
open OriginalOrbifoldRelativeMassShell (relativeMassShell differential
  relativeMassShell_eq_bot_of_one_lt)
open LatticeLightConeCoordinates.NullFrame (pPlus)
open LatticePositiveEnergy (chargeEnergy)
open LatticeRelativeMassShell (massShellCutoff)

open private perturbationInput perturbation_D perturbation_transferred_zero
  correctedI_ghostOne shellNumber_h shellNumber_K shellNumber_Q from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeQuartet

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private theorem correctedH_mem_ghostSector (F : Frame) (a : UCharge) (hp : F.pPlus a ≠ 0)
    (he : chargeEnergy hyperbolicData a ≤ 1) (n : ℕ)
    (q : ℤ) (x : relativeMassShell a) (hx : x ∈ ghostSector a q) :
    (perturbationInput F a hp he).H n x ∈ ghostSector a (q - 1) := by
  let C := perturbationInput F a hp he
  have hxN := Module.End.mem_eigenspace_iff.mp hx
  have hh : shellNumber a (shellH F a x) - (q : ℂ) • shellH F a x = -shellH F a x := by
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply, hxN, map_smul]
      using LinearMap.congr_fun (shellNumber_h F a) x
  have hH : shellNumber a (shellH F a x) = ((q - 1 : ℤ) : ℂ) • shellH F a x := by
    calc
      _ = -shellH F a x + (q : ℂ) • shellH F a x := sub_eq_iff_eq_add.mp hh
      _ = ((q - 1 : ℤ) : ℂ) • shellH F a x := by
        rw [Int.cast_sub, Int.cast_one, sub_smul, one_smul]
        abel
  apply Module.End.mem_eigenspace_iff.mpr
  change shellNumber a (C.K n (shellH F a x)) =
    ((q - 1 : ℤ) : ℂ) • C.K n (shellH F a x)
  simpa only [Module.End.mul_apply, hH, map_smul] using
    LinearMap.congr_fun (shellNumber_K F a hp he n) (shellH F a x)

private theorem differential_mem_ghostSector (a : UCharge) (q : ℤ)
    (x : relativeMassShell a) (hx : x ∈ ghostSector a (q - 1)) :
    differential a x ∈ ghostSector a q := by
  have hxN := Module.End.mem_eigenspace_iff.mp hx
  have hQ : shellNumber a (differential a x) -
      ((q - 1 : ℤ) : ℂ) • differential a x = differential a x := by
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, hxN, map_smul] using
      LinearMap.congr_fun (shellNumber_Q a) x
  apply Module.End.mem_eigenspace_iff.mpr
  calc
    shellNumber a (differential a x) =
        differential a x + ((q - 1 : ℤ) : ℂ) • differential a x :=
      sub_eq_iff_eq_add.mp hQ
    _ = (q : ℂ) • differential a x := by
      rw [Int.cast_sub, Int.cast_one, sub_smul, one_smul]
      abel

/-- The corrected inclusion and homotopy give an explicit decomposition for
every native shell cycle. On the ghost-number-q sector the primitive has
ghost number q - 1. -/
private theorem cycle_decomposition_inFrame (F : Frame) (a : UCharge) (hp : F.pPlus a ≠ 0)
    (he : chargeEnergy hyperbolicData a ≤ 1)
    (x : relativeMassShell a) (hx : differential a x = 0) :
    let C := perturbationInput F a hp he
    let n := 2 * massShellCutoff hyperbolicData a + 1
    C.I n (C.P n x) ∈ ghostOneCycles a ∧
      x - C.I n (C.P n x) = differential a (C.H n x) ∧
      (∀ q : ℤ, x ∈ ghostSector a q → C.H n x ∈ ghostSector a (q - 1)) := by
  let C := perturbationInput F a hp he
  let n := 2 * massShellCutoff hyperbolicData a + 1
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hnil : (C.h * C.delta) ^ n = 0 := hdelta_nilpotent F a
  have hD : C.D = differential a := perturbation_D F a hp he
  have hxD : C.D x = 0 := by rwa [hD]
  have htr := perturbation_transferred_zero F a hp he n
  obtain ⟨hreps, hdecomp, _⟩ := (C.finite_perturbation n hn hnil).representatives htr
  refine ⟨⟨correctedI_ghostOne F a hp he n (C.P n x), LinearMap.mem_ker.mpr ?_⟩, ?_, ?_⟩
  · simpa only [hD] using (hreps (C.P n x)).1
  · simpa only [hD] using hdecomp x hxD
  · exact fun q hq => correctedH_mem_ghostSector F a hp he n q x hq

/-- Every relative cocycle at nonzero momentum is cohomologous under the
actual restricted charge to a ghost-number-one cocycle. -/
theorem exists_ghostOne_representative (a : UCharge) (ha : a ≠ 0)
    (x : relativeMassShell a) (hx : differential a x = 0) :
    ∃ y : ghostOneCycles a, ∃ z : relativeMassShell a,
      x - (y : relativeMassShell a) = differential a z := by
  by_cases he : chargeEnergy hyperbolicData a ≤ 1
  · obtain ⟨F, hp⟩ := exists_frame a ha
    let C := perturbationInput F a hp he
    let n := 2 * massShellCutoff hyperbolicData a + 1
    obtain ⟨hy, hdecomp, _⟩ := cycle_decomposition_inFrame F a hp he x hx
    exact ⟨⟨C.I n (C.P n x), hy⟩, C.H n x, hdecomp⟩
  · let _ : Subsingleton (relativeMassShell a) :=
      Submodule.subsingleton_iff_eq_bot.mpr (relativeMassShell_eq_bot_of_one_lt a (lt_of_not_ge he))
    have hx0 : x = 0 := Subsingleton.elim x 0
    exact ⟨0, 0, by simp [hx0]⟩

/-- At nonzero momentum every native relative cocycle of ghost number q,
with q distinct from one, has a primitive of ghost number q - 1 under the
actual restricted charge. -/
theorem ghostSector_exact_of_ne_one (a : UCharge) (ha : a ≠ 0)
    (q : ℤ) (hq : q ≠ 1) (x : relativeMassShell a)
    (hx : differential a x = 0) (hgrade : x ∈ ghostSector a q) :
    ∃ z : ghostSector a (q - 1), differential a z = x := by
  by_cases he : chargeEnergy hyperbolicData a ≤ 1
  · obtain ⟨F, hp⟩ := exists_frame a ha
    let C := perturbationInput F a hp he
    let n := 2 * massShellCutoff hyperbolicData a + 1
    obtain ⟨hy, hdecomp, hlower⟩ := cycle_decomposition_inFrame F a hp he x hx
    let y := C.I n (C.P n x)
    let z := C.H n x
    change y ∈ ghostOneCycles a at hy
    change x - y = differential a z at hdecomp
    have hz : z ∈ ghostSector a (q - 1) := hlower q hgrade
    have hdH := differential_mem_ghostSector a q z hz
    have hyq : y ∈ ghostSector a q := by
      have hsub := (ghostSector a q).sub_mem hgrade hdH
      rwa [← hdecomp, sub_sub_cancel] at hsub
    have hNq := Module.End.mem_eigenspace_iff.mp hyq
    have hN1 : shellNumber a y = y := by
      have hy1 : y ∈ ghostSector a 1 := (Submodule.mem_inf.mp hy).1
      simpa only [Int.cast_one, one_smul] using Module.End.mem_eigenspace_iff.mp hy1
    have hscalar : ((q : ℂ) - 1) • y = 0 := by
      rw [sub_smul, one_smul, ← hNq, hN1, sub_self]
    have hqC : (q : ℂ) ≠ 1 := by exact_mod_cast hq
    have hy0 : y = 0 :=
      (smul_eq_zero.mp hscalar).resolve_left (sub_ne_zero.mpr hqC)
    refine ⟨⟨z, hz⟩, ?_⟩
    change differential a z = x
    simpa only [hy0, sub_zero] using hdecomp.symm
  · let _ : Subsingleton (relativeMassShell a) :=
      Submodule.subsingleton_iff_eq_bot.mpr (relativeMassShell_eq_bot_of_one_lt a (lt_of_not_ge he))
    have hx0 : x = 0 := Subsingleton.elim x 0
    exact ⟨0, by simp [hx0]⟩

#print axioms exists_ghostOne_representative
#print axioms ghostSector_exact_of_ne_one

end D5.S3.VertexAlgebra.OriginalOrbifoldRelativeQuartet
