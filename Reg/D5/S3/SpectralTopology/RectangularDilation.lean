import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.SpectralTopology.RectangularDilation

namespace Reg.D5.S3.SpectralTopology.RectangularDilation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
noncomputable section
universe u v
abbrev scalarSignature : Signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def rootReadout : ∀ (_ : Unit) (_ : Unit), ℝ → ℝ := fun _ _ => Real.sqrt
abbrev actual : Realization scalarSignature := realize scalarSignature rootReadout (fun e => nomatch e)
private def bad : Realization scalarSignature := realize scalarSignature (fun _ _ _ => -1) (fun e => nomatch e)
private theorem eigenvalue_one {𝕜 I : Type*} [RCLike 𝕜] [Fintype I] [DecidableEq I] [Nonempty I]
    (h : (1 : Matrix I I 𝕜).IsHermitian) (i : Fin (Fintype.card I)) : h.eigenvalues₀ i = 1 := by
  have hm := h.eigenvalues_mem_spectrum_real ((Fintype.equivOfCardEq (Fintype.card_fin _)) i)
  simpa only [IsHermitian.eigenvalues, Equiv.symm_apply_apply, spectrum.one_eq,
    Set.mem_singleton_iff] using hm

abbrev unequal_dilation_second_arena : Arena where
  signature := scalarSignature
  Law R := ∀ {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (B : Matrix ι κ ℂ) (ha : 1 < Fintype.card ι)
    (hP : (fromBlocks 0 B Bᴴ (0 : Matrix κ κ ℂ)).IsHermitian),
    0 < (isHermitian_mul_conjTranspose_self B).eigenvalues₀ ⟨1,ha⟩ →
    hP.eigenvalues₀ ⟨1, by simp only [Fintype.card_sum]; omega⟩ =
      R.readout () () ((isHermitian_mul_conjTranspose_self B).eigenvalues₀ ⟨1,ha⟩)
private theorem unequal_dilation_second_reject : ¬ unequal_dilation_second_arena.{u,v}.Law bad := by
  intro h
  let I := ULift.{u} (Fin 2)
  let J := ULift.{v} (Fin 2)
  let B : Matrix I J ℂ := fun i j => if i.down = j.down then 1 else 0
  have hG : B * Bᴴ = 1 := by
    ext i j
    rcases i with ⟨i⟩
    rcases j with ⟨j⟩
    fin_cases i <;> fin_cases j <;>
      norm_num [B, Matrix.mul_apply, Fintype.sum_ulift, Fin.sum_univ_two, Matrix.one_apply]
  have hp : 0 < (isHermitian_mul_conjTranspose_self B).eigenvalues₀ ⟨1,by simp [I]⟩ := by
    have he : (isHermitian_mul_conjTranspose_self B).eigenvalues₀ ⟨1,by simp [I]⟩ = 1 := by
      rw [hG]
      exact eigenvalue_one _ _
    rw [he]
    norm_num
  have hP : (fromBlocks 0 B Bᴴ (0 : Matrix J J ℂ)).IsHermitian := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      (isHermitian_zero.fromBlocks (B := B) rfl isHermitian_zero)
  have hh := h B (by simp [I]) hP hp
  rw [_root_.D5.S3.SpectralTopology.RectangularDilation.unequal_dilation_second B (by simp [I]) hP hp] at hh
  have hn := Real.sqrt_nonneg ((isHermitian_mul_conjTranspose_self B).eigenvalues₀ ⟨1,by simp [I]⟩)
  change Real.sqrt _ = -1 at hh
  linarith

def unequal_dilation_second_family : Registration unequal_dilation_second_arena
    (type_of% (@_root_.D5.S3.SpectralTopology.RectangularDilation.unequal_dilation_second)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.SpectralTopology.RectangularDilation.unequal_dilation_second, bad, unequal_dilation_second_reject⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ unequal_dilation_second_reject
  dependence := by
    intro i; cases i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, rootReadout, realize]
def registration_unequal_dilation_second : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.SpectralTopology.RectangularDilation.unequal_dilation_second)
    (Realization scalarSignature) Type Unit where
  unitName := `Reg.D5.S3.SpectralTopology.RectangularDilation.unequal_dilation_second_unit
  realizationName := `Reg.D5.S3.SpectralTopology.RectangularDilation.unequal_dilation_second_family
  realizationSource := none
  generated := false
  arena := .source ⟨unequal_dilation_second_arena⟩
  objectArena := .source ⟨unequal_dilation_second_arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source unequal_dilation_second_arena ⟨unequal_dilation_second_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature rootReadout (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev unequal_real_dilation_second_arena : Arena where
  signature := scalarSignature
  Law R := ∀ {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (B : Matrix ι κ ℝ) (ha : 1 < Fintype.card ι)
    (hP : (fromBlocks 0 B B.transpose (0 : Matrix κ κ ℝ)).IsHermitian),
    0 < (isHermitian_mul_conjTranspose_self B).eigenvalues₀ ⟨1,ha⟩ →
    hP.eigenvalues₀ ⟨1, by simp only [Fintype.card_sum]; omega⟩ =
      R.readout () () ((isHermitian_mul_conjTranspose_self B).eigenvalues₀ ⟨1,ha⟩)
private theorem unequal_real_dilation_second_reject : ¬ unequal_real_dilation_second_arena.{u,v}.Law bad := by
  intro h
  let I := ULift.{u} (Fin 2)
  let J := ULift.{v} (Fin 2)
  let B : Matrix I J ℝ := fun i j => if i.down = j.down then 1 else 0
  have hG : B * Bᴴ = 1 := by
    ext i j
    rcases i with ⟨i⟩
    rcases j with ⟨j⟩
    fin_cases i <;> fin_cases j <;>
      norm_num [B, Matrix.mul_apply, Fintype.sum_ulift, Fin.sum_univ_two, Matrix.one_apply]
  have hp : 0 < (isHermitian_mul_conjTranspose_self B).eigenvalues₀ ⟨1,by simp [I]⟩ := by
    have he : (isHermitian_mul_conjTranspose_self B).eigenvalues₀ ⟨1,by simp [I]⟩ = 1 := by
      rw [hG]
      exact eigenvalue_one _ _
    rw [he]
    norm_num
  have hP : (fromBlocks 0 B B.transpose (0 : Matrix J J ℝ)).IsHermitian := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      (isHermitian_zero.fromBlocks (B := B) rfl isHermitian_zero)
  have hh := h B (by simp [I]) hP hp
  rw [_root_.D5.S3.SpectralTopology.RectangularDilation.unequal_real_dilation_second B (by simp [I]) hP hp] at hh
  have hn := Real.sqrt_nonneg ((isHermitian_mul_conjTranspose_self B).eigenvalues₀ ⟨1,by simp [I]⟩)
  change Real.sqrt _ = -1 at hh
  linarith

def unequal_real_dilation_second_family : Registration unequal_real_dilation_second_arena
    (type_of% (@_root_.D5.S3.SpectralTopology.RectangularDilation.unequal_real_dilation_second)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.SpectralTopology.RectangularDilation.unequal_real_dilation_second, bad, unequal_real_dilation_second_reject⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ unequal_real_dilation_second_reject
  dependence := by
    intro i; cases i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, rootReadout, realize]
def registration_unequal_real_dilation_second : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.SpectralTopology.RectangularDilation.unequal_real_dilation_second)
    (Realization scalarSignature) Type Unit where
  unitName := `Reg.D5.S3.SpectralTopology.RectangularDilation.unequal_real_dilation_second_unit
  realizationName := `Reg.D5.S3.SpectralTopology.RectangularDilation.unequal_real_dilation_second_family
  realizationSource := none
  generated := false
  arena := .source ⟨unequal_real_dilation_second_arena⟩
  objectArena := .source ⟨unequal_real_dilation_second_arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source unequal_real_dilation_second_arena ⟨unequal_real_dilation_second_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature rootReadout (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.SpectralTopology.RectangularDilation
