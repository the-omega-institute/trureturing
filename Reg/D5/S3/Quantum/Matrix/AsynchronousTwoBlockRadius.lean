import D5.S3.Quantum.Matrix.AsynchronousTwoBlockRadius
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The original synchronous radius is observed on its full matrix domain. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open _root_.D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs (Vtx)
open _root_.D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation
open _root_.D5.S3.Quantum.Matrix.AsynchronousTwoBlockSpectrum
open _root_.D5.S3.Quantum.Matrix.AsynchronousTwoBlockRadius
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped ENNReal NNReal Matrix.Norms.Operator

namespace Reg.D5.S3.Quantum.Matrix.AsynchronousTwoBlockRadius

abbrev signature : Signature where
  Params := Σ _m : ℕ, ℕ
  State p := Matrix (Vtx (![p.1,p.2] : Fin 2 → ℕ)) (Vtx (![p.1,p.2] : Fin 2 → ℕ)) ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ M => radius M) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ENNReal.ofReal (1/2)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m n a b k K : ℕ} (_hm : 0<m) (_hn : 0<n)
    (U : Matrix (Fin m) (Fin n) ℝ) (V : Matrix (Fin n) (Fin m) ℝ)
    (_ha : 1≤a) (_hb : 1≤b) (_hak : a≤k) (_hbk : b≤k)
    (_haK : a≤K) (_hbK : b≤K)
    (lambda : ℝ) (_hl0 : 0<lambda) (_hl1 : lambda<1)
    (_hradius : R.readout () ⟨m,n⟩ (zeroDiagonal U V) = ENNReal.ofReal lambda),
    radius (asyncMatrix (zeroDiagonal U V) !![0,b; a,0] K) =
        ENNReal.ofReal (lambda ^ ((2:ℝ)/(a+b+2:ℕ))) ∧
      ENNReal.ofReal (lambda ^ ((2:ℝ)/(a+b+2:ℕ))) ≤
        ENNReal.ofReal (lambda ^ ((1:ℝ)/((k:ℝ)+1))) ∧
      ENNReal.ofReal (lambda ^ ((1:ℝ)/((k:ℝ)+1))) < 1

private theorem zero_delayed_radius :
    radius (asyncMatrix (zeroDiagonal (0 : Matrix (Fin 1) (Fin 1) ℝ) 0)
      !![0,1; 1,0] 1) = 0 := by
  have hz0 (z : ℂ) (h : z ∈ spectrum ℂ
      ((asyncMatrix (zeroDiagonal (0 : Matrix (Fin 1) (Fin 1) ℝ) 0)
        !![0,1; 1,0] 1).map (algebraMap ℝ ℂ))) : z=0 := by
    by_contra hz
    have hp := (nonzero_spectrum_iff (a:=1) (b:=1) (K:=1)
      (0 : Matrix (Fin 1) (Fin 1) ℝ) 0 (by omega) (by omega) z hz).mp h
    have hpow : z^4=0 := by simpa [Matrix.map_zero,spectrum.zero_eq] using hp
    exact hz (eq_zero_of_pow_eq_zero hpow)
  unfold radius
  rw [spectralRadius_eq_of_unital]
  apply le_antisymm _ bot_le
  apply iSup₂_le
  intro z hz
  rw [hz0 z hz]
  simp

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := law (m:=1) (n:=1) (a:=1) (b:=1) (k:=1) (K:=1)
    (by omega) (by omega) 0 0 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (1/2) (by norm_num) (by norm_num) rfl
  have hh := h.1
  rw [zero_delayed_radius] at hh
  have hpos : (0:ℝ≥0∞) < ENNReal.ofReal ((1/2:ℝ)^((2:ℝ)/(1+1+2:ℕ))) :=
    ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)
  exact (ne_of_gt hpos) hh.symm

private def halfBlock : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 1/2

private theorem half_radius : radius (zeroDiagonal halfBlock halfBlock) = ENNReal.ofReal (1/2) := by
  let A := (zeroDiagonal halfBlock halfBlock).map (algebraMap ℝ ℂ)
  have hentry (p q : Vtx (![1,1] : Fin 2 → ℕ)) :
      A p q = if p.1=q.1 then 0 else (1/2:ℂ) := by
    rcases p with ⟨i,x⟩
    rcases q with ⟨j,y⟩
    fin_cases i <;> fin_cases j <;> fin_cases x <;> fin_cases y
    all_goals first
      | change ((0:ℝ):ℂ) = 0
      | change ((1/2:ℝ):ℂ) = (1/2:ℂ)
    all_goals norm_num
  have hn : ‖A‖₊ ≤ (1/2 : ℝ≥0) := by
    rw [Matrix.linfty_opNNNorm_def,Finset.sup_le_iff]
    rintro ⟨i,x⟩ hi
    simp_rw [hentry]
    fin_cases i <;>
      norm_num [Fintype.sum_sigma,Fin.sum_univ_two,Fintype.sum_unique]
  have he : A *ᵥ (fun _ => (1:ℂ)) = (1/2:ℂ) • (fun _ => (1:ℂ)) := by
    funext p
    rcases p with ⟨i,x⟩
    simp only [Matrix.mulVec,dotProduct,hentry]
    fin_cases i <;>
      norm_num [Fintype.sum_sigma,Fin.sum_univ_two,Fintype.sum_unique]
  have hne : (fun _ : Vtx (![1,1] : Fin 2 → ℕ) => (1:ℂ)) ≠ 0 := by
    intro h
    have hh := congrFun h ⟨0,(⟨0,by decide⟩ : Fin 1)⟩
    norm_num at hh
  have hs := _root_.D5.S3.Combinatorics.NonBacktracking.LaplacianGapMinDegree.eigenpair_mem_spectrum
    A (1/2) (fun _ => 1) hne he
  change spectralRadius ℂ A = ENNReal.ofReal (1/2)
  apply le_antisymm
  · calc spectralRadius ℂ A ≤ (‖A‖₊ : ℝ≥0∞) := spectralRadius_le_nnnorm A
      _ ≤ ((1/2:ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr hn
      _ = ENNReal.ofReal (1/2) := by rw [←ENNReal.ofReal_coe_nnreal]; norm_num
  · rw [spectralRadius_eq_of_unital]
    have h := le_iSup₂ (f:=fun z (_ : z ∈ spectrum ℂ A) => (‖z‖₊ : ℝ≥0∞)) (1/2:ℂ) hs
    have hh : (‖(1/2:ℂ)‖₊ : ℝ≥0∞) = ENNReal.ofReal (1/2) := by
      rw [←ENNReal.ofReal_coe_nnreal]
      norm_num [coe_nnnorm,norm_div]
    rwa [hh] at h

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  letI : Nonempty (Vtx (![1,1] : Fin 2 → ℕ)) := ⟨⟨0,(⟨0,by decide⟩ : Fin 1)⟩⟩
  refine ⟨⟨1,1⟩,0,zeroDiagonal halfBlock halfBlock,?_⟩
  change radius (0 : Matrix (Vtx (![1,1] : Fin 2 → ℕ))
    (Vtx (![1,1] : Fin 2 → ℕ)) ℝ) ≠ radius (zeroDiagonal halfBlock halfBlock)
  rw [half_radius]
  norm_num [radius,Matrix.map_zero]

def family : Registration arena (type_of% (@two_block_radius)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@two_block_radius,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl,rejected_law⟩,fun e => nomatch e⟩
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@two_block_radius) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.AsynchronousTwoBlockRadius.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.AsynchronousTwoBlockRadius.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage:=.evidence,objectStage:=.evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ M => radius M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.AsynchronousTwoBlockRadius
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body",
        "body","body","body","body","body","body","body","body","body","domain","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Matrix.AsynchronousTwoBlockRadius
