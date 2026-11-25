import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentPhysical
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the dependence on the two actual marginal populations. -/

namespace Reg.D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentPhysical

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.PetzTangentArcsine
open _root_.D5.S3.Quantum.Recovery.PetzTangentPhysical
open _root_.D5.S3.Quantum.Recovery.PetzTangentReciprocalGram
open _root_.D5.S3.Quantum.Recovery.BKMFlagRefinement (partialTracePetz lift)
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open _root_.D5.S3.Quantum.Divergence.UmegakiConditionalBKM (residual)
open _root_.D5.S3.Quantum.Divergence.UmegakiReferenceTransport (partialTraceRight_posDef)
open Matrix MeasureTheory Set
open scoped ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 2 → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ p => parityMultiplier (2*Real.sqrt (p 0*p 1))) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {E : Type} [Fintype E] [DecidableEq E]
    (Z H : Matrix (Fin 2 × E) (Fin 2 × E) ℂ) (_hZ : Z.IsHermitian)
    (_hP : (partialTraceRight Z).PosDef)
    (U : Matrix.unitaryGroup (Fin 2 × E) ℂ) (V : Matrix.unitaryGroup (Fin 2) ℂ)
    (eigenvalues : Fin 2 × E → ℝ) (p : Fin 2 → ℝ)
    (_hZD : Z = U.val * Matrix.diagonal (fun k => (eigenvalues k : ℂ)) * U.valᴴ)
    (_hPD : partialTraceRight Z = V.val * Matrix.diagonal (fun a => (p a : ℂ)) * V.valᴴ)
    (_hp : ∀ a, 0 < p a) (_hpq : p 0 + p 1 = 1)
    (i j : Fin 2 × E) (_hi : 0 < eigenvalues i) (_hj : 0 < eigenvalues j),
    let u := (eigenvalues i + eigenvalues j)/2
    let β := (eigenvalues i - eigenvalues j)/(eigenvalues i + eigenvalues j)
    let g := Real.sqrt (eigenvalues i * eigenvalues j) / u
    let F := fun z : ℝ => (U.valᴴ *
      _root_.D5.S3.Quantum.Divergence.UmegakiConditionalBKM.residual Z H ((z+1)/2) * U.val) i j
    let Y := (U.valᴴ * (H - partialTracePetz Z (partialTraceRight H)) * U.val) i j
    Y = (g : ℂ) * arcIntegral (fun z => F z / ((1-β*z : ℝ) : ℂ)) ∧
      Complex.normSq Y ≤ R.readout () () p *
        (∫ z in Ioo (-1 : ℝ) 1, Complex.normSq (F z) / (1-β*z) / 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let i : Fin 2 × Fin 2 := (0, 0)
  let j : Fin 2 × Fin 2 := (0, 1)
  let Z : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := Matrix.diagonal (fun _ => ((1/4 : ℝ) : ℂ))
  let H : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := Matrix.single i j (1 : ℂ)
  let p : Fin 2 → ℝ := fun _ => 1/2
  let eig : Fin 2 × Fin 2 → ℝ := fun _ => 1/4
  have hZ : Z.PosDef := Matrix.PosDef.diagonal fun _ => by
    exact_mod_cast (by norm_num : (0 : ℝ) < 1/4)
  have hZD : Z = ((1 : Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ).val) *
      Matrix.diagonal (fun k => (eig k : ℂ)) * ((1 : Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ).val)ᴴ := by
    simp [Z, eig]
  have hPD : partialTraceRight Z = Matrix.diagonal (fun a => (p a : ℂ)) := by
    ext a b
    simp [Z, p, partialTraceRight, Matrix.diagonal_apply, Prod.ext_iff]
    split <;> norm_num
  have hH : partialTraceRight H = 0 := by
    ext a b
    simp [H, i, j, partialTraceRight, Matrix.single_apply, Prod.ext_iff]
  have h := (law Z H hZ.isHermitian (partialTraceRight_posDef Z hZ) 1 1 eig p hZD
    (by simpa using hPD) (fun _ => by norm_num [p]) (by norm_num [p])
    i j (by norm_num [eig]) (by norm_num [eig])).2
  dsimp only at h
  rw [hH] at h
  norm_num [partialTracePetz, lift, H, rejected, realize, Complex.normSq_apply] at h

def source_registration : Registration arena (type_of% @physical_entry_arcsine_and_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@physical_entry_arcsine_and_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), (fun _ => 1/2), (fun _ => 1/8), ?_⟩
    change parityMultiplier (2*Real.sqrt ((1/2)*(1/2))) ≠
      parityMultiplier (2*Real.sqrt ((1/8)*(1/8)))
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1/2),
      ← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1/8)]
    norm_num [parityMultiplier, max_def]

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Recovery.PetzTangentPhysical.physical_entry_arcsine_and_bound)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentPhysical.unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentPhysical.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ p => parityMultiplier (2*Real.sqrt (p 0*p 1))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentPhysical
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration


namespace FaithfulWitness

abbrev Index := Fin 2 × Fin 2

def reference : Matrix Index Index ℂ :=
  Matrix.diagonal fun _ => ((1 / 4 : ℝ) : ℂ)

def direction : Matrix Index Index ℂ :=
  Matrix.diagonal fun i => if i.2 = 0 then 1 else -1

theorem reference_pos : reference.PosDef :=
  Matrix.PosDef.diagonal fun _ => by exact_mod_cast (by norm_num : (0 : ℝ) < 1 / 4)

theorem reference_trace : reference.trace.re = 1 := by
  norm_num [reference, Matrix.trace_diagonal, Fintype.card_prod]

theorem direction_marginal : partialTraceRight direction = 0 := by
  ext a b
  simp [direction, partialTraceRight, Matrix.diagonal_apply, Prod.ext_iff]

theorem direction_ne_zero : direction ≠ 0 := by
  intro h
  have he := congrArg (fun A : Matrix Index Index ℂ => A (0, 0) (0, 0)) h
  norm_num [direction] at he

theorem direction_recovery : partialTracePetz reference (partialTraceRight direction) = 0 := by
  simp [direction_marginal, partialTracePetz, lift]

end FaithfulWitness

namespace Weighted

open _root_.D5.S3.Quantum.Divergence.UmegakiReferenceTransport (partialTraceRight_posDef)
open _root_.D5.S3.Divergence.LogDerivTrace (logDeriv)

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ δ => parityMultiplier δ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (Z H : Matrix (Fin 2 × E) (Fin 2 × E) ℂ) (hZ : Z.PosDef)
    (_htrace : (partialTraceRight Z).trace.re = 1),
    let P := partialTraceRight Z
    let M := partialTraceRight H
    let U := hZ.isHermitian.eigenvectorUnitary
    let lam := hZ.isHermitian.eigenvalues
    let p := (partialTraceRight_posDef Z hZ).isHermitian.eigenvalues
    let Y := U.valᴴ * (H - partialTracePetz Z M) * U.val
    ∑ i, ∑ j, Complex.normSq (Y i j) / ((lam i + lam j)/2) ≤
      R.readout () () (2*Real.sqrt (p 0*p 1)) *
        ((Hᴴ * logDeriv Z H).trace.re - (Mᴴ * logDeriv P M).trace.re)

private theorem rejected_law : ¬ arena.Law rejected := by
  open FaithfulWitness in
  intro law
  have ht : (partialTraceRight reference).trace.re = 1 := by
    rw [_root_.D5.S3.Quantum.Information.PartialTraceMutualInformation.trace_partialTraceRight]
    exact reference_trace
  have h := law reference direction reference_pos ht
  dsimp only at h
  rw [direction_recovery, sub_zero] at h
  let U := reference_pos.isHermitian.eigenvectorUnitary
  let A := U.valᴴ * direction * U.val
  let lam := reference_pos.isHermitian.eigenvalues
  have hsum : (∑ i, ∑ j, Complex.normSq (A i j) / ((lam i + lam j)/2)) ≤ 0 := by
    simpa only [rejected, realize, zero_mul] using h
  have hden (i j : Index) : 0 < (lam i + lam j)/2 :=
    div_pos (add_pos (reference_pos.eigenvalues_pos i) (reference_pos.eigenvalues_pos j)) (by norm_num)
  have hn (i j : Index) : 0 ≤ Complex.normSq (A i j) / ((lam i + lam j)/2) :=
    div_nonneg (Complex.normSq_nonneg _) (hden i j).le
  have hA : A = 0 := by
    ext i j
    change A i j = 0
    apply Complex.normSq_eq_zero.mp
    have h₁ := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => Complex.normSq (A i j) / ((lam i + lam j)/2))
      (fun k _ => hn i k) (Finset.mem_univ j)
    have h₂ := Finset.single_le_sum (s := Finset.univ)
      (f := fun i => ∑ j, Complex.normSq (A i j) / ((lam i + lam j)/2))
      (fun k _ => Finset.sum_nonneg (fun l _ => hn k l)) (Finset.mem_univ i)
    exact le_antisymm
      (by simpa only [zero_mul] using
        (div_le_iff₀ (hden i j)).mp (h₁.trans (h₂.trans hsum)))
      (Complex.normSq_nonneg _)
  have hU : U.val * U.valᴴ = 1 := Unitary.coe_mul_star_self U
  have hz : U.val * A * U.valᴴ = direction := by
    dsimp [A]
    calc
      _ = (U.val * U.valᴴ) * direction * (U.val * U.valᴴ) := by noncomm_ring
      _ = _ := by simp [hU]
  exact direction_ne_zero (by simpa [hA] using hz.symm)

def source_registration : Registration arena (type_of% @faithful_weighted_tangent) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@faithful_weighted_tangent, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (1 : ℝ), (1/4 : ℝ), ?_⟩
    change parityMultiplier 1 ≠ parityMultiplier (1/4)
    norm_num [parityMultiplier, max_def]

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Recovery.PetzTangentPhysical.faithful_weighted_tangent)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentPhysical.Weighted.unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentPhysical.Weighted.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ δ => parityMultiplier δ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentPhysical
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end Weighted

end
end Reg.D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentPhysical
