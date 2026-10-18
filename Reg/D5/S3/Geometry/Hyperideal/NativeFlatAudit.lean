import D5.S3.Geometry.Hyperideal.FlatComponentBudget
import Mathlib.Analysis.SpecialFunctions.Arcosh

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open _root_.D5.S3.Geometry.Hyperideal
open FlatComponentBudget PositiveFlatClassification TwoLengthAngleSum
open EdgeStarTransitions (RawFacePairing faceEdge)
namespace Reg.D5.S3.Geometry.Hyperideal.NativeFlatAudit
universe u

abbrev Block := ULift.{u} (Fin 2)

def blockSwap : Equiv.Perm Block.{u} :=
  Equiv.ulift.trans ((Equiv.swap 0 1).trans Equiv.ulift.symm)

/-- Two blocks paired face for face; no zero-curvature equation is asserted. -/
def pairing : RawFacePairing Block.{u} where
  facePair := Equiv.prodCongr blockSwap.{u} (Equiv.refl (Fin 4))
  faceMap := fun _ => Equiv.refl _
  pairInvolutive := by
    apply Equiv.ext
    rintro ⟨⟨t⟩,f⟩
    fin_cases t <;> fin_cases f <;> rfl
  pairFixedFree := by
    rintro ⟨⟨t⟩,f⟩ h
    have hh := congrArg (fun z => z.1.down) h
    fin_cases t <;> norm_num [blockSwap,Equiv.prodCongr] at hh
  mapInverse := by intros; rfl

private theorem step_slot {i j : Block.{u} × Fin 6} (h : pairing.{u}.edgeStep i j) : i.2 = j.2 := by
  obtain ⟨x,n,rfl,rfl⟩ := h
  rfl

def edgeSlot : pairing.{u}.GlobalEdge → Fin 6 := Quotient.lift Prod.snd (by
  intro i j h
  induction h with
  | rel i j h => exact step_slot h
  | refl i => rfl
  | symm i j h ih => exact ih.symm
  | trans i j k h h' ih ih' => exact ih.trans ih')

@[simp] theorem edgeSlot_label (t : Block.{u}) (q : Fin 6) :
    edgeSlot (pairing.{u}.edgeLabel t q) = q := rfl

def values (q : Fin 6) : ℝ := if q = 0 ∨ q = 3 then 14 else 2

def ell (e : pairing.{u}.GlobalEdge) : ℝ := Real.arcosh (values (edgeSlot e))

theorem values_gt_one (q : Fin 6) : 1 < values q := by
  unfold values
  split_ifs <;> norm_num

theorem positive : ∀ e, 0 < ell.{u} e := fun e => Real.arcosh_pos (values_gt_one _)

theorem coordinates_values (t : Block.{u}) : coordinates pairing.{u} ell t = values := by
  funext q
  change Real.cosh (Real.arcosh (values _)) = values q
  rw [edgeSlot_label,Real.cosh_arcosh (values_gt_one q).le]

theorem flat (t : Block.{u}) : Flat pairing.{u} ell t := by
  refine ⟨0,?_⟩
  rw [coordinates_values]
  change rawCos values 0 ≤ -1
  change FourCycleEnvelopes.cosine 14 2 2 14 2 2 ≤ -1
  unfold FourCycleEnvelopes.cosine
  norm_num [FourCycleEnvelopes.rad,FourCycleEnvelopes.numerator]
  rw [div_div,←pow_two,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 315)]
  norm_num

theorem weight_values (t : Block.{u}) (q : Fin 6) :
    weight pairing.{u} ell (pairing.edgeLabel t q) = Real.log (values q) := by
  change Real.log (Real.cosh (ell (pairing.edgeLabel t q))) = _
  change Real.log (Real.cosh (Real.arcosh (values _))) = _
  rw [edgeSlot_label,Real.cosh_arcosh (values_gt_one q).le]

theorem weight_dependence :
    weight pairing.{u} ell (pairing.edgeLabel ⟨0⟩ 0) ≠ weight pairing ell (pairing.edgeLabel ⟨0⟩ 1) := by
  rw [weight_values,weight_values]
  have h0 : values 0 = 14 := by norm_num [values,Fin.ext_iff]
  have h1 : values 1 = 2 := by norm_num [values,Fin.ext_iff]
  rw [h0,h1]
  exact ne_of_gt (Real.log_lt_log (by norm_num) (by norm_num))

end Reg.D5.S3.Geometry.Hyperideal.NativeFlatAudit
