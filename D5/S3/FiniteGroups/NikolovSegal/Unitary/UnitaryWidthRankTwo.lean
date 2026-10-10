/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRankTwo
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRankTwo
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryWidthTranspose
import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryInnerUNormalization
import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryRankTwoFixedFieldEquiv
import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.SLnUnipotentWidth

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The rank-two base of Hermitian rank reduction. The accepted coordinate
isomorphism is used unchanged; both triangular orientations are transported
by its literal matrix formula into the actual general SU carrier. -/
namespace NikolovSegal.UnitaryWholeGroupWidth
open Matrix UnitarySylow UnitaryField
universe u
variable {F : Type u} [Field F] [Finite F] {ι : RingAut F}

def rankTwoCarrierEquiv (hinv : Function.Involutive ι) :
    specialUnitary 2 ι ≃* UnitaryRankTwo.specialUnitary ι where
  toFun g := ⟨g.val,(mem_specialUnitary_iff_hermitian ι hinv g.val).mp g.prop⟩
  invFun g := ⟨g.val,(mem_specialUnitary_iff_hermitian ι hinv g.val).mpr g.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Absolute four-factor width on actual SU2 over every finite quadratic field.
There is no field-size or characteristic cutoff. -/
theorem rankTwo_four_factor (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (g : specialUnitary 2 ι) :
    ∃ a b c d : specialUnitary 2 ι,
      Positive a ∧ Negative b ∧ Positive c ∧ Negative d ∧ a*b*c*d=g := by
  classical
  obtain ⟨τ,hτ,hanti⟩ := UnitaryRankTwo.exists_antifixed ι hinv hne
  let e := (rankTwoCarrierEquiv hinv).trans (UnitaryRankTwo.coordinateEquiv ι τ hτ hanti)
  have back : ∀ B : SpecialLinearGroup (Fin 2) (fixedField ι),
      (e.symm B).val.val = !![(B.val 0 0:F),τ*(B.val 0 1:F);
        (B.val 1 0:F)/τ,(B.val 1 1:F)] := by
    intro B
    exact UnitaryRankTwo.coordinateEquiv_backward ι τ hτ hanti B
  have hu : ∀ B : SpecialLinearGroup (Fin 2) (fixedField ι),
      SLnUnipotentWidth.Upper B → Positive (e.symm B) := by
    intro B hB r c hrc
    rw [back]
    have h00 := congrArg (fun x : fixedField ι => (x:F)) (hB.2 0)
    have h11 := congrArg (fun x : fixedField ι => (x:F)) (hB.2 1)
    have h10 := congrArg (fun x : fixedField ι => (x:F)) (hB.1 1 0 (by decide))
    fin_cases r <;> fin_cases c <;>
      simp_all [Matrix.sub_apply,Matrix.one_apply]
  have hl : ∀ B : SpecialLinearGroup (Fin 2) (fixedField ι),
      SLnUnipotentWidth.Lower B → Negative (e.symm B) := by
    intro B hB r c hrc
    rw [back]
    have h00 := congrArg (fun x : fixedField ι => (x:F)) (hB.2 0)
    have h11 := congrArg (fun x : fixedField ι => (x:F)) (hB.2 1)
    have h01 := congrArg (fun x : fixedField ι => (x:F)) (hB.1 0 1 (by decide))
    fin_cases r <;> fin_cases c <;>
      simp_all [Matrix.sub_apply,Matrix.one_apply]
  obtain ⟨a,b,c,d,ha,hb,hc,hd,hprod⟩ := SLnUnipotentWidth.four_factor 2 (e g)
  refine ⟨e.symm a,e.symm b,e.symm c,e.symm d,hu a ha,hl b hb,hu c hc,hl d hd,?_⟩
  rw [← map_mul,← map_mul,← map_mul,hprod,e.symm_apply_apply]

/-- Degenerate ranks remain literal actual SU groups. -/
theorem trivial_four_factor {n : ℕ} [Subsingleton (Fin n)]
    (g : specialUnitary n ι) :
    ∃ a b c d : specialUnitary n ι,
      Positive a ∧ Negative b ∧ Positive c ∧ Negative d ∧ a*b*c*d=g := by
  exact ⟨1,1,1,1,positive_one,negative_one,positive_one,negative_one,Subsingleton.elim _ _⟩

/-- The desired literal ordered Fin25 endpoint, fully closed on the rank-two base. -/
theorem rankTwo_alternating_25 (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (g : specialUnitary 2 ι) :
    ∃ a : Fin 25 → specialUnitary 2 ι,
      (∀ j, if j.val % 2 = 0 then
        ∀ r c : Fin 2, c.val < r.val+1 → ((a j).val.val-1) r c=0
      else ∀ r c : Fin 2, r.val < c.val+1 → ((a j).val.val-1) r c=0) ∧
      (List.ofFn a).prod=g := by
  obtain ⟨a,b,c,d,ha,hb,hc,hd,hprod⟩ := rankTwo_four_factor hinv hne g
  let f : Fin 25 → specialUnitary 2 ι :=
    ![a,b,c,d,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
  refine ⟨f,?_,?_⟩
  · intro j
    fin_cases j
    all_goals first | exact ha | exact hb | exact hc | exact hd |
      exact (positive_one (F:=F) (n:=2) (ι:=ι)) | exact (negative_one (F:=F) (n:=2) (ι:=ι))
  · simpa [f,List.ofFn_succ,mul_assoc] using hprod

end NikolovSegal.UnitaryWholeGroupWidth
