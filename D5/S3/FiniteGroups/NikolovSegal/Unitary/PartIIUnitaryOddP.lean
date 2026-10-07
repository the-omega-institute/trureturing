/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryOddP
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryOddP
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryAmbientEvenUProduct
import Mathlib.Data.Matrix.ColumnRowPartitioned
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
/-! PartII pp271–272, the genuine two-step P for odd SU dimension.
The vector quotient and central VALUE coordinates are coupled by the
actual cross term. No half-trace formula or characteristic restriction. -/
namespace NikolovSegal.PartIIUnitaryOddP
open Matrix PartIIUnitriangularLayers PartIIUnitaryUpperTorus UnitaryField
universe u
variable {F : Type u} [Field F] [Finite F] {d : ℕ}

private def triple : (Fin d ⊕ (Unit ⊕ Fin d)) ≃ Option (Fin d ⊕ Fin d) where
  toFun
    | .inl i => some (.inl i)
    | .inr (.inl _) => none
    | .inr (.inr i) => some (.inr i)
  invFun
    | none => .inr (.inl ())
    | some (.inl i) => .inl i
    | some (.inr i) => .inr (.inr i)
  left_inv := by intro i; cases i with
    | inl i => rfl
    | inr i => cases i with
      | inl i => cases i; rfl
      | inr i => rfl
  right_inv := by intro i; cases i with
    | none => rfl
    | some i => cases i <;> rfl
private def label : (Fin d ⊕ (Unit ⊕ Fin d)) ≃ Fin (2*d+1) := triple.trans (oddLabel d)
private def left (i : Fin d) : Fin (2*d+1) := label (.inl i)
private def right (i : Fin d) : Fin (2*d+1) := label (.inr (.inr i))
private def swap : (Fin d ⊕ (Unit ⊕ Fin d)) ≃ (Fin d ⊕ (Unit ⊕ Fin d)) where
  toFun
    | .inl i => .inr (.inr i)
    | .inr (.inl x) => .inr (.inl x)
    | .inr (.inr i) => .inl i
  invFun
    | .inl i => .inr (.inr i)
    | .inr (.inl x) => .inr (.inl x)
    | .inr (.inr i) => .inl i
  left_inv := by intro i; cases i with
    | inl i => rfl
    | inr i => cases i <;> rfl
  right_inv := by intro i; cases i with
    | inl i => rfl
    | inr i => cases i <;> rfl
private theorem label_reflection (i : Fin d ⊕ (Unit ⊕ Fin d)) :
    label (swap i)=(label i).rev := by
  change oddLabel d (triple (swap i))=(oddLabel d (triple i)).rev
  rw [← oddLabel_reflection]
  congr 1
  cases i with
  | inl i => rfl
  | inr i => cases i <;> rfl

private def rawP (ι : RingAut F) (v : Fin d → F) (B : Matrix (Fin d) (Fin d) F) :
    SpecialLinearGroup (Fin d ⊕ (Unit ⊕ Fin d)) F :=
  ⟨fromBlocks 1 (fromCols (fun i _ => v i) B) 0
    (fromBlocks 1 (fun _ j => -ι (v j)) 0 1), by
      simp [det_fromBlocks_zero₂₁]⟩
def p (ι : RingAut F) (v : Fin d → F) (B : Matrix (Fin d) (Fin d) F) :
    SpecialLinearGroup (Fin (2*d+1)) F := SLnUnipotentWidth.reindexSL label (rawP ι v B)
theorem actual_p_entry (ι : RingAut F) (v : Fin d → F) (B : Matrix (Fin d) (Fin d) F)
    (i j : Fin d ⊕ (Unit ⊕ Fin d)) :
    p ι v B (label i) (label j)=rawP ι v B i j := by
  simp [p,SLnUnipotentWidth.reindexSL,Matrix.reindex_apply,Matrix.submatrix_apply]

theorem actual_p_multiply (ι : RingAut F) (v w : Fin d → F)
    (B C : Matrix (Fin d) (Fin d) F) :
    p ι v B*p ι w C=p ι (v+w) (B+C-(Matrix.of fun i j => v i*ι (w j))) := by
  unfold p
  rw [← map_mul]
  congr 1
  apply SpecialLinearGroup.ext
  intro i j
  rw [SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fintype.sum_sum_type]
  cases i with
  | inl i => cases j with
    | inl j => simp [rawP,Matrix.one_apply]
    | inr j => cases j with
      | inl j => simp [rawP,Matrix.one_apply] <;> ring
      | inr j => simp [rawP,Matrix.one_apply] <;> ring
  | inr i => cases i with
    | inl i => cases j with
      | inl j => simp [rawP]
      | inr j => cases j with
        | inl j => simp [rawP,Matrix.one_apply]
        | inr j => simp [rawP,Matrix.one_apply,map_add] <;> ring
    | inr i => cases j with
      | inl j => simp [rawP]
      | inr j => cases j <;> simp [rawP,Matrix.one_apply]
private theorem p_zero (ι : RingAut F) : p ι (0:Fin d → F) 0=1 := by
  unfold p
  rw [show rawP ι (0:Fin d → F) 0=1 by
    apply SpecialLinearGroup.ext
    intro i j
    cases i with
    | inl i => cases j with
      | inl j => simp [rawP,Matrix.one_apply]
      | inr j => cases j <;> simp [rawP,Matrix.one_apply]
    | inr i => cases i with
      | inl i => cases j with
        | inl j => simp [rawP,Matrix.one_apply]
        | inr j => cases j <;> simp [rawP,Matrix.one_apply]
      | inr i => cases j with
        | inl j => simp [rawP,Matrix.one_apply]
        | inr j => cases j <;> simp [rawP,Matrix.one_apply]]
  exact map_one _
theorem actual_p_inverse (ι : RingAut F) (v : Fin d → F) (B : Matrix (Fin d) (Fin d) F) :
    (p ι v B)⁻¹=p ι (-v) (-B-(Matrix.of fun i j => v i*ι (v j))) := by
  apply inv_eq_of_mul_eq_one_right
  rw [actual_p_multiply]
  have hv : v+ -v=0 := add_neg_cancel v
  have hB : B+(-B-(Matrix.of fun i j => v i*ι (v j)))-(Matrix.of fun i j => v i*ι ((-v) j))=0 := by
    ext i j; simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.neg_apply,Matrix.of_apply,Matrix.zero_apply,Pi.neg_apply,map_neg] <;> ring
  rw [hv,hB,p_zero]

/-- Actual central law for the vector quotient and true central layer. -/
def Constraint (ι : RingAut F) (v : Fin d → F) (B : Matrix (Fin d) (Fin d) F) : Prop :=
  ∀ i j, B i j+ι (B j i)+v i*ι (v j)=0
theorem actual_p_unitary_iff (ι : RingAut F) (hinv : Function.Involutive ι)
    (v : Fin d → F) (B : Matrix (Fin d) (Fin d) F) :
    steinberg ι (p ι v B)=p ι v B ↔ Constraint ι v B := by
  constructor
  · intro hh i j
    have he := congrArg (fun g : SpecialLinearGroup (Fin (2*d+1)) F => g (left i) (right j)) hh
    simp only [left,right] at he
    rw [steinberg_entry,actual_p_inverse,← label_reflection,← label_reflection] at he
    simp [swap,actual_p_entry,rawP,Matrix.sub_apply,Matrix.neg_apply,Matrix.of_apply,
      map_sub,map_neg,map_mul,hinv (v i)] at he
    linear_combination -he
  · intro hB
    apply SpecialLinearGroup.ext
    intro i j
    obtain ⟨i,rfl⟩ := label.surjective i
    obtain ⟨j,rfl⟩ := label.surjective j
    rw [steinberg_entry,actual_p_inverse,← label_reflection,← label_reflection,actual_p_entry,actual_p_entry]
    cases i with
    | inl i => cases j with
      | inl j => simp [swap,rawP,Matrix.one_apply,eq_comm]
      | inr j => cases j with
        | inl j => simp [swap,rawP,map_neg,hinv (v i)]
        | inr j => simp [swap,rawP,map_sub,map_neg,map_mul,hinv (v i)]; linear_combination -(hB i j)
    | inr i => cases i with
      | inl i => cases j with
        | inl j => simp [swap,rawP]
        | inr j => cases j <;> simp [swap,rawP,Matrix.one_apply]
      | inr i => cases j with
        | inl j => simp [swap,rawP]
        | inr j => cases j <;> simp [swap,rawP,Matrix.one_apply,eq_comm]

theorem actual_p_upper (ι : RingAut F) (v : Fin d → F) (B : Matrix (Fin d) (Fin d) F) :
    LayerDepth 1 ((p ι v B).val-1) := by
  intro i j hij
  obtain ⟨i,rfl⟩ := label.surjective i
  obtain ⟨j,rfl⟩ := label.surjective j
  simp only [Matrix.sub_apply,actual_p_entry,Matrix.one_apply,label.injective.eq_iff]
  cases i with
  | inl i => cases j with
    | inl j => simp [rawP,Matrix.one_apply]
    | inr j => cases j with
      | inl j =>
        have h := i.isLt
        change d < i.val+1 at hij
        omega
      | inr j =>
        have hi := i.isLt; have hj := j.isLt
        change 2*d-j.val < i.val+1 at hij
        omega
  | inr i => cases i with
    | inl i => cases j with
      | inl j => simp [rawP,Matrix.one_apply]
      | inr j => cases j with
        | inl j => simp [rawP,Matrix.one_apply]
        | inr j =>
          have h := j.isLt
          change 2*d-j.val < d+1 at hij
          omega
    | inr i => cases j with
      | inl j => simp [rawP,Matrix.one_apply]
      | inr j => cases j <;> simp [rawP,Matrix.one_apply]

/-- Every vector in the actual P/P(2) has a genuine unitary lift.
Diagonal central coordinates use relative trace; all off-diagonal
coupling is retained, including characteristic two. -/
theorem actual_p_vector_lift (ι : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (v : Fin d → F) :
    ∃ B : Matrix (Fin d) (Fin d) F, Constraint ι v B ∧
      steinberg ι (p ι v B)=p ι v B ∧ LayerDepth 1 ((p ι v B).val-1) := by
  classical
  have hz : ∀ i : Fin d, ∃ z : F, z+ι z= -(v i*ι (v i)) := by
    intro i
    let t : fixedField ι := ⟨-(v i*ι (v i)),by
      rw [mem_fixedField,map_neg,map_mul,hinv (v i)]; ring⟩
    exact trace_surjective ι hinv hne t
  choose z hz using hz
  let B : Matrix (Fin d) (Fin d) F := fun i j =>
    if i=j then z i else if i<j then -(v i*ι (v j)) else 0
  have hB : Constraint ι v B := by
    intro i j
    by_cases he : i=j
    · subst j
      simp only [B,ite_true]
      linear_combination hz i
    · by_cases hij : i<j
      · simp only [B,if_neg he,if_neg (Ne.symm he),if_pos hij,if_neg (not_lt.mpr (le_of_lt hij)),map_zero]
        ring
      · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij) (Ne.symm he)
        simp only [B,if_neg he,if_neg (Ne.symm he),if_neg hij,if_pos hji,map_neg,map_mul,hinv (v i)]
        ring
  exact ⟨B,hB,(actual_p_unitary_iff ι hinv v B).mpr hB,actual_p_upper ι v B⟩

end NikolovSegal.PartIIUnitaryOddP
