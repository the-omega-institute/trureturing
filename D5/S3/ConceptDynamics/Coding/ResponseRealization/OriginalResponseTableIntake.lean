/- GID: D5/S3/ConceptDynamics/Coding/ResponseRealization/OriginalResponseTableIntake
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResponseRealization/OriginalResponseTableIntake
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original automorphism windows yield total finite tables and the same actual forward and inverse history maps. -/

/- Reuse the realization-based finite tables of the original automorphism and its inverse. Keep the same TablePair and SameTableConjugacy witness. -/
import D5.S3.ConceptDynamics.Coding.ResponseGraphs.OriginalResponseGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.OriginalResponseTableIntake

open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion
open D5.S3.ConceptDynamics.Coding.StandardBeamHomeomorphisms

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
variable [TopologicalSpace V] [DiscreteTopology V]
variable [TopologicalSpace E] [DiscreteTopology E]
variable (G : DirectedMultigraph V E) (hG : Essential G) (h : FullAut G)

private def realization {N : ℕ} (w : LegalWord G N) (hN : 0 < N) : History G :=
  Classical.choose (every_prescribed_word_has_actual_history G hG w hN)

private def table (a b : ℕ) (_hab : Controls G h.val a b) :
    LegalWord G (a + b + 1) → E := fun w =>
  (h.val (realization G hG w (by omega))).val (a : ℤ)

private theorem table_apply {a b : ℕ} (hab : Controls G h.val a b)
    (x : History G) (i : ℤ) :
    (h.val x).val i = table G hG h a b hab
      (historyWindow G x (i - (a : ℤ)) (a + b + 1)) := by
  let w := historyWindow G x (i - (a : ℤ)) (a + b + 1)
  let z := realization G hG w (by omega)
  have hz : ∀ j : Fin (a + b + 1), z.val (j.val : ℤ) =
      x.val (i - (a : ℤ) + (j.val : ℤ)) := by
    intro j
    exact Classical.choose_spec (every_prescribed_word_has_actual_history G hG w (by omega)) j
  let z' := translate G ((a : ℤ) - i) z
  have hwindow : ∀ t : ℤ, i - (a : ℤ) ≤ t → t ≤ i + (b : ℤ) →
      z'.val t = x.val t := by
    intro t ht₀ ht₁
    have hn : 0 ≤ t + (a : ℤ) - i := by omega
    let j : Fin (a + b + 1) := ⟨(t + (a : ℤ) - i).toNat, by omega⟩
    have hj : (j.val : ℤ) = t + (a : ℤ) - i := by
      dsimp [j]
      exact Int.toNat_of_nonneg hn
    change z.val (t + ((a : ℤ) - i)) = x.val t
    have ht : t + ((a : ℤ) - i) = (j.val : ℤ) := by omega
    have hindex : i - (a : ℤ) + (j.val : ℤ) = t := by rw [hj]; omega
    rw [ht, hz]
    exact congrArg x.val hindex
  have ho := hab z' x i hwindow
  have hc : (h.val z').val i = (h.val z).val (a : ℤ) := by
    have ht : h.val z' = translate G ((a : ℤ) - i) (h.val z) :=
      commute_translate G h ((a : ℤ) - i) z
    rw [ht]
    change (h.val z).val (i + ((a : ℤ) - i)) = (h.val z).val (a : ℤ)
    exact congrArg (h.val z).val (by omega)
  exact ho.symm.trans hc

/-- This is the predecessor's actual finite pair, with the same realization
choice and original h/h⁻¹; it is consumed by the response construction. -/
def tables (a b c d : ℕ) (hab : Controls G h.val a b)
    (hcd : Controls G h.val.symm c d) : TablePair G G a b c d :=
  ⟨table G hG h a b hab, table G hG h⁻¹ c d hcd⟩

def actualWitness {a b c d : ℕ} (hab : Controls G h.val a b)
    (hcd : Controls G h.val.symm c d) :
    SameTableConjugacy (tables G hG h a b c d hab hcd) where
  forward := h.val
  backward := h.val.symm
  forward_table := table_apply G hG h hab
  backward_table := table_apply G hG h⁻¹ hcd
  left_inverse := h.val.symm_apply_apply
  right_inverse := h.val.apply_symm_apply
  continuous_forward := h.val.continuous
  continuous_backward := h.val.symm.continuous
  shift_forward := h.property
  shift_backward := by
    intro y
    apply h.val.injective
    simpa only [h.val.apply_symm_apply] using (h.property (h.val.symm y)).symm

end D5.S3.ConceptDynamics.Coding.OriginalResponseTableIntake
