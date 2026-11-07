/- GID: D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseComponentProjector
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SymmetricExtensions/BoseComponentProjector
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Tensor factorization of the graph component Bose projector. -/

import D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension

/-! The actual component permutation average and its tensor factorization. -/

open scoped BigOperators ComplexOrder
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor
open D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension

namespace D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseComponentProjector

set_option backward.isDefEq.respectTransparency false

variable {I L : Type*} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]

attribute [local instance] Classical.propDecidable

open Matrix
open private Q_mulVec Q_mul_P from
  D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor
open private pair_support_of_column_swap from
  D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension

/-- Two disconnected components can carry distinct basis labels. The resulting
rank-one positive operator has every required Bose edge marginal and fails
full Bose support. For the sole edge `{0,1}` on three qubits, this construction
with component labels `0,1` is exactly `|001⟩⟨001|`. -/
theorem disconnected_counterexample (G : SimpleGraph I) (a b : I)
    (hab : ¬ G.Reachable a b) (l m : L) (hlm : l ≠ m) :
    let w : I → L := fun i => if G.Reachable a i then l else m
    let v : (I → L) → ℂ := fun x => if x = w then 1 else 0
    let E := Matrix.vecMulVec v (star v)
    E.PosSemidef ∧
      (∀ c d (hcd : G.Adj c d), pairSymmetricProjector *
        edgeMarginal c d hcd.ne E * pairSymmetricProjector = edgeMarginal c d hcd.ne E) ∧
      P I L * E * P I L ≠ E := by
  classical
  let w : I → L := fun i => if G.Reachable a i then l else m
  let v : (I → L) → ℂ := fun x => if x = w then 1 else 0
  let E := Matrix.vecMulVec v (star v)
  have hp : E.PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
  refine ⟨hp,?_,?_⟩
  · intro c d hcd
    have hcol : w c = w d := by
      have hr : G.Reachable a c ↔ G.Reachable a d :=
        ⟨fun h => h.trans hcd.reachable, fun h => h.trans hcd.symm.reachable⟩
      simp only [w,hr]
    have hw : w ∘ Equiv.swap c d = w := by
      funext i
      by_cases hc : i = c
      · subst i
        simpa only [Function.comp_apply,Equiv.swap_apply_left] using hcol.symm
      by_cases hd : i = d
      · subst i
        simpa only [Function.comp_apply,Equiv.swap_apply_right] using hcol
      · simp only [Function.comp_apply,Equiv.swap_apply_of_ne_of_ne hc hd]
    have hx (x : I → L) : x ∘ Equiv.swap c d = w ↔ x = w := by
      constructor
      · intro h
        funext i
        have hh := congrFun h (Equiv.swap c d i)
        simpa only [Function.comp_apply,Equiv.swap_apply_self,
          Equiv.apply_swap_eq_self hcol i] using hh
      · rintro rfl
        exact hw
    apply pair_support_of_column_swap c d hcd.ne E hp
    intro x y
    simp only [E,Matrix.vecMulVec_apply,v,hx]
  · intro hs
    have he : Q (Equiv.swap a b) * E = E := by
      calc
        _ = Q (Equiv.swap a b) * (P I L * E * P I L) := by rw [hs]
        _ = P I L * E * P I L := by
          rw [← Matrix.mul_assoc,← Matrix.mul_assoc,Q_mul_P]
        _ = E := hs
    have hneq : w ∘ Equiv.swap a b ≠ w := by
      intro hh
      have hv := congrFun hh a
      change w (Equiv.swap a b a) = w a at hv
      rw [Equiv.swap_apply_left] at hv
      have hwa : w a = l := if_pos (.refl a)
      have hwb : w b = m := if_neg hab
      rw [hwa,hwb] at hv
      exact hlm hv.symm
    have hx : E (w ∘ Equiv.swap a b) w = E w w :=
      (congrFun (Q_mulVec (Equiv.swap a b) (fun z => E z w)) w).symm.trans
        (congrArg (fun A => A w w) he)
    have hz : (0 : ℂ) = 1 := by
      simpa [E,Matrix.vecMulVec_apply,v,hneq] using hx
    exact zero_ne_one hz

#print axioms disconnected_counterexample

end D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseComponentProjector
