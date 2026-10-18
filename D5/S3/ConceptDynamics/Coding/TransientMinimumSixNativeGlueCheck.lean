/-
UNCOMPILED transient exact-check draft. No kernel acceptance is claimed.

The quotient character below is copied from the actual anonymous original
root. It uses the forward time image, its literal subgroup of integer powers,
and the public residue-annihilation proof. The all-five obstruction is supplied
by the already published refutation; no finite certificate is reproved here.

This file checks only the native-character conversion and exclusion of every
positive single period below six. It does not prove the upper root, the exact
2/7 original-system orbit counts, or literal Fix(T^6) sufficiency. The complete
result must consume this glue inside the unchanged accepted anonymous root.

Do not compile while original flight 3821 can launch a compiler. First collect
its actual terminal result and clean its runner. The main 4.35 cache window
has completed; fixed11 is retired. Use canonical make lean with an explicit
nonempty target in the existing session worktree after its 4.35 migration. Keep this exact check
transient; do not publish a bind-only companion theorem.
-/
import D5.S3.ConceptDynamics.Coding.ResetQ4OriginalLocalizedCubes
import D5.S3.ConceptDynamics.Coding.PeriodicActions.ResetQ4SmallPeriodRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding
open EssentialWordRealization ResetNumberedHistories ResetStandardBeamGeometry

local instance nativeIntModule (q : ℕ) :
    Module ℤ (InertGroupBlockConjugacy.DimensionGroup (resetMatrix q)) :=
  AddCommGroup.toIntModule _

example :
    let psi := fun f : ResetFullAut 4 =>
      Units.map (ResetIntegralGluing.rplus 4).toMonoidHom
        (Units.map (ResetIntegralGluing.plus 4).toMonoidHom
          (ResetNativeUnitNormalForm.scalarUnit 4 (by decide)
            (ResetFullStandardBeamRepresentation.rho 4 (by decide) f)
            (ResetHistoryKernel.rho_time 4 (by decide) f)))
    let chi_add : ResetFullAut 4 → ZMod 3 := fun f =>
      ResetQ4UnitCubes.residueQuotientCharacter
        (psi (StandardBeamHomeomorphisms.unitShift (ResetGraph 4)))
        ResetQ4OriginalLocalizedCubes.original_time_residue (Additive.ofMul
          (QuotientGroup.mk'
            (Subgroup.zpowers (psi (StandardBeamHomeomorphisms.unitShift (ResetGraph 4))))
            (psi f)))
    (¬ chi_add.FactorsThrough
      (fun h : ResetFullAut 4 => fun i : Fin 5 =>
        fun x : {x : ResetHistory 4 //
          (shift (ResetGraph 4))^[i.val + 1] x = x} => h.val x.val)) ∧
    (∀ n : ℕ, 0 < n → n < 6 →
      ¬ chi_add.FactorsThrough
        (fun h : ResetFullAut 4 =>
          fun x : {x : ResetHistory 4 //
            (shift (ResetGraph 4))^[n] x = x} => h.val x.val)) := by
  classical
  let psi := fun f : ResetFullAut 4 =>
    Units.map (ResetIntegralGluing.rplus 4).toMonoidHom
      (Units.map (ResetIntegralGluing.plus 4).toMonoidHom
        (ResetNativeUnitNormalForm.scalarUnit 4 (by decide)
          (ResetFullStandardBeamRepresentation.rho 4 (by decide) f)
          (ResetHistoryKernel.rho_time 4 (by decide) f)))
  let chi_add : ResetFullAut 4 → ZMod 3 := fun f =>
    ResetQ4UnitCubes.residueQuotientCharacter
      (psi (StandardBeamHomeomorphisms.unitShift (ResetGraph 4)))
      ResetQ4OriginalLocalizedCubes.original_time_residue (Additive.ofMul
        (QuotientGroup.mk'
          (Subgroup.zpowers (psi (StandardBeamHomeomorphisms.unitShift (ResetGraph 4))))
          (psi f)))
  have lowerAll5 :
      ¬ chi_add.FactorsThrough
        (fun h : ResetFullAut 4 => fun i : Fin 5 =>
          fun x : {x : ResetHistory 4 //
            (shift (ResetGraph 4))^[i.val + 1] x = x} => h.val x.val) := by
    change ¬ ResetQ4SmallPeriodRefutation.claim
    exact ResetQ4SmallPeriodRefutation.result
  refine ⟨lowerAll5, ?_⟩
  intro n hn hn6 hnFactor
  apply lowerAll5
  intro h k hall
  apply hnFactor
  funext x
  let i : Fin 5 := ⟨n - 1, by omega⟩
  have hi : i.val + 1 = n := by
    dsimp only [i]
    omega
  have hx : (shift (ResetGraph 4))^[i.val + 1] x.val = x.val := by
    rw [hi]
    exact x.property
  exact congrFun (congrFun hall i) ⟨x.val, hx⟩

end D5.S3.ConceptDynamics.Coding
