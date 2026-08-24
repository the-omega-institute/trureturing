/- GID: D5/S3/ConceptDynamics/Dialectics/OneStepRepairUniversalProperty
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Dialectics/OneStepRepairUniversalProperty
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One-step factors are image-unique and kernel-coarsest, including empty states. -/
/- Library-search audit trail (2026-08-25):
   * Exact-name searches in `D5`, `Blueprint`, and the frozen ledger found no
     `one_step_repair_universal` declaration.
   * `DeterministicInterfaceEquivalence.depthOneKernel` is the existing
     one-step equality kernel and is reused in the kernel-containment proof.
   * `UniversalSufficiencyFactorization.universal_sufficiency_factorization`
     has the adjacent factorization-versus-fiber-constancy shape, but targets
     a realized image and needs a nonempty source for its off-range extension.
   * The exact pinned-Mathlib hit `Set.eqOn_range` converts equality after
     composition with `r` into equality on `Set.range r`; it is used below.
   * `EffectiveImageUniqueness.effective_image_uniqueness` and
     `RealizedImageKernelFactorization` are adjacent image-level packages, but
     neither states the requested concrete product-interface factorization.
   * The `loogle` and `leansearch` executables are absent from PATH on this lane.
-/

import D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence
import Mathlib.Data.Set.Function

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Dialectics.OneStepRepairUniversalProperty

open D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence

/-- The one-step interface records the current readout and its next value. -/
def oneStepInterface {X B : Type*} (q : X → B) (F : X → X) : X → B × B :=
  fun x ↦ (q x, q (F x))

/-- Any interface deciding both coordinates factors the one-step interface. -/
theorem one_step_repair_universal
    {X B C : Type*} (q : X → B) (F : X → X) (r : X → C)
    (a : C → B) (b : C → B)
    (hcurrent : q = a ∘ r) (hnext : q ∘ F = b ∘ r) :
    oneStepInterface q F = (fun c ↦ (a c, b c)) ∘ r := by
  funext x
  apply Prod.ext
  · simpa only [oneStepInterface, Function.comp_apply] using congrFun hcurrent x
  · simpa only [oneStepInterface, Function.comp_apply] using congrFun hnext x
#print axioms one_step_repair_universal

/-- Two factors of the one-step interface agree at every realized `r`-coordinate. -/
theorem one_step_repair_factor_unique_on_range
    {X B C : Type*} (q : X → B) (F : X → X) (r : X → C)
    (a1 b1 a2 b2 : C → B)
    (hfirst : oneStepInterface q F = (fun c ↦ (a1 c, b1 c)) ∘ r)
    (hsecond : oneStepInterface q F = (fun c ↦ (a2 c, b2 c)) ∘ r) :
    Set.EqOn (fun c ↦ (a1 c, b1 c)) (fun c ↦ (a2 c, b2 c)) (Set.range r) := by
  apply Set.eqOn_range.mpr
  exact hfirst.symm.trans hsecond
#print axioms one_step_repair_factor_unique_on_range

/-- Coarseness means every `r`-fiber lies inside the one-step interface kernel. -/
theorem one_step_repair_kernel_contains
    {X B C : Type*} (q : X → B) (F : X → X) (r : X → C)
    (a : C → B) (b : C → B)
    (hcurrent : q = a ∘ r) (hnext : q ∘ F = b ∘ r) :
    ∀ x y : X, r x = r y → oneStepInterface q F x = oneStepInterface q F y := by
  intro x y hxy
  have hDepth : depthOneKernel q F x y := by
    constructor
    · calc
        q x = a (r x) := by
          simpa only [Function.comp_apply] using congrFun hcurrent x
        _ = a (r y) := congrArg a hxy
        _ = q y := by
          simpa only [Function.comp_apply] using (congrFun hcurrent y).symm
    · calc
        q (F x) = b (r x) := by
          simpa only [Function.comp_apply] using congrFun hnext x
        _ = b (r y) := congrArg b hxy
        _ = q (F y) := by
          simpa only [Function.comp_apply] using (congrFun hnext y).symm
  exact Prod.ext hDepth.1 hDepth.2
#print axioms one_step_repair_kernel_contains

/-- The current-coordinate hypothesis cannot be omitted from factorization. -/
theorem current_factorization_hypothesis_is_necessary :
    ∃ (q : Bool → Bool) (F : Bool → Bool) (r : Bool → Unit)
      (a b : Unit → Bool),
      q ∘ F = b ∘ r ∧
        oneStepInterface q F ≠ (fun c ↦ (a c, b c)) ∘ r := by
  refine ⟨id, (fun _ ↦ false), (fun _ ↦ ()), (fun _ ↦ false),
    (fun _ ↦ false), rfl, ?_⟩
  intro hfactor
  simpa [oneStepInterface] using congrFun hfactor true
#print axioms current_factorization_hypothesis_is_necessary

/-- The next-coordinate hypothesis cannot be omitted from factorization. -/
theorem next_factorization_hypothesis_is_necessary :
    ∃ (q : Bool × Bool → Bool) (F : Bool × Bool → Bool × Bool)
      (r : Bool × Bool → Bool) (a b : Bool → Bool),
      q = a ∘ r ∧
        oneStepInterface q F ≠ (fun c ↦ (a c, b c)) ∘ r := by
  refine ⟨Prod.fst, (fun p ↦ (p.2, p.1)), Prod.fst, id, id, rfl, ?_⟩
  intro hfactor
  simpa [oneStepInterface] using congrFun hfactor (false, true)
#print axioms next_factorization_hypothesis_is_necessary

/-- The factorization remains valid when the state type is empty. -/
example :
    let q : Empty → Unit := fun x ↦ x.elim
    let F : Empty → Empty := id
    let r : Empty → Unit := fun x ↦ x.elim
    oneStepInterface q F = (fun c ↦ (c, c)) ∘ r := by
  dsimp
  funext x
  exact x.elim

/-- Constant maps on the singleton state type satisfy the factorization. -/
example :
    oneStepInterface (fun _ : Unit ↦ false) id =
      (fun _ : Unit ↦ (false, false)) ∘ id := rfl

/-- Identity readout, update, and comparison interface satisfy the factorization. -/
example :
    oneStepInterface (id : Bool → Bool) id = (fun c ↦ (c, c)) ∘ id := rfl

end D5.S3.ConceptDynamics.Dialectics.OneStepRepairUniversalProperty
