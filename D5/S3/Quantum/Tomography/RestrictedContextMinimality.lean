/- GID: D5/S3/Quantum/Tomography/RestrictedContextMinimality
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/RestrictedContextMinimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete complementary-context tomography is minimal among its context subfamilies. -/

import D5.S3.Quantum.Tomography.ObserverDiagonalSeparation

/-!
# Restricted Context Minimality

This module strengthens complete complementary-context tomography from a
sufficiency result to an exact subfamily classification. It supports the
paper's claim that every context in the supplied complete family is necessary:
omitting any one context makes two explicit projectors empirically
indistinguishable. This is minimality within the supplied context family, not a
global lower bound over arbitrary POVMs or experimental designs.
-/

/- Library-search audit trail (2026-09-06):
   * Repository searches for restricted context readouts, omitted contexts, and
     injective `Finset`-indexed readouts found no exact theorem. The existing
     `complete_context_tomography` theorem supplies the full-family injectivity
     direction and is applied directly.
   * Pinned mathlib has no `Finset.ne_univ_iff_exists_not_mem`; the exact hit
     `Finset.eq_univ_iff_forall` is used to extract an omitted context.
   * Related repository hits for coordinate deletion and restricted observers
     concern different carriers and do not imply projector-trace minimality.
-/

open scoped BigOperators

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.RestrictedContextMinimality

open Matrix
open D5.S3.Quantum.Tomography.RankOneContextCommutator
open D5.S3.Quantum.Tomography.CompleteContextTomography

/-- The projector-trace readout restricted to a finite subfamily of the
supplied complementary contexts. -/
def restrictedContextReadout {n : Nat}
    (context : Fin (n + 2) -> RankOneContext (n + 1))
    (S : Finset (Fin (n + 2)))
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    (ℓ : ↑S) -> Fin (n + 1) -> ℂ :=
  fun ℓ j => trace (X * (context ℓ.1).projector j)

/-- If a context is omitted in dimension at least two, its first two
projectors are distinct matrices but have identical restricted readouts. -/
theorem omitted_context_projectors_indistinguishable
    {n : Nat} (hn : 1 ≤ n)
    (context : Fin (n + 2) -> RankOneContext (n + 1))
    (hoverlap : ∀ ℓ k j r,
      trace ((context ℓ).projector j * (context k).projector r) =
        if ℓ = k then (if j = r then 1 else 0)
        else ((n + 1 : Nat) : ℂ)⁻¹)
    {S : Finset (Fin (n + 2))} {ℓ : Fin (n + 2)} (hℓ : ℓ ∉ S) :
    (context ℓ).projector ⟨0, by omega⟩ ≠
        (context ℓ).projector ⟨1, by omega⟩ ∧
      restrictedContextReadout context S ((context ℓ).projector ⟨0, by omega⟩) =
        restrictedContextReadout context S ((context ℓ).projector ⟨1, by omega⟩) := by
  let zero : Fin (n + 1) := ⟨0, by omega⟩
  let one : Fin (n + 1) := ⟨1, by omega⟩
  have hzeroOne : zero ≠ one := by
    intro h
    have hval := congrArg Fin.val h
    simp [zero, one] at hval
  have honeZero : one ≠ zero := Ne.symm hzeroOne
  constructor
  · intro hequal
    have htrace := congrArg
      (fun P => trace (P * (context ℓ).projector zero)) hequal
    rw [hoverlap ℓ ℓ zero zero, hoverlap ℓ ℓ one zero] at htrace
    simp [honeZero] at htrace
  · funext k j
    have hne : ℓ ≠ k.1 := by
      intro h
      apply hℓ
      rw [h]
      exact k.2
    simp only [restrictedContextReadout]
    rw [hoverlap ℓ k.1 zero j, hoverlap ℓ k.1 one j]
    simp [hne]

/-- For dimension at least two, restriction to a context subfamily is
injective on all complex matrices exactly when no context was omitted. -/
theorem restricted_contextReadout_injective_iff
    {n : Nat} (hn : 1 ≤ n)
    (context : Fin (n + 2) -> RankOneContext (n + 1))
    (hoverlap : ∀ ℓ k j r,
      trace ((context ℓ).projector j * (context k).projector r) =
        if ℓ = k then (if j = r then 1 else 0)
        else ((n + 1 : Nat) : ℂ)⁻¹)
    (S : Finset (Fin (n + 2))) :
    Function.Injective (restrictedContextReadout context S) ↔
      S = Finset.univ := by
  constructor
  · intro hinjective
    by_contra hproper
    rw [Finset.eq_univ_iff_forall, not_forall] at hproper
    obtain ⟨ℓ, hℓ⟩ := hproper
    obtain ⟨hdistinct, hindistinguishable⟩ :=
      omitted_context_projectors_indistinguishable hn context hoverlap hℓ
    exact hdistinct (hinjective hindistinguishable)
  · intro hfull
    subst S
    intro X Y hreadout
    apply (complete_context_tomography context hoverlap).2.2
    intro ℓ j
    have hcoordinate :=
      congrFun (congrFun hreadout ⟨ℓ, Finset.mem_univ ℓ⟩) j
    simpa [restrictedContextReadout] using hcoordinate

#print axioms restrictedContextReadout
#print axioms omitted_context_projectors_indistinguishable
#print axioms restricted_contextReadout_injective_iff

end D5.S3.Quantum.Tomography.RestrictedContextMinimality
