/- GID: D5/S3/Zeros/GRH/Lib/Shimura/TraceFormula/DefiniteTrace
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Shimura/TraceFormula/DefiniteTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Shimura.TraceFormula.DefiniteTrace. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Shimura/TraceFormula/DefiniteTrace.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Shimura.Transfer.MarkedPairs
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Simple trace formula: Hecke trace on a definite group; non-elliptic terms vanish (known
result; see Lib.Shimura.TraceFormula.MarkedEqDefinite).

This file: Trace of a Hecke operator on definite algebraic modular forms as orbital sum. -/

variable {E : Type} [Field E] [CMBase E] {n : Type} [Fintype n] (𝔑) {W} [AddCommGroup.{0} W]
  [Module ℂ W] (ξ : Representation ℂ (GL n E) W)

/-- The W-valued functions φ on GL_n of the finite adeles with φ(yx) = ξ(y)φ(x) for y in GL_n(E),
right K(𝔑)-invariant, and zero at every x without `IsSignedFrame` x 1. -/
noncomputable abbrev definiteForms :=
  ξ.coindV toFinGL ⊓ .pi {x | ¬IsSignedFrame x 1} ⊥ ⊓ levelSpace (rightRegular ..) (levelGU n 𝔑)

open Set Submodule

attribute [local simp] eigenReflection subset_def countTerm_mk ratConj mul_assoc

/-- The action of the Hecke algebra of level K(𝔑) on `definiteForms` by right translation. -/
noncomputable def definiteForms.rep := Representation.subrepresentation
  ((rightRegular ..).asAlgebraHom.comp (heckeAlgebra n ℂ 𝔑).val).toMonoidHom (definiteForms 𝔑 ξ)
  fun a φ h ↦ ⟨(comap ((rightRegular ..).asAlgebraHom.toLinearMap.flip φ) (_ ⊓ _)).span_le.2
  (by simp_all [↓image_subset_iff, isSignedFrame_mul_iff 1, GUPlus]) a.2.1, a.2.2 h.2⟩

open _root_.Quotient

/-- Trace formula, definite side: for E⁺ ≠ ℚ, 𝔑 neat, W finite-dimensional, the forms are
finite-dimensional and finitely many orbits of definite triples count; if a is regular and
tr ξ(y⁻¹) = ∑_μ w(P, μ) for separable P, then tr a is their orbit sum.

Known result: Simple trace formula: Hecke trace on a definite group; non-elliptic terms vanish. -/
lemma trace_definiteForms {𝔑} [Module.Finite ℂ W] (hN : IsNeat n 𝔑) a w :
  Module.Finite ℂ (definiteForms 𝔑 ξ) ∧ (countTerm False a w).support.Finite ∧
  (IsRegularHecke a → (∀ y, y.1.charpoly.Separable → (ξ y⁻¹).trace ℂ _ =
  ∑ i, w y.1.charpoly i) → (definiteForms.rep 𝔑 ξ a).trace ℂ _ = ∑ᶠ c, countTerm False a w c) := by
  let I := {c : DoubleCosets toFinGL.range (levelGU n 𝔑) // IsSignedFrame c.out 1}
  cases @nonempty_fintype I ((finite_isSignedFrame_classes (isOpen_congruenceGL_span hN.1)).subset
    fun c ↦ (⟨_, ⟨_, ·⟩, c.out_eq⟩))
  choose c γ e using by simpa [← inv_mul_eq_iff_eq_mul, -MonoidHom.coe_range] using
    exists_eq_map_mul_rep_mul toFinGL (levelGU n 𝔑) out_eq
  have D g := by simpa using
    isSignedFrame_mul_iff (x := (toFinGL (γ g))⁻¹ * g) (ℓ := 1) (γ g) (inv_mem (e g).1)
  have i {c} {d : I} := eq_and_eq_one_of_doubleCoset_rep (c := c) out_eq fun _ ↦
    (hN.2 d.2 · (by simp))
  refine .imp_right (⟨finite_of_finite_preimage (f := fun ((c : I), y, μ) ↦ ⟦(c.1.out, y⁻¹, μ)⟧) ?A
    ?S, fun r hw ↦ .trans · ?_⟩) (trace_eq_weighted_sum (·.1.out) 1 _ (range_subtype _) 1 (s := 1)
    (fun (j : I) g ↦ ite (j = c g) {γ g} ∅) (fun j g y ↦ ?_) (by
    simp +contextual [apply_ite, Subtype.coe_eq_iff, D]) (by tauto) rfl)
  exact (finite_iUnion fun c : I ↦ (((heckeCosetFn a).hasFiniteSupport.preimage (f :=
    (⟦c.1.out⁻¹ * toFinGL · * c.1.out⟧)) fun y _ z _ h ↦ inv_mul_eq_one.1 (i _ (by
    simpa using QuotientGroup.eq.1 h)).2).prod finite_univ).image (c, ·)).subset (by simp; tauto)
  use Quotient.ind fun ⟨q, y, μ⟩ ↦ q.inductionOn fun x H ↦ ⟨(⟨_, by simp_all⟩, (_ * _)⁻¹, μ), sound
    ⟨(γ x)⁻¹, Prod.ext (QuotientGroup.eq.2 (e x)).symm rfl⟩⟩
  rw [← indicator_eq_self.2 ?S, ← finsum_mem_def, finsum_mem_range, finsum_curry₃ _ ?A]
  simp [(_ : I).2, ← Finset.mul_sum]
  congr! 3; simpa [or_iff_not_imp_right] using hw _ ∘ @r _⁻¹ _
  use fun p q h ↦ (exact h).rec fun g h ↦ by
    grind [i g (by simpa using QuotientGroup.eq.1 congr($h.1).symm), inv_inj, one_smul]
  rw [← mul_mem_cancel_left (e g)]; simp [mem_ite]
  use by simp_all, fun H ↦ by grind [i ((γ g)⁻¹ * y) (by simpa), inv_mul_eq_one]
