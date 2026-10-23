/- GID: D5/S1/Words/Sequenceability/CharacteristicThreeOpposite
   generality: G
   mirror-B: D5/B/S1/Words/Sequenceability/CharacteristicThreeOpposite
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Every finite characteristic-three space admits an exact opposite-hole ordering. -/

import D5.S1.Words.Sequenceability.CharacteristicThreeOrdering
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Prescribed-direction transport from a finite-field cycle to the original vector space. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Sequenceability.CharacteristicThreeOpposite

open Function Finset
open D5.S1.Words.Sequenceability.CharacteristicThreeOrdering

variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]

private theorem prescribed_equiv {K : Type*} [Field K] [Algebra (ZMod 3) K]
    [FiniteDimensional (ZMod 3) K]
    (hd : Module.finrank (ZMod 3) (K × ZMod 3) = Module.finrank (ZMod 3) V)
    (x : V) (hx : x ≠ 0) :
    ∃ φ : (K × ZMod 3) ≃ₗ[ZMod 3] V, φ (0, 1) = x := by
  classical
  obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hd
  let w := e (0, 1)
  have hw : w ≠ 0 := by
    intro h
    have he : (0, 1) = ((0, 0) : K × ZMod 3) := e.injective (h.trans (map_zero e).symm)
    have := congrArg Prod.snd he
    exact one_ne_zero this
  let eone := LinearEquiv.toSpanNonzeroSingleton (ZMod 3) V w hw
  let etwo := LinearEquiv.toSpanNonzeroSingleton (ZMod 3) V x hx
  let f := eone.symm.trans etwo
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  let q : Submodule.span (ZMod 3) ({w} : Set V) :=
    ⟨w, Submodule.mem_span_singleton_self w⟩
  have hone : eone 1 = q := by simp [eone, q]
  have hf : f q = (⟨x, Submodule.mem_span_singleton_self x⟩ :
      Submodule.span (ZMod 3) ({x} : Set V)) := by
    change etwo (eone.symm q) = _
    rw [← hone, eone.symm_apply_apply]
    simp [etwo]
  refine ⟨e.trans g, ?_⟩
  have hgw := (hg q).symm
  rw [hf] at hgw
  exact hgw

/-- The first M prefixes are distinct; the sole full return is allowed, and no proper
nonempty interval has zero sum. The word enumerates the exact prescribed complement. -/
theorem exists_opposite_ordering (hd : 2 ≤ Module.finrank (ZMod 3) V)
    (x : V) (hx : x ≠ 0) :
    let M := 3 ^ Module.finrank (ZMod 3) V - 3
    ∃ w : ℕ → V,
      Injective (fun i : Fin M => w i.val) ∧
      Set.range (fun i : Fin M => w i.val) = {y | y ≠ 0 ∧ y ≠ x ∧ y ≠ -x} ∧
      Injective (fun k : Fin M => ∑ i ∈ range k.val, w i) ∧
      (∑ i ∈ range M, w i) = 0 ∧
      (∀ a b : ℕ, a < b → b ≤ M → (a ≠ 0 ∨ b ≠ M) →
        (∑ i ∈ Ico a b, w i) ≠ 0) := by
  classical
  let r := Module.finrank (ZMod 3) V - 1
  have hr : r ≠ 0 := by dsimp [r]; omega
  let K := GaloisField 3 r
  letI : Fintype K := Fintype.ofFinite K
  have hdim : Module.finrank (ZMod 3) (K × ZMod 3) = Module.finrank (ZMod 3) V := by
    rw [Module.finrank_prod, Module.finrank_self, GaloisField.finrank 3 hr]
    dsimp [r]
    omega
  obtain ⟨φ, hφ⟩ := prescribed_equiv hdim x hx
  have hcard : Fintype.card K = 3 ^ r := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 3 r hr
  have hM : 3 * (Fintype.card K - 1) = 3 ^ Module.finrank (ZMod 3) V - 3 := by
    rw [hcard]
    have hd' : Module.finrank (ZMod 3) V = r + 1 := by dsimp [r]; omega
    rw [hd', pow_succ]
    have hp : 1 ≤ 3 ^ r := Nat.one_le_pow r 3 (by decide)
    omega
  have hout := exists_transported_ordering φ.toAddEquiv x hφ
  dsimp only at hout ⊢
  rw [hM] at hout
  exact hout

#print axioms exists_opposite_ordering

end D5.S1.Words.Sequenceability.CharacteristicThreeOpposite
