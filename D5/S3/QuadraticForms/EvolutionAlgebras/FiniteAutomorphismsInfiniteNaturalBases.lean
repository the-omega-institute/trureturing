/- GID: D5/S3/QuadraticForms/EvolutionAlgebras/FiniteAutomorphismsInfiniteNaturalBases
   generality: I
   mirror-B: D5/B/S3/QuadraticForms/EvolutionAlgebras/FiniteAutomorphismsInfiniteNaturalBases
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite full automorphisms coexist with an infinite natural-basis quotient. -/

import D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismControl
import Mathlib.LinearAlgebra.Basis.Fin

/-!
The algebra A_(8,1) and its full automorphism classification are prior results
of Goncalves, Goncalves, Martin Barquero, Martin Gonzalez and Siles Molina,
arXiv:1807.02362v1, Lemma 3.15 and section 5.1. The endpoint answers only the
entire final interrogative of arXiv:2610.22248v1, section 2.2.2, Question 14.
Multiplication is complex bilinear, without conjugation or associativity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.QuadraticForms.EvolutionAlgebras.FiniteAutomorphismsInfiniteNaturalBases

open D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismControl

noncomputable section

/-- All actual two-element natural bases, before taking any equivalence. -/
def NaturalBasis {A : Type*} [AddCommGroup A] [Module ℂ A]
    (μ : A →ₗ[ℂ] A →ₗ[ℂ] A) :=
  {b : Module.Basis (Fin 2) ℂ A // ∀ i j, i ≠ j → μ (b i) (b j) = 0}

/-- The exact relation allows every permutation and independent nonzero field scalars.
Units and nonzero scalars coincide over the field; no algebra automorphisms act here. -/
def basisSetoid {A : Type*} [AddCommGroup A] [Module ℂ A]
    (μ : A →ₗ[ℂ] A →ₗ[ℂ] A) : Setoid (NaturalBasis μ) where
  r b c := ∃ (σ : Equiv.Perm (Fin 2)) (u : Fin 2 → ℂˣ),
    ∀ i, b.val i = (u i : ℂ) • c.val (σ i)
  iseqv := {
    refl := by
      intro b
      exact ⟨Equiv.refl _, fun _ => 1, by simp⟩
    symm := by
      rintro b c ⟨σ, u, h⟩
      refine ⟨σ.symm, fun i => (u (σ.symm i))⁻¹, fun i => ?_⟩
      rw [h (σ.symm i)]
      simp [smul_smul]
    trans := by
      rintro b c d ⟨σ, u, h⟩ ⟨τ, v, k⟩
      refine ⟨σ.trans τ, fun i => u i * v (σ i), fun i => ?_⟩
      rw [h i, k (σ i)]
      simp [smul_smul] }

/-- The published two-dimensional rank-one-square multiplication. -/
def mu : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) :=
  LinearMap.mk₂ ℂ (fun x y => (x.1 * y.1 + x.2 * y.2, 0))
    (by intros; ext <;> simp [add_mul] <;> ring)
    (by intros; ext <;> simp [smul_eq_mul] <;> ring)
    (by intros; ext <;> simp [mul_add] <;> ring)
    (by intros; ext <;> simp [smul_eq_mul] <;> ring)

/- proof_shape: bind-only; consumer: result. -/
private theorem annihilator_zero (x : ℂ × ℂ) (h : ∀ y, mu x y = 0) : x = 0 := by
  have h₀ := congrArg Prod.fst (h (1, 0))
  have h₁ := congrArg Prod.fst (h (0, 1))
  apply Prod.ext
  · simpa [mu] using h₀
  · simpa [mu] using h₁

/- proof_shape: bind-only; consumer: finite_full_aut. This is a formal check of
an already published classification, not a new algebra or group classification. -/
private theorem aut_classify (f : Aut mu) :
    (∀ x : ℂ × ℂ, f.val x = (x.1, (f.val (0, 1)).2 * x.2)) ∧
    ((f.val (0, 1)).2 = 1 ∨ (f.val (0, 1)).2 = -1) := by
  let a := f.val (1, 0)
  let b := f.val (0, 1)
  have ha : a = mu a a := by
    simpa [a, mu] using f.property (1, 0) (1, 0)
  have ha₂ : a.2 = 0 := congrArg Prod.snd ha
  have haa : a.1 = a.1 * a.1 := by
    simpa [mu, ha₂] using congrArg Prod.fst ha
  have hane : a.1 ≠ 0 := by
    intro h
    have hz : a = 0 := Prod.ext h ha₂
    have : ((1, 0) : ℂ × ℂ) = 0 := f.val.injective (by simpa [a] using hz)
    have := congrArg Prod.fst this
    norm_num at this
  have ha₁ : a.1 = 1 := by
    apply mul_left_cancel₀ hane
    simpa using haa.symm
  have hae : a = (1, 0) := Prod.ext ha₁ ha₂
  have hab : mu a b = 0 := by
    have h := f.property (1, 0) (0, 1)
    have hz : mu (1, 0) (0, 1) = 0 := by ext <;> simp [mu]
    rw [hz, map_zero] at h
    exact h.symm
  have hb₁ : b.1 = 0 := by simpa [hae, mu] using congrArg Prod.fst hab
  have hbb : mu b b = a := by
    simpa [a, b, mu] using (f.property (0, 1) (0, 1)).symm
  have hd : b.2 * b.2 = 1 := by
    simpa [mu, hb₁, ha₁] using congrArg Prod.fst hbb
  refine ⟨?_, mul_self_eq_one_iff.mp hd⟩
  intro x
  have hx : x = x.1 • ((1, 0) : ℂ × ℂ) + x.2 • ((0, 1) : ℂ × ℂ) := by
    ext <;> simp
  calc
    f.val x = x.1 • a + x.2 • b := by
      simpa only [map_add, map_smul] using congrArg f.val hx
    _ = (x.1, (f.val (0, 1)).2 * x.2) := by
      ext <;> simp [hae, hb₁, b, smul_eq_mul, mul_comm]

/- proof_shape: bind-only; consumer: result. -/
private theorem finite_full_aut : Finite (Aut mu) := by
  classical
  let code : Aut mu → Bool := fun f => decide ((f.val (0, 1)).2 = 1)
  apply Finite.of_injective code
  intro f g h
  obtain ⟨hf, hdf⟩ := aut_classify f
  obtain ⟨hg, hdg⟩ := aut_classify g
  have hd : (f.val (0, 1)).2 = (g.val (0, 1)).2 := by
    change decide ((f.val (0, 1)).2 = 1) = decide ((g.val (0, 1)).2 = 1) at h
    have hi := decide_eq_decide.mp h
    rcases hdf with hf₁ | hfNeg
    · exact hf₁.trans (hi.mp hf₁).symm
    · rcases hdg with hg₁ | hgNeg
      · have hc : (1 : ℂ) = -1 := (hi.mpr hg₁).symm.trans hfNeg
        norm_num at hc
      · exact hfNeg.trans hgNeg.symm
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rw [hf, hg, hd]

/- proof_shape: bind-only; consumer: rotation. -/
private theorem denominator_ne (n : ℕ) : (1 + ((n + 1 : ℕ) : ℂ) ^ 2) ≠ 0 := by
  exact_mod_cast (show 1 + (n + 1) ^ 2 ≠ 0 by positivity)

private def rotation (n : ℕ) : (ℂ × ℂ) ≃ₗ[ℂ] (ℂ × ℂ) := by
  let t : ℂ := (n + 1 : ℕ)
  have hd : 1 + t ^ 2 ≠ 0 := denominator_ne n
  exact {
    toFun := fun x => (x.1 - t * x.2, t * x.1 + x.2)
    invFun := fun x => ((x.1 + t * x.2) / (1 + t ^ 2),
      (-t * x.1 + x.2) / (1 + t ^ 2))
    map_add' := by intros; ext <;> simp <;> ring
    map_smul' := by intros; ext <;> simp [smul_eq_mul] <;> ring
    left_inv := by
      intro x
      ext <;> dsimp only <;> field_simp [hd] <;> ring
    right_inv := by
      intro x
      ext <;> dsimp only <;> field_simp [hd] <;> ring }

private def familyBasis (n : ℕ) : Module.Basis (Fin 2) ℂ (ℂ × ℂ) :=
  (Module.Basis.finTwoProd ℂ).map (rotation n)

/- proof_shape: bind-only; consumers: family, family_separation. -/
private theorem family_zero (n : ℕ) : familyBasis n 0 = (1, ((n + 1 : ℕ) : ℂ)) := by
  simp [familyBasis, rotation]

/- proof_shape: bind-only; consumers: family, family_separation. -/
private theorem family_one (n : ℕ) : familyBasis n 1 = (-((n + 1 : ℕ) : ℂ), 1) := by
  simp [familyBasis, rotation]

private def family (n : ℕ) : NaturalBasis mu := ⟨familyBasis n, by
  intro i j hij
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals simp [family_zero, family_one, mu]⟩

/- proof_shape: bind-only; consumer: infinite_classes.
This separates arbitrary complex rescalings, including the swapped case. -/
private theorem family_separation {n m : ℕ}
    (h : (basisSetoid mu).r (family n) (family m)) : n = m := by
  obtain ⟨σ, u, h⟩ := h
  have hh := h 0
  change familyBasis n 0 = (u 0 : ℂ) • familyBasis m (σ 0) at hh
  have hs : σ 0 = 0 ∨ σ 0 = 1 := by omega
  rcases hs with hs | hs
  · rw [hs, family_zero, family_zero] at hh
    have h₀ := congrArg Prod.fst hh
    have h₁ := congrArg Prod.snd hh
    have hu : (u 0 : ℂ) = 1 := by simpa using h₀.symm
    have hn : n + 1 = m + 1 := by
      exact_mod_cast (show ((n + 1 : ℕ) : ℂ) = (m + 1 : ℕ) by simpa [hu] using h₁)
    omega
  · rw [hs, family_zero, family_one] at hh
    have h₀ := congrArg Prod.fst hh
    have h₁ := congrArg Prod.snd hh
    have hu : (u 0 : ℂ) = ((n + 1 : ℕ) : ℂ) := by simpa using h₁.symm
    have hz : (((n + 1) * (m + 1) + 1 : ℕ) : ℂ) = 0 := by
      simp only [Prod.smul_fst, smul_eq_mul, hu] at h₀
      push_cast at h₀ ⊢
      linear_combination h₀
    have : (n + 1) * (m + 1) + 1 = 0 := by exact_mod_cast hz
    omega

/- proof_shape: bind-only; consumer: result. -/
private theorem infinite_classes : Infinite (Quotient (basisSetoid mu)) := by
  apply Infinite.of_injective (fun n : ℕ => Quotient.mk (basisSetoid mu) (family n))
  intro n m h
  exact family_separation (Quotient.exact h)

/-- The complete positive existence answer to Question 14's final interrogative.
The fixed field is permitted, and the quotient is over all natural bases. -/
/- proof_shape: bind-only; admission_basis: open-problem-resolution.
computational_content: none. The proof classifies every linear automorphism and
separates an unbounded family in the exact quotient; no finite computation or
finite certified sample is the result. -/
theorem result :
    ∃ μ : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ),
      Module.finrank ℂ (ℂ × ℂ) = 2 ∧
      (∀ x y, μ x y = μ y x) ∧
      (∀ x, (∀ y, μ x y = 0) → x = 0) ∧
      Nonempty (NaturalBasis μ) ∧
      Finite (Aut μ) ∧ Infinite (Quotient (basisSetoid μ)) := by
  refine ⟨mu, ?_, ?_, annihilator_zero, ⟨family 0⟩, finite_full_aut, infinite_classes⟩
  · simp
  · intro x y
    ext <;> simp [mu, mul_comm]

end
end D5.S3.QuadraticForms.EvolutionAlgebras.FiniteAutomorphismsInfiniteNaturalBases
