import D5.S3.VertexAlgebra.Lattice.ActualLeechHyperbolic
import D5.S3.VertexAlgebra.LatticeActualStateFieldCalculus
import D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldTranslation
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTwistedModeMorphisms
import Mathlib.Data.Rat.Floor
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! Vacuum-first intertwiners for integer-moded modules, with rational Hahn
coefficients allowed in the intertwiner itself. The lower truncation, Jacobi,
and source derivative laws follow the intertwining-operator formulation of
Frenkel, Huang and Lepowsky, *On axiomatic approaches to vertex operator
algebras and modules*, Memoirs of the AMS 104 (1993), §5.4.
The Leech specialization uses the fixed parity action of
`OriginalOrbifoldSectorModules` and the mode Hom computation of
`OriginalOrbifoldTwistedModeMorphisms`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.VacuumFirstIntertwinerDraft

open LatticeActualVertexAlgebra (StateFieldVertexAlgebra)
open LatticeActualStateFieldCalculus (minus_one_binomial)
open StateFieldResidueReconstruction (epsilon integerBinomial)

noncomputable section

variable {V S T : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup S] [Module ℂ S] [AddCommGroup T] [Module ℂ T]

abbrev Action (V S : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup S] [Module ℂ S] :=
  V →ₗ[ℂ] VertexOperator ℂ S

abbrev Fields (V S T : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup S] [Module ℂ S] [AddCommGroup T] [Module ℂ T] :=
  V →ₗ[ℂ] HVertexOperator ℚ ℂ S T

def mode (J : Fields V S T) (a : V) (q : ℚ) : S →ₗ[ℂ] T :=
  (J a).coeff (-q - 1)

/-- Lower truncation on the second input, expressed in mode indices. -/
theorem lower_truncation (J : Fields V S T) (a : V) (u : S) :
    ∃ bound : ℚ, ∀ q : ℚ, bound < q → mode J a q u = 0 := by
  let P := (HahnModule.of ℂ).symm (J a u)
  refine ⟨-P.order - 1, ?_⟩
  intro q hq
  change P.coeff (-q - 1) = 0
  exact HahnSeries.coeff_eq_zero_of_lt_order (by linarith)

private def integralCoeff (F : VertexOperator ℂ S) (e : ℚ) : Module.End ℂ S :=
  if (⌊e⌋ : ℚ) = e then F.coeff ⌊e⌋ else 0

/-- Rational indexing of an integer-moded field, by zero extension. -/
def rationalMode (F : VertexOperator ℂ S) (q : ℚ) : Module.End ℂ S :=
  integralCoeff F (-q - 1)

@[simp] theorem rationalMode_int (F : VertexOperator ℂ S) (n : ℤ) :
    rationalMode F (n : ℚ) = F[[n]] := by
  rw [rationalMode, show -(n : ℚ) - 1 = ((-n - 1 : ℤ) : ℚ) by push_cast; ring]
  rw [integralCoeff, Int.floor_intCast, ite_eq_left rfl, VertexOperator.coeff_eq_ncoeff]
  rw [show -(-n - 1) - 1 = n by omega]

private theorem rationalMode_nonintegral (F : VertexOperator ℂ S) (q : ℚ)
    (hq : ¬ ∃ n : ℤ, (n : ℚ) = q) : rationalMode F q = 0 := by
  unfold rationalMode integralCoeff
  apply ite_eq_right
  intro h
  apply hq
  refine ⟨-⌊-q - 1⌋ - 1, ?_⟩
  push_cast
  linarith

private theorem nonintegral_shift {q t : ℚ} (hq : ¬ ∃ n : ℤ, (n : ℚ) = q)
    (n : ℤ) (ht : t = q + (n : ℚ)) : ¬ ∃ m : ℤ, (m : ℚ) = t := by
  rintro ⟨m, hm⟩
  apply hq
  refine ⟨m - n, ?_⟩
  push_cast
  linarith

variable (A : StateFieldVertexAlgebra V) (ρ : Action V S) (σ : Action V T)

def leftTerm (J : Fields V S T) (a b : V) (u : S)
    (p r : ℤ) (q : ℚ) (i : ℕ) : T :=
  integerBinomial p i • mode J (((A.stateField a)[[r + i]]) b) ((p : ℚ) + q - i) u

def firstTerm (J : Fields V S T) (a b : V) (u : S)
    (p r : ℤ) (q : ℚ) (i : ℕ) : T :=
  (((-1 : ℂ)^i) * integerBinomial r i) •
    ((σ a)[[p + r - i]]) (mode J b (q + i) u)

def secondTerm (J : Fields V S T) (a b : V) (u : S)
    (p r : ℤ) (q : ℚ) (i : ℕ) : T :=
  (((-1 : ℂ)^i) * integerBinomial r i) •
    (epsilon r • mode J b (q + (r : ℚ) - i) (((ρ a)[[p + i]]) u))

/-- Source translation and full mixed Jacobi with three finite summand
supports. The pointwise Hahn support requirement is part of the field type. -/
structure Lawful (J : Fields V S T) : Prop where
  source : ∀ (a : V) (q : ℚ) (u : S),
    mode J (A.translation a) q u = -(q : ℂ) • mode J a (q - 1) u
  jacobi : ∀ (a b : V) (u : S) (p r : ℤ) (q : ℚ),
    Function.HasFiniteSupport (leftTerm A J a b u p r q) ∧
    Function.HasFiniteSupport (firstTerm σ J a b u p r q) ∧
    Function.HasFiniteSupport (secondTerm ρ J a b u p r q) ∧
      (∑ᶠ i, leftTerm A J a b u p r q i) =
        (∑ᶠ i, firstTerm σ J a b u p r q i) -
          (∑ᶠ i, secondTerm ρ J a b u p r q i)

/-- A map commuting with the action of every source state at every integer mode. -/
def modeHomSpace : Submodule ℂ (S →ₗ[ℂ] T) where
  carrier := {f | ∀ a n u, f (((ρ a)[[n]]) u) = ((σ a)[[n]]) (f u)}
  zero_mem' := by
    change ∀ a n u, (0 : S →ₗ[ℂ] T) (((ρ a)[[n]]) u) = ((σ a)[[n]]) ((0 : S →ₗ[ℂ] T) u)
    simp
  add_mem' := by
    intro f g hf hg
    change ∀ a n u, f (((ρ a)[[n]]) u) = ((σ a)[[n]]) (f u) at hf
    change ∀ a n u, g (((ρ a)[[n]]) u) = ((σ a)[[n]]) (g u) at hg
    intro a n u
    simp only [LinearMap.add_apply, map_add, hf a n u, hg a n u]
  smul_mem' := by
    intro c f hf
    change ∀ a n u, f (((ρ a)[[n]]) u) = ((σ a)[[n]]) (f u) at hf
    intro a n u
    simp only [LinearMap.smul_apply, map_smul, hf a n u]

private theorem sum_choose_zero {U : Type*} [AddCommGroup U] [Module ℂ U]
    (g : ℕ → U) : (∑ᶠ i : ℕ, integerBinomial 0 i • g i) = g 0 := by
  rw [finsum_eq_single _ 0]
  · simp [integerBinomial]
  · intro i hi
    simp [integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]

private theorem sum_signed_choose_zero {U : Type*} [AddCommGroup U] [Module ℂ U]
    (g : ℕ → U) :
    (∑ᶠ i : ℕ, (((-1 : ℂ)^i) * integerBinomial 0 i) • g i) = g 0 := by
  rw [finsum_eq_single _ 0]
  · simp [integerBinomial]
  · intro i hi
    simp [integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]

variable {A ρ σ} {J : Fields V S T}

theorem vacuum_mode_eq_zero (hJ : Lawful A ρ σ J) (q : ℚ) (hq : q ≠ -1) :
    mode J A.vacuum q = 0 := by
  apply LinearMap.ext
  intro u
  have h := hJ.source A.vacuum (q + 1) u
  have hz : (-(↑(q + 1) : ℂ)) ≠ 0 := by
    apply neg_ne_zero.mpr
    exact_mod_cast (show q + 1 ≠ 0 by intro he; apply hq; linarith)
  have hv : (-(↑(q + 1) : ℂ)) • mode J A.vacuum q u = 0 := by
    simpa [A.translation_vacuum, add_sub_cancel_right, mode] using h.symm
  exact (smul_eq_zero.mp hv).resolve_left hz

/-- The finite mixed commutator at separation index zero. -/
theorem ward (hJ : Lawful A ρ σ J) (a b : V) (u : S) (p : ℤ) (q : ℚ) :
    ((σ a)[[p]]) (mode J b q u) - mode J b q (((ρ a)[[p]]) u) =
      ∑ᶠ i, leftTerm A J a b u p 0 q i := by
  have h := (hJ.jacobi a b u p 0 q).2.2.2
  simpa only [firstTerm, secondTerm, sum_signed_choose_zero, epsilon, zpow_zero,
    one_smul, Nat.cast_zero, Int.cast_zero, add_zero, sub_zero] using h.symm

/-- If the source translation is the zero mode of the conformal state,
the translation commutator follows from mixed Jacobi and source differentiation. -/
theorem translation_commutator (hJ : Lawful A ρ σ J) (ω : V)
    (hω : (A.stateField ω)[[0]] = A.translation) (a : V) (q : ℚ) (u : S) :
    ((σ ω)[[0]]) (mode J a q u) - mode J a q (((ρ ω)[[0]]) u) =
      -(q : ℂ) • mode J a (q - 1) u := by
  have h := ward hJ ω a u 0 q
  have hsum : (∑ᶠ i, leftTerm A J ω a u 0 0 q i) = mode J (A.translation a) q u := by
    simp only [leftTerm, sum_choose_zero, Nat.cast_zero, Int.cast_zero,
      zero_add, sub_zero, hω]
  rw [hsum] at h
  exact h.trans (hJ.source a q u)

/-- The vacuum coefficient of an arbitrary lawful field is a module map. -/
def extractModeHom (hJ : Lawful A ρ σ J) : modeHomSpace ρ σ := by
  refine ⟨mode J A.vacuum (-1), ?_⟩
  intro a p u
  have h := ward hJ a A.vacuum u p (-1)
  have hz (i : ℕ) : leftTerm A J a A.vacuum u p 0 (-1) i = 0 := by
    have hc : VertexOperator.ncoeff (A.stateField a) (0 + (i : ℤ)) A.vacuum = 0 :=
      A.creativity a _ (by omega)
    rw [leftTerm, hc]
    simp [mode]
  have hsum : (∑ᶠ i, leftTerm A J a A.vacuum u p 0 (-1) i) = 0 := by
    simp only [hz, finsum_zero]
  rw [hsum] at h
  exact (sub_eq_zero.mp h).symm

/-- Reconstruction at every rational mode, with the integral module action
extended by zero. The coefficient argument forces the extension on J. -/
theorem mode_reconstruct (hJ : Lawful A ρ σ J) (a : V) (q : ℚ) (u : S) :
    mode J a q u = (extractModeHom hJ).val (rationalMode (ρ a) q u) := by
  let f := extractModeHom hJ
  have h := (hJ.jacobi a A.vacuum u 0 (-1) q).2.2.2
  have hleft : (∑ᶠ i, leftTerm A J a A.vacuum u 0 (-1) q i) = mode J a q u := by
    simp only [leftTerm, sum_choose_zero, Nat.cast_zero, Int.cast_zero, zero_add,
      add_zero, sub_zero, A.creation]
  rw [hleft] at h
  let l (i : ℕ) : T := VertexOperator.ncoeff (σ a) (-1 - (i : ℤ))
    (mode J A.vacuum (q + i) u)
  let r (i : ℕ) : T := mode J A.vacuum (q - 1 - i) (VertexOperator.ncoeff (ρ a) i u)
  have hsum : mode J a q u = (∑ᶠ i, l i) + (∑ᶠ i, r i) := by
    simpa only [firstTerm, secondTerm, minus_one_binomial, zero_add, zero_sub, one_smul,
      show ((-1 : ℤ) : ℚ) = -1 by norm_num, ← sub_eq_add_neg,
      show epsilon (-1) = -1 by norm_num [epsilon], neg_one_smul,
      finsum_neg_distrib, sub_neg_eq_add, l, r] using h
  by_cases hq : ∃ n : ℤ, (n : ℚ) = q
  · obtain ⟨n, rfl⟩ := hq
    rw [rationalMode_int]
    by_cases hn : n < 0
    · let k : ℕ := (-n - 1).toNat
      have hk : (k : ℤ) = -n - 1 := by dsimp [k]; omega
      have hkQ : (k : ℚ) = -(n : ℚ) - 1 := by exact_mod_cast hk
      have hl : (∑ᶠ i, l i) = ((σ a)[[n]]) (f.val u) := by
        rw [finsum_eq_single _ k]
        · have hindex : (n : ℚ) + (k : ℚ) = -1 := by linarith
          simp only [l, hindex, show (-1 : ℤ) - k = n by omega, f, extractModeHom]
        · intro i hi
          have hindex : (n : ℚ) + i ≠ -1 := by
            intro hz
            apply hi
            have hcast : (i : ℚ) = (k : ℚ) := by linarith
            exact_mod_cast hcast
          simp only [l, vacuum_mode_eq_zero hJ _ hindex, LinearMap.zero_apply, map_zero]
      have hr (i : ℕ) : r i = 0 := by
        have hindex : (n : ℚ) - 1 - i ≠ -1 := by
          have hnQ : (n : ℚ) < 0 := by exact_mod_cast hn
          have hiQ : (0 : ℚ) ≤ i := Nat.cast_nonneg i
          intro hz
          linarith
        simp only [r, vacuum_mode_eq_zero hJ _ hindex, LinearMap.zero_apply]
      rw [hsum, hl, show (∑ᶠ i, r i) = 0 by simp only [hr, finsum_zero], add_zero]
      exact (f.property a n u).symm
    · let k : ℕ := n.toNat
      have hk : (k : ℤ) = n := by dsimp [k]; omega
      have hkQ : (k : ℚ) = (n : ℚ) := by exact_mod_cast hk
      have hl (i : ℕ) : l i = 0 := by
        have hindex : (n : ℚ) + i ≠ -1 := by
          have hnQ : (0 : ℚ) ≤ n := by exact_mod_cast (le_of_not_gt hn)
          have hiQ : (0 : ℚ) ≤ i := Nat.cast_nonneg i
          intro hz
          linarith
        simp only [l, vacuum_mode_eq_zero hJ _ hindex, LinearMap.zero_apply, map_zero]
      have hr : (∑ᶠ i, r i) = f.val (((ρ a)[[n]]) u) := by
        rw [finsum_eq_single _ k]
        · have hindex : (n : ℚ) - 1 - (k : ℚ) = -1 := by linarith
          simp only [r, hindex, hk, f, extractModeHom]
        · intro i hi
          have hindex : (n : ℚ) - 1 - i ≠ -1 := by
            intro hz
            apply hi
            have hcast : (i : ℚ) = (k : ℚ) := by linarith
            exact_mod_cast hcast
          simp only [r, vacuum_mode_eq_zero hJ _ hindex, LinearMap.zero_apply]
      rw [hsum, hr, show (∑ᶠ i, l i) = 0 by simp only [hl, finsum_zero], zero_add]
  · have hl (i : ℕ) : l i = 0 := by
      have hindex : q + i ≠ -1 := by
        intro he
        exact hq ⟨-1 - (i : ℤ), by push_cast; linarith⟩
      simp only [l, vacuum_mode_eq_zero hJ _ hindex, LinearMap.zero_apply, map_zero]
    have hr (i : ℕ) : r i = 0 := by
      have hindex : q - 1 - i ≠ -1 := by
        intro he
        exact hq ⟨(i : ℤ), by push_cast; linarith⟩
      simp only [r, vacuum_mode_eq_zero hJ _ hindex, LinearMap.zero_apply]
    rw [hsum, show (∑ᶠ i, l i) = 0 by simp only [hl, finsum_zero],
      show (∑ᶠ i, r i) = 0 by simp only [hr, finsum_zero], rationalMode_nonintegral _ _ hq]
    simp

theorem mode_reconstruct_target (hJ : Lawful A ρ σ J) (a : V) (q : ℚ) (u : S) :
    mode J a q u = rationalMode (σ a) q ((extractModeHom hJ).val u) := by
  rw [mode_reconstruct hJ]
  by_cases hq : ∃ n : ℤ, (n : ℚ) = q
  · obtain ⟨n, rfl⟩ := hq
    simp only [rationalMode_int]
    exact (extractModeHom hJ).property a n u
  · rw [rationalMode_nonintegral _ _ hq, rationalMode_nonintegral _ _ hq]
    simp

private def postcomposeField (F : VertexOperator ℂ S) (f : S →ₗ[ℂ] T) :
    HVertexOperator ℚ ℂ S T :=
  HVertexOperator.of_coeff (fun e => f.comp (integralCoeff F e)) (by
    intro u
    have hp : (Function.support (fun n : ℤ => F.coeff n u)).IsPWO :=
      F.isPWO_support_coeff u
    have hi := hp.image_of_monotone (f := fun n : ℤ => (n : ℚ))
      (by
        intro a b hab
        change (a : ℚ) ≤ (b : ℚ)
        exact_mod_cast hab)
    apply hi.mono
    intro e he
    change f (integralCoeff F e u) ≠ 0 at he
    by_cases h : (⌊e⌋ : ℚ) = e
    · refine ⟨⌊e⌋, ?_, h⟩
      change F.coeff ⌊e⌋ u ≠ 0
      intro hz
      rw [integralCoeff, ite_eq_left h, hz, map_zero] at he
      exact he rfl
    · rw [integralCoeff, ite_eq_right h, LinearMap.zero_apply, map_zero] at he
      exact (he rfl).elim)

/-- Postcompose the genuine source-module field with a linear map. -/
def inducedField (ρ : Action V S) (f : S →ₗ[ℂ] T) : Fields V S T where
  toFun a := postcomposeField (ρ a) f
  map_add' a b := by
    apply HVertexOperator.coeff_inj
    funext e
    apply LinearMap.ext
    intro u
    by_cases he : (⌊e⌋ : ℚ) = e <;>
      simp [postcomposeField, integralCoeff, he, Pi.add_apply, LinearMap.add_apply]
  map_smul' c a := by
    apply HVertexOperator.coeff_inj
    funext e
    apply LinearMap.ext
    intro u
    by_cases he : (⌊e⌋ : ℚ) = e <;>
      simp [postcomposeField, integralCoeff, he, Pi.smul_apply, LinearMap.smul_apply]

@[simp] theorem inducedField_mode (f : S →ₗ[ℂ] T) (a : V) (q : ℚ) (u : S) :
    mode (inducedField ρ f) a q u = f (rationalMode (ρ a) q u) := rfl

/-- The same induced field is also the target action evaluated on the image. -/
theorem inducedField_mode_target (f : modeHomSpace ρ σ) (a : V) (q : ℚ) (u : S) :
    mode (inducedField ρ f.val) a q u = rationalMode (σ a) q (f.val u) := by
  rw [inducedField_mode]
  by_cases hq : ∃ n : ℤ, (n : ℚ) = q
  · obtain ⟨n, rfl⟩ := hq
    simp only [rationalMode_int]
    exact f.property a n u
  · rw [rationalMode_nonintegral _ _ hq, rationalMode_nonintegral _ _ hq]
    simp

/-- Module Borcherds in the form supplied by the actual parity-slice actions. -/
def ModuleBorcherds (A : StateFieldVertexAlgebra V) (ρ : Action V S) : Prop :=
  ∀ (a b : V) (u : S) (p q r : ℤ),
    let μ := fun (c : V) (n : ℤ) => (ρ c)[[n]]
    let l : ℕ → S := fun i =>
      integerBinomial p i • μ (((A.stateField a)[[r+i]]) b) (p+q-i) u
    let f : ℕ → S := fun i =>
      (((-1 : ℂ)^i) * integerBinomial r i) • μ a (p+r-i) (μ b (q+i) u)
    let g : ℕ → S := fun i =>
      (((-1 : ℂ)^i) * integerBinomial r i) • (epsilon r • μ b (q+r-i) (μ a (p+i) u))
    Function.HasFiniteSupport l ∧ Function.HasFiniteSupport f ∧
      Function.HasFiniteSupport g ∧
        (∑ᶠ i, l i) = ∑ᶠ i : ℕ,
          (((-1 : ℂ)^i) * integerBinomial r i) •
            (μ a (p+r-i) (μ b (q+i) u) - epsilon r • μ b (q+r-i) (μ a (p+i) u))

private theorem finite_map (f : S →ₗ[ℂ] T) {g : ℕ → S}
    (hg : Function.HasFiniteSupport g) :
    Function.HasFiniteSupport (fun i => f (g i)) := by
  refine hg.subset ?_
  intro i hi hz
  exact hi (show f (g i) = 0 by rw [show g i = 0 from hz, map_zero])

omit [Module ℂ T] in
private theorem finite_zero : Function.HasFiniteSupport (0 : ℕ → T) := by
  simp [Function.HasFiniteSupport, Function.support]

/-- Postcomposition with a mode map carries the module law and derivative
to the full mixed law, including rational modes and summand supports. -/
theorem inducedField_lawful (f : modeHomSpace ρ σ)
    (hB : ModuleBorcherds A ρ)
    (hD : ∀ (a : V) (n : ℤ) (u : S),
      ((ρ (A.translation a))[[n]]) u = -(n : ℂ) • ((ρ a)[[n - 1]]) u) :
    Lawful A ρ σ (inducedField ρ f.val) where
  source a q u := by
    by_cases hq : ∃ n : ℤ, (n : ℚ) = q
    · obtain ⟨n, rfl⟩ := hq
      rw [show (n : ℚ) - 1 = ((n - 1 : ℤ) : ℚ) by push_cast; ring]
      simp only [inducedField_mode, rationalMode_int, Rat.cast_intCast, hD, map_smul]
    · have hq' := nonintegral_shift hq (-1)
        (show q - 1 = q + ((-1 : ℤ) : ℚ) by norm_num; ring)
      simp [inducedField_mode, rationalMode_nonintegral _ _ hq, rationalMode_nonintegral _ _ hq']
  jacobi a b u p r q := by
    by_cases hq : ∃ n : ℤ, (n : ℚ) = q
    · obtain ⟨n, rfl⟩ := hq
      let μ := fun (c : V) (j : ℤ) => (ρ c)[[j]]
      let l : ℕ → S := fun i =>
        integerBinomial p i • μ (((A.stateField a)[[r+i]]) b) (p+n-i) u
      let g : ℕ → S := fun i =>
        (((-1 : ℂ)^i) * integerBinomial r i) • μ a (p+r-i) (μ b (n+i) u)
      let k : ℕ → S := fun i =>
        (((-1 : ℂ)^i) * integerBinomial r i) • (epsilon r • μ b (n+r-i) (μ a (p+i) u))
      obtain ⟨hl, hg, hk, he⟩ := hB a b u p n r
      change Function.HasFiniteSupport l at hl
      change Function.HasFiniteSupport g at hg
      change Function.HasFiniteSupport k at hk
      change (∑ᶠ i, l i) = ∑ᶠ i : ℕ, (((-1 : ℂ)^i) * integerBinomial r i) •
        (μ a (p+r-i) (μ b (n+i) u) - epsilon r • μ b (n+r-i) (μ a (p+i) u)) at he
      simp_rw [smul_sub] at he
      change (∑ᶠ i, l i) = (∑ᶠ i, (g i - k i)) at he
      rw [show (∑ᶠ i, (g i - k i)) = (∑ᶠ i, g i) - (∑ᶠ i, k i) from
        finsum_sub_distrib hg hk] at he
      have el : leftTerm A (inducedField ρ f.val) a b u p r (n : ℚ) =
          fun i => f.val (l i) := by
        funext i
        have hindex : (p : ℚ) + (n : ℚ) - i = ((p+n-(i : ℤ) : ℤ) : ℚ) := by
          push_cast
          ring
        simp only [leftTerm, inducedField_mode, hindex, rationalMode_int, l, μ, map_smul]
      have eg : firstTerm σ (inducedField ρ f.val) a b u p r (n : ℚ) =
          fun i => f.val (g i) := by
        funext i
        have hindex : (n : ℚ) + i = ((n + (i : ℤ) : ℤ) : ℚ) := by push_cast; ring
        simp only [firstTerm, inducedField_mode, hindex, rationalMode_int, g, μ, map_smul]
        rw [f.property a (p + r - i) (((ρ b)[[n + i]]) u)]
      have ek : secondTerm ρ (inducedField ρ f.val) a b u p r (n : ℚ) =
          fun i => f.val (k i) := by
        funext i
        have hindex : (n : ℚ) + (r : ℚ) - i = ((n+r-(i : ℤ) : ℤ) : ℚ) := by
          push_cast
          ring
        simp only [secondTerm, inducedField_mode, hindex, rationalMode_int, k, μ, map_smul]
      rw [el, eg, ek]
      refine ⟨finite_map f.val hl, finite_map f.val hg, finite_map f.val hk, ?_⟩
      rw [← map_finsum f.val hl, ← map_finsum f.val hg, ← map_finsum f.val hk, he, map_sub]
    · have el : leftTerm A (inducedField ρ f.val) a b u p r q = 0 := by
        funext i
        have hi := nonintegral_shift hq (p - (i : ℤ))
          (show (p : ℚ) + q - i = q + ((p - (i : ℤ) : ℤ) : ℚ) by push_cast; ring)
        simp [leftTerm, inducedField_mode, rationalMode_nonintegral _ _ hi]
      have eg : firstTerm σ (inducedField ρ f.val) a b u p r q = 0 := by
        funext i
        have hi := nonintegral_shift hq (i : ℤ)
          (show q + i = q + ((i : ℤ) : ℚ) by push_cast; ring)
        simp [firstTerm, inducedField_mode, rationalMode_nonintegral _ _ hi]
      have ek : secondTerm ρ (inducedField ρ f.val) a b u p r q = 0 := by
        funext i
        have hi := nonintegral_shift hq (r - (i : ℤ))
          (show q + (r : ℚ) - i = q + ((r - (i : ℤ) : ℤ) : ℚ) by push_cast; ring)
        simp [secondTerm, inducedField_mode, rationalMode_nonintegral _ _ hi]
      rw [el, eg, ek]
      exact ⟨finite_zero, finite_zero, finite_zero, by simp⟩

private theorem lawful_add {J K : Fields V S T}
    (hJ : Lawful A ρ σ J) (hK : Lawful A ρ σ K) : Lawful A ρ σ (J + K) where
  source a q u := by
    simpa [mode, smul_add] using congrArg₂ (· + ·) (hJ.source a q u) (hK.source a q u)
  jacobi a b u p r q := by
    obtain ⟨hJl, hJf, hJg, hJe⟩ := hJ.jacobi a b u p r q
    obtain ⟨hKl, hKf, hKg, hKe⟩ := hK.jacobi a b u p r q
    have hl : leftTerm A (J + K) a b u p r q =
        leftTerm A J a b u p r q + leftTerm A K a b u p r q := by
      funext i
      simp [leftTerm, mode, smul_add]
    have hf : firstTerm σ (J + K) a b u p r q =
        firstTerm σ J a b u p r q + firstTerm σ K a b u p r q := by
      funext i
      simp [firstTerm, mode, smul_add]
    have hg : secondTerm ρ (J + K) a b u p r q =
        secondTerm ρ J a b u p r q + secondTerm ρ K a b u p r q := by
      funext i
      simp [secondTerm, mode, smul_add]
    rw [hl, hf, hg]
    refine ⟨hJl.add hKl, hJf.add hKf, hJg.add hKg, ?_⟩
    simp only [Pi.add_apply]
    rw [finsum_add_distrib hJl hKl, finsum_add_distrib hJf hKf,
      finsum_add_distrib hJg hKg, hJe, hKe]
    abel

private theorem lawful_smul (c : ℂ) {J : Fields V S T}
    (hJ : Lawful A ρ σ J) : Lawful A ρ σ (c • J) where
  source a q u := by
    simpa [mode, smul_comm c] using congrArg (c • ·) (hJ.source a q u)
  jacobi a b u p r q := by
    obtain ⟨hJl, hJf, hJg, hJe⟩ := hJ.jacobi a b u p r q
    have hl : leftTerm A (c • J) a b u p r q =
        c • leftTerm A J a b u p r q := by
      funext i
      simp [leftTerm, mode, smul_comm c]
    have hf : firstTerm σ (c • J) a b u p r q =
        c • firstTerm σ J a b u p r q := by
      funext i
      simp [firstTerm, mode, smul_comm c]
    have hg : secondTerm ρ (c • J) a b u p r q =
        c • secondTerm ρ J a b u p r q := by
      funext i
      simp [secondTerm, mode, smul_comm c]
    rw [hl, hf, hg]
    refine ⟨hJl.smul_right (fun _ => c), hJf.smul_right (fun _ => c),
      hJg.smul_right (fun _ => c), ?_⟩
    simp only [Pi.smul_apply]
    rw [← smul_finsum' c hJl, ← smul_finsum' c hJf, ← smul_finsum' c hJg, hJe, smul_sub]

/-- The complex subspace of actual rational fields satisfying the mixed laws. -/
def operatorSpace (A : StateFieldVertexAlgebra V) (ρ : Action V S) (σ : Action V T) :
    Submodule ℂ (Fields V S T) where
  carrier := {J | Lawful A ρ σ J}
  zero_mem' := by
    change Lawful A ρ σ (0 : Fields V S T)
    constructor
    · intros
      simp [mode]
    · intros
      simp [leftTerm, firstTerm, secondTerm, mode, Function.HasFiniteSupport, Function.support]
  add_mem' := fun hJ hK => lawful_add hJ hK
  smul_mem' := fun c _ hJ => lawful_smul c hJ

/-- Evaluation of the vacuum mode and postcomposition are inverse linear maps. -/
def vacuumFirstEquiv (hB : ModuleBorcherds A ρ)
    (hD : ∀ (a : V) (n : ℤ) (u : S),
      ((ρ (A.translation a))[[n]]) u = -(n : ℂ) • ((ρ a)[[n - 1]]) u)
    (hV : ∀ u : S, ((ρ A.vacuum)[[-1]]) u = u) :
    operatorSpace A ρ σ ≃ₗ[ℂ] modeHomSpace ρ σ where
  toFun J := extractModeHom J.property
  invFun f := ⟨inducedField ρ f.val, inducedField_lawful f hB hD⟩
  left_inv J := by
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    apply HVertexOperator.coeff_inj
    funext e
    apply LinearMap.ext
    intro u
    have h := mode_reconstruct J.property a (-e-1) u
    have he : -(-e-1)-1 = e := by ring
    rw [← inducedField_mode (ρ := ρ)] at h
    simpa only [mode, he] using h.symm
  right_inv f := by
    apply Subtype.ext
    apply LinearMap.ext
    intro u
    change mode (inducedField ρ f.val) A.vacuum (-1) u = f.val u
    simp only [inducedField_mode, show (-1 : ℚ) = ((-1 : ℤ) : ℚ) by norm_num,
      rationalMode_int, hV]
  map_add' J K := by
    apply Subtype.ext
    apply LinearMap.ext
    intro u
    change mode (J.val + K.val) A.vacuum (-1) u =
      mode J.val A.vacuum (-1) u + mode K.val A.vacuum (-1) u
    simp [mode]
  map_smul' c J := by
    apply Subtype.ext
    apply LinearMap.ext
    intro u
    change mode (c • J.val) A.vacuum (-1) u = c • mode J.val A.vacuum (-1) u
    simp [mode]

end

section ActualTwisted

noncomputable section

open LatticeGeneratingFieldLocality (LatticeData)
open LatticeInvolution (FixedCarrier fixed_actualVertexAlgebra fixedTranslation)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open LatticeHalfFockCorrectedField (correctedField)
open LatticeHalfFockOriginalTranslation (correctedField_translation_physical)
open TwistedGround.OriginalOrbifoldSectorModules
  (fixedParityY fixedParitySlice_borcherds fixedParitySlice_vacuum_ncoeff)
open TwistedGround.OriginalOrbifoldTwistedModeMorphisms
  (fixedModeHom fixedModeHom_eq_bot_of_ne positiveTwistedModeEndEquiv
    positiveTwistedModeEndEquiv_apply)
open ActualLeechHyperbolic (leechData leech_spec)

open private fixedParitySlice_mode_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldSectorModules
open private stress stress_fixed_mode from
  D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldTranslation

private theorem twisted_source_derivative (D : LatticeData) (hu : IsUnit D.G.det)
    (s : ℂ) (a : FixedCarrier D) (n : ℤ) (u : paritySpace D hu s) :
    ((fixedParityY D hu s (fixedTranslation D a))[[n]]) u =
      -(n : ℂ) • ((fixedParityY D hu s a)[[n - 1]]) u := by
  apply Subtype.ext
  change (((HalfFock.LatticeHalfFockParityField.fixedParitySlice D hu s
      (fixedTranslation D a))[[n]]) u).val =
    ((-(n : ℂ)) • ((HalfFock.LatticeHalfFockParityField.fixedParitySlice D hu s
      a)[[n-1]]) u).val
  rw [Submodule.coe_smul, fixedParitySlice_mode_val, fixedParitySlice_mode_val]
  change (correctedField D hu (LatticeSugawaraConformal.translation D a.val)).coeff
      (-2*n-2) u.val = -(n : ℂ) • (correctedField D hu a.val).coeff (-2*(n-1)-2) u.val
  rw [correctedField_translation_physical]
  have exponent : (-2*n-2 : ℤ) + 2 = -2*(n-1)-2 := by omega
  have scalar : ((-2*(n-1)-2 : ℤ) : ℂ) / 2 = -(n : ℂ) := by
    push_cast
    ring
  rw [exponent, scalar]

private theorem fixedStateMode (D : LatticeData) (a : FixedCarrier D) (n : ℤ) :
    VertexOperator.ncoeff ((fixed_actualVertexAlgebra D).stateField a) n =
      LatticeInvolution.fixedMode D a n :=
  LatticeInvolution.fixedField_ncoeff D a n

private theorem twistedModuleBorcherds (D : LatticeData) (hu : IsUnit D.G.det) (s : ℂ) :
    ModuleBorcherds (fixed_actualVertexAlgebra D) (fixedParityY D hu s) := by
  intro a b u p q r
  dsimp only
  simp only [fixedStateMode]
  exact fixedParitySlice_borcherds D hu s a b u p q r

private theorem twistedVacuumMode (D : LatticeData) (hu : IsUnit D.G.det) (s : ℂ)
    (u : paritySpace D hu s) :
    VertexOperator.ncoeff (fixedParityY D hu s (fixed_actualVertexAlgebra D).vacuum)
      (-1) u = u := by
  exact (fixedParitySlice_vacuum_ncoeff D hu s (-1) u).trans (ite_eq_left rfl)

/-- The actual vacuum-first operator space for either choice of twisted signs. -/
abbrev twistedUnitSpace (D : LatticeData) (hu : IsUnit D.G.det) (s t : ℂ) :=
  operatorSpace (fixed_actualVertexAlgebra D) (fixedParityY D hu s) (fixedParityY D hu t)

/-- The maps between actual twisted slices that commute with all fixed modes. -/
abbrev twistedUnitHom (D : LatticeData) (hu : IsUnit D.G.det) (s t : ℂ) :=
  modeHomSpace (fixedParityY D hu s) (fixedParityY D hu t)

/-- The actual conformal zero modes give the mixed translation commutator. -/
theorem twistedUnit_translation_commutator (D : LatticeData) (hu : IsUnit D.G.det)
    (s t : ℂ) (J : twistedUnitSpace D hu s t) (a : FixedCarrier D) (q : ℚ)
    (u : paritySpace D hu s) :
    ((fixedParityY D hu t (stress D))[[0]]) (mode J.val a q u) -
      mode J.val a q (((fixedParityY D hu s (stress D))[[0]]) u) =
      -(q : ℂ) • mode J.val a (q - 1) u := by
  have hω : ((fixed_actualVertexAlgebra D).stateField (stress D))[[0]] =
      (fixed_actualVertexAlgebra D).translation := by
    change (LatticeInvolution.fixedField D (stress D))[[0]] = fixedTranslation D
    rw [LatticeInvolution.fixedField_ncoeff, stress_fixed_mode D hu]
  exact translation_commutator J.property (stress D) hω a q u

/-- The rational-mode vacuum-first equivalence for the actual lattice modules. -/
def twistedVacuumFirstEquiv (D : LatticeData) (hu : IsUnit D.G.det) (s t : ℂ) :
    twistedUnitSpace D hu s t ≃ₗ[ℂ] twistedUnitHom D hu s t :=
  vacuumFirstEquiv (A := fixed_actualVertexAlgebra D)
    (ρ := fixedParityY D hu s) (σ := fixedParityY D hu t)
    (twistedModuleBorcherds D hu s) (twisted_source_derivative D hu s)
    (twistedVacuumMode D hu s)

local notation "leechUnit" => And.left (And.right leech_spec)

/-- The generic Hom carrier specializes to the verified actual mode Hom carrier. -/
theorem leech_twisted_unit_hom_eq (s t : ℂ) :
    twistedUnitHom leechData leechUnit s t = fixedModeHom s t := rfl

/-- Vacuum evaluation as a linear equivalence to the actual Leech mode Hom. -/
def leechTwistedVacuumFirstEquiv (s t : ℂ) :
    twistedUnitSpace leechData leechUnit s t ≃ₗ[ℂ] fixedModeHom s t :=
  twistedVacuumFirstEquiv leechData leechUnit s t

/-- Exact dimension transfer for the actual Leech twisted unit channels. -/
theorem leech_twisted_unit_finrank (s t : ℂ) :
    Module.finrank ℂ (twistedUnitSpace leechData leechUnit s t) =
      Module.finrank ℂ (twistedUnitHom leechData leechUnit s t) :=
  (twistedVacuumFirstEquiv leechData leechUnit s t).finrank_eq

/-- A vanishing criterion that also detects triviality without assuming
finite dimensionality of the mode-Hom space. -/
theorem leech_twisted_unit_eq_zero_iff (s t : ℂ) :
    (∀ J : twistedUnitSpace leechData leechUnit s t, J = 0) ↔
      (∀ f : twistedUnitHom leechData leechUnit s t, f = 0) := by
  let e := twistedVacuumFirstEquiv leechData leechUnit s t
  constructor
  · intro h f
    calc
      f = e (e.symm f) := (e.apply_symm_apply f).symm
      _ = e 0 := congrArg (fun J => e J) (h (e.symm f))
      _ = 0 := e.map_zero
  · intro h J
    exact e.injective ((h (e J)).trans e.map_zero.symm)

/-- The identity of the actual positive twisted slice has a nonzero preimage. -/
theorem leech_twisted_positive_unit_exists :
    ∃ J : twistedUnitSpace leechData leechUnit 1 1, J ≠ 0 ∧
      (leechTwistedVacuumFirstEquiv 1 1 J).val = LinearMap.id := by
  let e := leechTwistedVacuumFirstEquiv 1 1
  refine ⟨e.symm (positiveTwistedModeEndEquiv 1), ?_, ?_⟩
  · exact e.symm.map_ne_zero_iff.mpr
      (positiveTwistedModeEndEquiv.map_ne_zero_iff.mpr one_ne_zero)
  · change (e (e.symm (positiveTwistedModeEndEquiv 1))).val = _
    rw [e.apply_symm_apply, positiveTwistedModeEndEquiv_apply, one_smul]

/-- The actual channel `V⁺ × T⁺ → T⁺` has multiplicity one. -/
theorem leech_twisted_positive_unit_finrank :
    Module.finrank ℂ (twistedUnitSpace leechData leechUnit 1 1) = 1 := by
  rw [(leechTwistedVacuumFirstEquiv 1 1).finrank_eq,
    ← positiveTwistedModeEndEquiv.finrank_eq, Module.finrank_self]

private theorem leech_twisted_unit_finrank_of_ne (s t : ℂ) (hst : s ≠ t) :
    Module.finrank ℂ (twistedUnitSpace leechData leechUnit s t) = 0 := by
  rw [(leechTwistedVacuumFirstEquiv s t).finrank_eq, fixedModeHom_eq_bot_of_ne s t hst,
    finrank_bot]

/-- The actual channel `V⁺ × T⁺ → T⁻` vanishes. -/
theorem leech_twisted_positive_to_negative_unit_finrank :
    Module.finrank ℂ (twistedUnitSpace leechData leechUnit 1 (-1)) = 0 :=
  leech_twisted_unit_finrank_of_ne 1 (-1) (by norm_num)

/-- The actual channel `V⁺ × T⁻ → T⁺` vanishes. -/
theorem leech_twisted_negative_to_positive_unit_finrank :
    Module.finrank ℂ (twistedUnitSpace leechData leechUnit (-1) 1) = 0 :=
  leech_twisted_unit_finrank_of_ne (-1) 1 (by norm_num)

#print axioms lower_truncation
#print axioms mode_reconstruct
#print axioms mode_reconstruct_target
#print axioms inducedField_lawful
#print axioms vacuumFirstEquiv
#print axioms twistedUnit_translation_commutator
#print axioms twistedVacuumFirstEquiv
#print axioms leech_twisted_unit_hom_eq
#print axioms leechTwistedVacuumFirstEquiv
#print axioms leech_twisted_unit_finrank
#print axioms leech_twisted_unit_eq_zero_iff
#print axioms leech_twisted_positive_unit_exists
#print axioms leech_twisted_positive_unit_finrank
#print axioms leech_twisted_positive_to_negative_unit_finrank
#print axioms leech_twisted_negative_to_positive_unit_finrank

end
end ActualTwisted

end D5.S3.VertexAlgebra.VacuumFirstIntertwinerDraft
