/- GID: D5/S3/VertexAlgebra/Lattice/NormFourVacuumVertexAlgebra
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/NormFourVacuumVertexAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual simple naturally graded norm-four vacuum state-field vertex algebra. -/

import D5.S3.VertexAlgebra.Lattice.NormFourVacuumIrreducible
import D5.S3.VertexAlgebra.LatticeActualVertexAlgebra
import D5.S3.VertexAlgebra.LatticeEnergyGrading
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! The actual cyclic vacuum space inherits all integer state-field coefficients,
full Borcherds and a finite natural grading. The norm-four state retains its
Dong-Mason-Zhu / Shimakura attribution; lattice fields and residue reconstruction
retain their Bakalov-Kac, Carnahan and Matsuo-Nagatomo attribution. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.NormFourVacuumVertexAlgebra

open LatticeGeneratingFieldLocality LatticeAllStateField
open LatticeAllStateReconstruction LatticeSugawaraConformal
open LatticeActualStateFieldCalculus LatticeActualStateDerivative
open NormFourVirasoroVector NormFourVacuumIrreducible
open LatticeActualVertexAlgebra (StateFieldVertexAlgebra)
open scoped BigOperators VertexOperator

-- Reuse the accepted cyclic-word, grade and finite-projector APIs.
open private word wordGrade word_mem all_modes_closed
  commute_action gradeSpace grade_eigen grade_zero assemble decompose
  cutValue_ne_zero projection_identity eigen_in_grade
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumIrreducible

noncomputable section

-- A finite-support sum in a submodule stays in the submodule.
private theorem finite_sum_mem {ι V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : Submodule ℂ V) (f : ι → V) (hf : Function.HasFiniteSupport f)
    (hm : ∀ i, f i ∈ W) : (∑ᶠ i, f i) ∈ W := by
  classical
  rw [finsum_eq_sum f hf]
  exact W.sum_mem fun i _ => hm i

-- Every normalized coefficient of the generator is an axis mode.
private theorem generator_closed (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (k : ℤ) (v : Carrier D)
    (hv : v ∈ vacuumDescendants D a s) :
    ((Y D (vector D a s))[[k]]) v ∈ vacuumDescendants D a s := by
  have h := all_modes_closed D a ha s hs (k - 1) v hv
  simpa only [mode, show k - 1 + 1 = k by omega] using h

-- Induction on the LEFT state uses BOTH finite iterate sums.
private theorem word_field_closed (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (w : List ℕ) :
    ∀ (k : ℤ) (v : Carrier D), v ∈ vacuumDescendants D a s →
      ((Y D (word D a s w))[[k]]) v ∈ vacuumDescendants D a s := by
  induction w with
  | nil =>
      intro k v hv
      simp only [word, stateField_vacuum, identity_modes]
      split_ifs
      · simpa using hv
      · exact (vacuumDescendants D a s).zero_mem
  | cons j w ih =>
      intro k v hv
      have it := stateField_iterate D (vector D a s) (word D a s w) v
        (-((j : ℤ) + 1) + 1) k
      dsimp only at it
      change ((Y D (((Y D (vector D a s))[[-((j : ℤ) + 1) + 1]])
        (word D a s w)))[[k]]) v ∈ vacuumDescendants D a s
      rw [it.2.2]
      apply (vacuumDescendants D a s).sub_mem
      · apply finite_sum_mem (vacuumDescendants D a s) _ it.1
        intro i
        exact (vacuumDescendants D a s).smul_mem _
          (generator_closed D a ha s hs _ _ (ih _ v hv))
      · apply (vacuumDescendants D a s).smul_mem
        apply finite_sum_mem (vacuumDescendants D a s) _ it.2.1
        intro i
        exact (vacuumDescendants D a s).smul_mem _
          (ih _ _ (generator_closed D a ha s hs _ v hv))

-- Full all-state closure; generator invariance was only a step.
private theorem full_field_closed (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (u : Carrier D)
    (hu : u ∈ vacuumDescendants D a s) (k : ℤ) (v : Carrier D)
    (hv : v ∈ vacuumDescendants D a s) :
    ((Y D u)[[k]]) v ∈ vacuumDescendants D a s := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨w, rfl⟩ := hu
      exact word_field_closed D a ha s hs w k v hv
  | zero => simpa using (vacuumDescendants D a s).zero_mem
  | add u z _ _ h₁ h₂ =>
      simpa only [map_add, LinearMap.add_apply, Pi.add_apply] using
        (vacuumDescendants D a s).add_mem h₁ h₂
  | smul c u _ h =>
      simpa only [map_smul, LinearMap.smul_apply, Pi.smul_apply] using
        (vacuumDescendants D a s).smul_mem c h

-- Ambient covariance, with the axis-mode indexing exposed.
private theorem translation_mode_commutator (D : LatticeData) (a : Charge D) (s : ℂ) (m : ℤ) (v : Carrier D) :
    translation D (mode D a s m v) - mode D a s m (translation D v) =
      -((m + 1 : ℤ) : ℂ) • mode D a s (m - 1) v := by
  have h := congrArg (fun A : Module.End ℂ (Carrier D) => A v)
    (stateField_covariance D (vector D a s) (m + 1))
  simpa only [mode, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply, show m + 1 - 1 = m by omega,
    show m - 1 + 1 = m by omega] using h

-- T=L[-1] ONLY on negative words of the actual vacuum.
private theorem translation_word (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (w : List ℕ) :
    translation D (word D a s w) = mode D a s (-1) (word D a s w) := by
  induction w with
  | nil =>
      simp only [word, translation_kills_vacuum]
      symm
      simpa only [mode, show (-1 : ℤ) + 1 = 0 by norm_num] using
        stateField_creativity D (vector D a s) 0 (by omega)
  | cons k w ih =>
      let m : ℤ := -((k : ℤ) + 1)
      have ambient := translation_mode_commutator D a s m (word D a s w)
      have axis := commute_action D a ha s hs (-1) m (word D a s w)
      have nc : (-1 : ℤ) + m ≠ 0 := by dsimp [m]; omega
      rw [if_neg nc, add_zero, show (-1 : ℤ) + m = m - 1 by omega] at axis
      have scalar : ((-1 : ℤ) : ℂ) - (m : ℂ) = -((m + 1 : ℤ) : ℂ) := by
        push_cast
        ring
      rw [scalar, ← ih] at axis
      change translation D (mode D a s m (word D a s w)) =
        mode D a s (-1) (mode D a s m (word D a s w))
      rw [axis]
      exact (sub_eq_iff_eq_add.mp ambient).trans (by abel)

-- Linearity extends the word identity to the actual span.
private theorem translation_axis (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (v : Carrier D)
    (hv : v ∈ vacuumDescendants D a s) :
    translation D v = mode D a s (-1) v := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨w, rfl⟩ := hv
      exact translation_word D a ha s hs w
  | zero => simp
  | add v u _ _ h₁ h₂ => simp only [map_add, h₁, h₂]
  | smul c v _ h => simp only [map_smul, h]

-- Translation preservation is derived, not assumed.
private theorem translation_closed (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (v : Carrier D)
    (hv : v ∈ vacuumDescendants D a s) :
    translation D v ∈ vacuumDescendants D a s := by
  rw [translation_axis D a ha s hs v hv]
  exact all_modes_closed D a ha s hs (-1) v hv

private def vacuumState (D : LatticeData) (a : Charge D) (s : ℂ) : vacuumDescendants D a s :=
  ⟨vacuum D, by simpa only [word] using word_mem D a s []⟩

-- Actual vector membership follows from actual creation.
private theorem vector_mem (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) : vector D a s ∈ vacuumDescendants D a s := by
  have h := all_modes_closed D a ha s hs (-2) (vacuum D)
    (vacuumState D a s).property
  simpa only [mode, show (-2 : ℤ) + 1 = -1 by norm_num,
    stateField_creation] using h

private def axisState (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) : vacuumDescendants D a s :=
  ⟨vector D a s, vector_mem D a ha s hs⟩

-- Unnormalized coefficients, needed by the genuine Hahn constructor.
private def rawCoefficient (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (u : vacuumDescendants D a s) (j : ℤ) :
    Module.End ℂ (vacuumDescendants D a s) :=
  (HVertexOperator.coeff (Y D u.val) j).restrict (by
    intro v hv
    simpa only [VertexOperator.coeff_eq_ncoeff] using
      full_field_closed D a ha s hs u.val u.property (-j - 1) v hv)

-- Support is inherited pointwise from the ambient Hahn field.
private theorem raw_support (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (u v : vacuumDescendants D a s) :
    (Function.support (fun j => rawCoefficient D a ha s hs u j v)).IsPWO := by
  refine Set.IsPWO.mono
    (HVertexOperator.isPWO_support_coeff (Y D u.val) v.val) ?_
  intro j hj
  change rawCoefficient D a ha s hs u j v ≠ 0 at hj
  change HVertexOperator.coeff (Y D u.val) j v.val ≠ 0
  intro hz
  exact hj (Subtype.ext hz)

-- Genuine HahnModule values with certified well-founded support.
private def fieldFor (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (u : vacuumDescendants D a s) :
    VertexOperator ℂ (vacuumDescendants D a s) :=
  HVertexOperator.of_coeff (rawCoefficient D a ha s hs u)
    (raw_support D a ha s hs u)

private def restrictedY (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) : (vacuumDescendants D a s) →ₗ[ℂ]
    VertexOperator ℂ (vacuumDescendants D a s) where
  toFun := fieldFor D a ha s hs
  map_add' u v := by
    apply HVertexOperator.coeff_inj
    funext j
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change HVertexOperator.coeff (Y D (u.val + v.val)) j x.val =
      HVertexOperator.coeff (Y D u.val) j x.val +
        HVertexOperator.coeff (Y D v.val) j x.val
    simp only [map_add, Pi.add_apply, LinearMap.add_apply]
  map_smul' c u := by
    apply HVertexOperator.coeff_inj
    funext j
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change HVertexOperator.coeff (Y D (c • u.val)) j x.val =
      c • HVertexOperator.coeff (Y D u.val) j x.val
    simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply]

-- Every integer NORMALIZED coefficient literally commutes with subtype.
private theorem coefficient_val (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (u v : vacuumDescendants D a s) (k : ℤ) :
    (((restrictedY D a ha s hs u)[[k]]) v : Carrier D) =
      ((Y D u.val)[[k]]) v.val := rfl

private def restrictedTranslation (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) : Module.End ℂ (vacuumDescendants D a s) :=
  (translation D).restrict (translation_closed D a ha s hs)

-- Injectivity preserves support and hence finite support.
private theorem finite_lift {ι V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : Submodule ℂ V) (f : ι → W)
    (hf : Function.HasFiniteSupport (fun i => (f i : V))) :
    Function.HasFiniteSupport f := by
  apply hf.subset
  intro i hi hz
  exact hi (Subtype.ext hz)

-- Finite sums commute with the genuine inclusion.
private theorem sum_val {ι V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : Submodule ℂ V) (f : ι → W) :
    ((∑ᶠ i, f i : W) : V) = ∑ᶠ i, (f i : V) :=
  W.subtype.toAddMonoidHom.map_finsum_of_injective Subtype.val_injective f

-- Polynomial delta and commutators commute with inclusion.
private theorem delta_val (D : LatticeData) (a : Charge D) (s : ℂ)
    (F : ℤ → ℤ → Module.End ℂ (vacuumDescendants D a s))
    (G : ℤ → ℤ → Module.End ℂ (Carrier D))
    (h : ∀ p q (v : vacuumDescendants D a s), (F p q v : Carrier D) = G p q v.val)
    (N : ℕ) (p q : ℤ) (v : vacuumDescendants D a s) :
    ((FieldNormalProductLocality.delta^[N] F) p q v : Carrier D) =
      (FieldNormalProductLocality.delta^[N] G) p q v.val := by
  induction N generalizing p q with
  | zero => exact h p q v
  | succ N ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change
        ((FieldNormalProductLocality.delta^[N] F) (p+1) q v : Carrier D) -
          ((FieldNormalProductLocality.delta^[N] F) p (q+1) v : Carrier D) =
        (FieldNormalProductLocality.delta^[N] G) (p+1) q v.val -
          (FieldNormalProductLocality.delta^[N] G) p (q+1) v.val
      rw [ih (p+1) q, ih p (q+1)]

-- Uniform locality order is inherited without changing the fields.
private theorem restricted_locality (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (u v : vacuumDescendants D a s) :
    ∃ N : ℕ, FieldNormalProductLocality.delta^[N]
      (FieldNormalProductLocality.commutator
        (restrictedY D a ha s hs u) (restrictedY D a ha s hs v)) = 0 := by
  obtain ⟨N, hN⟩ := LatticeAllStateLocality.stateField_locality D u.val v.val
  refine ⟨N, ?_⟩
  funext p q
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  have transport := delta_val D a s
    (FieldNormalProductLocality.commutator
      (restrictedY D a ha s hs u) (restrictedY D a ha s hs v))
    (FieldNormalProductLocality.commutator (Y D u.val) (Y D v.val))
    (by intro i j x; rfl) N p q w
  rw [hN] at transport
  exact transport

-- The FULL Borcherds identity, including all three support clauses.
private theorem restricted_borcherds (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (u v w : vacuumDescendants D a s) (p q r : ℤ) :
    let muS : (vacuumDescendants D a s) → ℤ → (vacuumDescendants D a s) →
        vacuumDescendants D a s := fun x k y => ((restrictedY D a ha s hs x)[[k]]) y
    let left : ℕ → vacuumDescendants D a s := fun i =>
      StateFieldResidueReconstruction.integerBinomial p i •
        muS (muS u (r+i) v) (p+q-i) w
    let first : ℕ → vacuumDescendants D a s := fun i =>
      (((-1 : ℂ)^i) * StateFieldResidueReconstruction.integerBinomial r i) •
        muS u (p+r-i) (muS v (q+i) w)
    let second : ℕ → vacuumDescendants D a s := fun i =>
      (((-1 : ℂ)^i) * StateFieldResidueReconstruction.integerBinomial r i) •
        (StateFieldResidueReconstruction.epsilon r • muS v (q+r-i) (muS u (p+i) w))
    Function.HasFiniteSupport left ∧ Function.HasFiniteSupport first ∧
      Function.HasFiniteSupport second ∧
        (∑ᶠ i, left i) = ∑ᶠ i,
          (((-1 : ℂ)^i) * StateFieldResidueReconstruction.integerBinomial r i) •
            (muS u (p+r-i) (muS v (q+i) w) -
              StateFieldResidueReconstruction.epsilon r •
                muS v (q+r-i) (muS u (p+i) w)) := by
  dsimp only
  let m : (vacuumDescendants D a s) → ℤ → (vacuumDescendants D a s) →
      vacuumDescendants D a s := fun x k y => ((restrictedY D a ha s hs x)[[k]]) y
  let L : ℕ → vacuumDescendants D a s := fun i =>
    StateFieldResidueReconstruction.integerBinomial p i • m (m u (r+i) v) (p+q-i) w
  let F : ℕ → vacuumDescendants D a s := fun i =>
    (((-1 : ℂ)^i) * StateFieldResidueReconstruction.integerBinomial r i) •
      m u (p+r-i) (m v (q+i) w)
  let B : ℕ → vacuumDescendants D a s := fun i =>
    (((-1 : ℂ)^i) * StateFieldResidueReconstruction.integerBinomial r i) •
      (StateFieldResidueReconstruction.epsilon r • m v (q+r-i) (m u (p+i) w))
  let R : ℕ → vacuumDescendants D a s := fun i =>
    (((-1 : ℂ)^i) * StateFieldResidueReconstruction.integerBinomial r i) •
      (m u (p+r-i) (m v (q+i) w) -
        StateFieldResidueReconstruction.epsilon r • m v (q+r-i) (m u (p+i) w))
  have h := (LatticeActualVertexAlgebra.actualVertexAlgebra D).borcherds
    u.val v.val w.val p q r
  dsimp only at h
  have hL := finite_lift (vacuumDescendants D a s) L h.1
  have hF := finite_lift (vacuumDescendants D a s) F h.2.1
  have hS := finite_lift (vacuumDescendants D a s) B h.2.2.1
  refine ⟨hL, hF, hS, ?_⟩
  change (∑ᶠ i, L i) = ∑ᶠ i, R i
  apply Subtype.ext
  rw [sum_val _ L, sum_val _ R]
  exact h.2.2.2

/-- The actual restricted state-field vertex algebra on the exact
accepted vacuumDescendants, constructed with genuine inherited Hahn support. -/
def vertexAlgebra (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) : StateFieldVertexAlgebra (vacuumDescendants D a s) where
  stateField := restrictedY D a ha s hs
  vacuum := vacuumState D a s
  translation := restrictedTranslation D a ha s hs
  vacuum_field := by
    apply HVertexOperator.coeff_inj
    funext j
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change HVertexOperator.coeff (Y D (vacuum D)) j v.val =
      (HVertexOperator.coeff
        (FieldNormalProduct.identityField : VertexOperator ℂ (vacuumDescendants D a s))
          j v : Carrier D)
    rw [stateField_vacuum]
    simp only [FieldNormalProduct.identityField, HVertexOperator.coeff_of_coeff,
      VertexOperator.of_coeff]
    split_ifs <;> rfl
  creation u := by
    apply Subtype.ext
    exact stateField_creation D u.val
  creativity u k hk := by
    apply Subtype.ext
    exact stateField_creativity D u.val k hk
  translation_vacuum := by
    apply Subtype.ext
    exact translation_kills_vacuum D
  covariance u k := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact congrArg (fun A : Module.End ℂ (Carrier D) => A v.val)
      (stateField_covariance D u.val k)
  locality := restricted_locality D a ha s hs
  borcherds := restricted_borcherds D a ha s hs

/-- Natural grades on the actual vacuum span, obtained by pulling
back the accepted word spans, rather than postulating an ambient grading. -/
def grade (D : LatticeData) (a : Charge D) (s : ℂ) (n : ℕ) : Submodule ℂ (vacuumDescendants D a s) :=
  (gradeSpace D a s n).comap (vacuumDescendants D a s).subtype

-- Positive-index words of total grade n form a finite set.
-- The entries k represent the POSITIVE indices k+1. No ordered/PBW basis is used.
private def wordsAt : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | n + 1 => (Finset.range (n + 1)).biUnion
      (fun k => (wordsAt (n - k)).image (List.cons k))
termination_by n => n
decreasing_by omega

-- This enumerates ALL words of grade n, including dependencies/zeros.
private theorem mem_wordsAt (w : List ℕ) (n : ℕ) :
    w ∈ wordsAt n ↔ wordGrade w = n := by
  induction n using Nat.strong_induction_on generalizing w with
  | h n ih =>
      cases n with
      | zero =>
          cases w with
          | nil => simp [wordsAt, wordGrade]
          | cons k w =>
              have positive : wordGrade (k :: w) ≠ 0 := by
                simp only [wordGrade]
                omega
              simp [wordsAt, positive]
      | succ n =>
          rw [wordsAt]
          constructor
          · intro hw
            obtain ⟨k, hk, hkw⟩ := Finset.mem_biUnion.mp hw
            obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hkw
            have hgrade := (ih (n-k) (by omega) l).mp hl
            have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
            simp only [wordGrade]
            omega
          · intro hw
            cases w with
            | nil => simp only [wordGrade] at hw; omega
            | cons k w =>
                have hkn : k ≤ n := by simp only [wordGrade] at hw; omega
                apply Finset.mem_biUnion.mpr
                refine ⟨k, Finset.mem_range.mpr (by omega), ?_⟩
                apply Finset.mem_image.mpr
                refine ⟨w, (ih (n-k) (by omega) w).mpr ?_, rfl⟩
                simp only [wordGrade] at hw
                omega

-- The accepted grade generators are the image of a finite word set.
private theorem grade_generators_finite (D : LatticeData) (a : Charge D) (s : ℂ) (n : ℕ) :
    Set.Finite {v : Carrier D | ∃ w, wordGrade w = n ∧ word D a s w = v} := by
  have eqset : {v : Carrier D | ∃ w, wordGrade w = n ∧ word D a s w = v} =
      (word D a s) '' (wordsAt n : Set (List ℕ)) := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, (mem_wordsAt w n).mpr hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, (mem_wordsAt w n).mp hw, rfl⟩
  rw [eqset]
  exact (wordsAt n).finite_toSet.image (word D a s)

private theorem grade_le (D : LatticeData) (a : Charge D) (s : ℂ) (n : ℕ) : gradeSpace D a s n ≤ vacuumDescendants D a s := by
  apply Submodule.span_le.mpr
  rintro v ⟨w, _, rfl⟩
  exact word_mem D a s w

-- Finite dimension is DERIVED from finite compositions, not PBW.
private theorem grade_finite (D : LatticeData) (a : Charge D) (s : ℂ) (n : ℕ) : FiniteDimensional ℂ (grade D a s n) := by
  letI : FiniteDimensional ℂ (gradeSpace D a s n) :=
    FiniteDimensional.span_of_finite ℂ (grade_generators_finite D a s n)
  let f : (grade D a s n) →ₗ[ℂ] (gradeSpace D a s n) :=
    { toFun := fun v => ⟨v.val.val, v.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact FiniteDimensional.of_injective f (by
    intro u v huv
    exact Subtype.ext (Subtype.ext
      (congrArg (fun z : gradeSpace D a s n => (z : Carrier D)) huv)))

-- Grade zero is literally the actual vacuum line.
private theorem grade_zero_line (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) : grade D a s 0 =
    Submodule.span ℂ {((vertexAlgebra D a ha s hs).vacuum)} := by
  apply Submodule.ext
  intro v
  constructor
  · intro hv
    change v.val ∈ gradeSpace D a s 0 at hv
    rw [grade_zero D a s] at hv
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
    exact Submodule.mem_span_singleton.mpr ⟨c, Subtype.ext hc⟩
  · intro hv
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
    change v.val ∈ gradeSpace D a s 0
    rw [grade_zero D a s]
    exact Submodule.mem_span_singleton.mpr ⟨c, congrArg Subtype.val hc⟩

-- Finite decomposition uses the accepted span proof, with its exact f.
private theorem finite_decomposition (D : LatticeData) (a : Charge D) (s : ℂ) (v : vacuumDescendants D a s) :
    ∃ f : ℕ →₀ vacuumDescendants D a s,
      (∑ n ∈ f.support, f n) = v ∧ ∀ n, f n ∈ grade D a s n := by
  classical
  obtain ⟨f, hf, hfg⟩ := decompose D a s v.val v.property
  let g : ℕ →₀ vacuumDescendants D a s :=
    { support := f.support
      toFun := fun n => ⟨f n, grade_le D a s n (hfg n)⟩
      mem_support_toFun := by
        intro n
        constructor
        · intro hn hz
          exact (Finsupp.mem_support_iff.mp hn) (congrArg Subtype.val hz)
        · intro hn
          apply Finsupp.mem_support_iff.mpr
          intro hz
          exact hn (Subtype.ext hz) }
  refine ⟨g, ?_, fun n => hfg n⟩
  apply Subtype.ext
  change (vacuumDescendants D a s).subtype (∑ n ∈ f.support, g n) = v.val
  rw [map_sum]
  exact hf

-- Directness consumes the accepted finite spectral projector.
private theorem decomposition_direct (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (f : ℕ →₀ vacuumDescendants D a s)
    (hf : ∀ n, f n ∈ grade D a s n) (hz : (∑ n ∈ f.support, f n) = 0) : f = 0 := by
  classical
  let g : ℕ →₀ Carrier D :=
    { support := f.support
      toFun := fun n => (f n).val
      mem_support_toFun := by
        intro n
        constructor
        · intro hn hz
          exact (Finsupp.mem_support_iff.mp hn) (Subtype.ext hz)
        · intro hn
          apply Finsupp.mem_support_iff.mpr
          intro hz
          exact hn (congrArg Subtype.val hz) }
  have gzero : assemble D g = 0 := by
    have h := congrArg (vacuumDescendants D a s).subtype hz
    change (∑ n ∈ f.support, (f n).val) = 0
    simpa only [map_sum, map_zero, Submodule.subtype_apply] using h
  have eigen : ∀ n, mode D a s 0 (g n) = (n : ℂ) • g n :=
    fun n => grade_eigen D a ha s hs n (f n).val (hf n)
  apply Finsupp.ext
  intro n
  by_cases hn : n ∈ f.support
  · have projected := projection_identity D a s g eigen n hn
    have nc := cutValue_ne_zero (g.support.erase n).toList n (by simp)
    rw [gzero, map_zero] at projected
    have component : g n = 0 :=
      (smul_eq_zero.mp projected.symm).resolve_left nc
    exact Subtype.ext component
  · exact Finsupp.notMem_support_iff.mp hn

-- The actual L0 commutator for an ARBITRARY state of S.
private theorem coefficient_weight_eigen (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (n t : ℕ) (k : ℤ)
    (u v : vacuumDescendants D a s)
    (hu : u ∈ grade D a s n) (hv : v ∈ grade D a s t) :
    mode D a s 0 (((Y D u.val)[[k]]) v.val) =
      (((n : ℤ) + (t : ℤ) - k - 1 : ℤ) : ℂ) •
        (((Y D u.val)[[k]]) v.val) := by
  have eu := grade_eigen D a ha s hs n u.val hu
  have ev := grade_eigen D a ha s hs t v.val hv
  have translate := translation_axis D a ha s hs u.val u.property
  have comm := congrArg (fun A : Module.End ℂ (Carrier D) => A v.val)
    (one_mode_commutator D (vector D a s) u.val k)
  change mode D a s 0 (((Y D u.val)[[k]]) v.val) -
      ((Y D u.val)[[k]]) (mode D a s 0 v.val) =
        ((Y D (mode D a s (-1) u.val))[[k+1]]) v.val +
          ((Y D (mode D a s 0 u.val))[[k]]) v.val at comm
  rw [← translate, state_derivative_modes, eu, ev, map_smul] at comm
  simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply,
    show k + 1 - 1 = k by omega] at comm
  have result := sub_eq_iff_eq_add.mp comm
  rw [result]
  push_cast
  module

-- Integer result weight; negative weights force zero explicitly.
private theorem coefficient_grading (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (n t : ℕ) (k : ℤ)
    (u v : vacuumDescendants D a s)
    (hu : u ∈ grade D a s n) (hv : v ∈ grade D a s t) :
    let w : ℤ := (n : ℤ) + (t : ℤ) - k - 1
    (0 ≤ w → (((vertexAlgebra D a ha s hs).stateField u)[[k]]) v ∈
      grade D a s w.toNat) ∧
    (w < 0 → (((vertexAlgebra D a ha s hs).stateField u)[[k]]) v = 0) := by
  dsimp only
  let w : ℤ := (n : ℤ) + (t : ℤ) - k - 1
  let z : vacuumDescendants D a s := (((vertexAlgebra D a ha s hs).stateField u)[[k]]) v
  have ez : mode D a s 0 z.val = (w : ℂ) • z.val :=
    coefficient_weight_eigen D a ha s hs n t k u v hu hv
  have locate : z ≠ 0 → ∃ j : ℕ, z.val ∈ gradeSpace D a s j ∧ w = (j : ℤ) := by
    intro hnz
    have nz : z.val ≠ 0 := fun h => hnz (Subtype.ext h)
    obtain ⟨j, hj, he⟩ := eigen_in_grade D a ha s hs (w : ℂ) z.val z.property nz ez
    refine ⟨j, hj, ?_⟩
    exact_mod_cast he
  constructor
  · intro hw
    by_cases hz : z = 0
    · change z ∈ grade D a s w.toNat
      rw [hz]
      exact (grade D a s w.toNat).zero_mem
    · obtain ⟨j, hj, hweight⟩ := locate hz
      have hjw : j = w.toNat := by omega
      change z.val ∈ gradeSpace D a s w.toNat
      simpa only [hjw] using hj
  · intro hw
    by_contra hnz
    obtain ⟨j, _, hweight⟩ := locate hnz
    omega

-- All actual axis modes are coefficients of the actual vector in S.
private theorem axis_modes (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (m : ℤ) :
    ((vertexAlgebra D a ha s hs).stateField (axisState D a ha s hs))[[m+1]] =
      restrictedMode D a ha s hs m := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  rfl

-- Consumed only by the genuine state-field endpoint below.
private theorem all_coefficient_simplicity (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (U : Submodule ℂ (vacuumDescendants D a s))
    (invariant : ∀ (u v : vacuumDescendants D a s) (k : ℤ), v ∈ U →
      (((vertexAlgebra D a ha s hs).stateField u)[[k]]) v ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  apply vacuum_descendants_irreducible D a ha s hs U
  intro m v hv
  rw [← axis_modes D a ha s hs m]
  exact invariant (axisState D a ha s hs) v (m+1) hv

-- c=1/2 self-products, transported from the actual norm-four vector.
private theorem axis_products (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    let V := vertexAlgebra D a ha s hs
    let e := axisState D a ha s hs
    ((V.stateField e)[[0]]) e = V.translation e ∧
      ((V.stateField e)[[1]]) e = (2 : ℂ) • e ∧
      ((V.stateField e)[[2]]) e = 0 ∧
      ((V.stateField e)[[3]]) e = (1 / 4 : ℂ) • V.vacuum ∧
      ∀ k : ℤ, 4 ≤ k → ((V.stateField e)[[k]]) e = 0 := by
  obtain ⟨h0, h1, h2, h3, ht⟩ := self_products D a ha s hs
  refine ⟨Subtype.ext h0, Subtype.ext h1, Subtype.ext h2, Subtype.ext h3, ?_⟩
  intro k hk
  exact Subtype.ext (ht k hk)

-- The vector's grade follows from its actual creation word L[-2]1.
private theorem axis_grade (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) : axisState D a ha s hs ∈ grade D a s 2 := by
  change vector D a s ∈ gradeSpace D a s 2
  apply Submodule.subset_span
  refine ⟨[1], by norm_num [wordGrade], ?_⟩
  norm_num [word, mode, stateField_creation]

-- Restriction of the ACTUAL central-charge-one-half relation.
private theorem restricted_virasoro (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (m n : ℤ) :
    restrictedMode D a ha s hs m * restrictedMode D a ha s hs n -
        restrictedMode D a ha s hs n * restrictedMode D a ha s hs m =
      ((m : ℂ) - (n : ℂ)) • restrictedMode D a ha s hs (m+n) +
        (if m+n = 0 then (((m : ℂ)^3 - (m : ℂ)) / 24) •
          (1 : Module.End ℂ (vacuumDescendants D a s)) else 0) := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  have h := congrArg (fun A : Module.End ℂ (Carrier D) => A v.val)
    (virasoro_commutator D a ha s hs m n)
  split_ifs at h ⊢ <;>
    simpa only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
      LinearMap.smul_apply, Module.End.one_apply, LinearMap.zero_apply,
      Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_zero,
      restrictedMode, LinearMap.coe_restrict_apply] using h

/-- Single mathematical endpoint for the actual simple graded
c=1/2 vacuum state-field algebra. Its StateFieldVertexAlgebra value already
contains creation, creativity, covariance, uniform locality, and FULL finite
Borcherds. The remaining conjuncts derive its actual embedding, translation,
axis, nonnegative finite word grading, directness, weight law and simplicity.
-/
theorem actual_simple_graded_vacuum_vertex_algebra (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    let S := vacuumDescendants D a s
    let V := vertexAlgebra D a ha s hs
    (V.vacuum : Carrier D) = vacuum D ∧ V.vacuum ≠ 0 ∧
    (∀ v : S, (V.translation v : Carrier D) = translation D v.val ∧
      V.translation v = restrictedMode D a ha s hs (-1) v) ∧
    (∀ (u v : S) (k : ℤ), (((V.stateField u)[[k]]) v : Carrier D) =
      ((Y D u.val)[[k]]) v.val) ∧
    (∀ (u v : S) (k : ℤ), ((Y D u.val)[[k]]) v.val ∈ S) ∧
    (∃ e : S, e.val = vector D a s ∧ e ∈ grade D a s 2 ∧
      (∀ m : ℤ, ((V.stateField e)[[m+1]]) = restrictedMode D a ha s hs m) ∧
      (∀ m n : ℤ,
        restrictedMode D a ha s hs m * restrictedMode D a ha s hs n -
            restrictedMode D a ha s hs n * restrictedMode D a ha s hs m =
          ((m : ℂ) - (n : ℂ)) • restrictedMode D a ha s hs (m+n) +
            (if m+n = 0 then (((m : ℂ)^3 - (m : ℂ)) / 24) •
              (1 : Module.End ℂ S) else 0)) ∧
      ((V.stateField e)[[0]]) e = V.translation e ∧
      ((V.stateField e)[[1]]) e = (2 : ℂ) • e ∧
      ((V.stateField e)[[2]]) e = 0 ∧
      ((V.stateField e)[[3]]) e = (1 / 4 : ℂ) • V.vacuum ∧
      ∀ k : ℤ, 4 ≤ k → ((V.stateField e)[[k]]) e = 0) ∧
    grade D a s 0 = Submodule.span ℂ {V.vacuum} ∧
    (∀ n : ℕ, FiniteDimensional ℂ (grade D a s n)) ∧
    (∀ v : S, ∃ f : ℕ →₀ S,
      (∑ n ∈ f.support, f n) = v ∧ ∀ n, f n ∈ grade D a s n) ∧
    (∀ f : ℕ →₀ S, (∀ n, f n ∈ grade D a s n) →
      (∑ n ∈ f.support, f n) = 0 → f = 0) ∧
    (∀ (n : ℕ) (v : S), v ∈ grade D a s n →
      restrictedMode D a ha s hs 0 v = (n : ℂ) • v) ∧
    (∀ (n t : ℕ) (k : ℤ) (u v : S), u ∈ grade D a s n → v ∈ grade D a s t →
      let w : ℤ := (n : ℤ) + (t : ℤ) - k - 1
      (0 ≤ w → ((V.stateField u)[[k]]) v ∈ grade D a s w.toNat) ∧
      (w < 0 → ((V.stateField u)[[k]]) v = 0)) ∧
    (∀ U : Submodule ℂ S,
      (∀ (u v : S) (k : ℤ), v ∈ U → ((V.stateField u)[[k]]) v ∈ U) →
      U = ⊥ ∨ U = ⊤) := by
  dsimp only
  refine ⟨rfl, ?_, ?_, coefficient_val D a ha s hs, ?_, ?_,
    grade_zero_line D a ha s hs, grade_finite D a s,
    finite_decomposition D a s, decomposition_direct D a ha s hs,
    ?_, coefficient_grading D a ha s hs, all_coefficient_simplicity D a ha s hs⟩
  · intro h
    exact LatticePositiveEnergy.vacuum_nonzero D (congrArg Subtype.val h)
  · intro v
    refine ⟨rfl, ?_⟩
    exact Subtype.ext (translation_axis D a ha s hs v.val v.property)
  · intro u v k
    exact full_field_closed D a ha s hs u.val u.property k v.val v.property
  · refine ⟨axisState D a ha s hs, rfl, axis_grade D a ha s hs,
      axis_modes D a ha s hs, restricted_virasoro D a ha s hs, ?_⟩
    exact axis_products D a ha s hs
  · intro n v hv
    exact Subtype.ext (grade_eigen D a ha s hs n v.val hv)

end
end D5.S3.VertexAlgebra.Lattice.NormFourVacuumVertexAlgebra
