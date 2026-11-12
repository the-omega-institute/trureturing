/- Source-only candidate: UNCOMPILED and UNACCEPTED.

Full rational Hahn fields with arbitrary actual weak-module targets. The
source/input actions and both translation laws are the literal laws of
LatticeDualCosetIntertwiner, with only the target replaced by J.stateField.
The three Jacobi supports stay separate. No exponent coset, grading,
finite-dimensionality, tensor model or support restriction is imposed.

Suppliers retain their original attributions: Bakalov--Kac, math/0402315v1,
section 4.1; Scott Carnahan's residue calculus and Kalle Kytölä's Sugawara
calculus. This file proves target functoriality, not fusion classification.
-/
import D5.S3.VertexAlgebra.Sectors.LatticeDualCosetFusion
import D5.S3.VertexAlgebra.Modules.FullJacobiModuleMaps

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Sectors.ActualWeakTargetFullIntertwiner
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeSugawaraCurrents LatticeActualConformalState
open LatticeDualCosetModule LatticeDualCosetConformal
open LatticeDiscriminantTheta
open Modules.FullJacobiCurrentTransport (FullJacobiLatticeModule)
open Modules.FullJacobiIntertwiner (ModuleHom ModuleIso)
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators VertexOperator Matrix
noncomputable section
universe u v w

abbrev Fields (D : LatticeData) (M : Type u) [AddCommGroup M] [Module ℂ M] :=
  Carrier D →ₗ[ℂ] HVertexOperator ℚ ℂ (Carrier D) M

variable {D : LatticeData} {M : Type u} {N : Type v} {P : Type w}
variable [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
variable [AddCommGroup P] [Module ℂ P]

attribute [local instance] Classical.propDecidable

def mode (I : Fields D M) (u : Carrier D) (targetShift : ℚ) :
    Carrier D →ₗ[ℂ] M := (I u).coeff (-targetShift - 1)

def targetTranslation (J : FullJacobiLatticeModule D M)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : Module.End ℂ M :=
  Modules.FullJacobiCurrentTransport.mode J (omega D H) 0

def leftTerm (D : LatticeData) (a : Charge D) (I : Fields D M)
    (h u v : Carrier D) (p m : ℤ) (targetShift : ℚ) (i : ℕ) : M :=
  integerBinomial p i • mode I (((action D a h)[[m + i]]) u)
    ((p : ℚ) + targetShift - i) v

def firstTerm (D : LatticeData) (J : FullJacobiLatticeModule D M) (I : Fields D M)
    (h u v : Carrier D) (p m : ℤ) (targetShift : ℚ) (i : ℕ) : M :=
  (((-1 : ℂ)^i) * integerBinomial m i) •
    ((J.stateField h)[[p + m - i]]) (mode I u (targetShift + i) v)

def secondTerm (D : LatticeData) (b : Charge D) (I : Fields D M)
    (h u v : Carrier D) (p m : ℤ) (targetShift : ℚ) (i : ℕ) : M :=
  (((-1 : ℂ)^i) * integerBinomial m i) •
    (StateFieldResidueReconstruction.epsilon m •
      mode I u (targetShift + m - i) (((action D b h)[[p + i]]) v))

/-- Exactly the full source/input laws, with the actual arbitrary target. -/
structure Lawful (D : LatticeData) (a b : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (J : FullJacobiLatticeModule D M) (I : Fields D M) : Prop where
  source : ∀ u τ, mode I (moduleL D a H (-1) u) τ =
    -(τ : ℂ) • mode I u (τ - 1)
  target : ∀ u τ, (targetTranslation J H).comp (mode I u τ) -
    (mode I u τ).comp (moduleL D b H (-1)) = -(τ : ℂ) • mode I u (τ - 1)
  jacobi : ∀ h u v p m τ,
    Function.HasFiniteSupport (leftTerm D a I h u v p m τ) ∧
    Function.HasFiniteSupport (firstTerm D J I h u v p m τ) ∧
    Function.HasFiniteSupport (secondTerm D b I h u v p m τ) ∧
      (∑ᶠ i : ℕ, leftTerm D a I h u v p m τ i) =
        (∑ᶠ i : ℕ, firstTerm D J I h u v p m τ i) -
          (∑ᶠ i : ℕ, secondTerm D b I h u v p m τ i)

theorem lawful_zero (D : LatticeData) (a b : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (J : FullJacobiLatticeModule D M) : Lawful D a b H J 0 where
  source u τ := by apply LinearMap.ext; intro v; simp [mode]
  target u τ := by apply LinearMap.ext; intro v; simp [mode]
  jacobi h u v p r τ := by
    simp [leftTerm, firstTerm, secondTerm, mode, Function.HasFiniteSupport, Function.support]

theorem lawful_add (D : LatticeData) (a b : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (J : FullJacobiLatticeModule D M)
    (I K : Fields D M) (hI : Lawful D a b H J I) (hK : Lawful D a b H J K) :
    Lawful D a b H J (I+K) where
  source u τ := by
    apply LinearMap.ext
    intro v
    have hi := congrArg (fun f : Carrier D →ₗ[ℂ] M => f v) (hI.source u τ)
    have hk := congrArg (fun f : Carrier D →ₗ[ℂ] M => f v) (hK.source u τ)
    simpa [mode, smul_add] using congrArg₂ (·+·) hi hk
  target u τ := by
    apply LinearMap.ext
    intro v
    have hi := congrArg (fun f : Carrier D →ₗ[ℂ] M => f v) (hI.target u τ)
    have hk := congrArg (fun f : Carrier D →ₗ[ℂ] M => f v) (hK.target u τ)
    simp only [mode, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      map_add, Pi.add_apply, LinearMap.add_apply, smul_add] at hi hk ⊢
    linear_combination (norm := module) hi + hk
  jacobi h u v p r τ := by
    have hi := hI.jacobi h u v p r τ
    have hk := hK.jacobi h u v p r τ
    have hl : leftTerm D a (I+K) h u v p r τ =
        leftTerm D a I h u v p r τ + leftTerm D a K h u v p r τ := by
      funext i; simp [leftTerm, mode, smul_add]
    have hf : firstTerm D J (I+K) h u v p r τ =
        firstTerm D J I h u v p r τ + firstTerm D J K h u v p r τ := by
      funext i; simp [firstTerm, mode, smul_add]
    have hs : secondTerm D b (I+K) h u v p r τ =
        secondTerm D b I h u v p r τ + secondTerm D b K h u v p r τ := by
      funext i; simp [secondTerm, mode, smul_add]
    rw [hl, hf, hs]
    refine ⟨hi.1.add hk.1, hi.2.1.add hk.2.1, hi.2.2.1.add hk.2.2.1, ?_⟩
    simp only [Pi.add_apply]
    rw [finsum_add_distrib hi.1 hk.1, finsum_add_distrib hi.2.1 hk.2.1,
      finsum_add_distrib hi.2.2.1 hk.2.2.1, hi.2.2.2, hk.2.2.2]
    abel

theorem lawful_smul (D : LatticeData) (a b : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (J : FullJacobiLatticeModule D M)
    (c : ℂ) (I : Fields D M) (hI : Lawful D a b H J I) : Lawful D a b H J (c • I) where
  source u τ := by
    apply LinearMap.ext
    intro v
    have hi := congrArg (fun f : Carrier D →ₗ[ℂ] M => f v) (hI.source u τ)
    simpa [mode, smul_comm c] using congrArg (c • ·) hi
  target u τ := by
    apply LinearMap.ext
    intro v
    have hi := congrArg (fun f : Carrier D →ₗ[ℂ] M => f v) (hI.target u τ)
    simpa [mode, ← smul_sub, smul_comm c] using congrArg (c • ·) hi
  jacobi h u v p r τ := by
    have hi := hI.jacobi h u v p r τ
    have hl : leftTerm D a (c • I) h u v p r τ = c • leftTerm D a I h u v p r τ := by
      funext i; simp [leftTerm, mode, smul_comm c]
    have hf : firstTerm D J (c • I) h u v p r τ = c • firstTerm D J I h u v p r τ := by
      funext i; simp [firstTerm, mode, smul_comm c]
    have hs : secondTerm D b (c • I) h u v p r τ = c • secondTerm D b I h u v p r τ := by
      funext i; simp [secondTerm, mode, smul_comm c]
    rw [hl, hf, hs]
    refine ⟨hi.1.smul_right (fun _ => c), hi.2.1.smul_right (fun _ => c),
      hi.2.2.1.smul_right (fun _ => c), ?_⟩
    simp only [Pi.smul_apply]
    rw [← smul_finsum' c hi.1, ← smul_finsum' c hi.2.1,
      ← smul_finsum' c hi.2.2.1, hi.2.2.2, smul_sub]

/-- The natural complex submodule of fields satisfying the actual full laws. -/
def operatorSpace (D : LatticeData) (a b : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (J : FullJacobiLatticeModule D M) : Submodule ℂ (Fields D M) where
  carrier := {I | Lawful D a b H J I}
  zero_mem' := lawful_zero D a b H J
  add_mem' := fun hi hk => lawful_add D a b H J _ _ hi hk
  smul_mem' := fun c _ hi => lawful_smul D a b H J c _ hi

/-- A linear image may kill coefficients. Injectivity is never needed. -/
theorem coefficient_support_post_subset (f : M →ₗ[ℂ] N) (c : ℚ → M) :
    Function.support (fun q => f (c q)) ⊆ Function.support c := by
  intro q hq
  change f (c q) ≠ 0 at hq
  change c q ≠ 0
  intro hz
  exact hq (by rw [hz, map_zero])

theorem coefficient_post_isPWO (f : M →ₗ[ℂ] N) (c : ℚ → M)
    (hc : (Function.support c).IsPWO) :
    (Function.support (fun q => f (c q))).IsPWO :=
  hc.mono (coefficient_support_post_subset f c)

/-- Coefficientwise linear image of a Hahn series, with its own support proof. -/
def seriesPost (f : M →ₗ[ℂ] N) (x : HahnSeries ℚ M) : HahnSeries ℚ N :=
  ⟨fun q => f (x.coeff q), coefficient_post_isPWO f x.coeff x.isPWO_support'⟩

def hahnPost (f : M →ₗ[ℂ] N) :
    HahnModule ℚ ℂ M →ₗ[ℂ] HahnModule ℚ ℂ N where
  toFun x := HahnModule.of ℂ (seriesPost f ((HahnModule.of ℂ).symm x))
  map_add' x y := by
    apply (HahnModule.of ℂ).symm.injective
    simp only [Equiv.symm_apply_apply, HahnModule.of_symm_add]
    apply HahnSeries.ext
    funext q
    simp [seriesPost, HahnSeries.coeff_add, map_add]
  map_smul' c x := by
    apply (HahnModule.of ℂ).symm.injective
    simp only [RingHom.id_apply, Equiv.symm_apply_apply, HahnModule.of_symm_smul]
    apply HahnSeries.ext
    funext q
    simp [seriesPost, HahnSeries.coeff_smul, map_smul]

/-- Literal postcomposition on complete fields, before any law is imposed. -/
def rawPost (f : M →ₗ[ℂ] N) : Fields D M →ₗ[ℂ] Fields D N where
  toFun I :=
    { toFun := fun u => (hahnPost f).comp (I u)
      map_add' := by intro u v; simp only [map_add, LinearMap.comp_add]
      map_smul' := by
        intro c u
        simp only [map_smul, LinearMap.comp_smul, RingHom.id_apply] }
  map_add' I K := by
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    exact map_add (hahnPost f) (I u v) (K u v)
  map_smul' c I := by
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    exact (hahnPost f).map_smul c (I u v)

@[simp] theorem rawPost_coeff (f : M →ₗ[ℂ] N) (I : Fields D M)
    (u v : Carrier D) (q : ℚ) :
    ((rawPost f I) u).coeff q v = f ((I u).coeff q v) := rfl

@[simp] theorem rawPost_mode (f : M →ₗ[ℂ] N) (I : Fields D M)
    (u v : Carrier D) (τ : ℚ) :
    mode (rawPost f I) u τ v = f (mode I u τ v) := rfl

/-- The support inclusion is statewise and inputwise on the full Hahn field. -/
theorem rawPost_support_subset (f : M →ₗ[ℂ] N) (I : Fields D M)
    (u v : Carrier D) :
    Function.support (fun q => ((rawPost f I) u).coeff q v) ⊆
      Function.support (fun q => (I u).coeff q v) :=
  coefficient_support_post_subset f (fun q => (I u).coeff q v)

theorem rawPost_isPWO (f : M →ₗ[ℂ] N) (I : Fields D M) (u v : Carrier D) :
    (Function.support (fun q => ((rawPost f I) u).coeff q v)).IsPWO :=
  ((I u).isPWO_support_coeff v).mono (rawPost_support_subset f I u v)

/-- Extensionality keeps all source states, input states and rational powers. -/
theorem fields_ext {I K : Fields D M}
    (h : ∀ (u v : Carrier D) (q : ℚ), (I u).coeff q v = (K u).coeff q v) : I = K := by
  apply LinearMap.ext
  intro u
  apply HVertexOperator.coeff_inj
  funext q
  apply LinearMap.ext
  intro v
  exact h u v q

@[simp] theorem rawPost_id (I : Fields D M) : rawPost LinearMap.id I = I := by
  apply fields_ext
  intro u v q
  rfl

theorem rawPost_comp (g : N →ₗ[ℂ] P) (f : M →ₗ[ℂ] N) (I : Fields D M) :
    rawPost (g.comp f) I = rawPost g (rawPost f I) := by
  apply fields_ext
  intro u v q
  rfl

@[simp] theorem rawPost_zero (I : Fields D M) : rawPost (0 : M →ₗ[ℂ] N) I = 0 := by
  apply fields_ext
  intro u v q
  rfl

theorem rawPost_add (f g : M →ₗ[ℂ] N) (I : Fields D M) :
    rawPost (f + g) I = rawPost f I + rawPost g I := by
  apply fields_ext
  intro u v q
  rfl

theorem rawPost_smul (c : ℂ) (f : M →ₗ[ℂ] N) (I : Fields D M) :
    rawPost (c • f) I = c • rawPost f I := by
  apply fields_ext
  intro u v q
  rfl

variable {J : FullJacobiLatticeModule D M} {K : FullJacobiLatticeModule D N}
variable {L : FullJacobiLatticeModule D P}

/-- This uses the actual omega state and its zero mode. -/
theorem map_targetTranslation (f : ModuleHom J K)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (x : M) :
    f.linearMap (targetTranslation J H x) = targetTranslation K H (f.linearMap x) :=
  f.intertwines (omega D H) 0 x

theorem post_leftTerm (a : Charge D) (f : ModuleHom J K) (I : Fields D M)
    (h u v : Carrier D) (p m : ℤ) (τ : ℚ) (i : ℕ) :
    leftTerm D a (rawPost f.linearMap I) h u v p m τ i =
      f.linearMap (leftTerm D a I h u v p m τ i) := by
  simp only [leftTerm, rawPost_mode, map_smul]

theorem post_firstTerm (f : ModuleHom J K) (I : Fields D M)
    (h u v : Carrier D) (p m : ℤ) (τ : ℚ) (i : ℕ) :
    firstTerm D K (rawPost f.linearMap I) h u v p m τ i =
      f.linearMap (firstTerm D J I h u v p m τ i) := by
  simp only [firstTerm, rawPost_mode, map_smul]
  exact congrArg (fun x : N => (((-1 : ℂ)^i) * integerBinomial m i) • x)
    (f.intertwines h (p + m - i) (mode I u (τ + i) v)).symm

theorem post_secondTerm (b : Charge D) (f : ModuleHom J K) (I : Fields D M)
    (h u v : Carrier D) (p m : ℤ) (τ : ℚ) (i : ℕ) :
    secondTerm D b (rawPost f.linearMap I) h u v p m τ i =
      f.linearMap (secondTerm D b I h u v p m τ i) := by
  simp only [secondTerm, rawPost_mode, map_smul]

/-- Each family gets its own containment proof, before any finsum is mapped. -/
theorem post_left_support (a : Charge D) (f : ModuleHom J K) (I : Fields D M)
    (h u v : Carrier D) (p m : ℤ) (τ : ℚ) :
    Function.support (leftTerm D a (rawPost f.linearMap I) h u v p m τ) ⊆
      Function.support (leftTerm D a I h u v p m τ) := by
  intro i hi
  change leftTerm D a I h u v p m τ i ≠ 0
  intro hz
  apply hi
  rw [post_leftTerm, hz, map_zero]

theorem post_first_support (f : ModuleHom J K) (I : Fields D M)
    (h u v : Carrier D) (p m : ℤ) (τ : ℚ) :
    Function.support (firstTerm D K (rawPost f.linearMap I) h u v p m τ) ⊆
      Function.support (firstTerm D J I h u v p m τ) := by
  intro i hi
  change firstTerm D J I h u v p m τ i ≠ 0
  intro hz
  apply hi
  rw [post_firstTerm, hz, map_zero]

theorem post_second_support (b : Charge D) (f : ModuleHom J K) (I : Fields D M)
    (h u v : Carrier D) (p m : ℤ) (τ : ℚ) :
    Function.support (secondTerm D b (rawPost f.linearMap I) h u v p m τ) ⊆
      Function.support (secondTerm D b I h u v p m τ) := by
  intro i hi
  change secondTerm D b I h u v p m τ i ≠ 0
  intro hz
  apply hi
  rw [post_secondTerm, hz, map_zero]

theorem post_left_finite (a : Charge D) (f : ModuleHom J K) (I : Fields D M)
    (h u v : Carrier D) (p m : ℤ) (τ : ℚ)
    (hf : Function.HasFiniteSupport (leftTerm D a I h u v p m τ)) :
    Function.HasFiniteSupport (leftTerm D a (rawPost f.linearMap I) h u v p m τ) :=
  hf.subset (post_left_support a f I h u v p m τ)

theorem post_first_finite (f : ModuleHom J K) (I : Fields D M)
    (h u v : Carrier D) (p m : ℤ) (τ : ℚ)
    (hf : Function.HasFiniteSupport (firstTerm D J I h u v p m τ)) :
    Function.HasFiniteSupport (firstTerm D K (rawPost f.linearMap I) h u v p m τ) :=
  hf.subset (post_first_support f I h u v p m τ)

theorem post_second_finite (b : Charge D) (f : ModuleHom J K) (I : Fields D M)
    (h u v : Carrier D) (p m : ℤ) (τ : ℚ)
    (hf : Function.HasFiniteSupport (secondTerm D b I h u v p m τ)) :
    Function.HasFiniteSupport (secondTerm D b (rawPost f.linearMap I) h u v p m τ) :=
  hf.subset (post_second_support b f I h u v p m τ)

/-- Full postcomposition law: no law of the mapped endpoint is assumed. -/
theorem lawful_post (a b : Charge D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (f : ModuleHom J K) (I : Fields D M) (hI : Lawful D a b H J I) :
    Lawful D a b H K (rawPost f.linearMap I) where
  source u τ := by
    apply LinearMap.ext
    intro v
    have e := congrArg (fun A : Carrier D →ₗ[ℂ] M => f.linearMap (A v))
      (hI.source u τ)
    simpa only [rawPost_mode, LinearMap.smul_apply, map_smul] using e
  target u τ := by
    apply LinearMap.ext
    intro v
    have e := congrArg (fun A : Carrier D →ₗ[ℂ] M => f.linearMap (A v))
      (hI.target u τ)
    simpa only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      rawPost_mode, map_sub, map_smul, map_targetTranslation] using e
  jacobi h u v p m τ := by
    have hj := hI.jacobi h u v p m τ
    refine ⟨post_left_finite a f I h u v p m τ hj.1,
      post_first_finite f I h u v p m τ hj.2.1,
      post_second_finite b f I h u v p m τ hj.2.2.1, ?_⟩
    have e := congrArg f.linearMap hj.2.2.2
    rw [map_sub, map_finsum f.linearMap hj.1,
      map_finsum f.linearMap hj.2.1, map_finsum f.linearMap hj.2.2.1] at e
    simpa only [post_leftTerm, post_firstTerm, post_secondTerm] using e

/-- The lawful-field target functor is literal coefficientwise postcomposition. -/
def post (a b : Charge D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (f : ModuleHom J K) : operatorSpace D a b H J →ₗ[ℂ] operatorSpace D a b H K where
  toFun I := ⟨rawPost f.linearMap I.val, lawful_post a b H f I.val I.property⟩
  map_add' I Q := Subtype.ext ((rawPost f.linearMap).map_add I.val Q.val)
  map_smul' c I := Subtype.ext ((rawPost f.linearMap).map_smul c I.val)

@[simp] theorem post_coeff (a b : Charge D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (f : ModuleHom J K) (I : operatorSpace D a b H J) (u v : Carrier D) (q : ℚ) :
    ((post a b H f I).val u).coeff q v = f.linearMap ((I.val u).coeff q v) := rfl

@[simp] theorem post_mode (a b : Charge D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (f : ModuleHom J K) (I : operatorSpace D a b H J) (u v : Carrier D) (τ : ℚ) :
    mode (post a b H f I).val u τ v = f.linearMap (mode I.val u τ v) := rfl

/-- Every actual source state is retained in the morphism square. -/
theorem map_stateField_coeff (f : ModuleHom J K) (h : Carrier D) (x : M) (k : ℤ) :
    f.linearMap ((J.stateField h).coeff k x) =
      (K.stateField h).coeff k (f.linearMap x) := by
  simpa only [Modules.FullJacobiCurrentTransport.mode, VertexOperator.coeff_eq_ncoeff]
    using f.intertwines h (-k - 1) x

theorem post_source_action (a b : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (f : ModuleHom J K)
    (I : operatorSpace D a b H J) (h u v : Carrier D) (n : ℤ) (τ : ℚ) :
    mode (post a b H f I).val (((action D a h)[[n]]) u) τ v =
      f.linearMap (mode I.val (((action D a h)[[n]]) u) τ v) := rfl

theorem post_target_action (a b : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (f : ModuleHom J K)
    (I : operatorSpace D a b H J) (h u v : Carrier D) (n : ℤ) (τ : ℚ) :
    ((K.stateField h)[[n]]) (mode (post a b H f I).val u τ v) =
      f.linearMap (((J.stateField h)[[n]]) (mode I.val u τ v)) :=
  (f.intertwines h n (mode I.val u τ v)).symm

@[simp] theorem post_id (a b : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    post a b H (ModuleHom.id J) = LinearMap.id := by
  apply LinearMap.ext
  intro I
  apply Subtype.ext
  exact rawPost_id I.val

theorem post_comp (a b : Charge D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (g : ModuleHom K L) (f : ModuleHom J K) :
    post a b H (g.comp f) = (post a b H g).comp (post a b H f) := by
  apply LinearMap.ext
  intro I
  apply Subtype.ext
  exact rawPost_comp g.linearMap f.linearMap I.val

@[simp] theorem post_zero (a b : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    post a b H (ModuleHom.zero J K) = 0 := by
  apply LinearMap.ext
  intro I
  apply Subtype.ext
  exact rawPost_zero I.val

theorem post_add (a b : Charge D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (f g : ModuleHom J K) :
    post a b H (f.add g) = post a b H f + post a b H g := by
  apply LinearMap.ext
  intro I
  apply Subtype.ext
  exact rawPost_add f.linearMap g.linearMap I.val

theorem post_smul (a b : Charge D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (c : ℂ) (f : ModuleHom J K) :
    post a b H (ModuleHom.smul c f) = c • post a b H f := by
  apply LinearMap.ext
  intro I
  apply Subtype.ext
  exact rawPost_smul c f.linearMap I.val

/-- Full isomorphisms induce actual linear equivalences on all lawful fields.
Both inverse laws are proved coefficientwise, with no law assumption on images. -/
def isoPost (a b : Charge D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (e : ModuleIso J K) : operatorSpace D a b H J ≃ₗ[ℂ] operatorSpace D a b H K where
  toLinearMap := post a b H e.hom
  invFun := post a b H e.inv
  left_inv I := by
    apply Subtype.ext
    apply fields_ext
    intro u v q
    change e.linearEquiv.symm (e.linearEquiv ((I.val u).coeff q v)) = _
    exact e.linearEquiv.symm_apply_apply _
  right_inv I := by
    apply Subtype.ext
    apply fields_ext
    intro u v q
    change e.linearEquiv (e.linearEquiv.symm ((I.val u).coeff q v)) = _
    exact e.linearEquiv.apply_symm_apply _

@[simp] theorem isoPost_coeff (a b : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (e : ModuleIso J K)
    (I : operatorSpace D a b H J) (u v : Carrier D) (q : ℚ) :
    ((isoPost a b H e I).val u).coeff q v = e.linearEquiv ((I.val u).coeff q v) := rfl

@[simp] theorem isoPost_inverse_coeff (a b : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (e : ModuleIso J K)
    (I : operatorSpace D a b H K) (u v : Carrier D) (q : ℚ) :
    (((isoPost a b H e).symm I).val u).coeff q v =
      e.linearEquiv.symm ((I.val u).coeff q v) := rfl

/-- Naturality includes every actual target state and every rational IO mode. -/
theorem isoPost_natural (a b : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (e : ModuleIso J K)
    (I : operatorSpace D a b H J) (h u v : Carrier D) (n : ℤ) (τ : ℚ) :
    ((K.stateField h)[[n]]) (mode (isoPost a b H e I).val u τ v) =
      e.linearEquiv (((J.stateField h)[[n]]) (mode I.val u τ v)) :=
  (e.intertwines h n (mode I.val u τ v)).symm

theorem isoPost_inverse_natural (a b : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (e : ModuleIso J K)
    (I : operatorSpace D a b H K) (h u v : Carrier D) (n : ℤ) (τ : ℚ) :
    ((J.stateField h)[[n]]) (mode ((isoPost a b H e).symm I).val u τ v) =
      e.linearEquiv.symm (((K.stateField h)[[n]]) (mode I.val u τ v)) :=
  (e.inverse_intertwines h n (mode I.val u τ v)).symm

@[simp] theorem isoPost_left_inverse (a b : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (e : ModuleIso J K)
    (I : operatorSpace D a b H J) :
    (isoPost a b H e).symm (isoPost a b H e I) = I :=
  (isoPost a b H e).symm_apply_apply I

@[simp] theorem isoPost_right_inverse (a b : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (e : ModuleIso J K)
    (I : operatorSpace D a b H K) :
    isoPost a b H e ((isoPost a b H e).symm I) = I :=
  (isoPost a b H e).apply_symm_apply I

/-- The actual additive scalar sector, with the original complete module laws. -/
def scalarModule (D : LatticeData) (c : Charge D) :
    FullJacobiLatticeModule D (Carrier D) where
  stateField := action D c
  vacuum_field := module_vacuum D c
  borcherds := by
    intro h u v p q r
    change Function.HasFiniteSupport (moduleLeft D c p q r h u v) ∧
      Function.HasFiniteSupport (moduleFirst D c p q r h u v) ∧
      Function.HasFiniteSupport (moduleSecond D c p q r h u v) ∧ _
    exact module_borcherds D c h u v p q r

/-- Read back the literal original scalar predicate, including its signs,
three finite supports and both translation laws. No inverse-Gram hypothesis
is needed merely to identify these definitions. -/
theorem scalar_lawful_iff (D : LatticeData) (a b : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (I : Fields D (Carrier D)) :
    Lawful D a b H (scalarModule D (a + b)) I ↔
      LatticeDualCosetIntertwiner.Lawful D a b H I := by
  constructor
  · intro h
    refine ⟨h.source, ?_, ?_⟩
    · intro u τ
      simpa only [targetTranslation, Modules.FullJacobiCurrentTransport.mode,
        scalarModule, moduleL, neg_add_cancel, mode, LatticeDualCosetIntertwiner.mode] using h.target u τ
    · intro h' u v p r τ
      exact h.jacobi h' u v p r τ
  · intro h
    refine ⟨h.source, ?_, ?_⟩
    · intro u τ
      simpa only [targetTranslation, Modules.FullJacobiCurrentTransport.mode,
        scalarModule, moduleL, neg_add_cancel, mode, LatticeDualCosetIntertwiner.mode] using h.target u τ
    · intro h' u v p r τ
      exact h.jacobi h' u v p r τ

/-- Identity on the entire field carrier, between the new and original spaces. -/
def scalarReadback (D : LatticeData) (a b : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    operatorSpace D a b H (scalarModule D (a + b)) ≃ₗ[ℂ]
      LatticeDualCosetIntertwiner.operatorSpace D a b H where
  toFun I := ⟨I.val, (scalar_lawful_iff D a b H I.val).mp I.property⟩
  invFun I := ⟨I.val, (scalar_lawful_iff D a b H I.val).mpr I.property⟩
  left_inv I := Subtype.ext rfl
  right_inv I := Subtype.ext rfl
  map_add' I Q := Subtype.ext rfl
  map_smul' c I := Subtype.ext rfl

@[simp] theorem scalarReadback_coeff (D : LatticeData) (a b : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (I : operatorSpace D a b H (scalarModule D (a + b)))
    (u v : Carrier D) (q : ℚ) :
    (((scalarReadback D a b H) I).val u).coeff q v = (I.val u).coeff q v := rfl

@[simp] theorem scalarReadback_inverse_coeff (D : LatticeData) (a b : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (I : LatticeDualCosetIntertwiner.operatorSpace D a b H)
    (u v : Carrier D) (q : ℚ) :
    ((((scalarReadback D a b H).symm I).val u).coeff q v) =
      (I.val u).coeff q v := rfl

/-- The original scalar equivalence, after the identity-on-fields readback.
Positivity and BOTH Gram inverse equations occur precisely where they occur
in the original scalar equivalence. They are unnecessary for postcomposition. -/
def scalarCoordinate (D : LatticeData) (hD : (gramReal D).PosDef)
    (a b : Charge D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (μ ν : Fin D.rank → ℚ)
    (ha : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (a i : ℚ))
    (hb : ∀ i, ∑ j, (D.G i j : ℚ) * ν j = (b i : ℚ)) :
    operatorSpace D a b H (scalarModule D (a + b)) ≃ₗ[ℂ] ℂ :=
  (scalarReadback D a b H).trans
    (LatticeDualCosetFusion.scalarEquiv D hD a b H hHG hGH μ ν ha hb)

theorem scalarCoordinate_apply (D : LatticeData) (hD : (gramReal D).PosDef)
    (a b : Charge D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (μ ν : Fin D.rank → ℚ)
    (ha : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (a i : ℚ))
    (hb : ∀ i, ∑ j, (D.G i j : ℚ) * ν j = (b i : ℚ))
    (I : operatorSpace D a b H (scalarModule D (a + b))) :
    scalarCoordinate D hD a b H hHG hGH μ ν ha hb I =
      LatticeDualCosetIntertwiner.groundScalar D I.val μ ν 0 0 := rfl

end
end D5.S3.VertexAlgebra.Sectors.ActualWeakTargetFullIntertwiner
