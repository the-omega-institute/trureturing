/-
IMPLEMENTATION SOURCE CANDIDATE. ACTIVE / INCOMPLETE; no compiler was run.
The imported suppliers are independently native accepted in the exact final99
closure even where their inherited opening comments say source-only.

Actual arbitrary source, input, and target weak modules. No positive Gram,
nonzero/rank, grading, dimension, semisimplicity, or common-support premise.
The rational mode is raw coefficient (-tau-1). Each translation is the actual
omega(D,H) zero mode. The Jacobi signs and three families are literally those
of ActualWeakTargetFullIntertwiner, with both sector actions generalized.

Attribution: the accepted full-law supplier and Scott Carnahan's Hahn API;
Bakalov--Kac math/0402315v1 section 4.1 and Kalle Kytölä's Sugawara calculus.
No sector-pair native21855 implementation or Pro90265 output was inspected.
-/
import D5.S3.VertexAlgebra.Sectors.ActualWeakTargetFullIntertwiner
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleHom

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleFullIntertwiner
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeActualConformalState LatticeSugawaraCurrents
open FullJacobiCurrentTransport (FullJacobiLatticeModule)
open FullJacobiIntertwiner (ModuleHom)
open Sectors.ActualWeakTargetFullIntertwiner
  (targetTranslation map_targetTranslation hahnPost seriesPost coefficient_support_post_subset)
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators VertexOperator Matrix
noncomputable section
universe uX uY uZ uX' uY' uZ' uX'' uY'' uZ''

abbrev Fields (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z] := X →ₗ[ℂ] HVertexOperator ℚ ℂ Y Z

variable {D : LatticeData}
variable {X : Type uX} {Y : Type uY} {Z : Type uZ}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable [AddCommGroup Z] [Module ℂ Z]
attribute [local instance] Classical.propDecidable

def mode (I : Fields X Y Z) (u : X) (τ : ℚ) : Y →ₗ[ℂ] Z :=
  (I u).coeff (-τ - 1)

def leftTerm (A : FullJacobiLatticeModule D X) (I : Fields X Y Z)
    (h : Carrier D) (u : X) (v : Y) (p r : ℤ) (τ : ℚ) (i : ℕ) : Z :=
  integerBinomial p i • mode I (((A.stateField h)[[r + i]]) u)
    ((p : ℚ) + τ - i) v

def firstTerm (J : FullJacobiLatticeModule D Z) (I : Fields X Y Z)
    (h : Carrier D) (u : X) (v : Y) (p r : ℤ) (τ : ℚ) (i : ℕ) : Z :=
  (((-1 : ℂ)^i) * integerBinomial r i) •
    ((J.stateField h)[[p + r - i]]) (mode I u (τ + i) v)

def secondTerm (B : FullJacobiLatticeModule D Y) (I : Fields X Y Z)
    (h : Carrier D) (u : X) (v : Y) (p r : ℤ) (τ : ℚ) (i : ℕ) : Z :=
  (((-1 : ℂ)^i) * integerBinomial r i) •
    (StateFieldResidueReconstruction.epsilon r •
      mode I u (τ + r - i) (((B.stateField h)[[p + i]]) v))

structure Lawful (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (I : Fields X Y Z) : Prop where
  source : ∀ u τ, mode I (targetTranslation A H u) τ =
    -(τ : ℂ) • mode I u (τ - 1)
  target : ∀ u τ, (targetTranslation J H).comp (mode I u τ) -
    (mode I u τ).comp (targetTranslation B H) = -(τ : ℂ) • mode I u (τ - 1)
  jacobi : ∀ h u v p r τ,
    Function.HasFiniteSupport (leftTerm A I h u v p r τ) ∧
    Function.HasFiniteSupport (firstTerm J I h u v p r τ) ∧
    Function.HasFiniteSupport (secondTerm B I h u v p r τ) ∧
      (∑ᶠ i : ℕ, leftTerm A I h u v p r τ i) =
        (∑ᶠ i : ℕ, firstTerm J I h u v p r τ i) -
          (∑ᶠ i : ℕ, secondTerm B I h u v p r τ i)

theorem lawful_zero (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : Lawful A B J H 0 where
  source u τ := by apply LinearMap.ext; intro v; simp [mode]
  target u τ := by apply LinearMap.ext; intro v; simp [mode]
  jacobi h u v p r τ := by
    simp [leftTerm, firstTerm, secondTerm, mode, Function.HasFiniteSupport, Function.support]

theorem lawful_add (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (I K : Fields X Y Z) (hI : Lawful A B J H I) (hK : Lawful A B J H K) :
    Lawful A B J H (I+K) where
  source u τ := by
    apply LinearMap.ext
    intro v
    have hi := congrArg (fun f : Y →ₗ[ℂ] Z => f v) (hI.source u τ)
    have hk := congrArg (fun f : Y →ₗ[ℂ] Z => f v) (hK.source u τ)
    simpa [mode, smul_add] using congrArg₂ (·+·) hi hk
  target u τ := by
    apply LinearMap.ext
    intro v
    have hi := congrArg (fun f : Y →ₗ[ℂ] Z => f v) (hI.target u τ)
    have hk := congrArg (fun f : Y →ₗ[ℂ] Z => f v) (hK.target u τ)
    simp only [mode, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      map_add, Pi.add_apply, LinearMap.add_apply, smul_add] at hi hk ⊢
    linear_combination (norm := module) hi + hk
  jacobi h u v p r τ := by
    have hi := hI.jacobi h u v p r τ
    have hk := hK.jacobi h u v p r τ
    have hl : leftTerm A (I+K) h u v p r τ =
        leftTerm A I h u v p r τ + leftTerm A K h u v p r τ := by
      funext i; simp [leftTerm, mode, smul_add]
    have hf : firstTerm J (I+K) h u v p r τ =
        firstTerm J I h u v p r τ + firstTerm J K h u v p r τ := by
      funext i; simp [firstTerm, mode, smul_add]
    have hs : secondTerm B (I+K) h u v p r τ =
        secondTerm B I h u v p r τ + secondTerm B K h u v p r τ := by
      funext i; simp [secondTerm, mode, smul_add]
    rw [hl, hf, hs]
    refine ⟨hi.1.add hk.1, hi.2.1.add hk.2.1, hi.2.2.1.add hk.2.2.1, ?_⟩
    simp only [Pi.add_apply]
    rw [finsum_add_distrib hi.1 hk.1, finsum_add_distrib hi.2.1 hk.2.1,
      finsum_add_distrib hi.2.2.1 hk.2.2.1, hi.2.2.2, hk.2.2.2]
    abel

theorem lawful_smul (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (c : ℂ) (I : Fields X Y Z) (hI : Lawful A B J H I) : Lawful A B J H (c • I) where
  source u τ := by
    apply LinearMap.ext
    intro v
    have hi := congrArg (fun f : Y →ₗ[ℂ] Z => f v) (hI.source u τ)
    simpa [mode, smul_comm c] using congrArg (c • ·) hi
  target u τ := by
    apply LinearMap.ext
    intro v
    have hi := congrArg (fun f : Y →ₗ[ℂ] Z => f v) (hI.target u τ)
    simpa [mode, ← smul_sub, smul_comm c] using congrArg (c • ·) hi
  jacobi h u v p r τ := by
    have hi := hI.jacobi h u v p r τ
    have hl : leftTerm A (c • I) h u v p r τ = c • leftTerm A I h u v p r τ := by
      funext i; simp [leftTerm, mode, smul_comm c]
    have hf : firstTerm J (c • I) h u v p r τ = c • firstTerm J I h u v p r τ := by
      funext i; simp [firstTerm, mode, smul_comm c]
    have hs : secondTerm B (c • I) h u v p r τ = c • secondTerm B I h u v p r τ := by
      funext i; simp [secondTerm, mode, smul_comm c]
    rw [hl, hf, hs]
    refine ⟨hi.1.smul_right (fun _ => c), hi.2.1.smul_right (fun _ => c),
      hi.2.2.1.smul_right (fun _ => c), ?_⟩
    simp only [Pi.smul_apply]
    rw [← smul_finsum' c hi.1, ← smul_finsum' c hi.2.1,
      ← smul_finsum' c hi.2.2.1, hi.2.2.2, smul_sub]

/-- The natural complex submodule of fields satisfying the actual full laws. -/
def operatorSpace (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (J : FullJacobiLatticeModule D Z) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : Submodule ℂ (Fields X Y Z) where
  carrier := {I | Lawful A B J H I}
  zero_mem' := lawful_zero A B J H
  add_mem' := fun hi hk => lawful_add A B J H _ _ hi hk
  smul_mem' := fun c _ hi => lawful_smul A B J H c _ hi

/-- Extensionality at every raw rational coefficient, on both actual inputs. -/
theorem fields_ext {I Q : Fields X Y Z}
    (h : ∀ (u : X) (v : Y) (q : ℚ), (I u).coeff q v = (Q u).coeff q v) : I = Q := by
  apply LinearMap.ext
  intro u
  apply HVertexOperator.coeff_inj
  funext q
  apply LinearMap.ext
  intro v
  exact h u v q

variable {X' : Type uX'} {Y' : Type uY'} {Z' : Type uZ'}
variable [AddCommGroup X'] [Module ℂ X'] [AddCommGroup Y'] [Module ℂ Y']
variable [AddCommGroup Z'] [Module ℂ Z']

/-- Transport complete pointwise Hahn series. The only coefficient image
construction is the accepted public hahnPost; restrictions are composition. -/
def rawMap (f : X' →ₗ[ℂ] X) (g : Y' →ₗ[ℂ] Y) (k : Z →ₗ[ℂ] Z') :
    Fields X Y Z →ₗ[ℂ] Fields X' Y' Z' where
  toFun I :=
    { toFun u := ((hahnPost k).comp (I (f u))).comp g
      map_add' u w := by
        apply LinearMap.ext
        intro v
        simp only [LinearMap.comp_apply, map_add, LinearMap.add_apply]
      map_smul' c u := by
        apply LinearMap.ext
        intro v
        simp only [LinearMap.comp_apply, map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  map_add' I Q := by
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    exact map_add (hahnPost k) (I (f u) (g v)) (Q (f u) (g v))
  map_smul' c I := by
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    exact (hahnPost k).map_smul c (I (f u) (g v))

theorem rawMap_series (f : X' →ₗ[ℂ] X) (g : Y' →ₗ[ℂ] Y) (k : Z →ₗ[ℂ] Z')
    (I : Fields X Y Z) (u : X') (v : Y') :
    (HahnModule.of ℂ).symm (rawMap f g k I u v) =
      seriesPost k ((HahnModule.of ℂ).symm (I (f u) (g v))) := by
  change (HahnModule.of ℂ).symm ((HahnModule.of ℂ) _) = _
  exact (HahnModule.of ℂ).symm_apply_apply _

@[simp] theorem rawMap_coeff (f : X' →ₗ[ℂ] X) (g : Y' →ₗ[ℂ] Y)
    (k : Z →ₗ[ℂ] Z') (I : Fields X Y Z) (u : X') (v : Y') (q : ℚ) :
    ((rawMap f g k I) u).coeff q v = k ((I (f u)).coeff q (g v)) := by
  change ((HahnModule.of ℂ).symm (rawMap f g k I u v)).coeff q = _
  rw [rawMap_series]
  rfl

@[simp] theorem rawMap_mode (f : X' →ₗ[ℂ] X) (g : Y' →ₗ[ℂ] Y)
    (k : Z →ₗ[ℂ] Z') (I : Fields X Y Z) (u : X') (v : Y') (τ : ℚ) :
    mode (rawMap f g k I) u τ v = k (mode I (f u) τ (g v)) :=
  rawMap_coeff f g k I u v (-τ - 1)

/-- The old support is evaluated at the actual mapped vectors f u and g v.
No global truncation or injectivity is used, including when one map is zero. -/
theorem rawMap_support_subset (f : X' →ₗ[ℂ] X) (g : Y' →ₗ[ℂ] Y)
    (k : Z →ₗ[ℂ] Z') (I : Fields X Y Z) (u : X') (v : Y') :
    Function.support (fun q => ((rawMap f g k I) u).coeff q v) ⊆
      Function.support (fun q => (I (f u)).coeff q (g v)) := by
  simpa only [rawMap_coeff] using
    coefficient_support_post_subset k (fun q => (I (f u)).coeff q (g v))

theorem rawMap_isPWO (f : X' →ₗ[ℂ] X) (g : Y' →ₗ[ℂ] Y)
    (k : Z →ₗ[ℂ] Z') (I : Fields X Y Z) (u : X') (v : Y') :
    (Function.support (fun q => ((rawMap f g k I) u).coeff q v)).IsPWO :=
  ((I (f u)).isPWO_support_coeff (g v)).mono (rawMap_support_subset f g k I u v)

variable {A : FullJacobiLatticeModule D X} {B : FullJacobiLatticeModule D Y}
variable {J : FullJacobiLatticeModule D Z}
variable {A' : FullJacobiLatticeModule D X'} {B' : FullJacobiLatticeModule D Y'}
variable {J' : FullJacobiLatticeModule D Z'}

/-- Three separate support proofs appear before the first map_finsum.
Source and input squares use their full original ModuleHom law. -/
theorem lawful_map (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (f : ModuleHom A' A) (g : ModuleHom B' B) (k : ModuleHom J J')
    (I : Fields X Y Z) (hI : Lawful A B J H I) :
    Lawful A' B' J' H (rawMap f.linearMap g.linearMap k.linearMap I) where
  source u τ := by
    apply LinearMap.ext
    intro v
    have e := congrArg (fun T : Y →ₗ[ℂ] Z => k.linearMap (T (g.linearMap v)))
      (hI.source (f.linearMap u) τ)
    simpa only [rawMap_mode, map_targetTranslation, LinearMap.smul_apply, map_smul]
      using e
  target u τ := by
    apply LinearMap.ext
    intro v
    have e := congrArg (fun T : Y →ₗ[ℂ] Z => k.linearMap (T (g.linearMap v)))
      (hI.target (f.linearMap u) τ)
    simpa only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      rawMap_mode, map_sub, map_smul, map_targetTranslation] using e
  jacobi h u v p r τ := by
    have hj := hI.jacobi h (f.linearMap u) (g.linearMap v) p r τ
    have eL (i : ℕ) :
        leftTerm A' (rawMap f.linearMap g.linearMap k.linearMap I) h u v p r τ i =
          k.linearMap (leftTerm A I h (f.linearMap u) (g.linearMap v) p r τ i) := by
      simp only [leftTerm, rawMap_mode, map_smul]
      exact congrArg (fun x : X => integerBinomial p i •
        k.linearMap (mode I x ((p : ℚ) + τ - i) (g.linearMap v)))
        (f.intertwines h (r + i) u)
    have eF (i : ℕ) :
        firstTerm J' (rawMap f.linearMap g.linearMap k.linearMap I) h u v p r τ i =
          k.linearMap (firstTerm J I h (f.linearMap u) (g.linearMap v) p r τ i) := by
      simp only [firstTerm, rawMap_mode, map_smul]
      exact congrArg (fun x : Z' => (((-1 : ℂ)^i) * integerBinomial r i) • x)
        (k.intertwines h (p + r - i)
          (mode I (f.linearMap u) (τ + i) (g.linearMap v))).symm
    have eS (i : ℕ) :
        secondTerm B' (rawMap f.linearMap g.linearMap k.linearMap I) h u v p r τ i =
          k.linearMap (secondTerm B I h (f.linearMap u) (g.linearMap v) p r τ i) := by
      simp only [secondTerm, rawMap_mode, map_smul]
      exact congrArg (fun y : Y => (((-1 : ℂ)^i) * integerBinomial r i) •
        (StateFieldResidueReconstruction.epsilon r •
          k.linearMap (mode I (f.linearMap u) (τ + r - i) y)))
        (g.intertwines h (p + i) v)
    have sL : Function.support
        (leftTerm A' (rawMap f.linearMap g.linearMap k.linearMap I) h u v p r τ) ⊆
        Function.support (leftTerm A I h (f.linearMap u) (g.linearMap v) p r τ) := by
      intro i hi hz
      apply hi
      rw [eL, hz, map_zero]
    have sF : Function.support
        (firstTerm J' (rawMap f.linearMap g.linearMap k.linearMap I) h u v p r τ) ⊆
        Function.support (firstTerm J I h (f.linearMap u) (g.linearMap v) p r τ) := by
      intro i hi hz
      apply hi
      rw [eF, hz, map_zero]
    have sS : Function.support
        (secondTerm B' (rawMap f.linearMap g.linearMap k.linearMap I) h u v p r τ) ⊆
        Function.support (secondTerm B I h (f.linearMap u) (g.linearMap v) p r τ) := by
      intro i hi hz
      apply hi
      rw [eS, hz, map_zero]
    have hL := hj.1.subset sL
    have hF := hj.2.1.subset sF
    have hS := hj.2.2.1.subset sS
    refine ⟨hL, hF, hS, ?_⟩
    have e := congrArg k.linearMap hj.2.2.2
    rw [map_sub, map_finsum k.linearMap hj.1,
      map_finsum k.linearMap hj.2.1, map_finsum k.linearMap hj.2.2.1] at e
    simpa only [eL, eF, eS] using e

/-- Lawful transport on the genuine submodules, with no law assumption on
an image and no injectivity assumption on any of the three morphisms. -/
def map (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (f : ModuleHom A' A) (g : ModuleHom B' B) (k : ModuleHom J J') :
    operatorSpace A B J H →ₗ[ℂ] operatorSpace A' B' J' H where
  toFun I := ⟨rawMap f.linearMap g.linearMap k.linearMap I.val,
    lawful_map H f g k I.val I.property⟩
  map_add' I Q := Subtype.ext ((rawMap f.linearMap g.linearMap k.linearMap).map_add I.val Q.val)
  map_smul' c I := Subtype.ext ((rawMap f.linearMap g.linearMap k.linearMap).map_smul c I.val)

@[simp] theorem map_coeff (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (f : ModuleHom A' A) (g : ModuleHom B' B) (k : ModuleHom J J')
    (I : operatorSpace A B J H) (u : X') (v : Y') (q : ℚ) :
    (((map H f g k I).val) u).coeff q v =
      k.linearMap ((I.val (f.linearMap u)).coeff q (g.linearMap v)) :=
  rawMap_coeff f.linearMap g.linearMap k.linearMap I.val u v q

@[simp] theorem map_mode (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (f : ModuleHom A' A) (g : ModuleHom B' B) (k : ModuleHom J J')
    (I : operatorSpace A B J H) (u : X') (v : Y') (τ : ℚ) :
    mode (map H f g k I).val u τ v =
      k.linearMap (mode I.val (f.linearMap u) τ (g.linearMap v)) :=
  map_coeff H f g k I u v (-τ - 1)

/-- Readback of the support and PWO evidence on the actual lawful image.
The two clauses refer to the same full pointwise Hahn field. -/
theorem map_support (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (f : ModuleHom A' A) (g : ModuleHom B' B) (k : ModuleHom J J')
    (I : operatorSpace A B J H) (u : X') (v : Y') :
    Function.support (fun q => (((map H f g k I).val) u).coeff q v) ⊆
        Function.support (fun q => (I.val (f.linearMap u)).coeff q (g.linearMap v)) ∧
      (Function.support (fun q => (((map H f g k I).val) u).coeff q v)).IsPWO :=
  ⟨rawMap_support_subset f.linearMap g.linearMap k.linearMap I.val u v,
    rawMap_isPWO f.linearMap g.linearMap k.linearMap I.val u v⟩

@[simp] theorem map_id (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    map H (ModuleHom.id A) (ModuleHom.id B) (ModuleHom.id J) = LinearMap.id := by
  apply LinearMap.ext
  intro I
  apply Subtype.ext
  apply fields_ext
  intro u v q
  rfl

variable {X'' : Type uX''} {Y'' : Type uY''} {Z'' : Type uZ''}
variable [AddCommGroup X''] [Module ℂ X''] [AddCommGroup Y''] [Module ℂ Y'']
variable [AddCommGroup Z''] [Module ℂ Z'']
variable {A'' : FullJacobiLatticeModule D X''} {B'' : FullJacobiLatticeModule D Y''}
variable {J'' : FullJacobiLatticeModule D Z''}

theorem map_comp (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (f : ModuleHom A' A) (g : ModuleHom B' B) (k : ModuleHom J J')
    (f' : ModuleHom A'' A') (g' : ModuleHom B'' B') (k' : ModuleHom J' J'') :
    map H (f.comp f') (g.comp g') (k'.comp k) =
      (map H f' g' k').comp (map H f g k) := by
  apply LinearMap.ext
  intro I
  apply Subtype.ext
  apply fields_ext
  intro u v q
  rfl

/-- Source restriction, input restriction, and target postcomposition are
special cases of the proved full lawful transport. -/
def source (B : FullJacobiLatticeModule D Y) (J : FullJacobiLatticeModule D Z)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (f : ModuleHom A' A) :
    operatorSpace A B J H →ₗ[ℂ] operatorSpace A' B J H :=
  map H f (ModuleHom.id B) (ModuleHom.id J)

def input (A : FullJacobiLatticeModule D X) (J : FullJacobiLatticeModule D Z)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (g : ModuleHom B' B) :
    operatorSpace A B J H →ₗ[ℂ] operatorSpace A B' J H :=
  map H (ModuleHom.id A) g (ModuleHom.id J)

def post (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (k : ModuleHom J J') :
    operatorSpace A B J H →ₗ[ℂ] operatorSpace A B J' H :=
  map H (ModuleHom.id A) (ModuleHom.id B) k

theorem source_input_interchange (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (f : ModuleHom A' A) (g : ModuleHom B' B) :
    (input A' J H g).comp (source B J H f) =
      (source B' J H f).comp (input A J H g) := by
  unfold source input
  rw [← map_comp, ← map_comp]
  rfl

theorem source_target_interchange (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (f : ModuleHom A' A) (k : ModuleHom J J') :
    (post A' B H k).comp (source B J H f) =
      (source B J' H f).comp (post A B H k) := by
  unfold source post
  rw [← map_comp, ← map_comp]
  rfl

theorem input_target_interchange (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (g : ModuleHom B' B) (k : ModuleHom J J') :
    (post A B' H k).comp (input A J H g) =
      (input A J' H g).comp (post A B H k) := by
  unfold input post
  rw [← map_comp, ← map_comp]
  rfl

/-- Bilinear dependence on actual source/input morphisms, using the accepted
faithful Hom submodule rather than introducing a second morphism record.
Its map_add/map_smul laws are the descent API for arbitrary multiplicities. -/
def restrictionLinear (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    ActualWeakModuleHom.homSpace A' A →ₗ[ℂ]
      ActualWeakModuleHom.homSpace B' B →ₗ[ℂ]
        operatorSpace A B J H →ₗ[ℂ] operatorSpace A' B' J H where
  toFun f :=
    { toFun g := map H ((ActualWeakModuleHom.recordEquiv A' A).symm f)
        ((ActualWeakModuleHom.recordEquiv B' B).symm g) (ModuleHom.id J)
      map_add' g g' := by
        apply LinearMap.ext
        intro I
        apply Subtype.ext
        apply fields_ext
        intro u v q
        change (I.val (f.val u)).coeff q (g.val v + g'.val v) =
          (I.val (f.val u)).coeff q (g.val v) +
            (I.val (f.val u)).coeff q (g'.val v)
        exact map_add ((I.val (f.val u)).coeff q) (g.val v) (g'.val v)
      map_smul' c g := by
        apply LinearMap.ext
        intro I
        apply Subtype.ext
        apply fields_ext
        intro u v q
        change (I.val (f.val u)).coeff q (c • g.val v) =
          c • (I.val (f.val u)).coeff q (g.val v)
        exact ((I.val (f.val u)).coeff q).map_smul c (g.val v) }
  map_add' f f' := by
    apply LinearMap.ext
    intro g
    apply LinearMap.ext
    intro I
    apply Subtype.ext
    apply fields_ext
    intro u v q
    change (I.val (f.val u + f'.val u)).coeff q (g.val v) =
      (I.val (f.val u)).coeff q (g.val v) +
        (I.val (f'.val u)).coeff q (g.val v)
    simp only [map_add, Pi.add_apply, LinearMap.add_apply]
  map_smul' c f := by
    apply LinearMap.ext
    intro g
    apply LinearMap.ext
    intro I
    apply Subtype.ext
    apply fields_ext
    intro u v q
    change (I.val (c • f.val u)).coeff q (g.val v) =
      c • (I.val (f.val u)).coeff q (g.val v)
    simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply]

/-- Linear dependence on the actual target morphism, independently of the
operator's own linearity, and without finite-dimensional multiplicities. -/
def postLinear (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    ActualWeakModuleHom.homSpace J J' →ₗ[ℂ]
      operatorSpace A B J H →ₗ[ℂ] operatorSpace A B J' H where
  toFun k := post A B H ((ActualWeakModuleHom.recordEquiv J J').symm k)
  map_add' k k' := by
    apply LinearMap.ext
    intro I
    apply Subtype.ext
    apply fields_ext
    intro u v q
    rfl
  map_smul' c k := by
    apply LinearMap.ext
    intro I
    apply Subtype.ext
    apply fields_ext
    intro u v q
    rfl
/-- The linear/bilinear descent operators act by the same complete-Hahn map,
not merely by an equality after dual evaluation. -/
theorem descent_coeff (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (f : ActualWeakModuleHom.homSpace A' A) (g : ActualWeakModuleHom.homSpace B' B)
    (k : ActualWeakModuleHom.homSpace J J') (I : operatorSpace A B J H)
    (u : X') (v : Y') (q : ℚ) :
    (((postLinear (A := A') (B := B') H k
      (restrictionLinear (J := J) H f g I)).val) u).coeff q v =
        k.val ((I.val (f.val u)).coeff q (g.val v)) := by
  rw [show postLinear (A := A') (B := B') H k =
      post A' B' H ((ActualWeakModuleHom.recordEquiv J J').symm k) by rfl]
  simp only [post, map_coeff, ModuleHom.id, LinearMap.id_apply]
  rfl

/-- This identity identifies the simultaneous lawful transport with the
linear and bilinear operators used for multiplicity descent. -/
theorem map_eq_descent (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (f : ModuleHom A' A) (g : ModuleHom B' B) (k : ModuleHom J J') :
    map H f g k =
      (postLinear (A := A') (B := B') H (ActualWeakModuleHom.recordEquiv J J' k)).comp
        (restrictionLinear (J := J) H (ActualWeakModuleHom.recordEquiv A' A f)
          (ActualWeakModuleHom.recordEquiv B' B g)) := by
  apply LinearMap.ext
  intro I
  apply Subtype.ext
  apply fields_ext
  intro u v q
  exact (descent_coeff H (ActualWeakModuleHom.recordEquiv A' A f)
    (ActualWeakModuleHom.recordEquiv B' B g)
    (ActualWeakModuleHom.recordEquiv J J' k) I u v q).symm

/-- The compatibility bridge reuses the already accepted scalarModule for
both input slots. It is only identification of the literal existing law. -/
theorem sector_lawful_iff (a b : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (J : FullJacobiLatticeModule D Z)
    (I : Fields (Carrier D) (Carrier D) Z) :
    Lawful (Sectors.ActualWeakTargetFullIntertwiner.scalarModule D a)
      (Sectors.ActualWeakTargetFullIntertwiner.scalarModule D b) J H I ↔
        Sectors.ActualWeakTargetFullIntertwiner.Lawful D a b H J I := by
  constructor
  · intro hi
    refine ⟨?_, ?_, ?_⟩
    · intro u τ
      simpa only [targetTranslation, FullJacobiCurrentTransport.mode,
        Sectors.ActualWeakTargetFullIntertwiner.scalarModule,
        LatticeDualCosetConformal.moduleL, neg_add_cancel,
        mode, Sectors.ActualWeakTargetFullIntertwiner.mode] using hi.source u τ
    · intro u τ
      simpa only [targetTranslation, FullJacobiCurrentTransport.mode,
        Sectors.ActualWeakTargetFullIntertwiner.scalarModule,
        LatticeDualCosetConformal.moduleL, neg_add_cancel,
        mode, Sectors.ActualWeakTargetFullIntertwiner.mode] using hi.target u τ
    · intro h u v p r τ
      exact hi.jacobi h u v p r τ
  · intro hi
    refine ⟨?_, ?_, ?_⟩
    · intro u τ
      simpa only [targetTranslation, FullJacobiCurrentTransport.mode,
        Sectors.ActualWeakTargetFullIntertwiner.scalarModule,
        LatticeDualCosetConformal.moduleL, neg_add_cancel,
        mode, Sectors.ActualWeakTargetFullIntertwiner.mode] using hi.source u τ
    · intro u τ
      simpa only [targetTranslation, FullJacobiCurrentTransport.mode,
        Sectors.ActualWeakTargetFullIntertwiner.scalarModule,
        LatticeDualCosetConformal.moduleL, neg_add_cancel,
        mode, Sectors.ActualWeakTargetFullIntertwiner.mode] using hi.target u τ
    · intro h u v p r τ
      exact hi.jacobi h u v p r τ

/-- Identity on entire raw fields, with both lawful submodule directions. -/
def sectorReadback (a b : Charge D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (J : FullJacobiLatticeModule D Z) :
    operatorSpace (Sectors.ActualWeakTargetFullIntertwiner.scalarModule D a)
      (Sectors.ActualWeakTargetFullIntertwiner.scalarModule D b) J H ≃ₗ[ℂ]
        Sectors.ActualWeakTargetFullIntertwiner.operatorSpace D a b H J where
  toFun I := ⟨I.val, (sector_lawful_iff a b H J I.val).mp I.property⟩
  invFun I := ⟨I.val, (sector_lawful_iff a b H J I.val).mpr I.property⟩
  left_inv I := Subtype.ext rfl
  right_inv I := Subtype.ext rfl
  map_add' I Q := Subtype.ext rfl
  map_smul' c I := Subtype.ext rfl

/-- Compatibility of the actual lawful maps, before any ground projection. -/
theorem sectorReadback_post (a b : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (k : ModuleHom J J') :
    (sectorReadback a b H J').toLinearMap.comp
        (post (Sectors.ActualWeakTargetFullIntertwiner.scalarModule D a)
          (Sectors.ActualWeakTargetFullIntertwiner.scalarModule D b) H k) =
      (Sectors.ActualWeakTargetFullIntertwiner.post a b H k).comp
        (sectorReadback a b H J).toLinearMap := by
  apply LinearMap.ext
  intro I
  apply Subtype.ext
  apply fields_ext
  intro u v q
  rfl

/-- Exact canonical raw-field compatibility. All positivity and inverse-Gram
premises here are solely the existing canonical supplier's premises; none
occur in the arbitrary-module laws, support transport, or functoriality. -/
theorem sectorReadback_canonical_raw (D : LatticeData)
    (hD : (LatticeDiscriminantTheta.gramReal D).PosDef)
    (a b : Charge D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    ((sectorReadback a b H
      (Sectors.ActualWeakTargetFullIntertwiner.scalarModule D (a + b))).symm
      ((Sectors.ActualWeakTargetFullIntertwiner.scalarReadback D a b H).symm
        (LatticeDualCosetFusion.canonicalOperator D hD a b H hHG hGH))).val =
      LatticeCosetCanonicalIntertwiner.intertwiner D (1 : Matrix _ _ ℤ) a b := rfl

end
end D5.S3.VertexAlgebra.Modules.ActualWeakModuleFullIntertwiner
