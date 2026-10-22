/- GID: D5/S3/VertexAlgebra/LatticeSectorFullFusion
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeSectorFullFusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Natural universal equivalence for the complete mixed-field subspace on finite sector sums. -/

import D5.S3.VertexAlgebra.LatticeSectorNaturalFusion

/-!
Coordinate IO and the full mixed-target coefficient subspace are equivalent.
All three global Jacobi supports and a statewise truncation bound are proved;
conversely the full laws project to the component laws. Thus the universal
consumer classifies every lawful mixed field on the actual finite-sum carrier.
-/

set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorIntertwiner
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators
noncomputable section
namespace FiniteSectorObject
variable (D : LatticeData)

abbrev FullCoefficients (α β : Charge D) (M : FiniteSectorObject D) :=
  Sector D α →ₗ[ℂ] (ℤ → (Sector D β →ₗ[ℂ] M.States D))

def coordinate (α β : Charge D) (M : FiniteSectorObject D)
    (F : FullCoefficients D α β M) (i : Fin M.size) : Coefficients D α β (M.charge i) where
  toFun u n := (LinearMap.proj i).comp (F u n)
  map_add' u v := by funext n; apply LinearMap.ext; intro w; simp
  map_smul' c u := by funext n; apply LinearMap.ext; intro w; simp

def fullLeft (α β : Charge D) (M : FiniteSectorObject D) (F : FullCoefficients D α β M)
    (a : Sector D 0) (u : Sector D α) (v : Sector D β) (p q r : ℤ) (i : ℕ) : M.States D :=
  integerBinomial p i • F (action D α a (r + i) u) (p + q - i) v

def fullFirst (α β : Charge D) (M : FiniteSectorObject D) (F : FullCoefficients D α β M)
    (a : Sector D 0) (u : Sector D α) (v : Sector D β) (p q r : ℤ) (i : ℕ) : M.States D :=
  (((-1 : ℂ)^i) * integerBinomial r i) • mode D M a (p + r - i) (F u (q + i) v)

def fullSecond (α β : Charge D) (M : FiniteSectorObject D) (F : FullCoefficients D α β M)
    (a : Sector D 0) (u : Sector D α) (v : Sector D β) (p q r : ℤ) (i : ℕ) : M.States D :=
  (((-1 : ℂ)^i) * integerBinomial r i) •
    (StateFieldResidueReconstruction.epsilon r • F u (q + r - i) (action D β a (p + i) v))

/-- Exactly the full mixed-target laws, without a uniform cutoff across states. -/
structure FullLawful (α β : Charge D) (M : FiniteSectorObject D)
    (F : FullCoefficients D α β M) : Prop where
  truncation : ∀ u v, ∃ N : ℤ, ∀ n : ℤ, N ≤ n → F u n v = 0
  source : ∀ u n, F (sectorT D α u) n = -(n : ℂ) • F u (n - 1)
  target : ∀ u n, (translation D M).comp (F u n) - (F u n).comp (sectorT D β) =
    -(n : ℂ) • F u (n - 1)
  jacobi : ∀ a u v p q r,
    Function.HasFiniteSupport (fullLeft D α β M F a u v p q r) ∧
    Function.HasFiniteSupport (fullFirst D α β M F a u v p q r) ∧
    Function.HasFiniteSupport (fullSecond D α β M F a u v p q r) ∧
      (∑ᶠ i : ℕ, fullLeft D α β M F a u v p q r i) =
        (∑ᶠ i : ℕ, fullFirst D α β M F a u v p q r i) -
          (∑ᶠ i : ℕ, fullSecond D α β M F a u v p q r i)

/-- Full finite-sum IO laws are equivalent to all component IO laws. -/
theorem fullLawful_iff (α β : Charge D) (M : FiniteSectorObject D)
    (F : FullCoefficients D α β M) :
    FullLawful D α β M F ↔ ∀ i, Lawful D α β (M.charge i) (coordinate D α β M F i) := by
  constructor
  · intro h i
    let P : M.States D →ₗ[ℂ] Sector D (M.charge i) := LinearMap.proj i
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u v
      obtain ⟨N, hN⟩ := h.truncation u v
      exact ⟨N, fun n hn => by simp [coordinate, hN n hn]⟩
    · intro u n
      apply LinearMap.ext; intro v
      exact congrArg (fun f : Sector D β →ₗ[ℂ] M.States D => P (f v)) (h.source u n)
    · intro u n
      apply LinearMap.ext; intro v
      exact congrArg (fun f : Sector D β →ₗ[ℂ] M.States D => P (f v)) (h.target u n)
    · intro a u v p q r
      have hi := h.jacobi a u v p q r
      have hl : leftTerm D α β (M.charge i) (coordinate D α β M F i) a u v p q r =
          fun j => P (fullLeft D α β M F a u v p q r j) := rfl
      have hf : firstTerm D α β (M.charge i) (coordinate D α β M F i) a u v p q r =
          fun j => P (fullFirst D α β M F a u v p q r j) := rfl
      have hs : secondTerm D α β (M.charge i) (coordinate D α β M F i) a u v p q r =
          fun j => P (fullSecond D α β M F a u v p q r j) := rfl
      rw [hl, hf, hs]
      refine ⟨hi.1.fun_comp (map_zero P), hi.2.1.fun_comp (map_zero P),
        hi.2.2.1.fun_comp (map_zero P), ?_⟩
      have e := congrArg P hi.2.2.2
      rw [map_sub, map_finsum P hi.1, map_finsum P hi.2.1, map_finsum P hi.2.2.1] at e
      exact e
  · intro h
    let I : Intertwiners D α β M := fun i => ⟨coordinate D α β M F i, h i⟩
    have restore : coefficients D α β M I = F := by
      apply LinearMap.ext; intro u; funext n; apply LinearMap.ext; intro v; rfl
    rw [← restore]
    exact ⟨coefficients_truncation D α β M I,
      fun u n => (coefficients_derivatives D α β M I u n).1,
      fun u n => (coefficients_derivatives D α β M I u n).2,
      coefficients_jacobi D α β M I⟩

/-- The subspace is the entire lawful mixed-field domain, in target coordinates. -/
def fullOperatorSpace (α β : Charge D) (M : FiniteSectorObject D) :
    Submodule ℂ (FullCoefficients D α β M) where
  carrier := {F | ∀ i, coordinate D α β M F i ∈ operatorSpace D α β (M.charge i)}
  zero_mem' := fun i => (operatorSpace D α β (M.charge i)).zero_mem
  add_mem' := by
    intro F G hF hG i
    have hc : coordinate D α β M (F + G) i =
        coordinate D α β M F i + coordinate D α β M G i := rfl
    rw [hc]
    exact (operatorSpace D α β (M.charge i)).add_mem (hF i) (hG i)
  smul_mem' := by
    intro c F hF i
    have hc : coordinate D α β M (c • F) i = c • coordinate D α β M F i := rfl
    rw [hc]
    exact (operatorSpace D α β (M.charge i)).smul_mem c (hF i)

abbrev FullIO (α β : Charge D) (M : FiniteSectorObject D) := fullOperatorSpace D α β M

/-- An explicit linear equivalence between complete target fields and coordinates. -/
def fullIOEquiv (α β : Charge D) (M : FiniteSectorObject D) :
    Intertwiners D α β M ≃ₗ[ℂ] FullIO D α β M where
  toFun I := ⟨coefficients D α β M I, fun i => (I i).property⟩
  invFun F i := ⟨coordinate D α β M F.val i, F.property i⟩
  left_inv I := by funext i; apply Subtype.ext; rfl
  right_inv F := by
    apply Subtype.ext; apply LinearMap.ext; intro u; funext n
    apply LinearMap.ext; intro v; rfl
  map_add' I K := rfl
  map_smul' c I := rfl

/-- Every member satisfies actual full-carrier truncation, derivatives and Jacobi. -/
theorem fullIO_lawful (α β : Charge D) (M : FiniteSectorObject D) (I : FullIO D α β M) :
    FullLawful D α β M I.val := (fullLawful_iff D α β M I.val).mpr I.property

/-- Genuine fusion representation on the entire mixed-target IO subspace. -/
def fullUniversal (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β : Charge D) (M : FiniteSectorObject D) :
    Incoming D (α + β) M ≃ₗ[ℂ] FullIO D α β M :=
  (universal D H hHG hGH α β M).trans (fullIOEquiv D α β M)

/-- Its forward direction is precisely actual postcomposition with J. -/
theorem fullUniversal_apply (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β : Charge D) (M : FiniteSectorObject D) (f : Incoming D (α + β) M)
    (u : Sector D α) (v : Sector D β) (n : ℤ) :
    (fullUniversal D H hHG hGH α β M f).val u n v = f.val (canonical D α β u n v) := rfl

/-- The target-map action is actual coefficient postcomposition. -/
def fullPost (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β : Charge D) {M N : FiniteSectorObject D} (g : Hom D M N) :
    FullIO D α β M →ₗ[ℂ] FullIO D α β N :=
  (fullIOEquiv D α β N).toLinearMap.comp
    ((intertwinerPost D H hHG hGH α β g).comp (fullIOEquiv D α β M).symm.toLinearMap)

/-- Postcomposition agrees with the actual target map at every coefficient. -/
theorem fullPost_apply (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β : Charge D) {M N : FiniteSectorObject D} (g : Hom D M N)
    (I : FullIO D α β M) (u : Sector D α) (v : Sector D β) (n : ℤ) :
    (fullPost D H hHG hGH α β g I).val u n v = g.val (I.val u n v) :=
  intertwinerPost_coefficients D H hHG hGH α β g ((fullIOEquiv D α β M).symm I) u v n

/-- Naturality of the full universal linear equivalence. -/
theorem fullUniversal_natural (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β : Charge D) {M N : FiniteSectorObject D} (g : Hom D M N)
    (f : Incoming D (α + β) M) :
    fullUniversal D H hHG hGH α β N (incomingPost D (α + β) g f) =
      fullPost D H hHG hGH α β g (fullUniversal D H hHG hGH α β M f) := by
  apply Subtype.ext
  apply LinearMap.ext; intro u; funext n
  apply LinearMap.ext; intro v
  rw [fullUniversal_apply, fullPost_apply, fullUniversal_apply]
  rfl

end FiniteSectorObject
end
end D5.S3.VertexAlgebra.LatticeSectorIntertwiner
