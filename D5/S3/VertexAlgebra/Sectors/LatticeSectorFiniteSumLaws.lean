/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorFiniteSumLaws
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorFiniteSumLaws
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full statewise and supported Jacobi laws on actual finite-sum IO carriers. -/

import D5.S3.VertexAlgebra.Sectors.LatticeSectorCategory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorIntertwiner
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators
noncomputable section
namespace FiniteSectorObject
variable (D : LatticeData)

private theorem support_tuple {ι : Type} [Fintype ι] {X : ι → Type}
    [∀ i, Zero (X i)] (f : ℕ → ∀ i, X i)
    (h : ∀ i, Function.HasFiniteSupport (fun n => f n i)) :
    Function.HasFiniteSupport f := by
  apply (Set.finite_iUnion fun i => h i).subset
  intro n hn
  simp only [Set.mem_iUnion, Function.mem_support] at hn ⊢
  by_contra bad
  apply hn
  funext i
  by_contra hi
  exact bad ⟨i, hi⟩

/-- A finite coordinate family has a single statewise bound, even for an empty sum. -/
theorem coefficients_truncation (α β : Charge D) (M : FiniteSectorObject D)
    (I : Intertwiners D α β M) (u : Sector D α) (v : Sector D β) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → coefficients D α β M I u n v = 0 := by
  classical
  choose N hN using fun i => (I i).property.truncation u v
  refine ⟨(Finset.univ.sup fun i => (N i).toNat : ℕ), ?_⟩
  intro n hn
  funext i
  have bound : (N i).toNat ≤ Finset.univ.sup (fun i => (N i).toNat) :=
    Finset.le_sup (f := fun i => (N i).toNat) (Finset.mem_univ i)
  exact hN i n (by omega)

/-- Both derivatives hold as equalities of mixed maps into the entire sum. -/
theorem coefficients_derivatives (α β : Charge D) (M : FiniteSectorObject D)
    (I : Intertwiners D α β M) (u : Sector D α) (n : ℤ) :
    coefficients D α β M I (sectorT D α u) n =
        -(n : ℂ) • coefficients D α β M I u (n - 1) ∧
      (translation D M).comp (coefficients D α β M I u n) -
        (coefficients D α β M I u n).comp (sectorT D β) =
          -(n : ℂ) • coefficients D α β M I u (n - 1) := by
  constructor
  · apply LinearMap.ext; intro v; funext i
    exact congrArg (fun f : Sector D β →ₗ[ℂ] Sector D (M.charge i) => f v)
      ((I i).property.source u n)
  · apply LinearMap.ext; intro v; funext i
    exact congrArg (fun f : Sector D β →ₗ[ℂ] Sector D (M.charge i) => f v)
      ((I i).property.target u n)

def sumLeft (α β : Charge D) (M : FiniteSectorObject D) (I : Intertwiners D α β M)
    (a : Sector D 0) (u : Sector D α) (v : Sector D β) (p q r : ℤ) (i : ℕ) : M.States D :=
  integerBinomial p i • coefficients D α β M I (action D α a (r + i) u) (p + q - i) v

def sumFirst (α β : Charge D) (M : FiniteSectorObject D) (I : Intertwiners D α β M)
    (a : Sector D 0) (u : Sector D α) (v : Sector D β) (p q r : ℤ) (i : ℕ) : M.States D :=
  (((-1 : ℂ)^i) * integerBinomial r i) •
    mode D M a (p + r - i) (coefficients D α β M I u (q + i) v)

def sumSecond (α β : Charge D) (M : FiniteSectorObject D) (I : Intertwiners D α β M)
    (a : Sector D 0) (u : Sector D α) (v : Sector D β) (p q r : ℤ) (i : ℕ) : M.States D :=
  (((-1 : ℂ)^i) * integerBinomial r i) •
    (StateFieldResidueReconstruction.epsilon r •
      coefficients D α β M I u (q + r - i) (action D β a (p + i) v))

/-- Full three-term mixed Borcherds, with three global finite supports. -/
theorem coefficients_jacobi (α β : Charge D) (M : FiniteSectorObject D)
    (I : Intertwiners D α β M) (a : Sector D 0) (u : Sector D α) (v : Sector D β)
    (p q r : ℤ) :
    Function.HasFiniteSupport (sumLeft D α β M I a u v p q r) ∧
    Function.HasFiniteSupport (sumFirst D α β M I a u v p q r) ∧
    Function.HasFiniteSupport (sumSecond D α β M I a u v p q r) ∧
      (∑ᶠ i : ℕ, sumLeft D α β M I a u v p q r i) =
        (∑ᶠ i : ℕ, sumFirst D α β M I a u v p q r i) -
        (∑ᶠ i : ℕ, sumSecond D α β M I a u v p q r i) := by
  have hl : Function.HasFiniteSupport (sumLeft D α β M I a u v p q r) :=
    support_tuple _ (fun j => ((I j).property.jacobi a u v p q r).1)
  have hf : Function.HasFiniteSupport (sumFirst D α β M I a u v p q r) :=
    support_tuple _ (fun j => ((I j).property.jacobi a u v p q r).2.1)
  have hs : Function.HasFiniteSupport (sumSecond D α β M I a u v p q r) :=
    support_tuple _ (fun j => ((I j).property.jacobi a u v p q r).2.2.1)
  refine ⟨hl, hf, hs, ?_⟩
  funext j
  have e := ((I j).property.jacobi a u v p q r).2.2.2
  have l := map_finsum (LinearMap.proj (R := ℂ) (φ := fun i : Fin M.size => Sector D (M.charge i)) j) hl
  have f := map_finsum (LinearMap.proj (R := ℂ) (φ := fun i : Fin M.size => Sector D (M.charge i)) j) hf
  have s := map_finsum (LinearMap.proj (R := ℂ) (φ := fun i : Fin M.size => Sector D (M.charge i)) j) hs
  simp only [LinearMap.proj_apply] at l f s
  change (∑ᶠ i, sumLeft D α β M I a u v p q r i) j =
    (∑ᶠ i, sumFirst D α β M I a u v p q r i) j -
      (∑ᶠ i, sumSecond D α β M I a u v p q r i) j
  rw [l, f, s]
  exact e

end FiniteSectorObject
end
end D5.S3.VertexAlgebra.LatticeSectorIntertwiner
