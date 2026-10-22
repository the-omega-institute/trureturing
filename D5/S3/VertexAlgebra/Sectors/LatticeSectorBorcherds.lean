/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorBorcherds
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorBorcherds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full mixed sector Borcherds identities and actual translation laws. -/

import D5.S3.VertexAlgebra.Sectors.LatticeSectorIntertwiner

/- Classical Heisenberg-sector restrictions of Bakalov--Kac's lattice fields.
The supported Borcherds supplier retains the Carnahan and Matsuo--Nagatomo
attributions in LatticeAllStateJacobi. No mixed Jacobi law is assumed.
The support invariant from LatticeSectorIntertwiner is a live dependency of
each nested term. These are general algebraic laws, not finite instances.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeSectorIntertwiner
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeSugawaraConformal
open LatticeAllStateJacobi LatticeAllStateReconstruction
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators VertexOperator
noncomputable section

/-- The action of the neutral sector, restricted from the actual ordinary Y. -/
def action (D : LatticeData) (δ : Charge D) :
    Sector D 0 →ₗ[ℂ] (ℤ → Module.End ℂ (Sector D δ)) := canonical D 0 δ

def sectorT (D : LatticeData) (δ : Charge D) : Module.End ℂ (Sector D δ) :=
  sectorTranslation D δ

@[simp] theorem single_canonical (D : LatticeData) (α β : Charge D)
    (u : Sector D α) (v : Sector D β) (n : ℤ) :
    Finsupp.single (α + β) (canonical D α β u n v) =
      ((Y D (Finsupp.single α u))[[n]]) (Finsupp.single β v) :=
  inclusion_canonical D α β u v n

@[simp] theorem single_action (D : LatticeData) (δ : Charge D)
    (a : Sector D 0) (v : Sector D δ) (n : ℤ) :
    Finsupp.single δ (action D δ a n v) =
      ((Y D (Finsupp.single 0 a))[[n]]) (Finsupp.single δ v) := by
  simpa only [action, zero_add] using single_canonical D 0 δ a v n

@[simp] theorem single_sectorT (D : LatticeData) (δ : Charge D) (v : Sector D δ) :
    Finsupp.single δ (sectorT D δ v) = translation D (Finsupp.single δ v) := by
  simp [sectorT, sectorTranslation, LinearMap.add_apply, Finsupp.single_add]

/-- Lower truncation is statewise in both inputs. -/
theorem canonical_truncation (D : LatticeData) (α β : Charge D)
    (u : Sector D α) (v : Sector D β) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → canonical D α β u n v = 0 := by
  let A := Y D (Finsupp.single α u)
  refine ⟨-((HahnModule.of ℂ).symm (A (Finsupp.single β v))).order, ?_⟩
  intro n hn
  have h : (A[[n]]) (Finsupp.single β v) = 0 :=
    VertexOperator.ncoeff_eq_zero_of_lt_order A n _ (by omega)
  simpa [canonical, inclusion, projection, A] using
    congrArg (fun w : Carrier D => w (α + β)) h

/-- Source translation differentiates the actual heterogeneous field. -/
theorem canonical_source_derivative (D : LatticeData) (α β : Charge D)
    (u : Sector D α) (n : ℤ) :
    canonical D α β (sectorT D α u) n = -(n : ℂ) • canonical D α β u (n - 1) := by
  apply LinearMap.ext
  intro v
  have h := congrArg (fun A : Module.End ℂ (Carrier D) =>
    (A (Finsupp.single β v)) (α + β))
    (LatticeActualStateDerivative.state_derivative_modes D (Finsupp.single α u) n)
  simpa [canonical, inclusion, projection, sectorT, sectorTranslation,
    LinearMap.add_apply] using h

/-- Target translation includes the translation on the second input. -/
theorem canonical_target_derivative (D : LatticeData) (α β : Charge D)
    (u : Sector D α) (n : ℤ) :
    (sectorT D (α + β)).comp (canonical D α β u n) -
      (canonical D α β u n).comp (sectorT D β) =
        -(n : ℂ) • canonical D α β u (n - 1) := by
  apply LinearMap.ext
  intro v
  have h := congrArg (fun A : Module.End ℂ (Carrier D) => A (Finsupp.single β v))
    (stateField_covariance D (Finsupp.single α u) n)
  have hs : ((Y D (Finsupp.single α u))[[n]]) (Finsupp.single β v) =
      Finsupp.single (α + β) (canonical D α β u n v) :=
    (single_canonical D α β u v n).symm
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    hs, ← single_sectorT, ← single_canonical, ← Finsupp.single_sub,
    ← Finsupp.smul_single] at h
  simpa [canonical, inclusion, projection, ← single_sectorT] using
    congrArg (fun w : Carrier D => w (α + β)) h

def mixedLeft (D : LatticeData) (α β : Charge D) (a : Sector D 0)
    (u : Sector D α) (v : Sector D β) (p q r : ℤ) (i : ℕ) : Sector D (α + β) :=
  integerBinomial p i • canonical D α β (action D α a (r + i) u) (p + q - i) v

def mixedFirst (D : LatticeData) (α β : Charge D) (a : Sector D 0)
    (u : Sector D α) (v : Sector D β) (p q r : ℤ) (i : ℕ) : Sector D (α + β) :=
  (((-1 : ℂ)^i) * integerBinomial r i) •
    action D (α + β) a (p + r - i) (canonical D α β u (q + i) v)

def mixedSecond (D : LatticeData) (α β : Charge D) (a : Sector D 0)
    (u : Sector D α) (v : Sector D β) (p q r : ℤ) (i : ℕ) : Sector D (α + β) :=
  (((-1 : ℂ)^i) * integerBinomial r i) •
    (StateFieldResidueReconstruction.epsilon r •
      canonical D α β u (q + r - i) (action D β a (p + i) v))

/-- Full three-term mixed Jacobi, including all three finite supports. -/
theorem canonical_borcherds (D : LatticeData) (α β : Charge D) (a : Sector D 0)
    (u : Sector D α) (v : Sector D β) (p q r : ℤ) :
    Function.HasFiniteSupport (mixedLeft D α β a u v p q r) ∧
    Function.HasFiniteSupport (mixedFirst D α β a u v p q r) ∧
    Function.HasFiniteSupport (mixedSecond D α β a u v p q r) ∧
      (∑ᶠ i : ℕ, mixedLeft D α β a u v p q r i) =
        (∑ᶠ i : ℕ, mixedFirst D α β a u v p q r i) -
          (∑ᶠ i : ℕ, mixedSecond D α β a u v p q r i) := by
  let A := Finsupp.single (0 : Charge D) a
  let U := Finsupp.single α u
  let V := Finsupp.single β v
  let P : Carrier D →ₗ[ℂ] Sector D (α + β) := projection D (α + β)
  have h := LatticeAllStateJacobi.borcherds D A U V p q r
  have hl (i : ℕ) : P (jacobiLeftTerm D p q r A U V i) =
      mixedLeft D α β a u v p q r i := by
    have e : Finsupp.single (α + β) (mixedLeft D α β a u v p q r i) =
        jacobiLeftTerm D p q r A U V i := by
      simp only [mixedLeft, ← Finsupp.smul_single, single_canonical, single_action,
        jacobiLeftTerm, mu, A, U, V]
    simpa only [P, projection, Finsupp.lapply_apply, Finsupp.single_eq_same, Sector] using
      (congrArg P e).symm
  have hf (i : ℕ) : P (jacobiRightFirstTerm D p q r A U V i) =
      mixedFirst D α β a u v p q r i := by
    have e : Finsupp.single (α + β) (mixedFirst D α β a u v p q r i) =
        jacobiRightFirstTerm D p q r A U V i := by
      simp only [mixedFirst, ← Finsupp.smul_single, single_action, single_canonical,
        jacobiRightFirstTerm, mu, A, U, V]
    simpa only [P, projection, Finsupp.lapply_apply, Finsupp.single_eq_same, Sector] using
      (congrArg P e).symm
  have hs (i : ℕ) : P (jacobiRightSecondTerm D p q r A U V i) =
      mixedSecond D α β a u v p q r i := by
    have e : Finsupp.single (α + β) (mixedSecond D α β a u v p q r i) =
        jacobiRightSecondTerm D p q r A U V i := by
      simp only [mixedSecond, ← Finsupp.smul_single, single_canonical, single_action,
        jacobiRightSecondTerm, mu, A, U, V]
    simpa only [P, projection, Finsupp.lapply_apply, Finsupp.single_eq_same, Sector] using
      (congrArg P e).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hl] using h.1.fun_comp (map_zero P)
  · simpa only [hf] using h.2.1.fun_comp (map_zero P)
  · simpa only [hs] using h.2.2.1.fun_comp (map_zero P)
  · have e := h.2.2.2
    simp_rw [smul_sub] at e
    change (∑ᶠ i : ℕ, jacobiLeftTerm D p q r A U V i) =
      ∑ᶠ i : ℕ, (jacobiRightFirstTerm D p q r A U V i -
        jacobiRightSecondTerm D p q r A U V i) at e
    rw [finsum_sub_distrib h.2.1 h.2.2.1] at e
    have projected := congrArg P e
    rw [map_sub, map_finsum P h.1, map_finsum P h.2.1,
      map_finsum P h.2.2.1] at projected
    simpa only [hl, hf, hs] using projected

end
end D5.S3.VertexAlgebra.LatticeSectorIntertwiner
