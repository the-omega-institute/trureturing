/- GID: D5/S3/VertexAlgebra/LatticeSectorOperatorSpace
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeSectorOperatorSpace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lawful mixed sector fields, their linear space and Ward identity. -/

import D5.S3.VertexAlgebra.LatticeNeutralVertexAlgebra
import D5.S3.VertexAlgebra.LatticeActualConformalState

/-!
Actual mixed-carrier operators for neutral Heisenberg sectors. The definition
retains the full source domain and statewise truncation; zero is permitted.
Classical source: Bakalov--Kac, math/0402315v1, section 4.1, and
Matsuo--Nagatomo, hep-th/9706118v1. Supplier residue proofs retain their
Scott Carnahan attribution. No classification or universal property is an
assumption of the space or of the canonical construction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorIntertwiner
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeSugawaraConformal
open LatticeActualConformalState LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators VertexOperator
noncomputable section

abbrev Coefficients (D : LatticeData) (α β γ : Charge D) :=
  Sector D α →ₗ[ℂ] (ℤ → (Sector D β →ₗ[ℂ] Sector D γ))

def leftTerm (D : LatticeData) (α β γ : Charge D) (I : Coefficients D α β γ)
    (a : Sector D 0) (u : Sector D α) (v : Sector D β) (p q r : ℤ) (i : ℕ) : Sector D γ :=
  integerBinomial p i • I (action D α a (r + i) u) (p + q - i) v

def firstTerm (D : LatticeData) (α β γ : Charge D) (I : Coefficients D α β γ)
    (a : Sector D 0) (u : Sector D α) (v : Sector D β) (p q r : ℤ) (i : ℕ) : Sector D γ :=
  (((-1 : ℂ)^i) * integerBinomial r i) •
    action D γ a (p + r - i) (I u (q + i) v)

def secondTerm (D : LatticeData) (α β γ : Charge D) (I : Coefficients D α β γ)
    (a : Sector D 0) (u : Sector D α) (v : Sector D β) (p q r : ℤ) (i : ℕ) : Sector D γ :=
  (((-1 : ℂ)^i) * integerBinomial r i) •
    (StateFieldResidueReconstruction.epsilon r • I u (q + r - i) (action D β a (p + i) v))

/-- The full algebraic IO laws, not merely a commutator condition. -/
structure Lawful (D : LatticeData) (α β γ : Charge D) (I : Coefficients D α β γ) : Prop where
  truncation : ∀ u v, ∃ N : ℤ, ∀ n : ℤ, N ≤ n → I u n v = 0
  source : ∀ u n, I (sectorT D α u) n = -(n : ℂ) • I u (n - 1)
  target : ∀ u n, (sectorT D γ).comp (I u n) - (I u n).comp (sectorT D β) =
    -(n : ℂ) • I u (n - 1)
  jacobi : ∀ a u v p q r,
    Function.HasFiniteSupport (leftTerm D α β γ I a u v p q r) ∧
    Function.HasFiniteSupport (firstTerm D α β γ I a u v p q r) ∧
    Function.HasFiniteSupport (secondTerm D α β γ I a u v p q r) ∧
      (∑ᶠ i : ℕ, leftTerm D α β γ I a u v p q r i) =
        (∑ᶠ i : ℕ, firstTerm D α β γ I a u v p q r i) -
          (∑ᶠ i : ℕ, secondTerm D α β γ I a u v p q r i)

/-- Every law is proved from the actual untwisted Y. -/
theorem canonical_lawful (D : LatticeData) (α β : Charge D) :
    Lawful D α β (α + β) (canonical D α β) where
  truncation := canonical_truncation D α β
  source := canonical_source_derivative D α β
  target := canonical_target_derivative D α β
  jacobi := canonical_borcherds D α β

private theorem lawful_zero (D : LatticeData) (α β γ : Charge D) :
    Lawful D α β γ 0 where
  truncation u v := ⟨0, by simp⟩
  source u n := by simp
  target u n := by apply LinearMap.ext; intro v; simp
  jacobi a u v p q r := by
    simp [leftTerm, firstTerm, secondTerm, Function.HasFiniteSupport, Function.support]

private theorem lawful_add (D : LatticeData) (α β γ : Charge D)
    (I K : Coefficients D α β γ) (hI : Lawful D α β γ I) (hK : Lawful D α β γ K) :
    Lawful D α β γ (I + K) where
  truncation u v := by
    obtain ⟨N, hN⟩ := hI.truncation u v
    obtain ⟨M, hM⟩ := hK.truncation u v
    exact ⟨max N M, fun n hn => by simp [hN n (le_trans (le_max_left _ _) hn),
      hM n (le_trans (le_max_right _ _) hn)]⟩
  source u n := by
    simpa only [LinearMap.add_apply, Pi.add_apply, smul_add] using
      congrArg₂ (· + ·) (hI.source u n) (hK.source u n)
  target u n := by
    apply LinearMap.ext
    intro v
    have hi := congrArg (fun f : Sector D β →ₗ[ℂ] Sector D γ => f v) (hI.target u n)
    have hk := congrArg (fun f : Sector D β →ₗ[ℂ] Sector D γ => f v) (hK.target u n)
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply] at hi hk
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.add_apply,
      Pi.add_apply, map_add, LinearMap.smul_apply, smul_add]
    rw [show sectorT D γ (I u n v) + sectorT D γ (K u n v) -
      (I u n (sectorT D β v) + K u n (sectorT D β v)) =
      (sectorT D γ (I u n v) - I u n (sectorT D β v)) +
      (sectorT D γ (K u n v) - K u n (sectorT D β v)) by abel, hi, hk]
  jacobi a u v p q r := by
    have hi := hI.jacobi a u v p q r
    have hk := hK.jacobi a u v p q r
    have hl : leftTerm D α β γ (I + K) a u v p q r =
      leftTerm D α β γ I a u v p q r + leftTerm D α β γ K a u v p q r := by
      ext i; simp [leftTerm, smul_add]
    have hf : firstTerm D α β γ (I + K) a u v p q r =
      firstTerm D α β γ I a u v p q r + firstTerm D α β γ K a u v p q r := by
      ext i; simp [firstTerm, smul_add]
    have hs : secondTerm D α β γ (I + K) a u v p q r =
      secondTerm D α β γ I a u v p q r + secondTerm D α β γ K a u v p q r := by
      ext i; simp [secondTerm, smul_add]
    rw [hl, hf, hs]
    refine ⟨hi.1.add hk.1, hi.2.1.add hk.2.1, hi.2.2.1.add hk.2.2.1, ?_⟩
    simp only [Pi.add_apply]
    rw [finsum_add_distrib hi.1 hk.1, finsum_add_distrib hi.2.1 hk.2.1,
      finsum_add_distrib hi.2.2.1 hk.2.2.1, hi.2.2.2, hk.2.2.2]
    abel

private theorem lawful_smul (D : LatticeData) (α β γ : Charge D)
    (c : ℂ) (I : Coefficients D α β γ) (hI : Lawful D α β γ I) :
    Lawful D α β γ (c • I) where
  truncation u v := by
    obtain ⟨N, hN⟩ := hI.truncation u v
    exact ⟨N, fun n hn => by simp [hN n hn]⟩
  source u n := by
    simpa only [LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply,
      smul_comm c (-(n : ℂ))] using congrArg (c • ·) (hI.source u n)
  target u n := by
    apply LinearMap.ext
    intro v
    have hi := congrArg (fun f : Sector D β →ₗ[ℂ] Sector D γ => f v) (hI.target u n)
    simpa only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      Pi.smul_apply, map_smul, RingHom.id_apply, ← smul_sub, smul_comm c (-(n : ℂ))]
      using congrArg (c • ·) hi
  jacobi a u v p q r := by
    have hi := hI.jacobi a u v p q r
    have hl : leftTerm D α β γ (c • I) a u v p q r =
      c • leftTerm D α β γ I a u v p q r := by
      funext i
      simp only [leftTerm, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply,
        smul_comm (integerBinomial p i) c]
    have hf : firstTerm D α β γ (c • I) a u v p q r =
      c • firstTerm D α β γ I a u v p q r := by
      funext i
      simp only [firstTerm, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply,
        map_smul, smul_comm (((-1 : ℂ)^i) * integerBinomial r i) c]
    have hs : secondTerm D α β γ (c • I) a u v p q r =
      c • secondTerm D α β γ I a u v p q r := by
      funext i
      simp only [secondTerm, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply,
        smul_comm (StateFieldResidueReconstruction.epsilon r) c,
        smul_comm (((-1 : ℂ)^i) * integerBinomial r i) c]
    rw [hl, hf, hs]
    refine ⟨hi.1.smul_right (fun _ => c), hi.2.1.smul_right (fun _ => c),
      hi.2.2.1.smul_right (fun _ => c), ?_⟩
    simp only [Pi.smul_apply]
    rw [← smul_finsum' c hi.1, ← smul_finsum' c hi.2.1,
      ← smul_finsum' c hi.2.2.1, hi.2.2.2, smul_sub]

/-- The complex subspace of all lawful mixed intertwiners. -/
def operatorSpace (D : LatticeData) (α β γ : Charge D) : Submodule ℂ (Coefficients D α β γ) where
  carrier := {I | Lawful D α β γ I}
  zero_mem' := lawful_zero D α β γ
  add_mem' := fun hi hk => lawful_add D α β γ _ _ hi hk
  smul_mem' := fun c _ hi => lawful_smul D α β γ c _ hi

abbrev IO (D : LatticeData) (α β γ : Charge D) := operatorSpace D α β γ

def canonicalIO (D : LatticeData) (α β : Charge D) : IO D α β (α + β) :=
  ⟨canonical D α β, canonical_lawful D α β⟩

/-- Full Jacobi implies the current/state commutator, with its finite support. -/
theorem ward (D : LatticeData) (α β γ : Charge D) (I : IO D α β γ)
    (a : Sector D 0) (u : Sector D α) (v : Sector D β) (m n : ℤ) :
    Function.HasFiniteSupport (leftTerm D α β γ I.val a u v m n 0) ∧
      action D γ a m (I.val u n v) - I.val u n (action D β a m v) =
        ∑ᶠ j : ℕ, leftTerm D α β γ I.val a u v m n 0 j := by
  have h := I.property.jacobi a u v m n 0
  refine ⟨h.1, ?_⟩
  have first : (∑ᶠ j : ℕ, firstTerm D α β γ I.val a u v m n 0 j) =
      action D γ a m (I.val u n v) := by
    rw [finsum_eq_single _ 0]
    · simp [firstTerm, integerBinomial]
    · intro j hj
      simp [firstTerm, integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hj)]
  have second : (∑ᶠ j : ℕ, secondTerm D α β γ I.val a u v m n 0 j) =
      I.val u n (action D β a m v) := by
    rw [finsum_eq_single _ 0]
    · simp [secondTerm, integerBinomial, StateFieldResidueReconstruction.epsilon]
    · intro j hj
      simp [secondTerm, integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hj)]
  rw [first, second] at h
  exact h.2.2.2.symm

end
end D5.S3.VertexAlgebra.LatticeSectorIntertwiner
