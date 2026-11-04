/- GID: D5/S3/Quantum/Fermionic/GaussianRenyiStrongSubadditivity
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/GaussianRenyiStrongSubadditivity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Fermionic Gaussian Renyi strong subadditivity for orders strictly between zero and one. -/

import D5.S3.Quantum.Analysis.FermionicRenyiStieltjes
import D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity

noncomputable section

open Matrix MeasureTheory Set
open scoped ComplexOrder
open D5.S3.Quantum.Analysis.FermionicRenyiStieltjes

namespace D5.S3.Quantum.Fermionic.GaussianRenyiStrongSubadditivity

/-- Real Majorana covariance with Hermitian spectrum in `[-1, 1]`. -/
def physicalCovariance {n : ℕ}
    (G : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) : Prop :=
  Gᵀ = -G ∧ ∃ h : (Complex.I • G.map Complex.ofReal).IsHermitian,
    ∀ i, |h.eigenvalues i| ≤ 1

/-- Restriction to all Majorana indices belonging to the selected modes. -/
def reducedCovariance {n : ℕ}
    (G : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) (X : Finset (Fin n)) :
    Matrix {p : Fin n × Fin 2 // p.1 ∈ X} {p : Fin n × Fin 2 // p.1 ∈ X} ℝ :=
  G.submatrix Subtype.val Subtype.val

/-- The source entropy: half the sum over the complete Majorana spectrum. -/
def fermionicGaussianRenyiEntropy {n : ℕ} {X : Finset (Fin n)} (α : ℝ)
    (G : Matrix {p : Fin n × Fin 2 // p.1 ∈ X}
      {p : Fin n × Fin 2 // p.1 ∈ X} ℝ) : ℝ :=
  if h : (Complex.I • G.map Complex.ofReal).IsHermitian then
    (1 / 2 : ℝ) * ∑ i, fermionicRenyiFunction α (h.eigenvalues i)
  else 0

def claim : Prop :=
  ∀ (n : ℕ) (G : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ),
    physicalCovariance G → ∀ A B C : Finset (Fin n),
      Disjoint A B → Disjoint A C → Disjoint B C → ∀ α : ℝ,
        0 < α → α < 1 →
          fermionicGaussianRenyiEntropy α (reducedCovariance G (A ∪ B)) +
            fermionicGaussianRenyiEntropy α (reducedCovariance G (B ∪ C)) ≥
          fermionicGaussianRenyiEntropy α (reducedCovariance G (A ∪ B ∪ C)) +
            fermionicGaussianRenyiEntropy α (reducedCovariance G B)

private def interpolation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (u : ℝ) : Matrix ι ι ℂ :=
  1 + (u : ℂ) • (Complex.I • G.map Complex.ofReal)

private lemma skew_hermitian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : Gᵀ = -G) :
    (Complex.I • G.map Complex.ofReal).IsHermitian := by
  sorry

private lemma interpolation_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (h : (Complex.I • G.map Complex.ofReal).IsHermitian)
    (hb : ∀ i, |h.eigenvalues i| ≤ 1) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (interpolation G u).PosDef := by
  sorry

private lemma reduced_physical {n : ℕ}
    (G : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) (hG : physicalCovariance G)
    (X : Finset (Fin n)) :
    (reducedCovariance G X)ᵀ = -(reducedCovariance G X) ∧
      ∃ h : (Complex.I • (reducedCovariance G X).map Complex.ofReal).IsHermitian,
        ∀ i, |h.eigenvalues i| ≤ 1 := by
  sorry

private lemma determinant_log_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : Gᵀ = -G)
    (h : (Complex.I • G.map Complex.ofReal).IsHermitian)
    (hb : ∀ i, |h.eigenvalues i| ≤ 1) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Real.log (interpolation G u).det.re =
      (1 / 2 : ℝ) * ∑ i, Real.log (1 - u ^ 2 * h.eigenvalues i ^ 2) := by
  sorry

private lemma entropy_mixture {n : ℕ}
    (G : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) (hG : physicalCovariance G)
    (X : Finset (Fin n)) {α : ℝ} (ha0 : 0 < α) (ha1 : α < 1) :
    IntegrableOn (fun u : ℝ => fermionicWeight α u *
      Real.log (interpolation (reducedCovariance G X) u).det.re) (Ioo 0 1) ∧
    fermionicGaussianRenyiEntropy α (reducedCovariance G X) =
      (X.card : ℝ) * Real.log 2 + ∫ u in Ioo (0 : ℝ) 1,
        fermionicWeight α u * Real.log (interpolation (reducedCovariance G X) u).det.re := by
  sorry

private lemma mode_interpolation_det {n : ℕ}
    (G : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)
    (Y : Finset (Fin n × Fin 2)) (X : Finset (Fin n))
    (hYX : ∀ p, p ∈ Y ↔ p.1 ∈ X) (u : ℝ) :
    ((interpolation G u).submatrix
      (Subtype.val : ↥Y → Fin n × Fin 2) Subtype.val).det =
      (interpolation (reducedCovariance G X) u).det := by
  sorry

private lemma settlement_main : claim := by
  intro n G hG A B C hAB hAC hBC α ha0 ha1
  let L := fun (X : Finset (Fin n)) (u : ℝ) =>
    Real.log (interpolation (reducedCovariance G X) u).det.re
  have hm (X : Finset (Fin n)) :
      IntegrableOn (fun u => fermionicWeight α u * L X u) (Ioo (0 : ℝ) 1) ∧
      fermionicGaussianRenyiEntropy α (reducedCovariance G X) =
        (X.card : ℝ) * Real.log 2 +
          ∫ u in Ioo (0 : ℝ) 1, fermionicWeight α u * L X u :=
    entropy_mixture G hG X ha0 ha1
  have hk (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
      L (A ∪ B ∪ C) u + L B u ≤ L (A ∪ B) u + L (B ∪ C) u := by
    obtain ⟨h, hb⟩ := hG.2
    have hk := D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.log_koteljanskii
      (interpolation G u) (interpolation_posDef G h hb hu0 hu1)
      (A ×ˢ (Finset.univ : Finset (Fin 2))) (B ×ˢ Finset.univ) (C ×ˢ Finset.univ)
      (Finset.disjoint_product.mpr (Or.inl hAB))
      (Finset.disjoint_product.mpr (Or.inl hAC))
      (Finset.disjoint_product.mpr (Or.inl hBC))
    rw [mode_interpolation_det G _ (A ∪ B ∪ C)
        (fun p => by simp only [Finset.mem_union, Finset.mem_product,
          Finset.mem_univ, and_true]) u,
      mode_interpolation_det G _ B
        (fun p => by simp only [Finset.mem_product, Finset.mem_univ, and_true]) u,
      mode_interpolation_det G _ (A ∪ B)
        (fun p => by simp only [Finset.mem_union, Finset.mem_product,
          Finset.mem_univ, and_true]) u,
      mode_interpolation_det G _ (B ∪ C)
        (fun p => by simp only [Finset.mem_union, Finset.mem_product,
          Finset.mem_univ, and_true]) u] at hk
    exact hk
  have hpoint : ∀ᵐ u ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      fermionicWeight α u * L (A ∪ B ∪ C) u + fermionicWeight α u * L B u ≤
        fermionicWeight α u * L (A ∪ B) u + fermionicWeight α u * L (B ∪ C) u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    simpa only [mul_add] using mul_le_mul_of_nonneg_left (hk u hu.1.le hu.2)
      (weight_pos ha0 ha1 hu.1.le hu.2).le
  have hi := integral_mono_ae ((hm (A ∪ B ∪ C)).1.add (hm B).1)
    ((hm (A ∪ B)).1.add (hm (B ∪ C)).1) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_add (hm (A ∪ B ∪ C)).1 (hm B).1,
    integral_add (hm (A ∪ B)).1 (hm (B ∪ C)).1] at hi
  have hUC : Disjoint (A ∪ B) C := Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩
  have hc : (A ∪ B).card + (B ∪ C).card = (A ∪ B ∪ C).card + B.card := by
    rw [Finset.card_union_of_disjoint hAB, Finset.card_union_of_disjoint hBC,
      Finset.card_union_of_disjoint hUC, Finset.card_union_of_disjoint hAB]
    omega
  have hcr : ((A ∪ B).card : ℝ) + (B ∪ C).card = (A ∪ B ∪ C).card + B.card := by
    exact_mod_cast hc
  have hconst := congrArg (fun t : ℝ => t * Real.log 2) hcr
  rw [(hm (A ∪ B)).2, (hm (B ∪ C)).2, (hm (A ∪ B ∪ C)).2, (hm B).2]
  linarith only [hi, hconst]

theorem result : claim := settlement_main

end D5.S3.Quantum.Fermionic.GaussianRenyiStrongSubadditivity
