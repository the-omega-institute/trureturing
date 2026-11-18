/- GID: D5/S3/Quantum/TensorNetworks/CZXParentLindbladianOrderedTransfer
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/CZXParentLindbladianOrderedTransfer
   mirror-E: none
   anchors: []
   utility: none
   digest: Finite-time CZX evolution as a cyclic ordered transfer product. -/

import D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel

/-! The weighted gauge sector of the CZX evolution and its ordered transfer formula. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.TensorNetworks.CZXParentLindbladianOrderedTransfer

open CZXParentLindbladianAveraging CZXParentLindbladianWindowChannel
open Matrix
open scoped ComplexConjugate

private abbrev Config (n : ℕ) := Fin n → Fin 2
private abbrev Operator (n : ℕ) := Matrix (Config n) (Config n) ℂ
private abbrev Superoperator (n : ℕ) := Matrix (Config n × Config n) (Config n × Config n) ℂ

private lemma middle_sites_ne (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    site i 1 ≠ site i 2 := fun h =>
  (by decide : (1 : Fin 4) ≠ 2) ((site_injective n hn i 1 2).mp h)

private def exchangeMiddle (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    (Config n × (Fin 2 × Fin 2)) ≃ (Config n × (Fin 2 × Fin 2)) := by
  let exchange : Config n × (Fin 2 × Fin 2) → Config n × (Fin 2 × Fin 2) :=
    fun z => (middleUpdate i z.1 z.2.1 z.2.2, z.1 (site i 1), z.1 (site i 2))
  have hinv : Function.Involutive exchange := by
    rintro ⟨x, b, c⟩
    have hne := middle_sites_ne n hn i
    have hb : middleUpdate i x b c (site i 1) = b := by simp [middleUpdate, hne]
    have hc : middleUpdate i x b c (site i 2) = c := by simp [middleUpdate]
    have hx : middleUpdate i (middleUpdate i x b c) (x (site i 1)) (x (site i 2)) = x := by
      funext j
      by_cases h₂ : j = site i 2
      · simp [middleUpdate, h₂]
      by_cases h₁ : j = site i 1
      · simp [middleUpdate, h₁, hne]
      · simp [middleUpdate, h₂, h₁]
    change (middleUpdate i (middleUpdate i x b c) (x (site i 1)) (x (site i 2)),
      middleUpdate i x b c (site i 1), middleUpdate i x b c (site i 2)) = _
    rw [hx, hb, hc]
  exact ⟨exchange, exchange, hinv, hinv⟩

private noncomputable def coeff (n : ℕ) (δ : Config n) (φ : Config n → ℂ) : Operator n :=
  ∑ x, φ x • gaugedUnit n δ x

private lemma window_coeff (n : ℕ) (hn : 4 ≤ n) (i : Fin n)
    (δ : Config n) (hδ : goodWindow i δ) (φ : Config n → ℂ) :
    windowChannel n i (coeff n δ φ) =
      coeff n δ (avg n {site i 1, site i 2} φ) := by
  classical
  let G := gaugedUnit n δ
  let r : ℂ := (4 : ℂ)⁻¹
  have hf : (∑ x : Config n, ∑ b : Fin 2, ∑ c : Fin 2,
      φ x • G (middleUpdate i x b c)) =
      ∑ x : Config n, ∑ b : Fin 2, ∑ c : Fin 2, φ (middleUpdate i x b c) • G x := by
    simp only [← Fintype.sum_prod_type']
    apply Fintype.sum_equiv (exchangeMiddle n hn i).symm
    rintro ⟨x, b, c⟩
    change φ x • G (middleUpdate i x b c) =
      φ (middleUpdate i (middleUpdate i x b c) (x (site i 1)) (x (site i 2))) •
        G (middleUpdate i x b c)
    congr 1
    exact congrArg φ (congrArg Prod.fst ((exchangeMiddle n hn i).left_inv (x, b, c))).symm
  change windowLM n i (∑ x, φ x • G x) = ∑ x, (avg n {site i 1, site i 2} φ) x • G x
  have hchannel (x : Config n) : windowLM n i (G x) =
      r • ∑ b : Fin 2, ∑ c : Fin 2, G (middleUpdate i x b c) := by
    change windowChannel n i (gaugedUnit n δ x) =
      (4 : ℂ)⁻¹ • ∑ b : Fin 2, ∑ c : Fin 2, gaugedUnit n δ (middleUpdate i x b c)
    simpa only [hδ, ite_true] using gauged_window_sector n hn i δ x
  have havg (x : Config n) : (avg n {site i 1, site i 2} φ) x =
      r • ∑ b : Fin 2, ∑ c : Fin 2, φ (middleUpdate i x b c) :=
    avg_pair_apply n _ _ (middle_sites_ne n hn i) φ x
  calc
    _ = r • ∑ x : Config n, ∑ b : Fin 2, ∑ c : Fin 2, φ x • G (middleUpdate i x b c) := by
      simp only [map_sum, map_smul, hchannel, smul_comm (φ _) r, Finset.smul_sum]
    _ = r • ∑ x : Config n, ∑ b : Fin 2, ∑ c : Fin 2, φ (middleUpdate i x b c) • G x :=
      congrArg (r • ·) hf
    _ = _ := by
      simp only [havg, smul_assoc, Finset.sum_smul, Finset.smul_sum]

end D5.S3.Quantum.TensorNetworks.CZXParentLindbladianOrderedTransfer
