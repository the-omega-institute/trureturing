/- GID: D5/S3/VertexAlgebra/LatticeBcGhostBrstCharge
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeBcGhostBrstCharge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Statewise finite actual tensor BRST charge on every finite-rank lattice carrier. -/

import D5.S3.VertexAlgebra.LatticeSugawaraCurrents
import D5.S3.VertexAlgebra.BcGhostBrstSupport
import D5.S3.VertexAlgebra.BcGhostStressCurrent
import Mathlib.LinearAlgebra.TensorProduct.Map

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents BcGhostFockSupport
  BcGhostStressCurrent
open scoped BigOperators TensorProduct VertexOperator

noncomputable section

abbrev State (D : LatticeData) := Carrier D ⊗[ℂ] Fock ℂ

def matterCutoff (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (u : Carrier D) : ℤ :=
  -HahnSeries.order ((HahnModule.of ℂ).symm (sugawaraField D H u)) - 2

private theorem matter_high (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (u : Carrier D)
    (n : ℤ) (hn : matterCutoff D H u < n) : sugawaraMode D H n u = 0 := by
  apply VertexOperator.ncoeff_eq_zero_of_lt_order
  dsimp [matterCutoff] at hn
  omega

def M (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (n : ℤ) :
    Module.End ℂ (State D) := TensorProduct.map (sugawaraMode D H n) LinearMap.id

def G (D : LatticeData) (n : ℤ) : Module.End ℂ (State D) :=
  TensorProduct.map LinearMap.id (L n)

def C (D : LatticeData) (q : ℤ) : Module.End ℂ (State D) :=
  TensorProduct.map LinearMap.id (c q)

def B (D : LatticeData) (m : ℤ) : Module.End ℂ (State D) :=
  TensorProduct.map LinearMap.id (b m)

def P (D : LatticeData) (m n : ℤ) : Module.End ℂ (State D) :=
  TensorProduct.map LinearMap.id (normalPair (m + n) (-n))

def N (D : LatticeData) (n : ℤ) : Module.End ℂ (State D) :=
  if -1 ≤ n then (C D (-n)).comp (G D n) else (G D n).comp (C D (-n))

def A (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (n : ℤ) :
    Module.End ℂ (State D) :=
  (C D (-n)).comp (M D H n) + (2 : ℂ)⁻¹ • N D n

private theorem A_tmul (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (n : ℤ) (u : Carrier D) (g : Fock ℂ) :
    A D H n (u ⊗ₜ[ℂ] g) =
      sugawaraMode D H n u ⊗ₜ[ℂ] c (-n) g +
        (2 : ℂ)⁻¹ • (u ⊗ₜ[ℂ] BcGhostStressTails.outerNormalPair n g) := by
  by_cases hn : -1 ≤ n <;> simp [A, N, M, G, C, BcGhostStressTails.outerNormalPair, hn]

private theorem lift_bc (D : LatticeData) (p q : ℤ) :
    C D q * B D p + B D p * C D q =
      if p + q = 0 then 1 else 0 := by
  have h := congrArg (LinearMap.lTensorHom (Carrier D)) (b_c (K := ℂ) p q)
  by_cases hpq : p + q = 0
  · simp only [hpq, if_true, map_add, LinearMap.coe_lTensorHom,
      LinearMap.lTensor_mul, Module.End.one_eq_id, LinearMap.lTensor_id] at h
    simpa only [B, C, hpq, if_true, Module.End.one_eq_id,
      LinearMap.lTensor_def, add_comm] using h
  · simp only [hpq, if_false, map_add, map_zero, LinearMap.coe_lTensorHom,
      LinearMap.lTensor_mul] at h
    simpa only [B, C, hpq, if_false, LinearMap.lTensor_def, add_comm] using h

private theorem lift_gb (D : LatticeData) (m n : ℤ) :
    G D m * B D n - B D n * G D m =
      (m - n : ℂ) • B D (m + n) := by
  have h := congrArg (LinearMap.lTensorHom (Carrier D))
    (L_b_commutator (K := ℂ) m n)
  simp only [map_sub, map_smul, LinearMap.coe_lTensorHom, LinearMap.lTensor_mul] at h
  simpa only [G, B, LinearMap.lTensor_def] using h

private theorem lift_cm (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m n : ℤ) :
    M D H m * B D n = B D n * M D H m := by
  apply TensorProduct.ext'
  intro u g
  simp [M, B, Module.End.mul_apply]

private theorem P_eq (D : LatticeData) (m n : ℤ) :
    P D m n = if m + n ≤ -2 then B D (m + n) * C D (-n)
      else -(C D (-n) * B D (m + n)) := by
  change (normalPair (K := ℂ) (m + n) (-n)).lTensor (Carrier D) =
    if m + n ≤ -2 then
      (b (K := ℂ) (m + n)).lTensor (Carrier D) * (c (-n)).lTensor (Carrier D)
    else -((c (K := ℂ) (-n)).lTensor (Carrier D) *
      (b (m + n)).lTensor (Carrier D))
  by_cases hp : m + n ≤ -2 <;>
    simp only [normalPair, hp, ↓reduceIte, ← Module.End.mul_eq_comp,
      LinearMap.lTensor_neg, LinearMap.lTensor_mul]

private theorem product_anti_comm
    {D : LatticeData} (A B X U V : Module.End ℂ (State D))
    (hB : B * X - X * B = U) (hA : A * X + X * A = V) :
    (A * B) * X + X * (A * B) = A * U + V * B := by
  rw [← hB, ← hA]
  simp only [mul_sub, add_mul, mul_assoc]
  abel

private theorem product_anti_comm_rev
    {D : LatticeData} (A B X U V : Module.End ℂ (State D))
    (hB : B * X + X * B = U) (hA : A * X - X * A = V) :
    (A * B) * X + X * (A * B) = A * U - V * B := by
  rw [← hB, ← hA]
  simp only [mul_add, sub_mul, mul_assoc]
  abel

private theorem lift_nb (D : LatticeData) (m n : ℤ) :
    N D n * B D m + B D m * N D n =
      if -1 ≤ n then
        (if n = m then G D n else 0) +
          (n - m : ℂ) • (C D (-n) * B D (m + n))
      else
        (if n = m then G D n else 0) -
          (n - m : ℂ) • (B D (m + n) * C D (-n)) := by
  by_cases hn : -1 ≤ n
  · rw [N, if_pos hn, ← Module.End.mul_eq_comp]
    have h := product_anti_comm (D := D) (C D (-n)) (G D n) (B D m)
      ((n - m : ℂ) • B D (m + n))
      (if m + (-n) = 0 then 1 else 0)
      (by simpa [add_comm] using (lift_gb D n m)) (lift_bc D m (-n))
    by_cases hnm : n = m <;>
      simpa [hn, hnm, show m + (-n) = 0 ↔ n = m by omega,
        mul_smul_comm] using h
  · rw [N, if_neg hn, ← Module.End.mul_eq_comp]
    have h := product_anti_comm_rev (D := D) (G D n) (C D (-n)) (B D m)
      (if m + (-n) = 0 then 1 else 0)
      ((n - m : ℂ) • B D (m + n))
      (lift_bc D m (-n)) (by simpa [add_comm] using (lift_gb D n m))
    by_cases hnm : n = m <;>
      simpa [hn, hnm, show m + (-n) = 0 ↔ n = m by omega,
        smul_mul_assoc] using h

private theorem lift_cm_anti (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m n : ℤ) :
    (C D (-n) * M D H n) * B D m + B D m * (C D (-n) * M D H n) =
      if n = m then M D H n else 0 := by
  have h := product_anti_comm (D := D) (C D (-n)) (M D H n) (B D m)
    0 (if m + (-n) = 0 then 1 else 0)
    (by rw [lift_cm]; simp) (lift_bc D m (-n))
  by_cases hnm : n = m <;>
    simpa [hnm, show m + (-n) = 0 ↔ n = m by omega] using h

private theorem normal_threshold (D : LatticeData) (m n : ℤ) :
    (if -1 ≤ n then C D (-n) * B D (m + n)
      else -(B D (m + n) * C D (-n))) = -P D m n := by
  rw [P_eq]
  by_cases hn : -1 ≤ n <;> by_cases hp : m + n ≤ -2
  · have hm : m ≠ 0 := by omega
    have hcar : C D (-n) * B D (m + n) + B D (m + n) * C D (-n) = 0 := by
      simpa [hm] using (lift_bc D (m + n) (-n))
    simpa only [hn, hp, if_true] using eq_neg_of_add_eq_zero_left hcar
  · simp [hn, hp]
  · simp [hn, hp]
  · have hm : m ≠ 0 := by omega
    have hcar : C D (-n) * B D (m + n) + B D (m + n) * C D (-n) = 0 := by
      simpa [hm] using (lift_bc D (m + n) (-n))
    have hbc := eq_neg_of_add_eq_zero_right hcar
    simpa [hn, hp] using congrArg Neg.neg hbc

private theorem lift_ab_reconciled (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m n : ℤ) :
    A D H n * B D m + B D m * A D H n =
      (if n = m then M D H n + (2 : ℂ)⁻¹ • G D n else 0) +
        (2 : ℂ)⁻¹ • ((m - n : ℂ) • P D m n) := by
  have hN : N D n * B D m + B D m * N D n =
      (if n = m then G D n else 0) + (m - n : ℂ) • P D m n := by
    rw [lift_nb]
    have hthreshold := normal_threshold D m n
    have hsign : -(n - m : ℂ) = (m - n : ℂ) := by ring
    by_cases hn : -1 ≤ n
    · simp only [hn, if_true] at hthreshold ⊢
      rw [hthreshold, smul_neg, ← neg_smul, hsign]
    · simp only [hn, if_false] at hthreshold ⊢
      have hpair : B D (m + n) * C D (-n) = P D m n :=
        neg_injective hthreshold
      rw [hpair, sub_eq_add_neg]
      congr 1
      calc
        -((n - m : ℂ) • P D m n) = (-(n - m : ℂ)) • P D m n :=
          (neg_smul (n - m : ℂ) (P D m n)).symm
        _ = (m - n : ℂ) • P D m n := by rw [hsign]
  have heq : A D H n * B D m + B D m * A D H n =
      ((C D (-n) * M D H n) * B D m + B D m * (C D (-n) * M D H n)) +
        (2 : ℂ)⁻¹ • (N D n * B D m + B D m * N D n) := by
    simp only [A, ← Module.End.mul_eq_comp, add_mul, mul_add, smul_mul_assoc,
      mul_smul_comm, smul_add]
    abel
  rw [heq, lift_cm_anti, hN, smul_add]
  by_cases hnm : n = m <;> simp [hnm]

private theorem P_finite (D : LatticeData) (m : ℤ) (psi : State D) :
    Function.HasFiniteSupport (fun n : ℤ => P D m n psi) := by
  induction psi using TensorProduct.induction_on with
  | zero => simp [Function.HasFiniteSupport]
  | tmul u g =>
      apply (Set.finite_Icc (-cutoff m g) (cutoff m g)).subset
      intro n hn
      apply normal_pair_support_interval m g
      intro hzero
      exact hn (by simp [P, hzero])
  | add psi chi hpsi hchi =>
      apply (hpsi.union hchi).subset
      intro n hn
      by_cases hzero : P D m n psi = 0
      · right
        intro hother
        exact hn (by simp [map_add, hzero, hother])
      · exact Or.inl hzero

private theorem weighted_P_finite (D : LatticeData) (m : ℤ) (psi : State D) :
    Function.HasFiniteSupport (fun n : ℤ => (m - n : ℂ) • P D m n psi) := by
  apply (P_finite D m psi).subset
  intro n hn
  intro hzero
  exact hn (by simp [hzero])

private theorem row_eval (D : LatticeData) (m : ℤ) (psi : State D) :
    (∑ᶠ n : ℤ, (m - n : ℂ) • P D m n psi) = G D m psi := by
  induction psi using TensorProduct.induction_on with
  | zero => simp
  | tmul u g =>
      change (∑ᶠ n : ℤ, (m - n : ℂ) •
        (u ⊗ₜ[ℂ] normalPair (m + n) (-n) g)) =
        u ⊗ₜ[ℂ] L m g
      have hf : Function.HasFiniteSupport
          (fun n : ℤ => (m - n : ℂ) • normalPair (m + n) (-n) g) := by
        apply (Set.finite_Icc (-cutoff m g) (cutoff m g)).subset
        intro n hn
        apply normal_pair_support_interval m g
        intro hzero
        exact hn (by simp [hzero])
      have hmap := (TensorProduct.mk ℂ (Carrier D) (Fock ℂ) u).toAddMonoidHom.map_finsum
        hf
      simpa only [LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply,
        TensorProduct.tmul_smul, L, LinearMap.coe_mk, AddHom.coe_mk] using hmap.symm
  | add psi chi hpsi hchi =>
      simp only [map_add, smul_add]
      rw [finsum_add_distrib (weighted_P_finite D m psi)
        (weighted_P_finite D m chi), hpsi, hchi]

private theorem delta_finite (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ) (psi : State D) :
    Function.HasFiniteSupport
      (fun n : ℤ => if n = m then M D H n psi + (2 : ℂ)⁻¹ • G D n psi else 0) := by
  apply (Set.finite_singleton m).subset
  intro n hn
  by_contra hne
  have hnm : n ≠ m := by simpa only [Set.mem_singleton_iff] using hne
  exact hn (by simp [hnm])

private theorem delta_sum (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ) (psi : State D) :
    (∑ᶠ n : ℤ, if n = m then M D H n psi + (2 : ℂ)⁻¹ • G D n psi else 0) =
      M D H m psi + (2 : ℂ)⁻¹ • G D m psi := by
  rw [finsum_eq_single _ m]
  · simp
  · intro n hnm
    simp [hnm]

private theorem matter_tmul_support (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (u : Carrier D) (g : Fock ℂ) :
    Function.support (fun n : ℤ => sugawaraMode D H n u ⊗ₜ[ℂ] c (-n) g) ⊆
      Set.Icc (-BcGhostBrstSupport.bound g - 2) (matterCutoff D H u) := by
  intro n hn
  constructor
  · by_contra hlow
    have hc := BcGhostBrstSupport.c_vanish_below g n (lt_of_not_ge hlow)
    exact hn (by simp [hc])
  · by_contra hhigh
    have hm := matter_high D H u n (lt_of_not_ge hhigh)
    exact hn (by simp [hm])

def chargeUpper (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (u : Carrier D) (g : Fock ℂ) : ℤ :=
  max (matterCutoff D H u) (2 * BcGhostBrstSupport.bound g + 4)

theorem A_support_tmul (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (u : Carrier D) (g : Fock ℂ) :
    Function.support (fun n : ℤ => A D H n (u ⊗ₜ[ℂ] g)) ⊆
      Set.Icc (-BcGhostBrstSupport.bound g - 2) (chargeUpper D H u g) := by
  intro n hn
  have hzero (houtside : n < -BcGhostBrstSupport.bound g - 2 ∨
      chargeUpper D H u g < n) : A D H n (u ⊗ₜ[ℂ] g) = 0 := by
    have hm : sugawaraMode D H n u ⊗ₜ[ℂ] c (-n) g = 0 := by
      by_contra hne
      have hb : -BcGhostBrstSupport.bound g - 2 ≤ n ∧ n ≤ matterCutoff D H u :=
        matter_tmul_support D H u g hne
      rcases houtside with hlo | hhi
      · exact (not_lt_of_ge hb.1) hlo
      · exact (not_lt_of_ge (hb.2.trans (le_max_left _ _))) hhi
    have hg : BcGhostStressTails.outerNormalPair n g = 0 := by
      by_contra hne
      have hb : -BcGhostBrstSupport.bound g - 2 ≤ n ∧
          n ≤ 2 * BcGhostBrstSupport.bound g + 4 :=
        BcGhostBrstSupport.normalGhost_support_interval g hne
      rcases houtside with hlo | hhi
      · exact (not_lt_of_ge hb.1) hlo
      · exact (not_lt_of_ge (hb.2.trans (le_max_right _ _))) hhi
    simp [A_tmul, hm, hg]
  constructor
  · by_contra hlo
    exact hn (hzero (Or.inl (lt_of_not_ge hlo)))
  · by_contra hhi
    exact hn (hzero (Or.inr (lt_of_not_ge hhi)))

theorem A_finite (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (psi : State D) :
    Function.HasFiniteSupport (fun n : ℤ => A D H n psi) := by
  induction psi using TensorProduct.induction_on with
  | zero => simp [Function.HasFiniteSupport]
  | tmul u g =>
      have hmatter : Function.HasFiniteSupport
          (fun n : ℤ => sugawaraMode D H n u ⊗ₜ[ℂ] c (-n) g) :=
        (Set.finite_Icc _ _).subset (matter_tmul_support D H u g)
      have hghost := BcGhostStressTails.outer_has_finite_support g
      apply (hmatter.union hghost).subset
      intro n hn
      by_cases hm : sugawaraMode D H n u ⊗ₜ[ℂ] c (-n) g = 0
      · right
        intro hg
        exact hn (by simp [A_tmul, hm, hg])
      · exact Or.inl hm
  | add psi chi hpsi hchi =>
      apply (hpsi.union hchi).subset
      intro n hn
      by_cases hzero : A D H n psi = 0
      · right
        intro hother
        exact hn (by simp [map_add, hzero, hother])
      · exact Or.inl hzero

def Q (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Module.End ℂ (State D) where
  toFun psi := ∑ᶠ n : ℤ, A D H n psi
  map_add' psi chi := by
    simp only [map_add]
    exact finsum_add_distrib (A_finite D H psi) (A_finite D H chi)
  map_smul' scalar psi := by
    simp only [map_smul, RingHom.id_apply]
    exact (smul_finsum' scalar (A_finite D H psi)).symm

theorem Q_tmul (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (u : Carrier D) (g : Fock ℂ) :
    Q D H (u ⊗ₜ[ℂ] g) =
      ∑ n ∈ Finset.Icc (-BcGhostBrstSupport.bound g - 2) (chargeUpper D H u g),
        (sugawaraMode D H n u ⊗ₜ[ℂ] c (-n) g +
          (2 : ℂ)⁻¹ • (u ⊗ₜ[ℂ] BcGhostStressTails.outerNormalPair n g)) := by
  change (∑ᶠ n : ℤ, A D H n (u ⊗ₜ[ℂ] g)) = _
  rw [finsum_eq_sum_of_support_subset _ (s :=
    Finset.Icc (-BcGhostBrstSupport.bound g - 2) (chargeUpper D H u g))
    (by simpa only [Finset.coe_Icc] using A_support_tmul D H u g)]
  exact Finset.sum_congr rfl (fun n _ => A_tmul D H n u g)

theorem Q_tmul_expanded (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (u : Carrier D) (g : Fock ℂ) :
    Q D H (u ⊗ₜ[ℂ] g) =
      (∑ n ∈ Finset.Icc (-BcGhostBrstSupport.bound g - 2) (matterCutoff D H u),
        sugawaraMode D H n u ⊗ₜ[ℂ] c (-n) g) +
      (2 : ℂ)⁻¹ •
        (∑ n ∈ Finset.Icc (-BcGhostBrstSupport.bound g - 2)
            (2 * BcGhostBrstSupport.bound g + 4),
          ∑ k ∈ Finset.Icc (-(3 * BcGhostBrstSupport.bound g + 8))
              (3 * BcGhostBrstSupport.bound g + 8),
            (n - k : ℂ) • (u ⊗ₜ[ℂ] BcGhostBrstSupport.expanded g (n, k))) := by
  have hmatter : (∑ᶠ n : ℤ, sugawaraMode D H n u ⊗ₜ[ℂ] c (-n) g) =
      ∑ n ∈ Finset.Icc (-BcGhostBrstSupport.bound g - 2) (chargeUpper D H u g),
        sugawaraMode D H n u ⊗ₜ[ℂ] c (-n) g := by
    apply finsum_eq_sum_of_support_subset
    intro n hn
    have hb := matter_tmul_support D H u g hn
    change n ∈ Finset.Icc (-BcGhostBrstSupport.bound g - 2) (chargeUpper D H u g)
    exact Finset.mem_Icc.mpr ⟨hb.1, hb.2.trans (le_max_left _ _)⟩
  have hghost : (∑ᶠ n : ℤ, u ⊗ₜ[ℂ] BcGhostStressTails.outerNormalPair n g) =
      ∑ n ∈ Finset.Icc (-BcGhostBrstSupport.bound g - 2) (chargeUpper D H u g),
        u ⊗ₜ[ℂ] BcGhostStressTails.outerNormalPair n g := by
    apply finsum_eq_sum_of_support_subset
    intro n hn
    have hne : BcGhostStressTails.outerNormalPair n g ≠ 0 := by
      intro hzero
      exact hn (by simp [hzero])
    have hb := BcGhostBrstSupport.normalGhost_support_interval g hne
    change n ∈ Finset.Icc (-BcGhostBrstSupport.bound g - 2) (chargeUpper D H u g)
    exact Finset.mem_Icc.mpr ⟨hb.1, hb.2.trans (le_max_right _ _)⟩
  rw [Q_tmul, Finset.sum_add_distrib, ← Finset.smul_sum, ← hmatter, ← hghost]
  congr 1
  · apply finsum_eq_sum_of_support_subset
    simpa only [Finset.coe_Icc] using matter_tmul_support D H u g
  · congr 1
    have hghost : Function.HasFiniteSupport
        (fun n : ℤ => BcGhostStressTails.outerNormalPair n g) :=
      BcGhostStressTails.outer_has_finite_support g
    have hmap := (TensorProduct.mk ℂ (Carrier D) (Fock ℂ) u).toAddMonoidHom.map_finsum hghost
    simp only [LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply] at hmap
    rw [← hmap,
      BcGhostBrstSupport.normalGhost_joint_finsum, BcGhostBrstSupport.expanded_joint_sum]
    simp only [BcGhostBrstSupport.modeInterval, BcGhostBrstSupport.rowInterval,
      TensorProduct.tmul_sum, TensorProduct.tmul_smul]

theorem ward_identity (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ) :
    Q D H * B D m + B D m * Q D H = M D H m + G D m := by
  apply LinearMap.ext
  intro psi
  have hpsi := A_finite D H psi
  have hBpsi := A_finite D H (B D m psi)
  have hpost := hpsi.fun_comp (map_zero (B D m))
  have hmap := (B D m).toAddMonoidHom.map_finsum hpsi
  simp only [LinearMap.toAddMonoidHom_coe] at hmap
  change (∑ᶠ n : ℤ, A D H n (B D m psi)) +
      B D m (∑ᶠ n : ℤ, A D H n psi) = _
  rw [hmap, ← finsum_add_distrib hBpsi hpost]
  have hterm :
      (∑ᶠ n : ℤ, (A D H n (B D m psi) + B D m (A D H n psi))) =
        ∑ᶠ n : ℤ,
          ((if n = m then M D H n psi + (2 : ℂ)⁻¹ • G D n psi else 0) +
            (2 : ℂ)⁻¹ • ((m - n : ℂ) • P D m n psi)) := by
    apply finsum_congr
    intro n
    have h := congrArg (fun T : Module.End ℂ (State D) => T psi)
      (lift_ab_reconciled D H m n)
    by_cases hnm : n = m <;> simpa [hnm] using h
  have hrow : Function.HasFiniteSupport
      (fun n : ℤ => (2 : ℂ)⁻¹ • ((m - n : ℂ) • P D m n psi)) := by
    apply (weighted_P_finite D m psi).subset
    intro n hn hzero
    exact hn (by simp [hzero])
  rw [hterm, finsum_add_distrib (delta_finite D H m psi)
    hrow, delta_sum, ← smul_finsum' _ (weighted_P_finite D m psi), row_eval]
  simp only [LinearMap.add_apply]
  module


#print axioms matter_high
#print axioms A_tmul
#print axioms matter_tmul_support
#print axioms A_support_tmul
#print axioms A_finite
#print axioms Q
#print axioms Q_tmul
#print axioms Q_tmul_expanded
#print axioms ward_identity

end

end D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge
