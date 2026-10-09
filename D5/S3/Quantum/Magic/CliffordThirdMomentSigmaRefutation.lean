/- GID: D5/S3/Quantum/Magic/CliffordThirdMomentSigmaRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/CliffordThirdMomentSigmaRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Magic/CliffordThirdMomentSigmaRefutation.claim; result=D5/S3/Quantum/Magic/CliffordThirdMomentSigmaRefutation.result; claim=D5/S3/Quantum/Magic/CliffordThirdMomentSigmaRefutation.claim
   digest: The stochastic Lagrangian and nonsymmetric aggregate lower bounds fail in dimension five. -/

import D5.S3.Quantum.Magic.CliffordThirdMomentAggregateRefutation
import Mathlib.LinearAlgebra.Matrix.Permutation

namespace D5.S3.Quantum.Magic.CliffordThirdMomentSigmaRefutation

open Matrix
open D5.S3.Quantum.Magic.CliffordThirdMomentNegativity
open D5.S3.Quantum.Magic.CliffordThirdMomentAggregateRefutation
open scoped ComplexOrder

set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

/-- All subspaces satisfying the three stochastic Lagrangian conditions at t = 3. -/
noncomputable def sigmaSubspaces (d : ℕ) [NeZero d] :
    Finset (Submodule (ZMod d) ((Fin 3 → ZMod d) × (Fin 3 → ZMod d))) :=
  (Set.toFinite {T | IsStochasticLagrangian d T}).toFinset

/-- The source collection of graphs of the permutation matrices in S_3. -/
noncomputable def symSubspaces (d : ℕ) :
    Finset (Submodule (ZMod d) ((Fin 3 → ZMod d) × (Fin 3 → ZMod d))) := by
  classical
  exact Finset.univ.image (fun e : Equiv.Perm (Fin 3) =>
    graphSubspace (e.permMatrix (ZMod d)))

/-- The nonsymmetric subspaces are the stochastic Lagrangian subspaces minus permutation graphs. -/
noncomputable def nsSubspaces (d : ℕ) [NeZero d] :
    Finset (Submodule (ZMod d) ((Fin 3 → ZMod d) × (Fin 3 → ZMod d))) := by
  classical
  exact sigmaSubspaces d \ symSubspaces d

/-- The source aggregate over all stochastic Lagrangian subspaces. -/
noncomputable def kappaSigma (d n : ℕ) [NeZero d]
    (Psi : (Fin n → ZMod d) → ℂ) : ℂ := by
  classical
  exact ∑ T ∈ sigmaSubspaces d, kappa d n Psi T

/-- The source aggregate over the nonsymmetric subspaces. -/
noncomputable def kappaNs (d n : ℕ) [NeZero d]
    (Psi : (Fin n → ZMod d) → ℂ) : ℂ := by
  classical
  exact ∑ T ∈ nsSubspaces d, kappa d n Psi T

/-- Either printed universal lower bound of Zhu--Mao--Yi Conjecture 2. -/
def claim : Prop :=
  (∀ (d : ℕ) [Fact d.Prime], d ≠ 2 → ∀ (n : ℕ) (Psi : (Fin n → ZMod d) → ℂ),
      ∑ x, ‖Psi x‖ ^ 2 = 1 → (6 : ℂ) ≤ kappaSigma d n Psi) ∨
  (∀ (d : ℕ) [Fact d.Prime], d ≠ 2 → ∀ (n : ℕ) (Psi : (Fin n → ZMod d) → ℂ),
      ∑ x, ‖Psi x‖ ^ 2 = 1 → (0 : ℂ) ≤ kappaNs d n Psi)

private theorem graph_stochastic {d : ℕ} [Fact d.Prime]
    (O : Matrix (Fin 3) (Fin 3) (ZMod d))
    (hO : (∀ x : Fin 3 → ZMod d, (O *ᵥ x) ⬝ᵥ (O *ᵥ x) = x ⬝ᵥ x) ∧
      O *ᵥ (fun _ => 1) = (fun _ => 1)) :
    IsStochasticLagrangian d (graphSubspace O) := by
  classical
  obtain ⟨hquad, hone⟩ := hO
  refine ⟨?_, ?_, ?_⟩
  · rintro p ⟨y, rfl⟩
    exact sub_eq_zero.mpr (hquad y)
  · have hinj : Function.Injective ((Matrix.mulVecLin O).prod LinearMap.id) :=
      (show Function.LeftInverse Prod.snd ((Matrix.mulVecLin O).prod LinearMap.id)
        from fun _ => rfl).injective
    rw [graphSubspace, LinearMap.finrank_range_of_inj hinj]
    simp
  · exact ⟨fun _ => 1, Prod.ext hone rfl⟩

private theorem isotropic_zero_five : ∀ y : Fin 3 → ZMod 5,
    (∑ k, y k * y k) = 0 → (∑ k, y k) = 0 → y = 0 := by
  decide +kernel

private theorem zero_snd_five
    (T : Submodule (ZMod 5) ((Fin 3 → ZMod 5) × (Fin 3 → ZMod 5)))
    (hT : IsStochasticLagrangian 5 T) (y : Fin 3 → ZMod 5) (hy : (y, 0) ∈ T) :
    y = 0 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hq := hT.1 (y, 0) hy
  have ha := hT.1 ((fun _ => 1, fun _ => 1) + (y, 0)) (T.add_mem hT.2.2 hy)
  have hzero : (∑ k, y k * y k) = 0 := by simpa using hq
  apply isotropic_zero_five y hzero
  have hexpand : (∑ k, (1 + y k) * (1 + y k)) =
      3 + 2 * (∑ k, y k) + ∑ k, y k * y k := by
    simp only [Fin.sum_univ_three]
    ring
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.zero_apply, add_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at ha
  rw [hexpand, hzero] at ha
  apply mul_left_cancel₀ (by decide : (2 : ZMod 5) ≠ 0)
  linear_combination ha

private theorem sigma_graph_five
    (T : Submodule (ZMod 5) ((Fin 3 → ZMod 5) × (Fin 3 → ZMod 5)))
    (hT : IsStochasticLagrangian 5 T) :
    ∃ O ∈ stochasticOrthogonal 5, T = graphSubspace O := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let s : T →ₗ[ZMod 5] (Fin 3 → ZMod 5) := (LinearMap.snd _ _ _).comp T.subtype
  have hinj : Function.Injective s := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm
    · intro p hp
      have hy : p.val.2 = 0 := hp
      have hp : (p.val.1, p.val.2) ∈ T := p.property
      rw [hy] at hp
      have hz := zero_snd_five T hT p.val.1 hp
      change p = 0
      apply Subtype.ext
      exact Prod.ext hz hy
    · exact bot_le
  let e := LinearEquiv.ofInjectiveOfFinrankEq s hinj (by simpa using hT.2.1)
  let f := (LinearMap.fst _ _ _).comp (T.subtype.comp e.symm.toLinearMap)
  let O := LinearMap.toMatrix' f
  have hs (x : Fin 3 → ZMod 5) : (e.symm x).val.2 = x := e.apply_symm_apply x
  have hm (x : Fin 3 → ZMod 5) : (O *ᵥ x, x) ∈ T := by
    rw [LinearMap.toMatrix'_mulVec]
    change ((e.symm x).val.1, x) ∈ T
    have hp : ((e.symm x).val.1, (e.symm x).val.2) ∈ T := (e.symm x).property
    simpa only [hs x] using hp
  have hg : T = graphSubspace O := by
    ext p
    constructor
    · intro hp
      refine ⟨p.2, ?_⟩
      change (O *ᵥ p.2, p.2) = p
      apply Prod.ext
      · change O *ᵥ p.2 = p.1
        rw [LinearMap.toMatrix'_mulVec]
        change (e.symm p.2).val.1 = p.1
        have he : e.symm p.2 = ⟨p, hp⟩ := e.symm_apply_apply ⟨p, hp⟩
        exact congrArg (fun q : T => q.val.1) he
      · rfl
    · rintro ⟨x, rfl⟩
      exact hm x
  refine ⟨O, ?_, hg⟩
  unfold stochasticOrthogonal
  rw [Finset.mem_filter, and_iff_right (Finset.mem_univ _)]
  constructor
  · intro x
    simp only [dotProduct]
    have hq := hT.1 (O *ᵥ x, x) (hm x)
    exact sub_eq_zero.mp hq
  · have hp : (fun _ => 1, fun _ => 1) ∈ graphSubspace O := hg ▸ hT.2.2
    change ∃ x, (O *ᵥ x, x) = (fun _ => 1, fun _ => 1) at hp
    obtain ⟨x, hx⟩ := hp
    have hx2 : x = (fun _ => 1) := congrArg Prod.snd hx
    simpa only [hx2] using congrArg Prod.fst hx

/-- In dimension five every stochastic Lagrangian subspace is an isotropic graph. -/
theorem sigmaSubspaces_five : sigmaSubspaces 5 = isoSubspaces 5 := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  ext T
  unfold sigmaSubspaces isoSubspaces
  rw [Set.Finite.mem_toFinset, Finset.mem_image]
  change IsStochasticLagrangian 5 T ↔ ∃ O ∈ stochasticOrthogonal 5, graphSubspace O = T
  constructor
  · intro hT
    obtain ⟨O, hO, hT⟩ := sigma_graph_five T hT
    exact ⟨O, hO, hT.symm⟩
  · rintro ⟨O, hO, rfl⟩
    unfold stochasticOrthogonal at hO
    rw [Finset.mem_filter, and_iff_right (Finset.mem_univ _)] at hO
    exact graph_stochastic (d := 5) O hO

private theorem kappa_sigma_five : kappaSigma 5 2 psi = 140241723 / 24017978 := by
  unfold kappaSigma
  rw [sigmaSubspaces_five]
  exact kappa_iso

private theorem kappa_ns_five : kappaNs 5 2 psi = -3866145 / 24017978 := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hp (e : Equiv.Perm (Fin 3)) : e.permMatrix (ZMod 5) =
      (1 : Matrix (Fin 3) (Fin 3) (ZMod 5)).submatrix e id := by
    simpa only [Matrix.mul_one] using
      (PEquiv.toMatrix_toPEquiv_mul e (1 : Matrix (Fin 3) (Fin 3) (ZMod 5)))
  have hi : Function.Injective (fun e : Equiv.Perm (Fin 3) => e.permMatrix (ZMod 5)) := by
    intro a b h
    apply Equiv.ext
    intro i
    have ht := PEquiv.toMatrix_injective h
    exact Option.some.inj (congrArg (fun p : PEquiv (Fin 3) (Fin 3) => p i) ht)
  have hcard : (symSubspaces 5).card = 6 := by
    have hgi : Function.Injective (fun e : Equiv.Perm (Fin 3) =>
        graphSubspace (e.permMatrix (ZMod 5))) := fun a b h => hi (graphSubspace_injective h)
    rw [symSubspaces, Finset.card_image_of_injective _ hgi]
    norm_num [Fintype.card_perm]
  have hsub : symSubspaces 5 ⊆ sigmaSubspaces 5 := by
    intro T hT
    simp only [symSubspaces, Finset.mem_image] at hT
    obtain ⟨e, _, rfl⟩ := hT
    have ho : e.permMatrix (ZMod 5) ∈ stochasticOrthogonal 5 := by
      unfold stochasticOrthogonal
      rw [Finset.mem_filter, and_iff_right (Finset.mem_univ _)]
      constructor
      · intro x
        rw [Matrix.permMatrix_mulVec]
        exact Equiv.sum_comp e (fun k => x k * x k)
      · rw [Matrix.permMatrix_mulVec]
        rfl
    unfold sigmaSubspaces
    rw [Set.Finite.mem_toFinset]
    unfold stochasticOrthogonal at ho
    rw [Finset.mem_filter, and_iff_right (Finset.mem_univ _)] at ho
    exact graph_stochastic (d := 5) _ ho
  have hval : ∀ T ∈ symSubspaces 5, kappa 5 2 psi T = 1 := by
    intro T hT
    simp only [symSubspaces, Finset.mem_image] at hT
    obtain ⟨e, _, rfl⟩ := hT
    rw [hp, kappa_rows, kappa_identity psi normalized_psi]
  have hsum : (∑ T ∈ symSubspaces 5, kappa 5 2 psi T) = 6 := by
    rw [Finset.sum_congr rfl hval]
    simp only [Finset.sum_const, hcard, nsmul_eq_mul]
    norm_num
  rw [kappaNs, nsSubspaces, Finset.sum_sdiff_eq_sub hsub, hsum, ← kappaSigma,
    kappa_sigma_five]
  norm_num

/-- Both printed aggregate lower bounds fail for the same normalized two-qudit state. -/
theorem result : ¬ claim := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro h
  rcases h with h | h
  · have hb := h 5 (by decide) 2 psi normalized_psi
    rw [kappa_sigma_five, Complex.le_def] at hb
    norm_num at hb
  · have hb := h 5 (by decide) 2 psi normalized_psi
    rw [kappa_ns_five, Complex.le_def] at hb
    norm_num at hb

#print axioms result

end D5.S3.Quantum.Magic.CliffordThirdMomentSigmaRefutation
