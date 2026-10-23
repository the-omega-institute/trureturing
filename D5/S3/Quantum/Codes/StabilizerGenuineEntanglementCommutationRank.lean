/- GID: D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank
   generality: G
   mirror-B: D5/B/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Genuine entanglement forces the Makuta--Kuzaka--Augusiak commutation-rank lower bound. -/

import D5.S3.Quantum.Codes.QuditStabilizerProductVector
import Mathlib.FieldTheory.ChevalleyWarning

/-!
# The commutation-rank obstruction

Genuine entanglement forbids a vanishing coordinate subsum of the commutation space.
Chevalley--Warning converts this obstruction into a lower bound on its dimension.
-/

section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Module
open D5.S3.Quantum.Codes.QuditStabilizerProductVector

namespace D5.S3.Quantum.Codes.StabilizerGenuineEntanglementCommutationRank

noncomputable section

def stabilizerSubspace {N p k : ℕ} [NeZero p]
    (G : Fin k → PauliWord N p) :
    Submodule ℂ ((Fin N → ZMod p) → ℂ) :=
  { carrier := {ψ | ∀ i, (pauliWordOperator (G i)).mulVec ψ = ψ}
    zero_mem' := by simp
    add_mem' := by intro ψ φ hψ hφ i; rw [Matrix.mulVec_add, hψ i, hφ i]
    smul_mem' := by intro c ψ hψ i; rw [Matrix.mulVec_smul, hψ i] }

def productAcross {N p : ℕ} (Q : Set (Fin N))
    (ψ : (Fin N → ZMod p) → ℂ) : Prop :=
  ∃ u : (Q → ZMod p) → ℂ, ∃ v : ((Qᶜ : Set (Fin N)) → ZMod p) → ℂ,
    ∀ x, ψ x = u (fun q => x q.1) * v (fun q => x q.1)

def genuinelyEntangled {N p k : ℕ} [NeZero p]
    (G : Fin k → PauliWord N p) : Prop :=
  ∀ ψ, ψ ∈ stabilizerSubspace G → ψ ≠ 0 →
    ∀ Q : Set (Fin N), Q.Nonempty → Qᶜ.Nonempty → ¬ productAcross Q ψ

def commutationSpace {N p k : ℕ} [Fact p.Prime]
    (G : Fin k → PauliWord N p) :
    Submodule (ZMod p) (Fin N → ZMod p) :=
  Submodule.span (ZMod p) (Set.range (fun ij : Fin k × Fin k =>
    commutationVector (G ij.1) (G ij.2)))

def generatedOperators {N p k : ℕ} [NeZero p]
    (G : Fin k → PauliWord N p) : Submonoid (Matrix (Fin N → ZMod p) (Fin N → ZMod p) ℂ) :=
  Submonoid.closure (Set.range (fun i => pauliWordOperator (G i)))

def IsStabilizer {N p k : ℕ} [NeZero p]
    (G : Fin k → PauliWord N p) : Prop :=
  (∀ i j, Commute (pauliWordOperator (G i)) (pauliWordOperator (G j))) ∧
    (∀ A ∈ generatedOperators G, ∀ c : ℂ,
      A = Matrix.scalar (Fin N → ZMod p) c → c = 1)

def claim : Prop :=
  ∀ (N p k : ℕ), 1 ≤ N → ∀ hp : Nat.Prime p,
    ∀ G : Fin k → PauliWord N p,
      @IsStabilizer N p k ⟨hp.ne_zero⟩ G →
      @genuinelyEntangled N p k ⟨hp.ne_zero⟩ G →
      (N - 1 + (p - 2)) / (p - 1) ≤
        Module.finrank (ZMod p) (@commutationSpace N p k ⟨hp⟩ G)

private theorem zero_sum_subset_exists {p m r : ℕ} [Fact p.Prime]
    (u : Fin r → Fin m → ZMod p) (h : r * (p - 1) < m) :
    ∃ Q : Finset (Fin m), Q.Nonempty ∧ ∀ i, ∑ j ∈ Q, u i j = 0 := by
  classical
  let f : Fin r → MvPolynomial (Fin m) (ZMod p) := fun i =>
    ∑ j, MvPolynomial.C (u i j) * MvPolynomial.X j ^ (p - 1)
  have hp : 0 < p - 1 := Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  have hdegree (i : Fin r) : (f i).totalDegree ≤ p - 1 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro j hj
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  have hsum : (∑ i, (f i).totalDegree) < Fintype.card (Fin m) := by
    calc
      (∑ i, (f i).totalDegree) ≤ ∑ _i : Fin r, (p - 1) :=
        Finset.sum_le_sum (fun i _ => hdegree i)
      _ = r * (p - 1) := by simp
      _ < Fintype.card (Fin m) := by simpa using h
  let : Fintype {x : Fin m → ZMod p //
      ∀ i ∈ (Finset.univ : Finset (Fin r)), MvPolynomial.eval x (f i) = 0} :=
    @Subtype.fintype _
      (fun x : Fin m → ZMod p =>
        ∀ i ∈ (Finset.univ : Finset (Fin r)), MvPolynomial.eval x (f i) = 0)
      (fun _ => Finset.decidableDforallFinset) inferInstance
  have hdiv : p ∣ Fintype.card {x : Fin m → ZMod p //
      ∀ i ∈ (Finset.univ : Finset (Fin r)), MvPolynomial.eval x (f i) = 0} :=
    char_dvd_card_solutions_of_sum_lt p hsum
  have hz (i : Fin r) : MvPolynomial.eval (0 : Fin m → ZMod p) (f i) = 0 := by
    simp [f, zero_pow hp.ne']
  have hex : ∃ x : Fin m → ZMod p, x ≠ 0 ∧
      ∀ i, MvPolynomial.eval x (f i) = 0 := by
    by_contra hn
    have hall (x : Fin m → ZMod p) (hx : ∀ i, MvPolynomial.eval x (f i) = 0) :
        x = 0 := by
      by_contra hx0
      exact hn ⟨x, hx0, hx⟩
    have hcard : Fintype.card {x : Fin m → ZMod p //
        ∀ i ∈ (Finset.univ : Finset (Fin r)), MvPolynomial.eval x (f i) = 0} = 1 := by
      apply Fintype.card_eq_one_iff.mpr
      refine ⟨⟨0, fun i _ => hz i⟩, ?_⟩
      intro x
      apply Subtype.ext
      exact hall x.1 (fun i => x.2 i (Finset.mem_univ i))
    rw [hcard] at hdiv
    exact (Fact.out : p.Prime).not_dvd_one hdiv
  obtain ⟨x, hx, hfx⟩ := hex
  refine ⟨Finset.univ.filter (fun j => x j ≠ 0), ?_, ?_⟩
  · by_contra hQ
    apply hx
    funext j
    by_contra hj
    exact hQ ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  · intro i
    have hpow (j : Fin m) : x j ^ (p - 1) = if x j ≠ 0 then 1 else 0 := by
      split_ifs with hj
      · exact ZMod.pow_card_sub_one_eq_one hj
      · simp only [not_not] at hj
        simp [hj, zero_pow hp.ne']
    have he := hfx i
    simpa [f, hpow, Finset.sum_filter] using he

private theorem rank_bound_of_no_vanishing_subsum {n p : ℕ} [Fact p.Prime]
    (K : Submodule (ZMod p) (Fin (n + 1) → ZMod p))
    (hno : ∀ Q : Finset (Fin n), Q.Nonempty →
      ∃ v ∈ K, ∑ j ∈ Q, v j.castSucc ≠ 0) :
    n ≤ Module.finrank (ZMod p) K * (p - 1) := by
  classical
  by_contra hn
  let b := Module.finBasis (ZMod p) K
  obtain ⟨Q, hQ, hu⟩ := zero_sum_subset_exists
    (fun i j => (b i).1 j.castSucc) (Nat.lt_of_not_ge hn)
  let L : K →ₗ[ZMod p] ZMod p :=
    { toFun := fun v => ∑ j ∈ Q, v.1 j.castSucc
      map_add' := by intro v w; simp [Finset.sum_add_distrib]
      map_smul' := by intro c v; simp [Finset.mul_sum] }
  have hL : L = 0 := b.ext (fun i => hu i)
  obtain ⟨v, hv, hne⟩ := hno Q hQ
  exact hne (congrArg (fun T : K →ₗ[ZMod p] ZMod p => T ⟨v, hv⟩) hL)

private theorem no_vanishing_subsum {n p k : ℕ} [Fact p.Prime]
    (G : Fin k → PauliWord (n + 1) p) (hS : IsStabilizer G)
    (hGE : genuinelyEntangled G) (Q : Finset (Fin n)) (hQ : Q.Nonempty) :
    ∃ v ∈ commutationSpace G, ∑ j ∈ Q, v j.castSucc ≠ 0 := by
  classical
  by_contra! hn
  let S : Finset (PauliWord (n + 1) p) := Finset.univ.image G
  have hclosure :
      Submonoid.closure (pauliWordOperator '' (S : Set (PauliWord (n + 1) p))) ≤
        generatedOperators G := by
    apply Submonoid.closure_le.mpr
    rintro A ⟨a, ha, rfl⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact Submonoid.subset_closure ⟨i, rfl⟩
  have hV := common_fixed_subspace_nontrivial S
    (fun A hA c hc => hS.2 A (hclosure hA) c hc)
  let R : Set (Fin (n + 1)) := (Q.image Fin.castSucc : Finset (Fin (n + 1)))
  have hR : R.Nonempty := by
    obtain ⟨j, hj⟩ := hQ
    exact ⟨j.castSucc, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
  have hRc : Rᶜ.Nonempty := by
    refine ⟨Fin.last n, ?_⟩
    change Fin.last n ∉ Q.image Fin.castSucc
    rintro hlast
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hlast
    exact Fin.castSucc_ne_last j heq
  have hsum (v : Fin (n + 1) → ZMod p) :
      (∑ j : R, v j.1) = ∑ j ∈ Q, v j.castSucc := by
    change (∑ j : (Q.image Fin.castSucc : Finset (Fin (n + 1))), v j.1) = _
    rw [Finset.sum_coe_sort, Finset.sum_image]
    exact fun a ha b hb heq => Fin.castSucc_injective _ heq
  have hcommQ : ∀ a ∈ S, ∀ b ∈ S, ∑ j : R, commutationVector a b j.1 = 0 := by
    rintro a ha b hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    rw [hsum]
    exact hn _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  obtain ⟨ψ, hψ, hfix, hprod⟩ := product_vector_of_restricted_commuting S R
    (by
      intro a ha b hb
      convert! hcommQ a ha b hb using 1
      apply Finset.sum_congr (by ext j; simp)
      intro j hj
      rfl) hV
  have hψmem : ψ ∈ stabilizerSubspace G := fun i =>
    hfix (G i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  exact hGE ψ hψmem hψ R hR hRc hprod

theorem result : claim := by
  intro N p k hN hp G hS hGE
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have hbound := rank_bound_of_no_vanishing_subsum (commutationSpace G)
    (no_vanishing_subsum G hS hGE)
  have hpos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  change (n + (p - 2)) / (p - 1) ≤ Module.finrank (ZMod p) (commutationSpace G)
  apply (Nat.div_le_iff_le_mul_add_pred hpos).mpr
  have hbound' : n ≤ (p - 1) * Module.finrank (ZMod p) (commutationSpace G) := by
    simpa only [Nat.mul_comm] using hbound
  simpa only [Nat.sub_sub] using Nat.add_le_add_right hbound' (p - 2)

end

end D5.S3.Quantum.Codes.StabilizerGenuineEntanglementCommutationRank


end
