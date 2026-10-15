/- GID: D5/S3/VertexAlgebra/BcGhostFockSupport
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/BcGhostFockSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed ghost modes have statewise finite normal-ordering support. -/

import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.BcGhostFockSupport

noncomputable section

variable {K : Type*} [CommRing K]

/-- Algebraic states have finite support among all finite subsets of the infinite mode set. -/
abbrev Fock (K : Type*) [CommRing K] := (Finset ℕ) →₀ K

def vacuum : Fock K := Finsupp.single ∅ 1

def sign (i : ℕ) (S : Finset ℕ) : K :=
  (-1) ^ (S.filter fun s => s < i).card

def createBasis (i : ℕ) (S : Finset ℕ) : Fock K :=
  if i ∈ S then 0 else Finsupp.single (insert i S) (sign i S)

def annihilateBasis (i : ℕ) (S : Finset ℕ) : Fock K :=
  if i ∈ S then Finsupp.single (S.erase i) (sign i S) else 0

noncomputable def create (i : ℕ) : Module.End K (Fock K) :=
  Finsupp.linearCombination K (createBasis i)

noncomputable def annihilate (i : ℕ) : Module.End K (Fock K) :=
  Finsupp.linearCombination K (annihilateBasis i)

/-- The even sites encode the b-creators and the odd sites the c-creators. -/
noncomputable def b (m : ℤ) : Module.End K (Fock K) :=
  if m ≤ -2 then create (2 * (-m - 2).toNat)
  else annihilate (2 * (m + 1).toNat + 1)

noncomputable def c (n : ℤ) : Module.End K (Fock K) :=
  if n ≤ 1 then create (2 * (1 - n).toNat + 1)
  else annihilate (2 * (n - 2).toNat)

noncomputable def normalPair (p q : ℤ) : Module.End K (Fock K) :=
  if p ≤ -2 then (b (K := K) p).comp (c q) else -((c (K := K) q).comp (b p))

/-- The union includes every occupied site in every basis state of a superposition. -/
def occupied (v : Fock K) : Finset ℕ := v.support.biUnion id

def cutoff (m : ℤ) (v : Fock K) : ℤ :=
  ((occupied v).sup id : ℕ) + (m.natAbs : ℤ) + 4

theorem annihilate_eq_zero (v : Fock K) (i : ℕ) (hi : i ∉ occupied v) :
    annihilate i v = 0 := by
  rw [annihilate, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro S hS
  have hnot : i ∉ S := by
    intro hmem
    exact hi (Finset.mem_biUnion.mpr ⟨S, hS, hmem⟩)
  simp [annihilateBasis, hnot]

theorem annihilate_eq_zero_of_sup_lt (v : Fock K) (i : ℕ)
    (hi : (occupied v).sup id < i) : annihilate i v = 0 := by
  apply annihilate_eq_zero
  intro hmem
  have : i ≤ (occupied v).sup id := Finset.le_sup (f := id) hmem
  omega

/-- Every state has an explicit finite interval of nonzero normal-ordered summands.
The interval depends on the state, not merely on the operator mode. -/
theorem normal_pair_support_interval (m : ℤ) (v : Fock K) :
    Function.support (fun k : ℤ => normalPair (m + k) (-k) v) ⊆
      Set.Icc (-cutoff m v) (cutoff m v) := by
  intro k hk
  have hmhi : m ≤ (m.natAbs : ℤ) := Int.le_natAbs
  have hmlo : -(m.natAbs : ℤ) ≤ m := by
    have h : -m ≤ (m.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -m))
    omega
  have hv : (0 : ℤ) ≤ (((occupied v).sup id : ℕ) : ℤ) := Int.natCast_nonneg _
  have hleft : -cutoff m v ≤ k := by
    by_contra h
    have hklt : k < -cutoff m v := lt_of_not_ge h
    have hp : m + k ≤ -2 := by dsimp [cutoff] at hklt; omega
    have hq : ¬ -k ≤ 1 := by dsimp [cutoff] at hklt; omega
    have hidx : (occupied v).sup id < 2 * (-k - 2).toNat := by
      have hnonneg : 0 ≤ -k - 2 := by dsimp [cutoff] at hklt; omega
      have hcast := Int.toNat_of_nonneg hnonneg
      dsimp [cutoff] at hklt
      omega
    exact hk (by
      simp [normalPair, hp, c, hq, annihilate_eq_zero_of_sup_lt v _ hidx])
  have hright : k ≤ cutoff m v := by
    by_contra h
    have hkgt : cutoff m v < k := lt_of_not_ge h
    have hp : ¬ m + k ≤ -2 := by dsimp [cutoff] at hkgt; omega
    have hidx : (occupied v).sup id < 2 * (m + k + 1).toNat + 1 := by
      have hnonneg : 0 ≤ m + k + 1 := by dsimp [cutoff] at hkgt; omega
      have hcast := Int.toNat_of_nonneg hnonneg
      dsimp [cutoff] at hkgt
      omega
    exact hk (by
      simp [normalPair, hp, b, annihilate_eq_zero_of_sup_lt v _ hidx])
  exact ⟨hleft, hright⟩

/-- The weight-(2,-1) ghost stress-tensor candidate is a linear operator, because its
normal-ordered defining sum is finite on each input separately. -/
noncomputable def L (m : ℤ) : Module.End K (Fock K) where
  toFun v := ∑ᶠ k : ℤ, (m - k : K) • normalPair (m + k) (-k) v
  map_add' v w := by
    have hf (u : Fock K) : Function.HasFiniteSupport
        (fun k : ℤ => (m - k : K) • normalPair (m + k) (-k) u) := by
      apply (Set.finite_Icc (-cutoff m u) (cutoff m u)).subset
      intro k hk
      apply normal_pair_support_interval m u
      intro hz
      exact hk (by simp only [hz, smul_zero])
    simp only [map_add, smul_add]
    exact finsum_add_distrib (hf v) (hf w)
  map_smul' a v := by
    have hf : Function.HasFiniteSupport
        (fun k : ℤ => (m - k : K) • normalPair (m + k) (-k) v) := by
      apply (Set.finite_Icc (-cutoff m v) (cutoff m v)).subset
      intro k hk
      apply normal_pair_support_interval m v
      intro hz
      exact hk (by simp only [hz, smul_zero])
    simp only [map_smul, RingHom.id_apply]
    simp_rw [smul_comm (m - _ : K) a]
    exact (smul_finsum' a hf).symm

/-- The same linear action can be computed on any interval enclosing the explicit bound. -/
theorem L_interval_sum (m : ℤ) (v : Fock K) (a z : ℤ)
    (ha : a ≤ -cutoff m v) (hz : cutoff m v ≤ z) :
    L m v = ∑ k ∈ Finset.Icc a z, (m - k : K) • normalPair (m + k) (-k) v := by
  change (∑ᶠ k : ℤ, (m - k : K) • normalPair (m + k) (-k) v) = _
  apply finsum_eq_sum_of_support_subset
  intro k hk
  have hp : k ∈ Function.support (fun j : ℤ => normalPair (m + j) (-j) v) := by
    intro hzero
    exact hk (by simp only [hzero, smul_zero])
  have hbound := normal_pair_support_interval m v hp
  simp only [Set.mem_Icc] at hbound
  simp only [Finset.mem_coe, Finset.mem_Icc]
  omega

/-- The actual negative b-modes and nonpositive shifted c-modes generate every state
from the vacuum. The assertion concerns arbitrary finite superpositions, without a cutoff. -/
theorem creation_cyclic (W : Submodule K (Fock K)) (hvac : vacuum ∈ W)
    (hb : ∀ m : ℤ, m ≤ -2 → ∀ v ∈ W, b m v ∈ W)
    (hc : ∀ n : ℤ, n ≤ 1 → ∀ v ∈ W, c n v ∈ W) : W = ⊤ := by
  have hcreate (i : ℕ) (v : Fock K) (hv : v ∈ W) : create i v ∈ W := by
    by_cases heven : i % 2 = 0
    · have hmode : b (K := K) (-(i / 2 : ℕ) - 2) = create i := by
        have hbranch : (-(i / 2 : ℕ) - 2 : ℤ) ≤ -2 := by omega
        have hind : 2 * (-(-(i / 2 : ℕ) - 2 : ℤ) - 2).toNat = i := by omega
        simp only [b, if_pos hbranch, hind]
      rw [← hmode]
      exact hb _ (by omega) v hv
    · have hmode : c (K := K) (1 - (i / 2 : ℕ)) = create i := by
        have hbranch : (1 - (i / 2 : ℕ) : ℤ) ≤ 1 := by omega
        have hind : 2 * (1 - (1 - (i / 2 : ℕ) : ℤ)).toNat + 1 = i := by omega
        simp only [c, if_pos hbranch, hind]
      rw [← hmode]
      exact hc _ (by omega) v hv
  have hsingle (S : Finset ℕ) : Finsupp.single S (1 : K) ∈ W := by
    induction S using Finset.induction_on with
    | empty => exact hvac
    | @insert i S hi ih =>
        have hprod : sign (K := K) i S * sign i S = 1 := by
          rcases neg_one_pow_eq_or K (S.filter fun s => s < i).card with h | h <;>
            simp [sign, h]
        have heq : sign (K := K) i S • create i (Finsupp.single S (1 : K)) =
            Finsupp.single (insert i S) (1 : K) := by
          simp [create, Finsupp.linearCombination_single, createBasis, hi,
            Finsupp.smul_single, hprod]
        rw [← heq]
        exact W.smul_mem _ (hcreate i _ ih)
  have hall (v : Fock K) : v ∈ W := by
    induction v using Finsupp.induction_linear with
    | zero => exact W.zero_mem
    | add v w hv hw => exact W.add_mem hv hw
    | single S a =>
        simpa only [Finsupp.smul_single, smul_eq_mul, mul_one] using W.smul_mem a (hsingle S)
  exact top_unique (fun v _ => hall v)

#check @annihilate_eq_zero
#check @annihilate_eq_zero_of_sup_lt
#check @normal_pair_support_interval
#check @L_interval_sum
#check @creation_cyclic

#print axioms annihilate_eq_zero
#print axioms annihilate_eq_zero_of_sup_lt
#print axioms normal_pair_support_interval
#print axioms L_interval_sum
#print axioms creation_cyclic

end

end D5.S3.VertexAlgebra.BcGhostFockSupport
