/- GID: D5/S3/Arith/Covering/SingleChainCofactorBound
   generality: G
   mirror-B: D5/B/S3/Arith/Covering/SingleChainCofactorBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A complete saturated prime chain forces its cofactor prime below the chain prime. -/

import D5.S3.Arith.Covering.SingleChainFreshCompletion
import D5.S3.Arith.Covering.ConcentratedPrimeSingleton
import D5.S3.Arith.Covering.PrimeFactorPureClass
import D5.S3.Arith.Congruence.ConditionalComparison.PrimeRootCompression

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open private Erdos7.OddDistinctCoveringSystem.owner_has_private_point from
  D5.S3.Arith.Covering.ConcentratedPrimeSingleton

namespace Erdos7.OddDistinctCoveringSystem

/- A complete saturated chain cannot have a larger cofactor prime.
The proof reuses the actual residual alignment and prime-root compression. -/
theorem single_chain_cofactor_lt_prime
    {n p ell : ℕ} (F : OddDistinctCoveringSystem n)
    (countMin : ∀ {N : ℕ}, OddDistinctCoveringSystem N → n ≤ N)
    (sumMin : ∀ G : OddDistinctCoveringSystem n,
      (∑ i, F.modulus i) ≤ ∑ i, G.modulus i)
    (hp : Nat.Prime p) (hell : Nat.Prime ell) (hne : p ≠ ell)
    (slot : Fin p → Fin n)
    (hmod : ∀ j, F.modulus (slot j) = p * ell ^ j.val)
    (hroot : Function.Injective (fun j => F.residue (slot j) % p))
    (hcomplete : ∀ i, p ∣ F.modulus i → ∃ j, slot j = i) :
    ell < p := by
  classical
  by_contra hnot
  have hpell : p < ell := by omega
  let zero : Fin p := ⟨0, hp.pos⟩
  let one : Fin p := ⟨1, hp.one_lt⟩
  let guard : Fin n := slot zero
  have hguard : F.modulus guard = p := by
    simpa only [guard, zero, pow_zero, mul_one] using hmod zero
  have hone : ell ∣ F.modulus (slot one) := by
    rw [hmod]
    simpa only [one, pow_one] using dvd_mul_left ell p
  obtain ⟨donor, hdonor⟩ := prime_dvd_modulus_is_present F sumMin (slot one) ell hell hone
  obtain ⟨x, _, hxOther⟩ :=
    Erdos7.OddDistinctCoveringSystem.owner_has_private_point F countMin guard
  have hxFree : ∀ i, ¬p ∣ F.modulus i → ¬x ≡ F.residue i [MOD F.modulus i] := by
    intro i hfree
    apply hxOther i
    intro heq
    subst i
    exact hfree (by rw [hguard])
  have hcofactor := single_chain_pfree_residual_subset F hp hell hne
    slot hmod hroot hcomplete x hxFree
  let c : Fin ell := ⟨x % ell, Nat.mod_lt _ hell.pos⟩
  let d : Fin ell := ⟨F.residue donor % ell, Nat.mod_lt _ hell.pos⟩
  let T : Finset (Fin ell) := {c, d}
  let R : Finset (Fin ell) := Finset.univ \ T
  let B := {b : Fin p // b.val ≠ F.residue guard % p}
  have hB : Fintype.card B < p := by
    simpa only [B, Fintype.card_fin] using
      (Fintype.card_subtype_lt
        (x := (⟨F.residue guard % p, Nat.mod_lt _ hp.pos⟩ : Fin p))
        (show ¬((F.residue guard % p) ≠ F.residue guard % p) from not_not.mpr rfl))
  have hT : T.card ≤ 2 := by
    dsimp only [T]
    calc
      (insert c ({d} : Finset (Fin ell))).card ≤
          ({d} : Finset (Fin ell)).card + 1 := Finset.card_insert_le _ _
      _ = 2 := by simp
  have hR : R.card + T.card = ell := by
    simpa only [R, Finset.card_univ, Fintype.card_fin] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
  have hsize : Fintype.card B ≤ Fintype.card R := by
    simp only [Fintype.card_coe]
    omega
  obtain ⟨embedding⟩ := Function.Embedding.nonempty_of_card_le hsize
  let sigma : B → Fin ell := fun b => (embedding b).val
  have hinj : Function.Injective sigma := by
    intro b b' heq
    exact embedding.injective (Subtype.ext heq)
  have hav (b : B) : sigma b ≠ c ∧ sigma b ≠ d := by
    have ht := (Finset.mem_sdiff.mp (embedding b).property).2
    simpa only [T, Finset.mem_insert, Finset.mem_singleton, not_or] using ht
  have hmixed : ∀ (b : B) (i : Fin n),
      ell ∣ F.modulus i → p ∣ F.modulus i → F.residue i % p = b.val.val →
      (sigma b).val ≠ F.residue i % ell := by
    intro b i heli hpi _
    obtain ⟨j, rfl⟩ := hcomplete i hpi
    have hj : j.val ≠ 0 := by
      intro hjzero
      have hdiv : ell ∣ p := by simpa only [hmod, hjzero, pow_zero, mul_one] using heli
      exact hne ((Nat.prime_dvd_prime_iff_eq hell hp).mp hdiv).symm
    have hrootEll : x % ell = F.residue (slot j) % ell :=
      (hcofactor j).of_dvd (dvd_pow_self ell hj)
    intro hsig
    apply (hav b).1
    apply Fin.ext
    exact hsig.trans hrootEll.symm
  have hcollision : ∀ (b : B) (i j : Fin n) (u : ℕ),
      Nat.Coprime u (ell*p) → F.modulus i = ell*u → F.modulus j = p*u →
      (sigma b).val ≠ F.residue i % ell := by
    intro b i j u hu hi hj
    have hpj : p ∣ F.modulus j := by rw [hj]; exact dvd_mul_right p u
    obtain ⟨k, rfl⟩ := hcomplete j hpj
    have hupow : u = ell ^ k.val :=
      Nat.eq_of_mul_eq_mul_left hp.pos (hj.symm.trans (hmod k))
    have hellNot : ¬ell ∣ u :=
      hell.coprime_iff_not_dvd.mp
        (hu.coprime_dvd_right (dvd_mul_right ell p)).symm
    have hkzero : k.val = 0 := by
      by_contra hk
      apply hellNot
      rw [hupow]
      exact dvd_pow_self ell hk
    have huone : u = 1 := by simpa only [hkzero, pow_zero] using hupow
    have hidonor : i = donor :=
      F.modulus_injective (by simpa only [hi, huone, mul_one] using hdonor.symm)
    subst i
    intro hsig
    apply (hav b).2
    apply Fin.ext
    exact hsig
  obtain ⟨N, smaller, hN⟩ := prime_root_compression F hell hp hne.symm
    donor guard hdonor hguard sigma hinj hmixed hcollision
  exact (Nat.not_lt_of_ge (countMin smaller)) hN

#print axioms single_chain_cofactor_lt_prime

end Erdos7.OddDistinctCoveringSystem
