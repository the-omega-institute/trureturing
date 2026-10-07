/- GID: D5/S3/Arith/Covering/SingleChainQLadderCapacity
   generality: G
   mirror-B: D5/B/S3/Arith/Covering/SingleChainQLadderCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A complete p-chain leaves at most q-2 fresh q-ell heights when q is a smaller nonchain prime. -/

import D5.S3.Arith.Covering.SingleChainFreshCompletion
import D5.S3.Arith.Covering.PrimeFactorPureClass
import D5.S3.Arith.Congruence.ConditionalComparison.PrimeRootCompression

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos7.OddDistinctCoveringSystem

open scoped BigOperators

/- The complete p*ell^j inventory makes the prime-root compression collision
   image equal to the occupied q*ell^j heights. -/
theorem single_chain_q_ladder_height_bound
    {n p ell q : ℕ} (F : OddDistinctCoveringSystem n)
    (countMin : ∀ {N : ℕ}, OddDistinctCoveringSystem N → n ≤ N)
    (sumMin : ∀ G : OddDistinctCoveringSystem n,
      (∑ i, F.modulus i) ≤ ∑ i, G.modulus i)
    (hp : Nat.Prime p) (hell : Nat.Prime ell) (hq : Nat.Prime q)
    (hqp : q < p) (hqell : q ≠ ell)
    (slot : Fin p → Fin n)
    (hmod : ∀ j, F.modulus (slot j) = p * ell ^ j.val)
    (hcomplete : ∀ i, p ∣ F.modulus i → ∃ j, slot j = i)
    (hqsupport : ∃ i, q ∣ F.modulus i) :
    (freshLadderHeights F p ell q).card ≤ q - 2 := by
  classical
  obtain ⟨i, hqi⟩ := hqsupport
  obtain ⟨guard, hguard⟩ := prime_dvd_modulus_is_present F sumMin i q hq hqi
  let occupied : Finset (Fin p) := Finset.univ.filter fun j =>
    ∃ i : Fin n, F.modulus i = q * ell ^ j.val
  have hoccupied_lower : p - q + 2 ≤ occupied.card := by
    by_contra hfail
    have hocc : occupied.card ≤ p - q + 1 := by omega
    let T : Finset (Fin p) := occupied.image (fun j : Fin p =>
      (⟨F.residue (slot j) % p, Nat.mod_lt _ hp.pos⟩ : Fin p))
    let R : Finset (Fin p) := Finset.univ \ T
    have hT : T.card ≤ occupied.card := by
      dsimp only [T]
      exact Finset.card_image_le
    have hR : R.card + T.card = p := by
      simpa only [R, Finset.card_univ, Fintype.card_fin] using
        Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
    let B := {b : Fin q // b.val ≠ F.residue guard % q}
    have hB : Fintype.card B < q := by
      simpa only [B, Fintype.card_fin] using
        (Fintype.card_subtype_lt
          (x := (⟨F.residue guard % q, Nat.mod_lt _ hq.pos⟩ : Fin q))
          (show ¬((F.residue guard % q) ≠ F.residue guard % q) from
            not_not.mpr rfl))
    have hsize : Fintype.card B ≤ Fintype.card R := by
      simp only [Fintype.card_coe]
      omega
    obtain ⟨embedding⟩ := Function.Embedding.nonempty_of_card_le hsize
    let sigma : B → Fin p := fun b => (embedding b).val
    have hinj : Function.Injective sigma := by
      intro b b' heq
      exact embedding.injective (Subtype.ext heq)
    have hav (b : B) : sigma b ∉ T :=
      (Finset.mem_sdiff.mp (embedding b).property).2
    have hmixed : ∀ (b : B) (i : Fin n),
        p ∣ F.modulus i → q ∣ F.modulus i → F.residue i % q = b.val.val →
        (sigma b).val ≠ F.residue i % p := by
      intro b i hpi hqi _
      obtain ⟨j, rfl⟩ := hcomplete i hpi
      rw [hmod] at hqi
      rcases hq.dvd_mul.mp hqi with hqpdiv | hqelldiv
      · exact False.elim ((Nat.ne_of_lt hqp)
          ((Nat.prime_dvd_prime_iff_eq hq hp).mp hqpdiv))
      · exact False.elim (hqell ((Nat.prime_dvd_prime_iff_eq hq hell).mp
          (hq.dvd_of_dvd_pow hqelldiv)))
    have hcollision : ∀ (b : B) (i j : Fin n) (u : ℕ),
        Nat.Coprime u (p*q) → F.modulus i = p*u → F.modulus j = q*u →
        (sigma b).val ≠ F.residue i % p := by
      intro b i j u hu hi hj hsig
      have hpi : p ∣ F.modulus i := by
        rw [hi]
        exact dvd_mul_right p u
      obtain ⟨k, rfl⟩ := hcomplete i hpi
      have hupow : u = ell ^ k.val := by
        apply Nat.eq_of_mul_eq_mul_left hp.pos
        exact hi.symm.trans (hmod k)
      have hj' : F.modulus j = q * ell ^ k.val := by simpa [hupow] using hj
      have hkOcc : k ∈ occupied := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        exact ⟨j, hj'⟩
      have hmem : sigma b ∈ T := by
        apply Finset.mem_image.mpr
        refine ⟨k, hkOcc, ?_⟩
        apply Fin.ext
        dsimp only [sigma]
        exact hsig.symm
      exact (hav b) hmem
    obtain ⟨N, G, hN⟩ := prime_root_compression F hp hq
      (Ne.symm (Nat.ne_of_lt hqp)) (slot ⟨0, hp.pos⟩) guard
      (by simpa only [hmod, pow_zero, mul_one]) hguard sigma hinj hmixed hcollision
    exact (Nat.not_lt_of_ge (countMin G)) hN
  let U := freshLadderHeights F p ell q
  have hU : U = Finset.univ \ occupied := by
    ext j
    simp only [U, freshLadderHeights, occupied, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_sdiff, not_exists]
  have hcard : U.card + occupied.card = p := by
    rw [hU]
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ occupied)
  change U.card ≤ q - 2
  omega

#print axioms single_chain_q_ladder_height_bound

end Erdos7.OddDistinctCoveringSystem
