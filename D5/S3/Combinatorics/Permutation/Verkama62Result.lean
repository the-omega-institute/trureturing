/- GID: D5/S3/Combinatorics/Permutation/Verkama62Result
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permutation/Verkama62Result
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The exact rational inversion bound for every ordinarily two-connected 351624-avoiding permutation. -/

import D5.S3.Combinatorics.Permutation.Verkama62Run

/-! Ordinary vertex connectivity constructs a complete northeast ear run. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Permutation.Verkama62Local

open D5.S3.Combinatorics.IndecomposableInversion

private theorem run_size {n : ℕ} {π : Equiv.Perm (Fin n)} {S : Finset (Fin n)}
    (run : EarRun π S) : 3 ≤ S.card := by
  classical
  induction run with
  | triangle a b c hab hbc hba hcb =>
    simp [ne_of_lt hab, ne_of_lt hbc, ne_of_lt (hab.trans hbc)]
  | square a b c d hab hbc hcd hcv hda hav =>
    simp [ne_of_lt hab, ne_of_lt hbc, ne_of_lt hcd, ne_of_lt (hab.trans hbc),
      ne_of_lt (hab.trans (hbc.trans hcd)), ne_of_lt (hbc.trans hcd)]
  | @singleton S run x hx hd ih =>
    have := Finset.card_le_card (Finset.subset_insert x S)
    omega
  | @double S run e ih =>
    have h₁ := Finset.card_le_card (Finset.subset_insert e.v S)
    have h₂ := Finset.card_le_card (Finset.subset_insert e.u (insert e.v S))
    omega

/-- The full ordinary connectivity hypothesis supplies an ear run on every point. -/
theorem complete_run {n : ℕ} (π : Equiv.Perm (Fin n)) (hn : 3 ≤ n)
    (hc : (valueGraph π).Connected)
    (hd : ∀ v, ((valueGraph π).induce {v}ᶜ).Connected) : EarRun π Finset.univ := by
  classical
  let z : Fin n := ⟨0, by omega⟩
  let b := π.symm z
  have hz : z.val = 0 := rfl
  have hb : (π b).val = 0 := by simp [b, z]
  have hzb : z ≠ b := by
    intro h
    have hbz : π.symm z = z := h.symm
    letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    obtain ⟨a, ha⟩ := hc.preconnected.exists_adj_of_nontrivial z
    rw [value_adj, hbz] at ha
    rcases ha with ha | ha
    · have := ha.2; change (π.symm a).val < 0 at this; omega
    · have := ha.1; change a.val < 0 at this; omega
  have finish : ∀ k : ℕ, ∀ S : Finset (Fin n), n - S.card = k →
      EarRun π S → z ∈ S → b ∈ S → EarRun π Finset.univ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro S hk run hzS hbS
      by_cases hp : S = Finset.univ
      · simpa [hp] using run
      have hScard : S.card ≤ n := by
        simpa only [Finset.card_univ, Fintype.card_fin] using
          Finset.card_le_card (Finset.subset_univ S)
      rcases anchored_extension π S (run_size run) (fun w _ => run.robust w)
        z b hz hb hzb hzS hbS hp hc hd with ⟨u, hu, hdegree⟩ | he
      · let T := insert u S
        have hTcard : T.card = S.card + 1 := Finset.card_insert_of_notMem hu
        have hTle : T.card ≤ n := by
          simpa only [Finset.card_univ, Fintype.card_fin] using
            Finset.card_le_card (Finset.subset_univ T)
        exact ih (n - T.card) (by omega) T rfl (run.singleton u hu hdegree)
          (Finset.mem_insert_of_mem hzS) (Finset.mem_insert_of_mem hbS)
      · obtain ⟨e⟩ := he
        let T := insert e.u (insert e.v S)
        have huv : e.u ≠ e.v := ne_of_lt (e.hux.trans e.hxv)
        have hTcard : T.card = S.card + 2 := by
          dsimp [T]
          rw [Finset.card_insert_of_notMem (by simp [huv, e.hu]),
            Finset.card_insert_of_notMem e.hv]
        have hTle : T.card ≤ n := by
          simpa only [Finset.card_univ, Fintype.card_fin] using
            Finset.card_le_card (Finset.subset_univ T)
        exact ih (n - T.card) (by omega) T rfl (run.double e)
          (by simp [T, hzS]) (by simp [T, hbS])
  obtain ⟨S, run, hzS, hbS⟩ := anchored_start π hn hc hd
  exact finish _ S rfl run hzS hbS

/-- Verkama Conjecture 6.2, with its unchanged classical avoidance,
    ordinary vertex-2-connectivity, and exact rational comparison. -/
theorem result {n : ℕ} (π : Equiv.Perm (Fin n)) (hn : 3 ≤ n)
    (havoid : ¬ ContainsOneBased π)
    (hc : (valueGraph π).Connected)
    (hd : ∀ v, ((valueGraph π).induce {v}ᶜ).Connected) :
    (7 / 4 : ℚ) * n - 3 ≤ (FranklinInversionDefs.inv (PSW.word π) : ℚ) :=
  rational_bound_of_ear_run π havoid (complete_run π hn hc hd)

end D5.S3.Combinatorics.Permutation.Verkama62Local
