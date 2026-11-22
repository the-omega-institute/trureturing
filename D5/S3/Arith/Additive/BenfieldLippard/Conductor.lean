/- GID: D5/S3/Arith/Additive/BenfieldLippard/Conductor
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A bounded generator system gives a quantitative conductor for natural sums. -/

import Mathlib.NumberTheory.FrobeniusNumber
import Mathlib.Data.ZMod.Basic

namespace BenfieldLippard

/-- Bound the weight of a residue representative by the number of residues minus one,
using saturation under addition of the generators. -/
theorem bounded_conductor (S : Set ℕ) {A W : ℕ} (hA : 0 < A) (hAS : A ∈ S)
    (hW : ∀ s ∈ S, s ≤ W) (hgcd : Nat.setGcd S = 1) :
    ∀ n ≥ (A - 1) * W, n ∈ AddSubmonoid.closure S := by
  classical
  letI : NeZero A := ⟨hA.ne'⟩
  let M := AddSubmonoid.closure S
  let reach (t : ℕ) : Finset (ZMod A) :=
    Finset.univ.filter (fun z ↦ ∃ n ∈ M, n ≤ t * W ∧ (n : ZMod A) = z)
  have mem_reach (t : ℕ) (z : ZMod A) :
      z ∈ reach t ↔ ∃ n ∈ M, n ≤ t * W ∧ (n : ZMod A) = z := by
    simp [reach]
  have mono : Monotone reach := by
    intro t u htu z hz
    obtain ⟨n, hn, hnW, rfl⟩ := (mem_reach _ _).mp hz
    exact (mem_reach _ _).mpr ⟨n, hn, hnW.trans (Nat.mul_le_mul_right _ htu), rfl⟩
  have zero_reach (t : ℕ) : (0 : ZMod A) ∈ reach t :=
    (mem_reach _ _).mpr ⟨0, zero_mem M, Nat.zero_le _, Nat.cast_zero⟩
  have all_residues (z : ZMod A) : ∃ n ∈ M, (n : ZMod A) = z := by
    obtain ⟨N, hN⟩ := Nat.exists_mem_closure_of_ge S
    refine ⟨z.val + A * N, hN _ ?_ (by simp [hgcd]), ?_⟩
    · exact le_trans (by simpa using Nat.mul_le_mul_right N hA) (Nat.le_add_left _ _)
    · simp [ZMod.natCast_zmod_val]
  have saturated {t : ℕ} (heq : reach t = reach (t + 1)) : reach t = Finset.univ := by
    have step (s : ℕ) (hs : s ∈ S) (z : ZMod A) (hz : z ∈ reach t) :
        z + s ∈ reach t := by
      obtain ⟨n, hn, hnb, rfl⟩ := (mem_reach _ _).mp hz
      rw [heq]
      apply (mem_reach _ _).mpr
      refine ⟨n + s, add_mem hn (AddSubmonoid.subset_closure hs), ?_, Nat.cast_add _ _⟩
      simpa [Nat.add_mul] using Nat.add_le_add hnb (hW s hs)
    have extend (n : ℕ) (hn : n ∈ M) :
        ∀ z ∈ reach t, z + (n : ZMod A) ∈ reach t := by
      change n ∈ AddSubmonoid.closure S at hn
      induction hn using AddSubmonoid.closure_induction with
      | mem s hs => exact step s hs
      | zero => simpa using fun z (hz : z ∈ reach t) ↦ hz
      | add x y _ _ hx hy =>
        intro z hz
        simpa only [Nat.cast_add, add_assoc] using hy _ (hx _ hz)
    apply Finset.eq_univ_of_forall
    intro z
    obtain ⟨n, hn, rfl⟩ := all_residues z
    simpa using extend n hn 0 (zero_reach t)
  have grow (t : ℕ) : reach t ≠ Finset.univ → t + 1 ≤ (reach t).card := by
    induction t with
    | zero =>
      intro _
      exact Finset.card_pos.mpr ⟨0, zero_reach 0⟩
    | succ t ih =>
      intro ht
      have hstrict : reach t ⊂ reach (t + 1) :=
        Finset.ssubset_iff_subset_ne.mpr ⟨mono (Nat.le_succ t), fun h ↦ ht (h.symm.trans (saturated h))⟩
      have hprev : reach t ≠ Finset.univ := by
        intro h
        exact ht (Finset.eq_univ_of_forall fun z ↦ mono (Nat.le_succ t) (by simp [h]))
      exact Nat.succ_le_of_lt ((ih hprev).trans_lt (Finset.card_lt_card hstrict))
  have hfull : reach (A - 1) = Finset.univ := by
    by_contra h
    have hlt := Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, h⟩)
    have hcard := grow _ h
    rw [Finset.card_univ, ZMod.card] at hlt
    omega
  intro n hn
  have hnr : (n : ZMod A) ∈ reach (A - 1) := by simp [hfull]
  obtain ⟨v, hv, hvc, hvn⟩ := (mem_reach _ _).mp hnr
  have hvle : v ≤ n := hvc.trans hn
  have hdiv : A ∣ n - v := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hvle, hvn, sub_self]
  obtain ⟨c, hc⟩ := hdiv
  have hgen : A ∈ M := AddSubmonoid.subset_closure hAS
  have hadd : A * c ∈ M := by simpa [nsmul_eq_mul, Nat.mul_comm] using nsmul_mem hgen c
  have he : n = v + A * c := by omega
  rw [he]
  exact add_mem hv hadd

end BenfieldLippard
