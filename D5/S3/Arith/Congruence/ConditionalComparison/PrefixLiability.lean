/- GID: D5/S3/Arith/Congruence/ConditionalComparison/PrefixLiability
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/ConditionalComparison/PrefixLiability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prime-prefix deletion equals tail saturation of the pure anchor's private region. -/

import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Erdos7

/-- Deleting all classes above a literal prime-power parent leaves exactly the
parent and cofactor fibres represented in the pure anchor's complete private region. -/
theorem prefix_liability {L q G R k : ℕ} (modulus residue : Fin L → ℕ)
    (hq : Nat.Prime q) (hcoprime : Nat.Coprime q R)
    (hperiod : ∀ i, modulus i ∣ q ^ G * R)
    (hcover : ∀ x : ℕ, ∃ i, x ≡ residue i [MOD modulus i])
    (j : Fin L) (hpure : modulus j = q ^ (k + 1))
    (hnoContain : ∀ i,
      (q ^ (k + 1) ∣ modulus i ∧ residue i ≡ residue j [MOD q ^ k]) →
      i ≠ j → ∃ z : ℕ, z ≡ residue i [MOD modulus i] ∧
        ¬ z ≡ residue j [MOD modulus j]) :
    ∀ x : ℕ,
      (∀ i, ¬ (q ^ (k + 1) ∣ modulus i ∧ residue i ≡ residue j [MOD q ^ k]) →
        ¬ x ≡ residue i [MOD modulus i]) ↔
      x ≡ residue j [MOD q ^ k] ∧
        ∃ y : ℕ, y ≡ residue j [MOD modulus j] ∧
          (∀ i, i ≠ j → ¬ y ≡ residue i [MOD modulus i]) ∧ y ≡ x [MOD R] := by
  classical
  let removed : Fin L → Prop := fun i =>
    q ^ (k + 1) ∣ modulus i ∧ residue i ≡ residue j [MOD q ^ k]
  let hole : ℕ → Prop := fun x =>
    ∀ i, ¬ removed i → ¬ x ≡ residue i [MOD modulus i]
  have hparentDvd : q ^ k ∣ q ^ (k + 1) := pow_dvd_pow q (Nat.le_succ k)
  have hj : removed j := ⟨by rw [hpure], Nat.ModEq.refl _⟩
  have low_dvd {d : ℕ} (hd : d ∣ q ^ G * R) (hlow : ¬ q ^ (k + 1) ∣ d) :
      d ∣ q ^ k * R := by
    obtain ⟨a, b, ha, hb, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hd
    obtain ⟨e, _, rfl⟩ := (Nat.dvd_prime_pow hq).mp ha
    have hek : e ≤ k := by
      by_contra h
      have hke : k + 1 ≤ e := by omega
      exact hlow ((pow_dvd_pow q hke).trans (dvd_mul_right _ _))
    exact Nat.mul_dvd_mul (pow_dvd_pow q hek) hb
  have removed_parent {i : Fin L} (hi : removed i) {x : ℕ}
      (hxi : x ≡ residue i [MOD modulus i]) :
      x ≡ residue j [MOD q ^ k] :=
    (hxi.of_dvd (hparentDvd.trans hi.1)).trans hi.2
  have hole_parent {x : ℕ} (hx : hole x) : x ≡ residue j [MOD q ^ k] := by
    obtain ⟨i, hxi⟩ := hcover x
    by_cases hi : removed i
    · exact removed_parent hi hxi
    · exact False.elim (hx i hi hxi)
  have transport {x y : ℕ}
      (hxparent : x ≡ residue j [MOD q ^ k])
      (hyparent : y ≡ residue j [MOD q ^ k])
      (hxy : x ≡ y [MOD R]) (hx : hole x) : hole y := by
    intro i hi hyi
    by_cases hd : q ^ (k + 1) ∣ modulus i
    · exact hi ⟨hd, ((hyi.of_dvd (hparentDvd.trans hd)).symm).trans hyparent⟩
    · have hxyFull : x ≡ y [MOD q ^ k * R] :=
        (Nat.modEq_and_modEq_iff_modEq_mul (hcoprime.pow_left k)).mp
          ⟨hxparent.trans hyparent.symm, hxy⟩
      exact hx i hi ((hxyFull.of_dvd (low_dvd (hperiod i) hd)).trans hyi)
  have other_removed_misses_anchor {y : ℕ}
      (hyj : y ≡ residue j [MOD modulus j]) {i : Fin L}
      (hi : removed i) (hne : i ≠ j) : ¬ y ≡ residue i [MOD modulus i] := by
    intro hyi
    obtain ⟨z, hzi, hzj⟩ := hnoContain i hi hne
    apply hzj
    have hzy : z ≡ y [MOD q ^ (k + 1)] := (hzi.trans hyi.symm).of_dvd hi.1
    have hyq : y ≡ residue j [MOD q ^ (k + 1)] := by simpa [hpure] using hyj
    simpa [hpure] using hzy.trans hyq
  intro x
  change hole x ↔ _
  constructor
  · intro hx
    have hxparent := hole_parent hx
    obtain ⟨y, hyq, hyR⟩ :=
      Nat.chineseRemainder (hcoprime.pow_left (k + 1)) (residue j) x
    have hyparent := hyq.of_dvd hparentDvd
    have hyj : y ≡ residue j [MOD modulus j] := by simpa [hpure] using hyq
    have hyhole := transport hxparent hyparent hyR.symm hx
    refine ⟨hxparent, y, hyj, ?_, hyR⟩
    intro i hne hyi
    by_cases hi : removed i
    · exact other_removed_misses_anchor hyj hi hne hyi
    · exact hyhole i hi hyi
  · rintro ⟨hxparent, y, hyj, hyprivate, hyR⟩
    have hyparent : y ≡ residue j [MOD q ^ k] :=
      (show y ≡ residue j [MOD q ^ (k + 1)] from by simpa [hpure] using hyj).of_dvd
        hparentDvd
    have hyhole : hole y := by
      intro i hi hyi
      have hne : i ≠ j := by
        intro hij
        subst i
        exact hi hj
      exact hyprivate i hne hyi
    exact transport hyparent hxparent hyR hyhole

end Erdos7
