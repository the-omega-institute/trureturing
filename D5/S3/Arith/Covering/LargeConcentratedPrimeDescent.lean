/- GID: D5/S3/Arith/Covering/LargeConcentratedPrimeDescent
   generality: G
   mirror-B: D5/B/S3/Arith/Covering/LargeConcentratedPrimeDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A concentrated pure prime at least 73 cannot occur under terminal-donor period and minimality hypotheses. -/

import D5.S3.Arith.Congruence.ConditionalComparison.TerminalDonor
import D5.S3.Arith.Covering.ConcentratedPrimeSingleton

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos7.OddDistinctCoveringSystem

open scoped BigOperators

variable {L : ℕ}

private theorem private_mod9_card_le_three
    (F : OddDistinctCoveringSystem L) (g : Fin L) (a : ℕ)
    (hconc : ∀ x, Private F g x → x ≡ a [MOD 3]) :
    Nat.card {v : Fin 9 // ∃ y : ℕ,
      y ≡ F.residue g [MOD F.modulus g] ∧
      (∀ i : Fin L, i ≠ g → ¬ y ≡ F.residue i [MOD F.modulus i]) ∧
      y % 9 = v.val} ≤ 3 := by
  classical
  let S : Finset (Fin 9) := Finset.univ.filter (fun v => ∃ y : ℕ,
      y ≡ F.residue g [MOD F.modulus g] ∧
      (∀ i : Fin L, i ≠ g → ¬ y ≡ F.residue i [MOD F.modulus i]) ∧
      y % 9 = v.val)
  have hcard : S.card = Nat.card {v : Fin 9 // ∃ y : ℕ,
      y ≡ F.residue g [MOD F.modulus g] ∧
      (∀ i : Fin L, i ≠ g → ¬ y ≡ F.residue i [MOD F.modulus i]) ∧
      y % 9 = v.val} := by
    rw [Nat.card_eq_fintype_card]
    simpa [S] using (Fintype.card_coe S).symm
  rw [← hcard]
  let f : S → Fin 3 := fun v => ⟨v.1.val / 3, by
    have hv := v.1.isLt
    omega⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hxy' : x.1.val / 3 = y.1.val / 3 := congrArg Fin.val hxy
    have hxprop : ∃ xx : ℕ,
        xx ≡ F.residue g [MOD F.modulus g] ∧
        (∀ i : Fin L, i ≠ g → ¬xx ≡ F.residue i [MOD F.modulus i]) ∧
        xx % 9 = x.1.val := by
      have hxmem := x.property
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hxmem
      exact hxmem
    have hyprop : ∃ yy : ℕ,
        yy ≡ F.residue g [MOD F.modulus g] ∧
        (∀ i : Fin L, i ≠ g → ¬yy ≡ F.residue i [MOD F.modulus i]) ∧
        yy % 9 = y.1.val := by
      have hymem := y.property
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hymem
      exact hymem
    obtain ⟨xx, hxx, hxpriv, hxmod⟩ := hxprop
    obtain ⟨yy, hyy, hypriv, hymod⟩ := hyprop
    have hx3 := hconc xx ⟨hxx, hxpriv⟩
    have hy3 := hconc yy ⟨hyy, hypriv⟩
    change xx % 3 = a % 3 at hx3
    change yy % 3 = a % 3 at hy3
    have hxv3 : x.1.val % 3 = a % 3 := by
      rw [← hxmod, Nat.mod_mod_of_dvd xx (by decide : 3 ∣ 9)]
      exact hx3
    have hyv3 : y.1.val % 3 = a % 3 := by
      rw [← hymod, Nat.mod_mod_of_dvd yy (by decide : 3 ∣ 9)]
      exact hy3
    have hxlt := x.1.isLt
    have hylt := y.1.isLt
    omega
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_fin] using hc

/-- A concentrated pure prime at least 73 is incompatible with a
count-then-sum minimal cover when the terminal-donor period factorization is
available. The conclusion is a strict-descent contradiction, not an
unrestricted covering theorem. -/
theorem no_large_concentrated_pure_prime
    (F : OddDistinctCoveringSystem L)
    (hcountMin : ∀ {N : ℕ}, OddDistinctCoveringSystem N → L ≤ N)
    (hsumMin : ∀ H : OddDistinctCoveringSystem L,
      (∑ i, F.modulus i) ≤ ∑ i, H.modulus i)
    (p : ℕ) (hp : Nat.Prime p) (hp73 : 73 ≤ p)
    (g : Fin L) (hg : F.modulus g = p)
    (a : ℕ) (hconc : ∀ x, Private F g x → x ≡ a [MOD 3])
    (G W : ℕ) (hW : Nat.Coprime W (3 * p))
    (hperiod : ∀ i, F.modulus i ∣ 9 * p ^ G * W) : False := by
  have hp27 : 27 < p := by omega
  have hcard := private_mod9_card_le_three F g a hconc
  have hcap : 27 * Nat.card {v : Fin 9 // ∃ y : ℕ,
      y ≡ F.residue g [MOD F.modulus g] ∧
      (∀ i : Fin L, i ≠ g → ¬ y ≡ F.residue i [MOD F.modulus i]) ∧
      y % 9 = v.val} + 1 ≤ p + 9 := by omega
  obtain ⟨L', modulus', residue', hcover', hnonunit', hL', hsum', hinj', hodd'⟩ :=
    Erdos7.terminal_donor_descent (k := 0) F.modulus F.residue
      F.covers F.modulus_one_lt hp hW hperiod g (by simpa using hg) hp27 hcap
  by_cases hlt : L' < L
  · exact (Nat.not_lt_of_ge (hcountMin
      { modulus := modulus'
        residue := residue'
        covers := hcover'
        modulus_one_lt := hnonunit'
        modulus_odd := by intro i; exact hodd' (fun j => F.modulus_odd j) i
        modulus_injective := hinj' F.modulus_injective })) hlt
  · have heq : L' = L := by omega
    subst L'
    let H : OddDistinctCoveringSystem L :=
      { modulus := modulus'
        residue := residue'
        covers := hcover'
        modulus_one_lt := hnonunit'
        modulus_odd := by intro i; exact hodd' (fun j => F.modulus_odd j) i
        modulus_injective := hinj' F.modulus_injective }
    have hmin := hsumMin H
    exact (Nat.not_lt_of_ge hmin) hsum'

end Erdos7.OddDistinctCoveringSystem
