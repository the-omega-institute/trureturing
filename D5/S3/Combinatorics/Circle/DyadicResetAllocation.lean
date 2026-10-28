/- GID: D5/S3/Combinatorics/Circle/DyadicResetAllocation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Circle/DyadicResetAllocation
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.Finset.Max]
   utility: none
   digest: Dyadic residue allocation selects actual coins and fills coupled reset bins. -/
module
public import D5.S3.Combinatorics.Transportation.DyadicAllocation

/-! Exact coin selection and coupled reset-bin allocation use the same criterion. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.DyadicResetAllocation
open scoped BigOperators
open D5.S3.Combinatorics.Transportation.DyadicAllocation

/-- Selection of an exact power of two is a two-bin application of labelled
allocation, rather than a second selection construction. -/
theorem select_power {α : Type*} [DecidableEq α] (S : Finset α)
    (e : α → ℕ) (b : ℕ) (he : ∀ a ∈ S, e a ≤ b)
    (hmass : 2 ^ b ≤ ∑ a ∈ S, 2 ^ e a) :
    ∃ R : Finset α, R ⊆ S ∧ (∑ a ∈ R, 2 ^ e a) = 2 ^ b := by
  classical
  let T := ∑ a ∈ S, 2 ^ e a
  let cap : Fin 2 → ℕ := fun i => if i = 0 then 2 ^ b else T - 2 ^ b
  have htotal : (∑ a ∈ S, 2 ^ e a) = ∑ i, cap i := by
    simp only [Fin.sum_univ_two, cap, ite_true, show (1 : Fin 2) ≠ 0 by decide,
      ite_false]
    dsimp [T] at *
    omega
  have hsingle : Allocation S e (fun _ : Unit => T) := by
    refine ⟨fun _ => S, by simp, ?_, ?_, by simp [T]⟩
    · intro i j hij
      exact False.elim (hij (Subsingleton.elim i j))
    · intro a ha; exact ⟨(), ha⟩
  have hlow := (allocation_iff_residues S e (fun _ : Unit => T)
    (by simp [T])).mp hsingle
  have hr : ∀ q : ℕ, (∑ i, cap i % 2 ^ q) ≤
      ∑ a ∈ S.filter (fun a => e a < q), 2 ^ e a := by
    intro q
    simp only [Fin.sum_univ_two, cap, ite_true, show (1 : Fin 2) ≠ 0 by decide,
      ite_false]
    by_cases hq : q ≤ b
    · have hd : 2 ^ q ∣ (2 : ℕ) ^ b := pow_dvd_pow 2 hq
      have hsub : (T - 2 ^ b) % 2 ^ q = T % 2 ^ q := by
        have hz : T - 2 ^ b + 2 ^ b = T := Nat.sub_add_cancel hmass
        have h := congrArg (fun n => n % 2 ^ q) hz
        simpa [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd] using h
      rw [Nat.mod_eq_zero_of_dvd hd, zero_add, hsub]
      simpa using hlow q
    · have hf : S.filter (fun a => e a < q) = S := by
        apply Finset.filter_true_of_mem
        intro a ha
        have := he a ha
        omega
      rw [hf]
      have h1 := Nat.mod_le (2 ^ b) (2 ^ q)
      have h2 := Nat.mod_le (T - 2 ^ b) (2 ^ q)
      dsimp [T] at *
      omega
  obtain ⟨K, hK, _, _, hb⟩ := allocation_of_residues S e cap htotal hr
  exact ⟨K 0, hK 0, by simpa [cap] using hb 0⟩

end D5.S3.Combinatorics.Circle.DyadicResetAllocation
