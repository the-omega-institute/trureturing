/- GID: D5/S3/Arith/Additive/PlasticGappedFamily
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/PlasticGappedFamily
   mirror-E: none(waiver:exact-gapped-family-count)
   anchors: []
   utility: none
   digest: A gapped plastic-power family has exact large-size and nine-point sum counts. -/

import D5.S3.Arith.Additive.PlasticPowerCollisions

/-! Source: SUM_PRODUCT_PLASTIC_POWER_FAMILIES, Proposition 5.1, atom
20e95279ea783acb6bfbee6655e99cea266273d8ba7f387c4380bafa18d53bfb.
The full source is retained: nine-point strict comparison on actual real sumsets,
and every n >= 10 with literal four-template counts, actual image cardinality,
actual sumset cardinality, and a missing interior integer. No assertion of global
minimality is imported from the separately delivered extremal theorem.

Search: PlasticNestedFamily treats {0,3} union [5,n+2], not this family.
The frozen sumset_card_add_template_counts supplies the collision identity;
no new collision classification or generic cardinality identity is reproved.
The new combinatorial content identifies all four filters for the gapped family.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Additive.PlasticGappedFamily

open scoped Pointwise
open PlasticPowerCollisions

/-- For n ≥ 2, the n-point exponent family with the interior exponent one missing. -/
def family (n : ℕ) : Finset ℤ := insert 0 (Finset.Icc 2 (n : ℤ))

private theorem family_card (n : ℕ) (hn : 2 ≤ n) : (family n).card = n := by
  rw [family, Finset.card_insert_of_notMem (by simp), Int.card_Icc]
  omega

private theorem filters (n : ℕ) (hn : 10 ≤ n) :
    ((family n).filter fun t => t+2 ∈ family n ∧ t+3 ∈ family n ∧ t+4 ∈ family n).card = n-4 ∧
    ((family n).filter fun t => t+3 ∈ family n ∧ t+5 ∈ family n ∧ t+6 ∈ family n).card = n-6 ∧
    ((family n).filter fun t => t+5 ∈ family n ∧ t+7 ∈ family n).card = n-7 ∧
    ((family n).filter fun t => t+5 ∈ family n ∧ t+8 ∈ family n ∧ t+9 ∈ family n).card = n-9 := by
  have h4 : (family n).filter (fun t => t+2 ∈ family n ∧ t+3 ∈ family n ∧ t+4 ∈ family n) =
      insert 0 (Finset.Icc 2 ((n : ℤ)-4)) := by
    ext t
    simp only [family, Finset.mem_filter, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h6 : (family n).filter (fun t => t+3 ∈ family n ∧ t+5 ∈ family n ∧ t+6 ∈ family n) =
      insert 0 (Finset.Icc 2 ((n : ℤ)-6)) := by
    ext t
    simp only [family, Finset.mem_filter, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h7 : (family n).filter (fun t => t+5 ∈ family n ∧ t+7 ∈ family n) =
      insert 0 (Finset.Icc 2 ((n : ℤ)-7)) := by
    ext t
    simp only [family, Finset.mem_filter, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h9 : (family n).filter (fun t => t+5 ∈ family n ∧ t+8 ∈ family n ∧ t+9 ∈ family n) =
      insert 0 (Finset.Icc 2 ((n : ℤ)-9)) := by
    ext t
    simp only [family, Finset.mem_filter, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [h4,h6,h7,h9]
  simp only [Finset.card_insert_of_notMem (by simp : (0 : ℤ) ∉ Finset.Icc 2 ((n : ℤ)-4)),
    Finset.card_insert_of_notMem (by simp : (0 : ℤ) ∉ Finset.Icc 2 ((n : ℤ)-6)),
    Finset.card_insert_of_notMem (by simp : (0 : ℤ) ∉ Finset.Icc 2 ((n : ℤ)-7)),
    Finset.card_insert_of_notMem (by simp : (0 : ℤ) ∉ Finset.Icc 2 ((n : ℤ)-9)), Int.card_Icc]
  omega

/-- A nonconsecutive family has the same large-size formula, while its nine-point
member has strictly fewer actual sums than nine consecutive powers. -/
theorem whole_proposition_five_one :
    (∀ n : ℕ, 10 ≤ n →
      (family n).card = n ∧
      (0 : ℤ) ∈ family n ∧ (1 : ℤ) ∉ family n ∧ (2 : ℤ) ∈ family n ∧
      ((family n).filter fun t => t+2 ∈ family n ∧ t+3 ∈ family n ∧ t+4 ∈ family n).card +
      ((family n).filter fun t => t+3 ∈ family n ∧ t+5 ∈ family n ∧ t+6 ∈ family n).card +
      ((family n).filter fun t => t+5 ∈ family n ∧ t+7 ∈ family n).card +
      ((family n).filter fun t => t+5 ∈ family n ∧ t+8 ∈ family n ∧ t+9 ∈ family n).card = 4*n-26 ∧
      (∀ r : ℝ, 1 < r → r^3 = r+1 →
        ((family n).image fun e => r^e).card = n ∧
        (((family n).image fun e => r^e)+((family n).image fun e => r^e)).card =
          n*(n+1)/2-4*n+26)) ∧
    (∀ r : ℝ, 1 < r → r^3 = r+1 →
      let A := (family 9).image fun e => r^e
      let P := (Finset.Icc (0 : ℤ) 8).image fun e => r^e
      A.card = 9 ∧ P.card = 9 ∧ (A+A).card = 34 ∧ (P+P).card = 35 ∧
        (A+A).card < (P+P).card) := by
  constructor
  · intro n hn
    obtain ⟨h4,h6,h7,h9⟩ := filters n hn
    have hc := family_card n (by omega)
    refine ⟨hc, by simp [family], by simp [family], by simp [family]; omega, ?_, ?_⟩
    · rw [h4,h6,h7,h9]; omega
    · intro r hr hroot
      have hm := (zpow_right_strictMono₀ hr).injective
      refine ⟨by rw [Finset.card_image_of_injective _ hm, hc], ?_⟩
      have h := sumset_card_add_template_counts r hr hroot (family n)
      rw [hc,h4,h6,h7,h9,Nat.choose_two_right] at h
      have hn' : n+1-1=n := by omega
      rw [hn',Nat.mul_comm (n+1) n] at h
      have hp : 4*n ≤ n*(n+1)/2 := by
        have hmul : 8*n ≤ n*(n+1) := by nlinarith
        omega
      omega
  · intro r hr hroot
    dsimp only
    have hm := (zpow_right_strictMono₀ hr).injective
    have hF := sumset_card_add_template_counts r hr hroot (family 9)
    have hP := sumset_card_add_template_counts r hr hroot (Finset.Icc (0 : ℤ) 8)
    have hFc : (family 9).card = 9 := by decide +kernel
    have hPc : (Finset.Icc (0 : ℤ) 8).card = 9 := by decide +kernel
    have hF4 : ((family 9).filter fun t => t+2 ∈ family 9 ∧ t+3 ∈ family 9 ∧ t+4 ∈ family 9).card = 5 := by decide +kernel
    have hF6 : ((family 9).filter fun t => t+3 ∈ family 9 ∧ t+5 ∈ family 9 ∧ t+6 ∈ family 9).card = 3 := by decide +kernel
    have hF7 : ((family 9).filter fun t => t+5 ∈ family 9 ∧ t+7 ∈ family 9).card = 2 := by decide +kernel
    have hF9 : ((family 9).filter fun t => t+5 ∈ family 9 ∧ t+8 ∈ family 9 ∧ t+9 ∈ family 9).card = 1 := by decide +kernel
    have hP4 : ((Finset.Icc (0 : ℤ) 8).filter fun t => t+2 ∈ Finset.Icc (0 : ℤ) 8 ∧ t+3 ∈ Finset.Icc (0 : ℤ) 8 ∧ t+4 ∈ Finset.Icc (0 : ℤ) 8).card = 5 := by decide +kernel
    have hP6 : ((Finset.Icc (0 : ℤ) 8).filter fun t => t+3 ∈ Finset.Icc (0 : ℤ) 8 ∧ t+5 ∈ Finset.Icc (0 : ℤ) 8 ∧ t+6 ∈ Finset.Icc (0 : ℤ) 8).card = 3 := by decide +kernel
    have hP7 : ((Finset.Icc (0 : ℤ) 8).filter fun t => t+5 ∈ Finset.Icc (0 : ℤ) 8 ∧ t+7 ∈ Finset.Icc (0 : ℤ) 8).card = 2 := by decide +kernel
    have hP9 : ((Finset.Icc (0 : ℤ) 8).filter fun t => t+5 ∈ Finset.Icc (0 : ℤ) 8 ∧ t+8 ∈ Finset.Icc (0 : ℤ) 8 ∧ t+9 ∈ Finset.Icc (0 : ℤ) 8).card = 0 := by decide +kernel
    rw [hFc,hF4,hF6,hF7,hF9] at hF
    rw [hPc,hP4,hP6,hP7,hP9] at hP
    change (((family 9).image fun e => r^e)+((family 9).image fun e => r^e)).card + 5 + 3 + 2 + 1 = 45 at hF
    change (((Finset.Icc (0 : ℤ) 8).image fun e => r^e)+((Finset.Icc (0 : ℤ) 8).image fun e => r^e)).card + 5 + 3 + 2 + 0 = 45 at hP
    refine ⟨by rw [Finset.card_image_of_injective _ hm,hFc],
      by rw [Finset.card_image_of_injective _ hm,hPc], ?_, ?_, ?_⟩ <;> omega

#print axioms whole_proposition_five_one

end D5.S3.Arith.Additive.PlasticGappedFamily
