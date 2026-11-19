/- GID: D5/S3/FiniteGroups/Semilinear/WeightedArithmetic
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Semilinear/WeightedArithmetic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Norm fibers and cyclic element-order sums give the weighted Frobenius divisor average. -/

import D5.S3.FiniteGroups.Semilinear.WeightedFixedSets
import Mathlib.GroupTheory.Index

/-! The arithmetic of the actual fixed equations. All divisions occur in the rationals. -/

set_option autoImplicit false
open scoped Classical

namespace WeightedSemilinear

universe u
variable {F K : Type} [Field F] [Field K] [Fintype F] [Fintype K] [Algebra F K]
variable {I : Type u} [Fintype I] (w : I → ℕ)

local notation "E[" σ "]" => (IntermediateField.fixedField (Subgroup.zpowers σ))
local notation "N[" σ "]" => Units.map (Algebra.norm E[σ] (S := K))

private theorem sum_by_order {G : Type*} [Group G] [Fintype G] [IsCyclic G]
    (f : ℕ → ℚ) :
    ∑ g : G, f (orderOf g) =
      ∑ d ∈ (Fintype.card G).divisors, (Nat.totient d : ℚ) * f d := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
    (t := (Fintype.card G).divisors) (g := orderOf)
    (fun g _ => Nat.mem_divisors.mpr ⟨orderOf_dvd_card, Fintype.card_ne_zero⟩)]
  apply Finset.sum_congr rfl
  intro d hd
  calc
    _ = ∑ g ∈ Finset.univ.filter (fun g : G => orderOf g = d), f d := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [(Finset.mem_filter.mp hg).2]
    _ = _ := by
      simp [IsCyclic.card_orderOf_eq_totient (Nat.mem_divisors.mp hd).1]

private theorem fixedField_card (σ : Gal(K/F)) :
    Nat.card E[σ] = Fintype.card F ^ (Module.finrank F K / orderOf σ) := by
  have he : Module.finrank E[σ] K = orderOf σ := by
    rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers]
  have hr : Module.finrank F E[σ] = Module.finrank F K / orderOf σ := by
    rw [← Module.finrank_mul_finrank F E[σ] K, he,
      Nat.mul_div_cancel _ (orderOf_pos σ)]
  rw [Module.natCard_eq_pow_finrank (K := F), Nat.card_eq_fintype_card, hr]

/-- Average over all scalars using uniform fibers of the actual relative norm. -/
theorem norm_average (σ : Gal(K/F)) :
    (∑ c : Kˣ,
      (Nat.card {A : I → K // ∀ i, σ (A i) = (c : K) ^ w i * A i} : ℚ)) /
      (Fintype.card K - 1 : ℕ) =
    (∑ m ∈ (Nat.card E[σ] - 1).divisors, (Nat.totient m : ℚ) *
      (Nat.card E[σ] : ℚ) ^ (Finset.univ.filter (fun i => m ∣ w i)).card) /
      (Nat.card E[σ] - 1 : ℕ) := by
  letI : Fintype E[σ] := Fintype.ofFinite _
  let f : E[σ]ˣ → ℚ := fun u => (Nat.card E[σ] : ℚ) ^
    (Finset.univ.filter (fun i => orderOf u ∣ w i)).card
  let k := Nat.card (N[σ]).ker
  have hs := FiniteField.unitsMap_norm_surjective E[σ] K
  have hfib (u : E[σ]ˣ) :
      (Finset.univ.filter (fun c : Kˣ => N[σ] c = u)).card = k := by
    have h := Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective hs u)
    simpa only [k, Set.mem_preimage, Set.mem_singleton_iff, Nat.card_eq_fintype_card,
      Fintype.card_subtype] using h
  have hsum : ∑ c : Kˣ, f (N[σ] c) = (k : ℚ) * ∑ u, f u := by
    rw [← Finset.sum_fiberwise Finset.univ (N[σ]) (fun c => f (N[σ] c)),
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    calc
      _ = ∑ c ∈ Finset.univ.filter (fun c : Kˣ => N[σ] c = u), f u := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [(Finset.mem_filter.mp hc).2]
      _ = _ := by simp [hfib]
  have horder := sum_by_order (G := E[σ]ˣ)
    (fun m => (Nat.card E[σ] : ℚ) ^
      (Finset.univ.filter (fun i => m ∣ w i)).card)
  have hEU : Fintype.card E[σ]ˣ = Nat.card E[σ] - 1 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units]
  rw [hEU] at horder
  have hk : (k : ℚ) * (Nat.card E[σ] - 1 : ℕ) = (Fintype.card K - 1 : ℕ) := by
    have h := Subgroup.card_ker_mul_card_of_surjective hs
    rw [Nat.card_units, Nat.card_units, Nat.card_eq_fintype_card (α := K)] at h
    exact_mod_cast h
  have hQ : (Fintype.card K - 1 : ℕ) ≠ 0 := by
    exact Nat.sub_ne_zero_of_lt Fintype.one_lt_card
  have hq : (Nat.card E[σ] - 1 : ℕ) ≠ 0 := by
    exact Nat.sub_ne_zero_of_lt Finite.one_lt_card
  have hQ' : ((Fintype.card K - 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hQ
  have hq' : ((Nat.card E[σ] - 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hq
  simp_rw [vector_card w, Nat.cast_pow]
  change (∑ c, f (N[σ] c)) / _ = _
  rw [hsum, horder]
  apply (div_eq_div_iff hQ' hq').mpr
  rw [mul_right_comm, hk, mul_comm]

/-- Summing Galois components by their order gives the Frobenius gcd/totient sum. -/
theorem fixed_average :
    (∑ σ : Gal(K/F),
      (∑ c : Kˣ,
        (Nat.card {A : I → K // ∀ i, σ (A i) = (c : K) ^ w i * A i} : ℚ)) /
          (Fintype.card K - 1 : ℕ)) =
    ∑ d ∈ (Module.finrank F K).divisors,
      (Nat.totient (Module.finrank F K / d) : ℚ) /
        (Fintype.card F ^ d - 1 : ℕ) *
      ∑ m ∈ (Fintype.card F ^ d - 1).divisors, (Nat.totient m : ℚ) *
        (Fintype.card F : ℚ) ^
          (d * (Finset.univ.filter (fun i => m ∣ w i)).card) := by
  let n := Module.finrank F K
  let b : ℕ → ℚ := fun d =>
    (∑ m ∈ (Fintype.card F ^ d - 1).divisors, (Nat.totient m : ℚ) *
      (Fintype.card F : ℚ) ^ (d * (Finset.univ.filter (fun i => m ∣ w i)).card)) /
        (Fintype.card F ^ d - 1 : ℕ)
  have hσ (σ : Gal(K/F)) :
      (∑ c : Kˣ,
        (Nat.card {A : I → K // ∀ i, σ (A i) = (c : K) ^ w i * A i} : ℚ)) /
          (Fintype.card K - 1 : ℕ) = b (n / orderOf σ) := by
    rw [norm_average w σ, fixedField_card]
    simp only [b, n, Nat.cast_pow, pow_mul]
  have hGal : Fintype.card Gal(K/F) = n := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  calc
    _ = ∑ σ : Gal(K/F), b (n / orderOf σ) := Finset.sum_congr rfl (fun σ _ => hσ σ)
    _ = ∑ e ∈ n.divisors, (Nat.totient e : ℚ) * b (n / e) := by
      simpa only [hGal] using sum_by_order (G := Gal(K/F)) (fun e => b (n / e))
    _ = ∑ d ∈ n.divisors, (Nat.totient (n / d) : ℚ) * b d := by
      rw [← Nat.sum_div_divisors n (fun e => (Nat.totient e : ℚ) * b (n / e))]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Nat.div_div_self (Nat.mem_divisors.mp hd).1 (Module.finrank_pos.ne')]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      dsimp [b, n]
      ring

end WeightedSemilinear
