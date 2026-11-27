/- GID: D5/S3/Combinatorics/Matroids/CircuitDifferenceBasis
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/CircuitDifferenceBasis
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Difference coordinates around two representatives separate disjoint faces. -/

module

public import D5.S3.Combinatorics.Matroids.UniformCircuitBasis
import Mathlib.LinearAlgebra.Transvection.Basic

/-! Difference coordinates with a separate representative for one block. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.CircuitDifferenceBasis

open Finset

set_option autoImplicit false

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Subtract the local representative inside a block and the global
representative elsewhere. The new coordinate at the local representative
is the sum over its block, and the coordinate at the global representative
is the sum over the whole index set. -/
theorem exists_difference_basis (H : Finset I) (p q : I) (hp : p ∉ H) (hq : q ∈ H) :
    ∃ b : Module.Basis I ℤ (I → ℤ),
      b p = Pi.single p 1 ∧
      (∀ i, i ≠ p → b i = Pi.single i 1 - Pi.single (if i ∈ H.erase q then q else p) 1) ∧
      ∀ (x : I → ℤ) i, b.equivFun x i =
        if i = p then ∑ j, x j else if i = q then ∑ j ∈ H, x j else x i := by
  let e (i : I) : I → ℤ := Pi.single i 1
  let s (F : Finset I) : (I → ℤ) →ₗ[ℤ] ℤ := ∑ i ∈ F, LinearMap.proj i
  have hs (F : Finset I) (x : I → ℤ) : s F x = ∑ i ∈ F, x i := by
    simp [s, LinearMap.sum_apply]
  have he (F : Finset I) (i : I) : s F (e i) = if i ∈ F then 1 else 0 := by
    rw [hs]
    simp [e, Pi.single_apply]
  let T := (univ : Finset I).erase p
  let U := H.erase q
  have hpT : p ∉ T := notMem_erase p _
  have hqU : q ∉ U := notMem_erase q _
  have hpU : p ∉ U := fun h => hp (mem_of_mem_erase h)
  have hpq : p ≠ q := fun h => hp (h ▸ hq)
  have hqT : q ∈ T := mem_erase.mpr ⟨hpq.symm, mem_univ _⟩
  have hTp : s T (-e p) = 0 := by simp [he, hpT]
  have hUq : s U (-e q) = 0 := by simp [he, hqU]
  let global := LinearEquiv.transvection hTp
  let blockShift := LinearEquiv.transvection hUq
  let transform := blockShift.trans global
  let b := (Pi.basisFun ℤ I).map transform
  have hG (x : I → ℤ) : global x = x - s T x • e p := by
    change x + s T x • -e p = _
    rw [smul_neg, sub_eq_add_neg]
  have hL (x : I → ℤ) : blockShift x = x - s U x • e q := by
    change x + s U x • -e q = _
    rw [smul_neg, sub_eq_add_neg]
  have hb (i : I) : b i = global (blockShift (e i)) := by
    rw [Module.Basis.map_apply, Pi.basisFun_apply]
    rfl
  have hGinv (x : I → ℤ) : global.symm x = x + s T x • e p := by
    change x + s T x • -(-e p) = _
    rw [neg_neg]
  have hLinv (x : I → ℤ) : blockShift.symm x = x + s U x • e q := by
    change x + s U x • -(-e q) = _
    rw [neg_neg]
  refine ⟨b, ?_, ?_, ?_⟩
  · rw [hb, hL, he, ite_eq_right hpU, zero_smul, sub_zero,
      hG, he, ite_eq_right hpT, zero_smul, sub_zero]
  · intro i hi
    have hiT : i ∈ T := mem_erase.mpr ⟨hi, mem_univ _⟩
    by_cases hiU : i ∈ U
    · rw [hb, hL, he, ite_eq_left hiU, one_smul, hG, map_sub, he, he,
        ite_eq_left hiT, ite_eq_left hqT, sub_self, zero_smul, sub_zero, ite_eq_left hiU]
    · rw [hb, hL, he, ite_eq_right hiU, zero_smul, sub_zero, hG, he, ite_eq_left hiT,
        one_smul, ite_eq_right hiU]
  · intro x i
    change blockShift.symm (global.symm x) i = _
    rw [hLinv, hGinv, map_add, map_smul, he, ite_eq_right hpU, smul_zero, add_zero]
    change x i + s T x * e p i + s U x * e q i = _
    by_cases hip : i = p
    · subst i
      rw [ite_eq_left rfl, hs, ← sum_erase_add _ x (mem_univ p)]
      simp [e, hpq, T, add_comm]
    · by_cases hiq : i = q
      · subst i
        rw [ite_eq_right hip, ite_eq_left rfl, hs U, ← sum_erase_add _ x hq]
        simpa [e, hpq, hpq.symm, U] using add_comm (x q) (∑ j ∈ U, x j)
      · simp [e, hip, hiq]

omit [Fintype I] in
/-- Two faces with sparse intersection admit simultaneous difference
coordinates around chosen representatives. The pivot and all transformed
weights remain available for the lower-degree insertion equations. -/
theorem exists_two_face_difference_basis [Finite I] (H J : Finset I) {d : ℕ} (hd : 1 ≤ d)
    (hH : H.card = d + 2) (hJ : J.card = d + 2) (hsparse : (H ∩ J).card ≤ d)
    (weight : I → ℕ) (hweight : ∀ i, 0 < weight i) :
    ∃ (p : I) (_ : p ∈ H) (q : I) (_ : q ∈ J)
        (b : Module.Basis I ℤ (I → ℤ)) (w : I → ℕ),
      b p = Pi.single p 1 ∧ p ∉ J.erase q ∧
      1 < ((H.erase p) \ (J.erase q)).card ∧
      (∀ i ∈ H.erase p, b i = Pi.single i 1 - Pi.single p 1) ∧
      (∀ i ∈ J.erase q, b i = Pi.single i 1 - Pi.single q 1) ∧
      (∀ i, b.equivFun (fun k => (weight k : ℤ)) i = (w i : ℤ)) ∧ ∀ i, 0 < w i := by
  let _ := Fintype.ofFinite I
  obtain ⟨p, hp, q, hq, L, a, ha, hpL, hfirst, hsecond, hpSecond, hsep⟩ :
      ∃ (p : I) (_ : p ∈ H) (q : I) (_ : q ∈ J) (L : Finset I) (a : I),
        a ∈ L ∧ p ∉ L ∧ (∀ i ∈ H.erase p, i ∉ L.erase a) ∧
        (∀ i ∈ J.erase q, (if i ∈ L.erase a then a else p) = q) ∧
        p ∉ J.erase q ∧ 1 < ((H.erase p) \ (J.erase q)).card := by
    by_cases hinter : (H ∩ J).Nonempty
    · obtain ⟨p, hp⟩ := hinter
      have hpH := (mem_inter.mp hp).1
      have hpJ := (mem_inter.mp hp).2
      obtain ⟨a, ha⟩ := card_pos.mp (show 0 < (H.erase p).card by
        rw [card_erase_of_mem hpH, hH]; omega)
      have hpane : p ≠ a := (mem_erase.mp ha).1.symm
      refine ⟨p, hpH, p, hpJ, {a}, a, mem_singleton.mpr rfl, by simp [hpane],
        by simp, by simp, notMem_erase p _, ?_⟩
      have heq : H.erase p \ J.erase p = H \ J := by
        rw [← erase_sdiff_distrib, erase_eq_of_notMem (fun h => (mem_sdiff.mp h).2 hpJ)]
      rw [heq]
      have h := card_sdiff_add_card_inter H J
      omega
    · obtain ⟨p, hp⟩ := card_pos.mp (show 0 < H.card by omega)
      obtain ⟨q, hq⟩ := card_pos.mp (show 0 < J.card by omega)
      have disjoint (i : I) (hi : i ∈ H) : i ∉ J := fun hx => hinter ⟨i, mem_inter.mpr ⟨hi, hx⟩⟩
      have hd' : ∀ i ∈ H.erase p, i ∉ J.erase q := fun i hi hx =>
        disjoint i (mem_of_mem_erase hi) (mem_of_mem_erase hx)
      refine ⟨p, hp, q, hq, J, q, hq, disjoint p hp, hd', fun i hi => ite_eq_left hi,
        fun h => disjoint p hp (mem_of_mem_erase h), ?_⟩
      have heq : H.erase p \ J.erase q = H.erase p := by
        ext i
        exact ⟨fun hi => (mem_sdiff.mp hi).1, fun hi => mem_sdiff.mpr ⟨hi, hd' i hi⟩⟩
      rw [heq, card_erase_of_mem hp, hH]
      omega
  obtain ⟨b, hbp, hb, hread⟩ := exists_difference_basis L p a hpL ha
  let w (i : I) := if i = p then ∑ j, weight j else if i = a then ∑ j ∈ L, weight j else weight i
  refine ⟨p, hp, q, hq, b, w, hbp, hpSecond, hsep, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hb i (mem_erase.mp hi).1, ite_eq_right (hfirst i hi)]
  · intro i hi
    have hne : i ≠ p := fun h => hpSecond (h ▸ hi)
    rw [hb i hne, hsecond i hi]
  · intro i
    simpa only [w, Nat.cast_ite, Nat.cast_sum] using hread (fun k => (weight k : ℤ)) i
  · intro i
    by_cases hip : i = p
    · rw [show w i = ∑ j, weight j by simp [w, hip]]
      exact (hweight p).trans_le (single_le_sum (fun j _ => Nat.zero_le (weight j)) (mem_univ p))
    · by_cases hia : i = a
      · rw [show w i = ∑ j ∈ L, weight j by simp only [w, ite_eq_right hip, ite_eq_left hia]]
        exact (hweight a).trans_le (single_le_sum (fun j _ => Nat.zero_le (weight j)) ha)
      · simpa only [w, ite_eq_right hip, ite_eq_right hia] using hweight i

end D5.S3.Combinatorics.Matroids.CircuitDifferenceBasis
