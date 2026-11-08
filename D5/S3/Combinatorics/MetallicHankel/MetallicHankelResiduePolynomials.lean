/- GID: D5/S3/Combinatorics/MetallicHankel/MetallicHankelResiduePolynomials
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MetallicHankel/MetallicHankelResiduePolynomials
   mirror-E: none(waiver:metallic-hankel-all-residue-polynomials)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Basic]
   utility: none
   digest: Fixed boundaries give metallic Hankel residue polynomials from their first term. -/

import D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnbounded
import D5.S3.Combinatorics.MetallicHankel.MetallicHankelEndpointJets
import D5.S3.Combinatorics.MetallicHankel.MetallicHankelComplementaryMinor
import D5.S3.Combinatorics.MetallicHankel.MetallicHankelQuasipolynomialDefs
import D5.S3.Arith.PolynomialValues.BackwardPropagation

/-! The same normal continuants supply both ends of a fixed complementary matrix. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MetallicHankel.MetallicHankelResiduePolynomials

open PowerSeries Finset MetallicHankelDefs MetallicHankelBlocks
open MetallicHankelEndpointJets MetallicHankelComplementaryMinor MetallicHankelUnbounded
open scoped Matrix

private theorem boundary_polynomial (a u ρ K₀ r : ℕ)
    (P : ℕ → Fin 4 → Polynomial ℚ) (c d : ℕ → ℕ → ℤ)
    (hK₀ : 1 ≤ K₀)
    (coordinate : ∀ m : ℕ, (K₀ + m) * ρ = r + m * ρ + (a + u))
    (jets : ∀ K : ℕ, 1 ≤ K → ∀ h : ℕ, h < 2 * K * ρ →
      (P h 0).eval (K : ℚ) = (c K h : ℚ) ∧
      (P h 1).eval (K : ℚ) = (d K h : ℚ) ∧
      (P h 2).eval (K : ℚ) = (reverseCoeffs (K * ρ) (c K) h : ℚ) ∧
      (P h 3).eval (K : ℚ) = (reverseCoeffs (K * ρ) (d K) h : ℚ)) :
    ∃ B : Polynomial ℚ, ∀ m : ℕ,
      B.eval (m : ℚ) =
        ((boundaryMatrix a (r + m * ρ) u (c (K₀ + m)) (d (K₀ + m))).det : ℚ) := by
  classical
  let t := a + u
  let A : Matrix (Fin t) (Fin t) (Polynomial ℚ) := Matrix.of fun i k =>
    if i.val < a then
      -∑ v ∈ range (i.val + 1),
        if k.val + i.val + 1 ≤ t + v then
          P (t + v - (k.val + i.val + 1)) 2 * P v 1 -
          P (t + v - (k.val + i.val + 1)) 3 * P v 0
        else 0
    else
      ∑ v ∈ range (t - k.val),
        (P ((t - 1 - i.val) + (t - 1 - k.val) + 1 - v) 2 * P v 3 -
         P ((t - 1 - i.val) + (t - 1 - k.val) + 1 - v) 3 * P v 2)
  refine ⟨A.det.comp (Polynomial.C (K₀ : ℚ) + Polynomial.X), ?_⟩
  intro m
  let K := K₀ + m
  have hK : 1 ≤ K := by dsimp [K]; omega
  have hN : K * ρ = r + m * ρ + t := coordinate m
  have ht : t ≤ K * ρ := by omega
  have bounds (h : ℕ) (hh : h < 2 * t) : h < 2 * K * ρ := by nlinarith
  have entry (i k : Fin t) :
      (A i k).eval (K : ℚ) =
        (boundaryMatrix a (r + m * ρ) u (c K) (d K) i k : ℚ) := by
    dsimp only [A, Matrix.of_apply, boundaryMatrix]
    split_ifs with hi
    · rw [Polynomial.eval_neg, Polynomial.eval_finsetSum]
      push_cast
      congr 1
      apply sum_congr rfl
      intro v hv
      have hv' := mem_range.mp hv
      have vi : v < 2 * t := by have := i.isLt; omega
      have dd : t + v - (k.val + i.val + 1) < 2 * t := by
        have := i.isLt
        omega
      have jv := jets K hK v (bounds v vi)
      have jd := jets K hK _ (bounds _ dd)
      split_ifs with guard
      · simp only [Polynomial.eval_sub, Polynomial.eval_mul, jd.2.2.1, jd.2.2.2,
          jv.1, jv.2.1]
        rw [hN]
      · simp
    · rw [Polynomial.eval_finsetSum]
      push_cast
      apply sum_congr rfl
      intro v hv
      have hv' := mem_range.mp hv
      have vi : v < 2 * t := by have := k.isLt; omega
      have dd : (t - 1 - i.val) + (t - 1 - k.val) + 1 - v < 2 * t := by
        have := i.isLt
        have := k.isLt
        omega
      have jv := jets K hK v (bounds v vi)
      have jd := jets K hK _ (bounds _ dd)
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, jd.2.2.1, jd.2.2.2,
        jv.2.2.1, jv.2.2.2]
      rw [hN]
  rw [Polynomial.eval_comp]
  simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
  rw [show (K₀ : ℚ) + (m : ℚ) = (K : ℚ) by dsimp [K]; push_cast; rfl]
  change (Polynomial.evalRingHom (K : ℚ)) A.det = _
  rw [(Polynomial.evalRingHom (K : ℚ)).map_det]
  change (A.map (Polynomial.evalRingHom (K : ℚ))).det = _
  rw [show A.map (Polynomial.evalRingHom (K : ℚ)) =
      (boundaryMatrix a (r + m * ρ) u (c K) (d K)).map (Int.castRingHom ℚ) by
    ext i k
    exact entry i k]
  exact ((Int.castRingHom ℚ).map_det _).symm

/-- Every residue of every higher shifted metallic Hankel sequence is polynomial
from its first term, and each polynomial takes integer values at all integers. -/
theorem result : Trureturing.OpenProblems.HanPedonShiftedQMetallicHankel.claim := by
  classical
  intro n hn
  obtain ⟨Φ, metallic, unique, hbase, hgrow, L, k, b, D, Q, s, hL, data,
    hs0, hs, q0, q1, qrec, degree, normal⟩ := normal_family n hn
  refine ⟨⟨Φ, metallic⟩, ?_⟩
  intro Ψ hΨ ℓ hℓ
  rw [unique Ψ hΨ]
  let ρ := if n % 2 = 0 then 2 * n * (n + 1) else 4 * n * (n + 1)
  let ν := if n % 2 = 0 then 1 else 2
  let a := ℓ - (n + 1)
  have ha : 2 ≤ a := by dsimp [a]; omega
  have hρ : 0 < ρ := by dsimp [ρ]; split_ifs <;> positivity
  have evenρ : Even ρ := by
    dsimp [ρ]
    split_ifs
    · exact even_two.mul_right n |>.mul_right (n + 1)
    · exact (by decide : Even 4).mul_right n |>.mul_right (n + 1)
  have alljets := continuant_endpoint_jets n L hn k b D Q s hL data hs0 hs q0 q1 qrec
    (fun p => (degree p).2)
  choose P hdeg heval using alljets
  let p := fun K => (K * ν) * L
  let c := fun K r => if r ≤ s (p K) then coeff (s (p K) - r) (Q (p K)) else 0
  let d := fun K r => if r ≤ s (p K - 1) then coeff (s (p K - 1) - r) (Q (p K - 1)) else 0
  have jets (K : ℕ) (hK : 1 ≤ K) (h : ℕ) (hh : h < 2 * K * ρ) :
      (P h 0).eval (K : ℚ) = (c K h : ℚ) ∧
      (P h 1).eval (K : ℚ) = (d K h : ℚ) ∧
      (P h 2).eval (K : ℚ) = (reverseCoeffs (K * ρ) (c K) h : ℚ) ∧
      (P h 3).eval (K : ℚ) = (reverseCoeffs (K * ρ) (d K) h : ℚ) := by
    have nj := normal K hK
    have ej := heval h K hK
    change s (p K) = K * ρ ∧ _ at nj
    have lowc : c K h = coeff h (reverseAt (s (p K)) (Q (p K))) := by
      simp only [c, reverse_coeff]
    have lowd : d K h = coeff h (reverseAt (s (p K - 1)) (Q (p K - 1))) := by
      simp only [d, reverse_coeff]
    have highc : reverseCoeffs (K * ρ) (c K) h = coeff h (Q (p K)) := by
      rw [← ej.2.1]
      rw [reverse_coeff]
      simp only [reverseCoeffs, ← nj.1, c, reverse_coeff]
      rfl
    have highd : reverseCoeffs (K * ρ) (d K) h =
        coeff h (X ^ (n + 1) * Q (p K - 1)) := by
      rw [← ej.2.2.1]
      rw [reverse_coeff]
      simp only [reverseCoeffs, ← nj.1, d, reverse_coeff]
      rfl
    rw [lowc, lowd, highc, highd]
    exact ⟨ej.2.2.2.1, ej.2.2.2.2.1,
      (ej.2.2.2.2.2 hh).1, (ej.2.2.2.2.2 hh).2⟩
  have residue (r : Fin ρ) : ∃ B : Polynomial ℚ, ∀ m : ℕ,
      B.eval (m : ℚ) = (shiftedHankel Φ ℓ (r.val + m * ρ) : ℚ) := by
    let K₀ := a + 1
    let t := K₀ * ρ - r.val
    have hK₀ : 1 ≤ K₀ := by dsimp [K₀]; omega
    have enough : a ≤ t := by
      have hr := r.isLt
      have hmul : (a + 1) * ρ ≥ a + ρ := by nlinarith
      dsimp [t, K₀]
      omega
    let u := t - a
    have ht : a + u = t := by dsimp [u]; omega
    have coordinate (m : ℕ) : (K₀ + m) * ρ = r.val + m * ρ + (a + u) := by
      rw [ht, Nat.add_mul]
      dsimp [t]
      have hr := r.isLt
      have hle : r.val ≤ K₀ * ρ := by nlinarith
      omega
    obtain ⟨B, hB⟩ := boundary_polynomial a u ρ K₀ r.val P c d hK₀ coordinate jets
    refine ⟨Polynomial.C ((-1 : ℚ) ^ (a * r.val)) * B, ?_⟩
    intro m
    let K := K₀ + m
    let j := r.val + m * ρ
    have hK : 1 ≤ K := by dsimp [K]; omega
    have hjN : j + (a + u) = K * ρ := (coordinate m).symm
    have hN : 0 < j + (a + u) := by rw [hjN]; exact Nat.mul_pos (by omega) hρ
    have nb := normal K hK
    change s (p K) = K * ρ ∧ c K (K * ρ) = 1 ∧
      (∀ v, K * ρ < v → c K v = 0) ∧ d K (s (p K - 1)) = 1 ∧
      (∀ v, K * ρ ≤ v → d K v = 0) ∧ _ at nb
    have bound := shifted_hankel_boundary Φ (n + 1) a j u hN (c K) (d K)
      (by simpa only [hjN] using nb.2.1)
      (by simpa only [hjN] using nb.2.2.1)
      (by simpa only [hjN] using nb.2.2.2.2.1)
      (by simpa only [hjN] using nb.2.2.2.2.2.1)
      (by simpa only [hjN] using nb.2.2.2.2.2.2.1)
      (by rw [hjN, nb.2.2.2.2.2.2.2]; exact isUnit_one)
    rw [hjN, nb.2.2.2.2.2.2.2, mul_one,
      show n + 1 + a = ℓ by dsimp [a]; omega] at bound
    have sign : (-1 : ℤ) ^ (a * j) = (-1 : ℤ) ^ (a * r.val) := by
      dsimp [j]
      rw [Nat.mul_add, pow_add]
      have ev : Even (a * (m * ρ)) := (evenρ.mul_left m).mul_left a
      rw [ev.neg_one_pow, mul_one]
    rw [sign] at bound
    rw [Polynomial.eval_mul, Polynomial.eval_C, hB m]
    exact_mod_cast bound.symm
  choose B hB using residue
  refine ⟨B, ?_, ?_⟩
  · intro r z
    let H : AddSubgroup ℚ := (Int.castAddHom ℚ).range
    have natmem (m : ℕ) : (B r).eval (m : ℚ) ∈ H := by
      exact ⟨shiftedHankel Φ ℓ (r.val + m * ρ), (hB r m).symm⟩
    obtain ⟨w, hw⟩ :=
      D5.S3.Arith.PolynomialValues.BackwardPropagation.eval_int_mem_of_eval_nat_mem H (B r) natmem z
    exact ⟨w, hw.symm⟩
  · intro r m
    exact (hB r m).symm

#print axioms result

end D5.S3.Combinatorics.MetallicHankel.MetallicHankelResiduePolynomials
