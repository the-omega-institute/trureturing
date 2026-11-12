/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/PairResonanceSpectrum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/PairResonanceSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete local square tables and actual unbounded resonant nonintegrality family. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.PairResonanceLocal
import D5.S3.Combinatorics.SpectralGraph.Nikandish.PairLowArithmetic

/-! Source: four-prime-resonance-discriminant, supplied PR9
6d491f77b35dec808fc777b69939c56cdae5dc02. The two fixed-prime tables
are complete finite-field tables, never an exponent rectangle. The final
family has all n,m>=0 and c>=2a-2, including equality and without an
ordering or coprimality premise on the tails. Necessary tests do not
classify the remaining resonances, bad primes or general Q3. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.PairResonanceSpectrum
open PairedIdealIntersectionObstructions PairedIdealIntersectionLift
open IdealIntersectionSupport IdealIntersectionObstructions PairResonanceAlgebra

/-- Every residue at the first low root, including every passing residue. -/
theorem complete_table_five : ∀ z : ZMod 5,
    (∃ v : ZMod 5, v^2=localPolynomial 2 z) ↔ z=0 ∨ z=2 := by
  decide +kernel

/-- Every residue at the second low root, including every passing residue. -/
theorem complete_table_seven : ∀ z : ZMod 7,
    (∃ v : ZMod 7, v^2=localPolynomial 3 z) ↔ z=0 ∨ z=3 ∨ z=5 := by
  decide +kernel

/-- Root two is excluded for every integer third tail on the full source
progression. No tail ordering or coprimality is used. -/
theorem progression_two_nonzero (n m : ℕ) (c : ℤ) :
    (tensorK (6+25*(n : ℤ)) (20+100*(n : ℤ)+125*(m : ℤ)) c-(2 : ℤ) • 1).det ≠ 0 := by
  intro hr
  let H : ℤ := 1+5*(n : ℤ)
  let U : ℤ := 1+5*(n : ℤ)+5*(m : ℤ)
  have ha : (6+25*(n : ℤ))=(2 : ℤ)-1+(5 : ℤ)^1*H := by dsimp [H]; ring
  have hb : (20+100*(n : ℤ)+125*(m : ℤ))=
      -(5 : ℤ)^1*H+((5 : ℤ)^1)^2*U := by dsimp [H,U]; ring
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hH : ¬(5 : ℤ) ∣ H := by dsimp [H]; omega
  have hsq := PairResonanceLocal.scaled_root_square 5 1 H U c 2
    (by omega) hH (by norm_num) (by
      convert hr using 1 <;> dsimp [H,U] <;> norm_num <;> ring)
  have hrz : (U : ZMod 5)/(H : ZMod 5)^2=1 := by
    dsimp [H,U]
    push_cast
    have h5 : (5 : ZMod 5)=0 := by decide
    simp only [h5,zero_mul,add_zero,one_pow,div_one]
  rw [hrz] at hsq
  have hsquare : ∃ v : ZMod 5, v^2=localPolynomial 2 1 := by
    simpa only [Int.cast_ofNat] using hsq
  exact (by decide : ¬((1 : ZMod 5)=0 ∨ (1 : ZMod 5)=2))
    ((complete_table_five 1).mp hsquare)

/-- The full three-parameter nonintegrality family on actual ideal graphs. -/
theorem actual_progression (primes : Fin 4 → ℕ)
    (hp : ∀ i, Nat.Prime (primes i)) (hinj : Function.Injective primes)
    (n m c : ℕ) (hc : 2*(6+25*n)-2 ≤ c) :
    ¬ActualLaplacianIntegral
      (modulus primes (pairExponents (6+25*n) (20+100*n+125*m) c)) := by
  intro H
  let a : ℕ := 6+25*n
  let b : ℕ := 20+100*n+125*m
  have ha : 2 ≤ (a : ℝ) := by
    dsimp [a]
    push_cast
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hb : 2*(a : ℝ)-2 ≤ (b : ℝ) := by dsimp [a,b]; push_cast; nlinarith
  have hc' : 2*(a : ℝ)-2 ≤ (c : ℝ) := by
    have hnat : 2*a ≤ c+2 := by dsimp [a]; omega
    have hcast : (2 : ℝ)*(a : ℝ) ≤ (c : ℝ)+2 := by exact_mod_cast hnat
    linarith
  obtain ⟨e,hel,heu,v,hv,hS⟩ := PairLowArithmetic.large_tail_low a b c ha hb hc'
  obtain ⟨u,hu,hK⟩ := tensor_eigenpair_of_symmetric (a : ℝ) b c
    (by dsimp [b]; positivity) (by linarith) e v hv hS
  obtain ⟨z,hz⟩ := PairTailSpectrum.integer_tensor_root primes hp hinj a b c
    (by dsimp [a]; omega) (by dsimp [b]; omega) (by omega) H e u hu hK
  have hzl : (1 : ℤ)<z := by exact_mod_cast (hz ▸ hel)
  have hzu : z<(3 : ℤ) := by exact_mod_cast (hz ▸ heu)
  have hz2 : z=2 := by omega
  have hd := PairTailSpectrum.integer_det_zero a b c (z-a-1) e
    (by push_cast; linarith) u hu hK
  have he : (a : ℤ)+1+(z-a-1)=2 := by omega
  rw [he] at hd
  apply progression_two_nonzero n m c
  convert hd using 1 <;> dsimp [a,b] <;> push_cast <;> ring

end D5.S3.Combinatorics.SpectralGraph.PairResonanceSpectrum
