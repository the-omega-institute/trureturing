/- GID: D5/S3/Combinatorics/SpectralGraph/FourPrimeIdealIntersectionObstructions
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/FourPrimeIdealIntersectionObstructions
   mirror-E: none(waiver:source-only-positive-theorem)
   anchors: []
   utility: none
   digest: Complete paired four-prime obstructions on the actual ideal graph. -/
import D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionLift
import D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionCongruence
import Mathlib.Tactic

/-! The full four-prime families are attributed to the public
ideal-intersection-laplacian source, revision b93becea662a746badeadba42fdc3d3eb3db9382.
Endpoint exclusion and the infinite congruence family follow the completed
mathematical note supplied 2026-11-02. No novelty claim is made. -/
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped Classical
namespace D5.S3.Combinatorics.SpectralGraph.FourPrimeIdealIntersectionObstructions
open D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSupport
open D5.S3.Combinatorics.SpectralGraph.IdealIntersectionObstructions
open D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionObstructions
open D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionEndpoints
open D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionDeterminants
open D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionLift
open D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionCongruence

private lemma eigenvalue_ne_of_det_ne (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ)
    (e r : ℝ) (h : Fin 2 × Fin 2 → ℝ) (hh : h ≠ 0) (he : M*ᵥ h=e • h)
    (hd : (M-r • 1).det ≠ 0) : e ≠ r := by
  intro her
  apply hh
  apply Matrix.eq_zero_of_mulVec_eq_zero hd
  rw [sub_mulVec,he,smul_mulVec,one_mulVec,her,sub_self]

private lemma noninteger_of_interval (e : ℝ) (hl : 1 < e) (hu : e < 3) (he : e ≠ 2) :
    ¬∃ z : ℤ, e=z := by
  rintro ⟨z,hz⟩
  have hzl : (1 : ℤ) < z := by exact_mod_cast (hz ▸ hl)
  have hzu : z < (3 : ℤ) := by exact_mod_cast (hz ▸ hu)
  have hz2 : z=2 := by omega
  exact he (by rw [hz,hz2]; norm_num)

private lemma actual_nonintegral_of_paired (p : Fin 4 → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (e : ℝ) (he : ¬∃ z : ℤ, e=z) (h : Fin 2 × Fin 2 → ℝ)
    (hh : h ≠ 0) (hE : tensorK (a : ℝ) (b : ℝ) (c : ℝ)*ᵥ h=e • h) :
    ¬ActualLaplacianIntegral (modulus p (pairExponents a b c)) := by
  have hactual := actual_paired_eigenvalue p hp hinj a b c ha hb hc e h hh hE
  intro H
  obtain ⟨z,hz⟩ := H _ hactual
  apply he
  refine ⟨((((a+1)^2*(b+1)*(c+1))-2 : ℕ) : ℤ)+1-z,?_⟩
  push_cast
  linarith

private lemma modulus_permutation (p : Fin 4 → ℕ) (k : Fin 4 → ℕ)
    (σ : Equiv.Perm (Fin 4)) :
    modulus (fun i => p (σ.symm i)) k=modulus p (fun i => k (σ i)) := by
  unfold modulus
  simpa using (Equiv.prod_comp σ (fun i => p (σ.symm i)^k i)).symm

private lemma two_exception (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) :
    ¬ActualLaplacianIntegral (modulus p (pairExponents 2 5 8)) := by
  obtain ⟨e,he,h,hh,hE⟩ := two_mod_nine_noninteger 0 0 (by norm_num) (by norm_num)
  apply actual_nonintegral_of_paired p hp hinj 2 5 8 (by omega) (by omega) (by omega) e he h hh
  simpa using hE

private lemma two_base (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (b c : ℕ) (hb : 0 < b) (hc : 0 < c) :
    ¬ActualLaplacianIntegral (modulus p (pairExponents 2 b c)) := by
  have hk (i : Fin 4) : 0 < pairExponents 2 b c i := by
    fin_cases i <;> simp [pairExponents] <;> assumption
  by_cases hb1 : b=1
  · exact (unit_exponent_obstruction p hp hinj _ hk (by norm_num) 2
      (by simp [pairExponents,hb1])).choose_spec.2.2.2
  by_cases hc1 : c=1
  · exact (unit_exponent_obstruction p hp hinj _ hk (by norm_num) 3
      (by simp [pairExponents,hc1])).choose_spec.2.2.2
  have hb2 : 2 ≤ b := by omega
  have hc2 : 2 ≤ c := by omega
  by_cases hex : ((b=5 ∧ c=8) ∨ (b=8 ∧ c=5))
  · rcases hex with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact two_exception p hp hinj
    · let q : Fin 4 → ℕ := ![p 0,p 1,p 3,p 2]
      let τ : Equiv.Perm (Fin 4) := Equiv.swap 2 3
      have hq : q=fun i => p (τ i) := by
        ext i
        fin_cases i <;> simp [q,τ,Equiv.swap_apply_def]
      have hqp (i : Fin 4) : Nat.Prime (q i) := by rw [hq]; exact hp (τ i)
      have hqi : Function.Injective q := by rw [hq]; exact hinj.comp τ.injective
      have hm : modulus q (pairExponents 2 5 8)=modulus p (pairExponents 2 8 5) := by
        simp only [modulus,Fin.prod_univ_four]
        change p 0^2*p 1^2*p 3^5*p 2^8=p 0^2*p 1^2*p 2^8*p 3^5
        ring
      rw [← hm]
      exact two_exception q hqp hqi
  have hP : P2 (b : ℝ) (c : ℝ) ≠ 0 := by
    have hi : P2 (b : ℤ) (c : ℤ) ≠ 0 := by
      intro hz
      apply hex
      have hh := (P2_zero_iff (b : ℤ) (c : ℤ) (by omega) (by omega)).mp hz
      exact_mod_cast hh
    unfold P2 at *
    exact_mod_cast hi
  obtain ⟨e,hl,hu,v,hv,hE⟩ := two_symmetric_low_eigenpair (b : ℝ) (c : ℝ)
    (by exact_mod_cast hb) (by exact_mod_cast hc)
  obtain ⟨h,hh,hK⟩ := tensor_eigenpair_of_symmetric 2 (b : ℝ) (c : ℝ)
    (by exact_mod_cast hb) (by exact_mod_cast hc) e v hv hE
  have he2 : e ≠ 2 := eigenvalue_ne_of_det_ne _ e 2 h hh hK (by rwa [det_two_sub_two])
  exact actual_nonintegral_of_paired p hp hinj 2 b c (by omega) hb hc e
    (noninteger_of_interval e hl hu he2) h hh hK

/-- Every permutation of `(2,2,b,c)`, with all positive tail exponents, gives a
nonintegral Laplacian on the actual nonzero proper ideal-intersection graph. -/
theorem two_equal_obstruction (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (σ : Equiv.Perm (Fin 4))
    (b c : ℕ) (hb : 0 < b) (hc : 0 < c) :
    ¬ActualLaplacianIntegral (modulus p (fun i => pairExponents 2 b c (σ i))) := by
  rw [← modulus_permutation p (pairExponents 2 b c) σ]
  exact two_base _ (fun i => hp (σ.symm i)) (hinj.comp σ.symm.injective) b c hb hc

private lemma three_base_low (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (b c : ℕ) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    ∃ e : ℝ, (((16*(b+1)*(c+1)-2 : ℕ) : ℝ)-2 < e) ∧
      e < ((16*(b+1)*(c+1)-2 : ℕ) : ℝ) ∧
      e ≠ ((16*(b+1)*(c+1)-2 : ℕ) : ℝ)-1 ∧
      HasActualEigenvalue (modulus p (pairExponents 3 b c)) e ∧
      ¬ActualLaplacianIntegral (modulus p (pairExponents 3 b c)) := by
  have hP : P3 (b : ℝ) (c : ℝ) ≠ 0 := by
    have hi := P3_nonzero (b : ℤ) (c : ℤ) (by omega) (by omega)
    unfold P3 at *
    exact_mod_cast hi
  obtain ⟨e,hl,hu,v,hv,hE⟩ := three_symmetric_low_eigenpair (b : ℝ) (c : ℝ)
    (by exact_mod_cast hb) (by exact_mod_cast hc)
  obtain ⟨h,hh,hK⟩ := tensor_eigenpair_of_symmetric 3 (b : ℝ) (c : ℝ)
    (by exact_mod_cast (show 0 < b by omega)) (by exact_mod_cast (show 0 < c by omega)) e v hv hE
  have he2 : e ≠ 2 := eigenvalue_ne_of_det_ne _ e 2 h hh hK (by rwa [det_three_sub_two])
  let V : ℕ := 16*(b+1)*(c+1)-2
  have hactual : HasActualEigenvalue (modulus p (pairExponents 3 b c)) ((V : ℝ)+1-e) := by
    simpa [V] using actual_paired_eigenvalue p hp hinj 3 b c
      (by omega) (by omega) (by omega) e h hh hK
  refine ⟨(V : ℝ)+1-e,by linarith,by linarith,?_,hactual,?_⟩
  · intro he
    exact he2 (by linarith)
  · exact actual_nonintegral_of_paired p hp hinj 3 b c (by omega) (by omega) (by omega)
      e (noninteger_of_interval e hl hu he2) h hh hK

/-- Every permutation of `(3,3,b,c)`, with positive tails, is nonintegral. At
both tails at least two, the actual graph has an eigenvalue in `(V-2,V)` distinct
from `V-1`, with `V=16(b+1)(c+1)-2`. Unit boundaries use the arbitrary-prime H1. -/
theorem three_equal_obstruction (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (σ : Equiv.Perm (Fin 4))
    (b c : ℕ) (hb : 0 < b) (hc : 0 < c) :
    ¬ActualLaplacianIntegral (modulus p (fun i => pairExponents 3 b c (σ i))) ∧
    (2 ≤ b → 2 ≤ c → ∃ e : ℝ, (((16*(b+1)*(c+1)-2 : ℕ) : ℝ)-2 < e) ∧
      e < ((16*(b+1)*(c+1)-2 : ℕ) : ℝ) ∧
      e ≠ ((16*(b+1)*(c+1)-2 : ℕ) : ℝ)-1 ∧
      HasActualEigenvalue (modulus p (fun i => pairExponents 3 b c (σ i))) e) := by
  rw [← modulus_permutation p (pairExponents 3 b c) σ]
  let q : Fin 4 → ℕ := fun i => p (σ.symm i)
  have hqp (i : Fin 4) : Nat.Prime (q i) := hp (σ.symm i)
  have hqi : Function.Injective q := hinj.comp σ.symm.injective
  have hk (i : Fin 4) : 0 < pairExponents 3 b c i := by
    fin_cases i <;> simp [pairExponents] <;> assumption
  have hlow (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) := three_base_low q hqp hqi b c hb2 hc2
  constructor
  · by_cases hb1 : b=1
    · exact (unit_exponent_obstruction q hqp hqi _ hk (by norm_num) 2
        (by simp [pairExponents,hb1])).choose_spec.2.2.2
    by_cases hc1 : c=1
    · exact (unit_exponent_obstruction q hqp hqi _ hk (by norm_num) 3
        (by simp [pairExponents,hc1])).choose_spec.2.2.2
    exact (hlow (by omega) (by omega)).choose_spec.2.2.2.2
  · intro hb2 hc2
    obtain ⟨e,hl,hu,he,hactual,_⟩ := hlow hb2 hc2
    exact ⟨e,hl,hu,he,hactual⟩

end D5.S3.Combinatorics.SpectralGraph.FourPrimeIdealIntersectionObstructions
