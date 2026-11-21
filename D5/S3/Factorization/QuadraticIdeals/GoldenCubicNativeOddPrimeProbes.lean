/- GID: D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeOddPrimeProbes
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/GoldenCubicNativeOddPrimeProbes
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Uniform native residual probes and arithmetic inputs for the odd-prime image criterion. -/

import D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeFiveProbes
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo

set_option autoImplicit false

namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeOddPrimeProbes
open D5.S1.Scale D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeCyclic
open D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeElliptic
open D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeFiveProbes

private theorem invariant_states {p : ℕ} [Fact p.Prime] (S : Finset (ZMod p))
    (h₀ : 4 ∈ S) (hstep : ∀ l ∈ S, l*(l^2+3) ∈ S) (j : ℕ) (hj : 1 ≤ j) :
    (goldenLucas (3^j):ZMod p) ∈ S := by
  obtain ⟨n,rfl⟩ : ∃ n : ℕ, j=n+1 := ⟨j-1, by omega⟩
  clear hj
  induction n with
  | zero =>
    change (goldenLucas 3:ZMod p) ∈ S
    rw [show goldenLucas 3=4 by decide]
    simpa only [Int.cast_ofNat] using h₀
  | succ n ih =>
    rw [orbit_step (n+1) (by omega)]
    exact hstep _ ih

private def S5 : Finset (ZMod 5) := {4,1}
private def S7 : Finset (ZMod 7) := {4,6,3,1}
private def S31 : Finset (ZMod 31) := {4,14,27,17}
private def S41 : Finset (ZMod 41) := {4,35,12,1}

private theorem good5 : letI : Fact (Nat.Prime 5) := ⟨by decide⟩
    ∀ l ∈ S5, (model l 1).Δ ≠ 0 ∧ count 5 l=5 := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private theorem good7 : letI : Fact (Nat.Prime 7) := ⟨by decide⟩
    ∀ l ∈ S7, (model l 1).Δ ≠ 0 ∧
      count 7 l ∈ ({7,11,9,5}:Finset ℕ) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 3000000 in
private theorem good31 : letI : Fact (Nat.Prime 31) := ⟨by decide⟩
    ∀ l ∈ S31, (model l 1).Δ ≠ 0 ∧
      count 31 l ∈ ({23,24,41,40}:Finset ℕ) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 6000000 in
private theorem good41 : letI : Fact (Nat.Prime 41) := ⟨by decide⟩
    ∀ l ∈ S41, (model l 1).Δ ≠ 0 ∧
      count 41 l ∈ ({45,39,53}:Finset ℕ) := by decide

/-- The Frobenius trace at good prime seven always lies in the same four
nonzero integers. In particular it is nonzero modulo every prime above thirteen. -/
theorem native_trace7 (j : ℕ) (hj : 1 ≤ j) :
    let l := (goldenLucas (3^j):ZMod 7)
    (model l 1).Δ ≠ 0 ∧ formalTrace 7 (Nat.card (model l 1).Point) ∈
      ({1,-3,-1,3}:Finset ℤ) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  dsimp only
  let l := (goldenLucas (3^j):ZMod 7)
  obtain ⟨hΔ,hc⟩ := good7 l (invariant_states S7 (by decide) (by decide) j hj)
  refine ⟨hΔ,?_⟩
  rw [card_curve_points 7 l hΔ]
  have h := (by decide :
    ∀ n ∈ ({7,11,9,5}:Finset ℕ), formalTrace 7 n ∈ ({1,-3,-1,3}:Finset ℤ))
  exact h _ hc

theorem native_trace7_nonzero_mod (j ell : ℕ) (hj : 1 ≤ j) (hell : 3 < ell) :
    let l := (goldenLucas (3^j):ZMod 7)
    (formalTrace 7 (Nat.card (model l 1).Point):ZMod ell) ≠ 0 := by
  dsimp only
  let t := formalTrace 7 (Nat.card (model (goldenLucas (3^j):ZMod 7) 1).Point)
  change (t:ZMod ell) ≠ 0
  have h : t=1 ∨ t= -3 ∨ t= -1 ∨ t=3 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using (native_trace7 j hj).2
  intro H
  have hd : (ell:ℤ) ∣ t := (ZMod.intCast_zmod_eq_zero_iff_dvd t ell).mp H
  have h1 : ¬ (ell:ℤ) ∣ (1:ℤ) := by
    exact_mod_cast (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 1) (by omega : 1 < ell))
  have h3 : ¬ (ell:ℤ) ∣ (3:ℤ) := by
    exact_mod_cast (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 3) hell)
  rcases h with h|h|h|h
  · exact h1 (h ▸ hd)
  · exact h3 (dvd_neg.mp (h ▸ hd))
  · exact h1 (dvd_neg.mp (h ▸ hd))
  · exact h3 (h ▸ hd)

theorem two_imaginary_characters_at_seven :
    (¬ ∃ x : ZMod 7, x^2 = -1) ∧ (¬ ∃ x : ZMod 7, x^2 = -2) := by decide

theorem native_square_offset (j : ℕ) :
    let l := goldenLucas (3^j)
    (model (l:ℚ) 1).j - 1728 = (24*(l:ℚ))^2 := by
  dsimp only
  rw [model_j]
  ring

theorem native_j_offset_even_valuation (j p : ℕ) [Fact p.Prime] :
    let l := goldenLucas (3^j)
    ∃ e : ℤ, padicValRat p ((model (l:ℚ) 1).j - 1728) = 2*e := by
  dsimp only
  refine ⟨padicValRat p (24*(goldenLucas (3^j):ℚ)),?_⟩
  rw [native_square_offset j, padicValRat.pow]
  rfl

theorem native_j_two_exact (j : ℕ) (hj : 1 ≤ j) :
    let l := goldenLucas (3^j)
    padicValRat 2 (model (l:ℚ) 1).j = 6 := by
  dsimp only
  let l := goldenLucas (3^j)
  have he : l%2=0 := (native_lucas_mod j hj).2
  have ho : ¬ (2:ℤ) ∣ l^2+3 := by
    intro H
    have h := Int.emod_eq_zero_of_dvd H
    rw [Int.add_emod, pow_two, Int.mul_emod, he] at h
    norm_num at h
  have nB : (l:ℚ)^2+3 ≠ 0 := by positivity
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  rw [model_j, show (1728:ℚ)+(24*(l:ℚ))^2 = 576*((l:ℚ)^2+3) by ring,
    padicValRat.mul (by norm_num) nB]
  have hB : padicValRat 2 ((l:ℚ)^2+3) = 0 := by
    rw [show (l:ℚ)^2+3 = ((l^2+3:ℤ):ℚ) by push_cast; rfl,
      padicValRat.of_int, padicValInt.eq_zero_of_not_dvd ho]
    norm_num
  have h9 : padicValRat 2 (9:ℚ) = 0 := by
    change padicValRat 2 ((9:ℤ):ℚ)=0
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd (by decide : ¬ (2:ℤ) ∣ 9)]
    rfl
  have h2 : padicValRat 2 (2:ℚ)=1 := by
    change padicValRat 2 ((2:ℕ):ℚ)=1
    exact padicValRat.self (by decide : 1<2)
  rw [hB, add_zero, show (576:ℚ) = 2^6*9 by norm_num,
    padicValRat.mul (by norm_num) (by norm_num), padicValRat.pow,
    h2,h9]
  norm_num

/-- The matrix representing the characteristic data t and d in a cyclic basis. -/
def companion (ell : ℕ) (t d : ZMod ell) : Matrix (Fin 2) (Fin 2) (ZMod ell) :=
  !![0,-d;1,t]

def scalarTest {ell : ℕ} (M : Matrix (Fin 2) (Fin 2) (ZMod ell)) : Prop :=
  M 0 1=0 ∧ M 1 0=0 ∧ M 0 0=M 1 1

instance {ell : ℕ} (M : Matrix (Fin 2) (Fin 2) (ZMod ell)) :
    Decidable (scalarTest M) := by unfold scalarTest; infer_instance

/-- Finite arithmetic certificate: good trace polynomial is separable,
has the prescribed split type, and the companion matrix first becomes
scalar at exactly the prescribed positive power. -/
def dataCert (ell p n : ℕ) [NeZero ell] (split : Bool) (k : ℕ) : Prop :=
  let t := (formalTrace p n:ZMod ell)
  let d := (p:ZMod ell)
  let M := companion ell t d
  t^2-4*d ≠ 0 ∧
    ((∃ x : ZMod ell, x^2-t*x+d=0) ↔ split=true) ∧
    scalarTest (M^k) ∧
    ∀ i : Fin 14, 0 < i.val → i.val < k → ¬ scalarTest (M^i.val)

instance (ell p n : ℕ) [NeZero ell] (s : Bool) (k : ℕ) :
    Decidable (dataCert ell p n s k) := by unfold dataCert; infer_instance

set_option maxRecDepth 16384 in
private theorem readout_tables :
    dataCert 7 5 5 true 6 ∧
    (∀ n ∈ ({23,24,41,40}:Finset ℕ), dataCert 7 31 n false 8) ∧
    dataCert 11 5 5 true 5 ∧ dataCert 11 17 15 false 12 ∧
    dataCert 13 5 5 false 14 ∧
    (∀ n ∈ ({45,39,53}:Finset ℕ), dataCert 13 41 n true 12 ∨
      dataCert 13 41 n true 4) := by decide

theorem native_small_prime_certificates (j : ℕ) (hj : 1 ≤ j) :
    let l5 := (goldenLucas (3^j):ZMod 5)
    let l17 := (goldenLucas (3^j):ZMod 17)
    let l31 := (goldenLucas (3^j):ZMod 31)
    let l41 := (goldenLucas (3^j):ZMod 41)
    let n5 := Nat.card (model l5 1).Point
    let n17 := Nat.card (model l17 1).Point
    let n31 := Nat.card (model l31 1).Point
    let n41 := Nat.card (model l41 1).Point
    (model l5 1).Δ ≠ 0 ∧ (model l17 1).Δ ≠ 0 ∧
    (model l31 1).Δ ≠ 0 ∧ (model l41 1).Δ ≠ 0 ∧
    dataCert 7 5 n5 true 6 ∧ dataCert 7 31 n31 false 8 ∧
    dataCert 11 5 n5 true 5 ∧ dataCert 11 17 n17 false 12 ∧
    dataCert 13 5 n5 false 14 ∧
    (dataCert 13 41 n41 true 12 ∨ dataCert 13 41 n41 true 4) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fact (Nat.Prime 17) := ⟨by decide⟩
  let : Fact (Nat.Prime 31) := ⟨by decide⟩
  let : Fact (Nat.Prime 41) := ⟨by decide⟩
  dsimp only
  let l5 := (goldenLucas (3^j):ZMod 5)
  let l17 := (goldenLucas (3^j):ZMod 17)
  let l31 := (goldenLucas (3^j):ZMod 31)
  let l41 := (goldenLucas (3^j):ZMod 41)
  obtain ⟨h5,c5⟩ := good5 l5 (invariant_states S5 (by decide) (by decide) j hj)
  obtain ⟨c17,h17⟩ := native_good_probe17 (j:=j) hj
  obtain ⟨h31,c31⟩ := good31 l31 (invariant_states S31 (by decide) (by decide) j hj)
  obtain ⟨h41,c41⟩ := good41 l41 (invariant_states S41 (by decide) (by decide) j hj)
  refine ⟨h5,h17,h31,h41,?_⟩
  rw [card_curve_points 5 l5 h5, card_curve_points 17 l17 h17,
    card_curve_points 31 l31 h31, card_curve_points 41 l41 h41, c5,
    show count 17 l17=15 from c17]
  exact ⟨readout_tables.1, readout_tables.2.1 _ c31, readout_tables.2.2.1,
    readout_tables.2.2.2.1, readout_tables.2.2.2.2.1, readout_tables.2.2.2.2.2 _ c41⟩

end D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeOddPrimeProbes
