/- GID: D5/S3/Factorization/QuadraticIdeals/GoldenCubicSquareRoleNine
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/GoldenCubicSquareRoleNine
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The square role in the native Eisenstein product has forced coordinates modulo nine. -/

import D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct
import D5.S1.Scale.GoldenCubicBlockCongruences

set_option autoImplicit false

/-! The square role is measured in the original and rotated Eisenstein bases. -/

namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicSquareRoleNine

open D5.S1.Scale EisensteinOddQuotient GoldenCubicPrimaryProduct
open D5.S3.Arith.Primes.GoldenCubicBlockRanks
open D5.S3.Arith.Primes.FiniteFibonacciRankClosure

/-- In the primary Eisenstein basis the cube disappears modulo nine,
and the two square coordinates are forced by the original product. -/
theorem primary_square_coordinates_nine (η π γ : EisensteinOrder)
    (hπ : (3:EisensteinOrder) ∣ π-1) (hγ : (3:EisensteinOrder) ∣ γ-1)
    (he : η=π^2*γ^3) (hr : η.re%9=7) (hi : η.im%9=3) :
    π.re%9=4 ∧ π.im%9=6 := by
  obtain ⟨x,hx⟩ := hπ
  obtain ⟨y,hy⟩ := hγ
  have hπ' : π = 1+3*x := by linear_combination hx
  have hγ' : γ = 1+3*y := by linear_combination hy
  let z := x^2+(1+3*x)^2*(y+3*y^2+3*y^3)
  have hη : η=1+6*x+9*z := by
    rw [he,hπ',hγ']
    dsimp [z]
    ring
  have hre := congrArg QuadraticAlgebra.re hη
  have him := congrArg QuadraticAlgebra.im hη
  have hpr := congrArg QuadraticAlgebra.re hπ'
  have hpi := congrArg QuadraticAlgebra.im hπ'
  have hr3 : (3:EisensteinOrder).re=3 := rfl
  have hi3 : (3:EisensteinOrder).im=0 := rfl
  have hr6 : (6:EisensteinOrder).re=6 := rfl
  have hi6 : (6:EisensteinOrder).im=0 := rfl
  have hr9 : (9:EisensteinOrder).re=9 := rfl
  have hi9 : (9:EisensteinOrder).im=0 := rfl
  simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_mul,
    QuadraticAlgebra.im_mul, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
    hr3,hi3,hr6,hi6,hr9,hi9, zero_mul, mul_zero, zero_add, add_zero] at hre him hpr hpi
  omega

/-- On the actual oriented element modulo two, only the omega-squared
residue of the square factor is possible. -/
theorem primary_square_coordinates_two (η π γ : EisensteinOrder)
    (he : η=π^2*γ^3) (hr : (η.re:ZMod 2)=0) (hi : (η.im:ZMod 2)=1) :
    (π.re:ZMod 2)=1 ∧ (π.im:ZMod 2)=1 := by
  let A : ℤ := π.re^2-π.im^2
  let D : ℤ := 2*π.re*π.im-π.im^2
  let U : ℤ := γ.re^3-3*γ.re*γ.im^2+γ.im^3
  let V : ℤ := 3*γ.re*γ.im*(γ.re-γ.im)
  have hR : η.re = A*U-D*V := by
    have h := congrArg QuadraticAlgebra.re he
    norm_num [pow_succ, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] at h
    dsimp [A,D,U,V]
    linear_combination h
  have hI : η.im = A*V+D*U-D*V := by
    have h := congrArg QuadraticAlgebra.im he
    norm_num [pow_succ, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] at h
    dsimp [A,D,U,V]
    linear_combination h
  have heR := congrArg (fun z : ℤ => (z:ZMod 2)) hR
  have heI := congrArg (fun z : ℤ => (z:ZMod 2)) hI
  dsimp only [A,D,U,V] at heR heI
  push_cast at heR heI
  rw [hr] at heR
  rw [hi] at heI
  have htab : ∀ a b c d : ZMod 2,
      let A := a^2-b^2
      let D := 2*a*b-b^2
      let U := c^3-3*c*d^2+d^3
      let V := 3*c*d*(c-d)
      0=A*U-D*V → 1=A*V+D*U-D*V → a=1 ∧ b=1 := by
    decide
  exact htab _ _ _ _ heR heI

private theorem native_lucas_mod (j : ℕ) (hj : 1 ≤ j) :
    goldenLucas (3^j) % 9 = 4 ∧ goldenLucas (3^j) % 2 = 0 := by
  let L := goldenLucas (3^j)
  have h := (golden_cubic_lucas_block j hj).1
  have hm : L%72=4 := by
    simpa using (ZMod.intCast_eq_intCast_iff' L 4 72).mp h
  omega

/-- The primary generator fixed by the native ideal product, rotated
into its odd-norm square-root-minus-three coordinates, has both
coordinates prescribed modulo nine. -/
theorem native_oriented_coordinates (j : ℕ) (hj : 1 ≤ j) (π γ : EisensteinOrder)
    (hL : 1 ≤ goldenLucas (3^j))
    (hπ : (3:EisensteinOrder) ∣ π-1) (hγ : (3:EisensteinOrder) ∣ γ-1)
    (he : orientedFactor ((goldenLucas (3^j)-1).toNat) = π^2*γ^3) :
    ∃ a b : ℤ, a%9=4 ∧ b%9=8 ∧
      (⟨0,1⟩ : EisensteinOrder)*π = ⟨a+b,2*b⟩ ∧
      QuadraticAlgebra.norm π = a^2+3*b^2 := by
  let L := goldenLucas (3^j)
  let η := orientedFactor ((L-1).toNat)
  have him : η.im = L-1 := Int.toNat_of_nonneg (by change 1≤L at hL; omega)
  have hre : η.re = -2 := rfl
  have hmod := native_lucas_mod j hj
  change L%9=4 ∧ L%2=0 at hmod
  have h9 := primary_square_coordinates_nine η π γ hπ hγ he (by rw [hre]; decide) (by rw [him]; omega)
  have h2 := primary_square_coordinates_two η π γ he (by rw [hre]; decide) (by
    rw [him]
    have hh := (ZMod.intCast_eq_intCast_iff' (L-1) 1 2).mpr (by omega)
    simpa only [Int.cast_one] using hh)
  have hpo : π.re % 2 = 1 := by
    have hh := (ZMod.intCast_eq_intCast_iff' π.re 1 2).mp (by simpa only [Int.cast_one] using h2.1)
    omega
  have hqo : π.im % 2 = 1 := by
    have hh := (ZMod.intCast_eq_intCast_iff' π.im 1 2).mp (by simpa only [Int.cast_one] using h2.2)
    omega
  let b := (π.re-π.im)/2
  let a := -π.im-b
  have hb : 2*b = π.re-π.im := by dsimp [b]; omega
  have ha : a+b = -π.im := by dsimp [a]; ring
  refine ⟨a,b,?_,?_,?_,?_⟩
  · omega
  · omega
  · apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.re_mul]
      linear_combination -ha
    · simp only [QuadraticAlgebra.im_mul]
      linear_combination -hb
  · simp only [QuadraticAlgebra.norm_def]
    have hp : π.re = 2*b+π.im := by omega
    have hq : π.im = -a-b := by omega
    rw [hp,hq]
    ring

/-- The rotation in the native ideal orientation is multiplication by
omega: the witness in the integral square-root coordinates really
divides the oriented L plus square-root-minus-three. -/
theorem native_rotated_square_divisor (j : ℕ) (π γ : EisensteinOrder)
    (hL : 1 ≤ goldenLucas (3^j))
    (he : orientedFactor ((goldenLucas (3^j)-1).toNat) = π^2*γ^3) :
    (⟨0,1⟩ : EisensteinOrder)*π ∣ (⟨goldenLucas (3^j)+1,2⟩ : EisensteinOrder) := by
  let L := goldenLucas (3^j)
  let w : EisensteinOrder := ⟨0,1⟩
  let η := orientedFactor ((L-1).toNat)
  have him : η.im = L-1 := Int.toNat_of_nonneg (by change 1≤L at hL; omega)
  have hre : η.re = -2 := rfl
  have hrot : w^2*η = (⟨L+1,2⟩ : EisensteinOrder) := by
    apply QuadraticAlgebra.ext <;>
      norm_num [pow_succ,w,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,hre,him] <;> ring
  refine ⟨w*π*γ^3,?_⟩
  change (⟨L+1,2⟩ : EisensteinOrder) = (w*π)*(w*π*γ^3)
  rw [← hrot]
  change w^2*orientedFactor ((L-1).toNat) = _
  rw [he]
  ring

/-- If the original two-prime square-times-cube case occurs, its
square prime has an oriented norm representation with both
coordinates fixed modulo nine. The orientation is the square factor
of the existing native prime-ideal descent. -/
theorem actual_square_role_coordinates_nine (j P Q : ℕ) (hj : 1 ≤ j)
    (hP : P.Prime) (hQ : Q.Prime) (hPQ : P ≠ Q)
    (hfac : goldenLucas (3^j)^2+3 = (P:ℤ)^2*(Q:ℤ)^3) :
    ∃ a b : ℤ, a%9=4 ∧ b%9=8 ∧ a^2+3*b^2=(P:ℤ) ∧
      (⟨a+b,2*b⟩ : EisensteinOrder) ∣ (⟨goldenLucas (3^j)+1,2⟩ : EisensteinOrder) := by
  let L := goldenLucas (3^j)
  have hL : 1 ≤ L := by
    have hn : 3^j-1+1=3^j := by have := pow_pos (by decide : 0<(3:ℕ)) j; omega
    dsimp [L]
    rw [← hn,golden_lucas_succ_eq_fib_add_fib]
    have hp : 0 < (Nat.fib (3^j-1+2):ℤ) := by
      exact_mod_cast Nat.fib_pos.mpr (by omega : 0 < 3^j-1+2)
    have hn : 0 ≤ (Nat.fib (3^j-1):ℤ) := Int.natCast_nonneg _
    omega
  have hcast : (blockNorm ((L-1).toNat):ℤ)=L^2+3 := by
    simp only [blockNorm,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,
      Int.toNat_of_nonneg (show 0≤L-1 by omega)]
    ring
  have hfac' : blockNorm ((L-1).toNat)=P^2*Q^3 := by
    exact_mod_cast hcast.trans hfac
  let B := blockNorm ((L-1).toNat)
  have hB : B=P^2*Q^3 := hfac'
  have hsupport : B.primeFactors={P,Q} := by
    rw [hB, Nat.primeFactors_mul (pow_ne_zero _ hP.ne_zero) (pow_ne_zero _ hQ.ne_zero),
      Nat.primeFactors_prime_pow (by decide : 2 ≠ 0) hP,
      Nat.primeFactors_prime_pow (by decide : 3 ≠ 0) hQ]
    rfl
  have hPmem : P ∈ B.primeFactors := by rw [hsupport]; simp
  have hQmem : Q ∈ B.primeFactors := by rw [hsupport]; simp
  let _ : Fact P.Prime := ⟨hP⟩
  let _ : Fact Q.Prime := ⟨hQ⟩
  have hdepth (p : ℕ) (hp : p.Prime) (hpm : p ∈ B.primeFactors) :
      padicValNat p (Nat.fib (fibonacciRank p)) = padicValNat p B := by
    have hdvd : (p:ℤ) ∣ L^2+3 := by
      rw [← hcast]
      exact_mod_cast Nat.dvd_of_mem_primeFactors hpm
    rw [← (cubic_block_b_prime_rank j p hj hp hdvd).2.2, ← hcast, padicValInt.of_nat]
  have hPdepth : padicValNat P (Nat.fib (fibonacciRank P))=2 := by
    rw [hdepth P hP hPmem,hB]
    exact padicValNat_mul_pow_left 2 3 hPQ
  have hQdepth : padicValNat Q (Nat.fib (fibonacciRank Q))=3 := by
    rw [hdepth Q hQ hQmem,hB]
    exact padicValNat_mul_pow_right 2 3 hPQ.symm
  obtain ⟨_,_,_,_,pi,hpi,heta⟩ := golden_cubic_primary_product j hj
  obtain ⟨_,_,_,hπnorm,hπ,_⟩ := hpi P hPmem
  obtain ⟨_,_,_,_,hγ,_⟩ := hpi Q hQmem
  have hProd : orientedFactor ((L-1).toNat) = (pi P)^2*(pi Q)^3 := by
    change orientedFactor ((L-1).toNat) = ∏ p ∈ B.primeFactors,
      (pi p)^padicValNat p (Nat.fib (fibonacciRank p)) at heta
    rw [hsupport,Finset.prod_pair hPQ,hPdepth,hQdepth] at heta
    exact heta
  obtain ⟨a,b,ha,hb,hcoords,hnorm⟩ :=
    native_oriented_coordinates j hj (pi P) (pi Q) hL hπ hγ hProd
  have hDiv := native_rotated_square_divisor j (pi P) (pi Q) hL hProd
  rw [hcoords] at hDiv
  exact ⟨a,b,ha,hb,hnorm.symm.trans hπnorm,hDiv⟩


end D5.S3.Factorization.QuadraticIdeals.GoldenCubicSquareRoleNine
