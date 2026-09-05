/- GID: D5/S3/Analytic/PrimeZeckendorf/PrimeZeckendorfCoordinates
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime locality and Zeckendorf depth form a faithful transverse address for golden Euler weights. -/

import D5.S0.Conventions.WDigits
import D5.S3.Analytic.EulerGerm.GoldenLocalFactor
import D5.S3.ObserverMemory.Refinement.ProductCoordinateTransversality
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.PrimeZeckendorf.PrimeZeckendorfCoordinates

open D5.S0.Conventions
open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.ObserverMemory.Refinement.ProductCoordinateTransversality

/-- One arithmetic local channel together with one golden layer index. -/
abbrev PrimeGoldenCoordinate := ProductCoordinate Nat.Primes ℕ

/-- Decode a canonical Zeckendorf address back to its natural layer index. -/
def decodeWAddress (address : WDigitString) : ℕ :=
  (address.1.map Nat.fib).sum

/-- The canonical W encoding is lossless. -/
@[simp] theorem decode_wEncoding (layer : ℕ) :
    decodeWAddress (wEncoding layer) = layer := by
  change ((wdigits layer).map Nat.fib).sum = layer
  exact decode_wdigits layer

/-- Replace the ordinary layer number by its canonical Zeckendorf address while
retaining the prime-local coordinate. -/
def primeZeckendorfReadout :
    PrimeGoldenCoordinate → Nat.Primes × WDigitString :=
  fun state => (state.1, wEncoding state.2)

/-- Prime plus Zeckendorf address faithfully recovers the original `(p,v)`
coordinate. -/
theorem prime_zeckendorf_readout_injective :
    Function.Injective primeZeckendorfReadout := by
  intro left right hsame
  apply Prod.ext
  · simpa [primeZeckendorfReadout] using congrArg Prod.fst hsame
  · have haddress : wEncoding left.2 = wEncoding right.2 := by
      simpa [primeZeckendorfReadout] using congrArg Prod.snd hsame
    have hdecoded := congrArg decodeWAddress haddress
    simpa using hdecoded

/-- A fixed prime fiber and a fixed golden-layer fiber intersect in the single
address `(p,v)`. -/
theorem prime_fiber_inter_golden_layer_fiber
    (prime : Nat.Primes) (layer : ℕ) :
    localFiber (Layer := ℕ) prime ∩
        layerFiber (Local := Nat.Primes) layer =
      {(prime, layer)} :=
  local_fiber_inter_layer_fiber prime layer

/-- The analytic weight attached to one prime-local golden layer. -/
def primeLayerWeight (s : ℂ) (state : PrimeGoldenCoordinate) : ℂ :=
  (state.1 : ℂ) ^ (-s * (o5Beta state.2 : ℂ))

/-- The same weight computed from the prime plus canonical Zeckendorf address. -/
def primeZeckendorfWeight
    (s : ℂ) (address : Nat.Primes × WDigitString) : ℂ :=
  (address.1 : ℂ) ^
    (-s * (o5Beta (decodeWAddress address.2) : ℂ))

/-- The local analytic weight factors exactly through the faithful
prime-Zeckendorf address. -/
theorem prime_layer_weight_factors_through_zeckendorf
    (s : ℂ) (state : PrimeGoldenCoordinate) :
    primeZeckendorfWeight s (primeZeckendorfReadout state) =
      primeLayerWeight s state := by
  rcases state with ⟨prime, layer⟩
  simp [primeZeckendorfWeight, primeZeckendorfReadout,
    primeLayerWeight]

/-- The frozen golden local factor is precisely the sum over the Zeckendorf
addresses inside one fixed prime channel. -/
theorem germLocalFactor_eq_prime_zeckendorf_sum
    (s : ℂ) (prime : Nat.Primes) :
    germLocalFactor s prime =
      ∑' layer : ℕ,
        primeZeckendorfWeight s (prime, wEncoding layer) := by
  unfold germLocalFactor
  apply tsum_congr
  intro layer
  simp [primeZeckendorfWeight]

/-- The first excited golden layer in every prime channel has the common
`phi^2` exponent that supplies the zeta skeleton in the frozen factorization. -/
theorem first_golden_layer_weight
    (s : ℂ) (prime : Nat.Primes) :
    primeLayerWeight s (prime, 1) =
      (prime : ℂ) ^
        (-s * (((Real.goldenRatio ^ 2 : ℝ) : ℂ))) := by
  simp [primeLayerWeight, o5_beta_power_law.1]

#print axioms decode_wEncoding
#print axioms prime_zeckendorf_readout_injective
#print axioms prime_fiber_inter_golden_layer_fiber
#print axioms prime_layer_weight_factors_through_zeckendorf
#print axioms germLocalFactor_eq_prime_zeckendorf_sum
#print axioms first_golden_layer_weight

end D5.S3.Analytic.PrimeZeckendorf.PrimeZeckendorfCoordinates
