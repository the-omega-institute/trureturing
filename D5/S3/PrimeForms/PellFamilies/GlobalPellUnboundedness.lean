/- GID: D5/S3/PrimeForms/PellFamilies/GlobalPellUnboundedness
   generality: G
   mirror-B: D5/B/S3/PrimeForms/PellFamilies/GlobalPellUnboundedness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A Pell orbit is unbounded yet locally periodic; unit one and edge cases are audited. -/

/- Library-search audit trail (2026-08-25):
   * Repository searches found `LocalPellPeriodicity` as the exact prime-power
     periodicity source, but no theorem connecting its matrix orbit to global
     unboundedness. It is imported and applied below rather than reproved.
   * Pinned Mathlib exact hits `Pell.xz_succ`, `Pell.yz_succ`, `Pell.dz_val`,
     and `Pell.yn_ge_n` provide the coordinate recurrence and unbounded lower
     bound. `Matrix.map_pow` and `RingHom.map_mulVec` identify local reduction.
   * `lean_loogle` and `lean_local_search` are unavailable in this tool
     environment. The lean4 skill's `smart_search.sh` found `Pell.yn_ge_n`;
     source searches found no ready matrix-power/Pell-coordinate bridge.
-/

import D5.S3.PrimeForms.PellFamilies.LocalPellPeriodicity
import Mathlib.NumberTheory.PellMatiyasevic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix

namespace D5.S3.PrimeForms.PellFamilies.GlobalPellUnboundedness

/-- The integral orbit obtained by repeatedly multiplying by a Pell-unit matrix. -/
def PellOrbit (discriminant unitX unitY : Int) (seed : Fin 2 -> Int)
    (n : Nat) : Fin 2 -> Int :=
  (!![unitX, discriminant * unitY; unitY, unitX] ^ n) *ᵥ seed

/-- A vector orbit is unbounded when some coordinate exceeds every natural bound. -/
def OrbitUnbounded (orbit : Nat -> Fin 2 -> Int) : Prop :=
  forall bound : Nat, exists n i, (bound : Int) < orbit n i

private theorem two_is_greater_than_one : 1 < (2 : Nat) := by
  norm_num

/- Route B is used deliberately. No library theorem made the matrix orbit
   unbounded directly, while reproving growth from its recurrence would
   duplicate `Pell.yn_ge_n`. This one bridge keeps the global and local claims
   about the same matrix-power sequence rather than creating a second source. -/
private theorem sqrt_three_pell_orbit_coordinates (n : Nat) :
    PellOrbit 3 2 1 ![(1 : Int), 0] n =
      ![Pell.xz two_is_greater_than_one n, Pell.yz two_is_greater_than_one n] := by
  induction n with
  | zero =>
      simp [PellOrbit, Pell.xz, Pell.yz]
  | succ n induction_hypothesis =>
      rw [PellOrbit, pow_succ', ← Matrix.mulVec_mulVec]
      change
        !![(2 : Int), 3; 1, 2] *ᵥ PellOrbit 3 2 1 ![(1 : Int), 0] n =
          ![Pell.xz two_is_greater_than_one (n + 1),
            Pell.yz two_is_greater_than_one (n + 1)]
      rw [induction_hypothesis]
      calc
        !![(2 : Int), 3; 1, 2] *ᵥ
              ![Pell.xz two_is_greater_than_one n, Pell.yz two_is_greater_than_one n] =
            ![2 * Pell.xz two_is_greater_than_one n +
                3 * Pell.yz two_is_greater_than_one n,
              Pell.xz two_is_greater_than_one n +
                2 * Pell.yz two_is_greater_than_one n] :=
          by
            ext i
            fin_cases i <;>
              simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        _ = ![Pell.xz two_is_greater_than_one (n + 1),
              Pell.yz two_is_greater_than_one (n + 1)] := by
          rw [Pell.xz_succ, Pell.yz_succ, Pell.dz_val]
          norm_num [Pell.az]
          constructor <;> ring

/-- The powers of `2 + sqrt(3)`, started at `(1, 0)`, form an unbounded
integral Pell orbit. This existential witness avoids the false claim that
every Pell unit has an unbounded orbit. -/
theorem sqrt_three_pell_orbit_is_unbounded :
    OrbitUnbounded (PellOrbit 3 2 1 ![(1 : Int), 0]) := by
  intro bound
  refine ⟨bound + 1, 1, ?_⟩
  rw [sqrt_three_pell_orbit_coordinates]
  have coordinate_bound :
      bound < Pell.yn two_is_greater_than_one (bound + 1) :=
    lt_of_lt_of_le (Nat.lt_succ_self bound)
      (Pell.yn_ge_n two_is_greater_than_one (bound + 1))
  change (bound : Int) < (Pell.yn two_is_greater_than_one (bound + 1) : Int)
  exact_mod_cast coordinate_bound

#print axioms sqrt_three_pell_orbit_is_unbounded

/-- The Pell unit `1` has the constant nonzero orbit from seed `(1, 0)`, so a
universal unboundedness theorem without a nontrivial-unit condition is false. -/
theorem unit_one_pell_orbit_is_not_unbounded :
    Not (OrbitUnbounded (PellOrbit 3 1 0 ![(1 : Int), 0])) := by
  have identity_matrix :
      (!![(1 : Int), 0; 0, 1] : Matrix (Fin 2) (Fin 2) Int) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have constant_orbit (n : Nat) :
      PellOrbit 3 1 0 ![(1 : Int), 0] n = ![(1 : Int), 0] := by
    change (!![(1 : Int), 0; 0, 1] ^ n) *ᵥ ![(1 : Int), 0] = ![(1 : Int), 0]
    rw [identity_matrix]
    simp
  intro unbounded
  obtain ⟨n, i, coordinate_bound⟩ := unbounded 1
  rw [constant_orbit n] at coordinate_bound
  fin_cases i <;> norm_num at coordinate_bound

#print axioms unit_one_pell_orbit_is_not_unbounded

/-- One concrete integral Pell orbit is globally unbounded while its reduction
modulo every prime power is pure-periodic. The local half is the imported
`LocalPellPeriodicity` theorem applied to the very same matrix and seed. -/
theorem global_unboundedness_and_prime_power_local_periodicity :
    OrbitUnbounded (PellOrbit 3 2 1 ![(1 : Int), 0]) /\
      forall prime exponent : Nat, Nat.Prime prime ->
        exists period, 0 < period /\
          Function.Periodic
            (fun n i =>
              (PellOrbit 3 2 1 ![(1 : Int), 0] n i :
                ZMod (prime ^ exponent)))
            period := by
  refine ⟨sqrt_three_pell_orbit_is_unbounded, ?_⟩
  intro prime exponent prime_is_prime
  have local_periodicity :=
    (LocalPellPeriodicity.pell_unit_and_unimodular_recurrences_are_locally_periodic
      3 2 1 ![(1 : Int), 0] ![(1 : Int), 0]
      (1 : Matrix (Fin 2) (Fin 2) Int) prime exponent prime_is_prime).1
  obtain ⟨period, period_pos, periodicity⟩ := local_periodicity (by norm_num)
  let reduction := Int.castRingHom (ZMod (prime ^ exponent))
  change Function.Periodic
    (fun n =>
      ((!![(2 : Int), 3; 1, 2].map reduction) ^ n) *ᵥ
        fun i => reduction (![((1 : Int)), 0] i))
    period at periodicity
  have reduced_orbit_eq (n : Nat) :
      ((!![(2 : Int), 3; 1, 2].map reduction) ^ n) *ᵥ
          (fun i => reduction (![((1 : Int)), 0] i)) =
        fun i => reduction (PellOrbit 3 2 1 ![(1 : Int), 0] n i) := by
    funext i
    simpa only [PellOrbit, ← Matrix.map_pow, Function.comp_def, mul_one] using
      (RingHom.map_mulVec reduction
        (!![(2 : Int), 3; 1, 2] ^ n) ![(1 : Int), 0] i).symm
  refine ⟨period, period_pos, ?_⟩
  intro n
  change
    (fun i => reduction (PellOrbit 3 2 1 ![(1 : Int), 0] (n + period) i)) =
      fun i => reduction (PellOrbit 3 2 1 ![(1 : Int), 0] n i)
  rw [← reduced_orbit_eq (n + period), ← reduced_orbit_eq n]
  exact periodicity n

#print axioms global_unboundedness_and_prime_power_local_periodicity

/- Degenerate audit: time zero returns the seed, including the zero seed. -/
example (discriminant unitX unitY : Int) (seed : Fin 2 -> Int) :
    PellOrbit discriminant unitX unitY seed 0 = seed := by
  simp [PellOrbit]

/- Degenerate audit: a zero seed stays zero for every modulus and update. -/
example (discriminant unitX unitY : Int) (prime exponent : Nat) :
    Function.Periodic
      (fun n i =>
        (PellOrbit discriminant unitX unitY (0 : Fin 2 -> Int) n i :
          ZMod (prime ^ exponent)))
      1 := by
  intro n
  funext i
  simp [PellOrbit]

/- Degenerate audit: exponent zero gives the one-element local interface. -/
example (prime : Nat) (prime_is_prime : Nat.Prime prime) :
    exists period, 0 < period /\
      Function.Periodic
        (fun n i =>
          (PellOrbit 3 2 1 ![(1 : Int), 0] n i : ZMod (prime ^ 0)))
        period :=
  global_unboundedness_and_prime_power_local_periodicity.2
    prime 0 prime_is_prime

/- Degenerate audit: the smallest prime needs no special branch. -/
example (exponent : Nat) :
    exists period, 0 < period /\
      Function.Periodic
        (fun n i =>
          (PellOrbit 3 2 1 ![(1 : Int), 0] n i : ZMod (2 ^ exponent)))
        period :=
  global_unboundedness_and_prime_power_local_periodicity.2
    2 exponent Nat.prime_two

end D5.S3.PrimeForms.PellFamilies.GlobalPellUnboundedness
