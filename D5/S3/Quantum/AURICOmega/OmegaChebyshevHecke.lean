/- GID: D5/S3/Quantum/AURICOmega/OmegaChebyshevHecke
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/OmegaChebyshevHecke
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Chebyshev identities, pentagonal closure, quadrupoles and norm-five Hecke data. -/

module
prelude
public import OmegaMath.Algebra.QuadraticExt.SpecialValues
public import OmegaMath.Harmonic.ChebyshevHecke.Orbitals
public import OmegaMath.Harmonic.ChebyshevHecke.Traces

namespace D5.S3.Quantum.AURICOmega.OmegaChebyshevHecke

open Omega Omega.Chebyshev

/-- The signed Pell relation holds at every degree and integer input. -/
public theorem pell_chebyshev (x : Int) (n : Nat) :
    Eq ((Int.square (T intRing x n.succ)).sub
      (((Int.square x).sub Int.one).mul (Int.square (U intRing x n)))) Int.one :=
  pell intRing intRingLaws x n

/-- Doubling the index of the first-kind polynomial uses a single square. -/
public theorem chebyshev_doubling (x : Int) (n : Nat) :
    Eq (T intRing x (n.add n)) ((Int.two.mul (Int.square (T intRing x n))).sub Int.one) :=
  T_double intRing intRingLaws x n

/-- Every even-degree character evaluates as a polynomial of the squared argument. -/
public theorem even_chebyshev (x : Int) (n : Nat) :
    Eq (E intRing (Int.square x) n) (U intRing x (n.add n)) :=
  even_character intRing intRingLaws x n

/-- An odd-degree character retains the signed argument as a factor. -/
public theorem odd_chebyshev (x : Int) (n : Nat) :
    Eq (x.mul (oddFactor intRing (Int.square x) n)) (U intRing x (n.add n).succ) :=
  odd_character intRing intRingLaws x n

/-- The spin-two character is quadratic in the squared argument. -/
public theorem spin_two_character (k : FiniteRatio) :
    let four := rationalRing.square rationalRing.two
    let eight := rationalRing.mul rationalRing.two four
    FiniteRatio.Equivalent (E rationalRing k (.succ (.succ .zero)))
      ((((four.square).mul k.square).sub ((eight.add four).mul k)).add FiniteRatio.one) :=
  E_two rationalRing rationalRingLaws k

/-- The golden generator gives the exact first-kind pentagonal closures. -/
public theorem pentagonal_chebyshev :
    And (QPhi.scalarRing.eqv (T QPhi.scalarRing QPhi.phiHalf QPhi.five)
      (QPhi.scalarRing.neg QPhi.scalarRing.one))
      (And (QPhi.scalarRing.eqv (T QPhi.scalarRing QPhi.phiHalf QPhi.ten) QPhi.scalarRing.one)
        (QPhi.scalarRing.eqv (T QPhi.scalarRing QPhi.phiSubOneHalf QPhi.five) QPhi.scalarRing.one)) :=
  And.intro QPhi.T_five_phi_half (And.intro QPhi.T_ten_phi_half QPhi.T_five_phi_sub_one_half)

/-- Each diagonal entry of the closed shell vanishes. Removing a doubly occupied
orbital leaves an exact trace-free diagonal. -/
public theorem orbital_quadrupole :
    And (∀ a : Orbitals.Axis, IntRatio.Equivalent (Orbitals.closedShell a) (IntRatio.ofInt Int.zero))
      (And (IntRatio.Equivalent (Orbitals.deletedShell .x) (Orbitals.seventh (Int.ofNat Orbitals.four).neg))
        (And (IntRatio.Equivalent (Orbitals.deletedShell .y) (Orbitals.seventh (Int.ofNat Orbitals.four).neg))
          (And (IntRatio.Equivalent (Orbitals.deletedShell .z)
            (Orbitals.seventh (Int.ofNat (Orbitals.four.add Orbitals.four))))
            (IntRatio.Equivalent (((Orbitals.deletedShell .x).add (Orbitals.deletedShell .y)).add
              (Orbitals.deletedShell .z)) (IntRatio.ofInt Int.zero))))) :=
  let h := Orbitals.deleted_shell_diagonal
  And.intro Orbitals.closed_shell_zero
    (And.intro h.left (And.intro h.right.left (And.intro h.right.right Orbitals.deleted_shell_trace_zero)))

/-- The sum over the five real orbitals vanishes in each Cartesian direction. -/
public theorem full_orbital_quadrupole (a : Orbitals.Axis) :
    IntRatio.Equivalent (Orbitals.fullShell a) (IntRatio.ofInt Int.zero) :=
  Orbitals.full_shell_zero a

/-- Each of the six norm-five generators has the same scalar overlap. -/
public theorem lps_norm_five (g : S5.Generator) :
    And (Eq g.coordinates.normSq S5.i5)
      (Eq g.coordinates.kappa (IntRatio.value Int.one S5.n5)) :=
  And.intro (S5.norm_five g) (S5.kappa_one_fifth g)

/-- The scaled integer recurrence represents the character at one fifth at every degree. -/
public theorem lps_hecke_trace_formula (n : Nat) :
    IntRatio.Equivalent (S5.averageCharacter n).toRatio (S5.traceRepresentative n) :=
  S5.average_character_eq_trace n

/-- The first six character trace representatives are exact signed fractions. -/
public theorem lps_hecke_traces : S5.traceTable := S5.trace_table

/-- The integer matrix of the six-generator sum and its strict margin in each branch. -/
public theorem lps_ramanujan_margins (shell : S5.Shell) (branch : Bool) :
    And (S5.MatrixMatches shell)
      (IntRatio.Lt (IntRatio.ofInt Int.zero)
        ((IntRatio.ofInt S5.i20).sub (S5.squaredEigenvalue shell branch))) :=
  And.intro (S5.matrices_match shell)
    (Eq.subst (IntRatio.Lt (IntRatio.ofInt Int.zero)) (S5.margin_eq_difference shell branch)
      (S5.margin_positive shell branch))

/-- The five degree-four eigenlines and the two basis-change compositions. -/
public theorem lps_degree_four_eigenbasis :
    And (∀ line : S5.DegreeFourLine,
      Eq (S5.degreeFourAction line.vector)
        (line.vector.scale (S5.scaledEigenvalue .degreeFour line.negativeBranch)))
      (∀ v : S5.DegreeFourVector,
        And (Eq (S5.fromEigenCoordinates (S5.doubledEigenCoordinates v)) (v.scale Int.two))
          (Eq (S5.doubledEigenCoordinates (S5.fromEigenCoordinates v)) (v.scale Int.two))) :=
  And.intro S5.degree_four_eigenline S5.degree_four_basis_change

end D5.S3.Quantum.AURICOmega.OmegaChebyshevHecke
