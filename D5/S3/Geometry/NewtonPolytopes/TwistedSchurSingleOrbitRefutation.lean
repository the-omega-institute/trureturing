/- GID: D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation
   generality: I
   mirror-B: D5/B/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.claim; result=D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.result; claim=D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.claim
   digest: A twisted Schur Newton polytope need not be a single signed-permutation orbit. -/

/- Source: Carles Marín, arXiv:2608.18302v2, §1.1 and §8, Conjecture 8.1, p. 49.
   admission_basis: open-problem-resolution (#26737; Refuted)
   result proof_shape: bind-only; escape_witness: none.
   Direct frozen dependencies (result, with same-delivery helpers expanded):
   GID: D5/S3/Arith/InterlaceFan/Cyclotomic.zeta
   statement_id: sha256:e8aa7909f91dd6e576ae9c0ca5fc87df493a148eddedc7a3d512d1874731ac68
   The literal exponential is retained in alphabetPower; literal_zeta connects it to
   the existing Cyclotomic.zeta used in the proofs, without adding a root definition.
   The public result is the designated refutation result (`basis=refutes`) and is exempt
   from four-slot escape registration (CLAUDE.md §3.9).
   All private proof declarations are bind-only consumed helpers; none is an escape witness.
-/

import D5.S3.Arith.InterlaceFan.Cyclotomic

namespace D5.S3.Geometry.NewtonPolytopes.TwistedSchurSingleOrbitRefutation


def N (t r : ℕ) : ℕ := t + 2 * r

def sourceIndex {t r : ℕ} : (Fin t ⊕ (Fin r ⊕ Fin r)) → ℕ
  | .inl a => a.val
  | .inr (.inl k) => t + 2 * k.val
  | .inr (.inr k) => t + 2 * k.val + 1

def delta (t r : ℕ) (j : (Fin t ⊕ (Fin r ⊕ Fin r))) : ℤ :=
  (N t r : ℤ) - 1 - (sourceIndex j : ℤ)

def NormalizedBeta (t r : ℕ) (beta : (Fin t ⊕ (Fin r ⊕ Fin r)) → ℤ) : Prop :=
  (∀ i j : (Fin t ⊕ (Fin r ⊕ Fin r)), sourceIndex i < sourceIndex j → beta j < beta i) ∧
  (∀ j : (Fin t ⊕ (Fin r ⊕ Fin r)), sourceIndex j + 1 = N t r → beta j = 0)

/-- The powers x_i^b, with reciprocal variables represented by negative exponents. -/
noncomputable def alphabetPower (t r : ℕ) (b : ℤ) : (Fin t ⊕ (Fin r ⊕ Fin r)) → (AddMonoidAlgebra ℂ (Fin r → ℤ))
  | .inl a => AddMonoidAlgebra.single 0 (Complex.exp (((2 * Real.pi / (t : ℝ)) : ℂ) * Complex.I) ^ ((a.val : ℤ) * b))
  | .inr (.inl k) => AddMonoidAlgebra.single (Pi.single k b) 1
  | .inr (.inr k) => AddMonoidAlgebra.single (Pi.single k (-b)) 1

noncomputable def numerator (t r : ℕ) (beta : (Fin t ⊕ (Fin r ⊕ Fin r)) → ℤ) : (AddMonoidAlgebra ℂ (Fin r → ℤ)) :=
  Matrix.det (fun i j : (Fin t ⊕ (Fin r ⊕ Fin r)) => alphabetPower t r (beta j) i)

noncomputable def denominator (t r : ℕ) : (AddMonoidAlgebra ℂ (Fin r → ℤ)) :=
  Matrix.det (fun i j : (Fin t ⊕ (Fin r ⊕ Fin r)) => alphabetPower t r (delta t r j) i)

/-- The nonzero-denominator alternant quotient in the Laurent polynomial ring. -/
noncomputable def IsPhi (t r : ℕ) (beta : (Fin t ⊕ (Fin r ⊕ Fin r)) → ℤ) (f : (AddMonoidAlgebra ℂ (Fin r → ℤ))) : Prop :=
  denominator t r ≠ 0 ∧ f * denominator t r = numerator t r beta

noncomputable def newtonPolytope {r : ℕ} (f : (AddMonoidAlgebra ℂ (Fin r → ℤ))) : Set (Fin r → ℝ) :=
  convexHull ℝ ((fun a : (Fin r → ℤ) => fun k => (a k : ℝ)) ''
    (f.coeff.support : Set ((Fin r → ℤ))))

/-- W(C_r) acts by all signed coordinate permutations. -/
def signedOrbit {r : ℕ} (mu : (Fin r → ℤ)) : Set (Fin r → ℝ) :=
  {x | ∃ (sigma : Equiv.Perm (Fin r)) (epsilon : Fin r → ℤ),
    (∀ k : Fin r, epsilon k = 1 ∨ epsilon k = -1) ∧
    ∀ k : Fin r, x k = (epsilon k : ℝ) * (mu (sigma k) : ℝ)}

def orbitPolytope {r : ℕ} (mu : (Fin r → ℤ)) : Set (Fin r → ℝ) :=
  convexHull ℝ (signedOrbit mu)

def Dominant {r : ℕ} (mu : (Fin r → ℤ)) : Prop :=
  (∀ k : Fin r, 0 ≤ mu k) ∧ Antitone mu

/-- Conjecture 8.1 in its explicitly stated equivalent Newton-polytope form. -/
def claim : Prop :=
  ∀ (t r : ℕ), 1 ≤ t → 1 ≤ r →
    ∀ beta : (Fin t ⊕ (Fin r ⊕ Fin r)) → ℤ, NormalizedBeta t r beta →
      (∃ f : (AddMonoidAlgebra ℂ (Fin r → ℤ)), IsPhi t r beta f) ∧
      (∀ f : (AddMonoidAlgebra ℂ (Fin r → ℤ)), IsPhi t r beta f → f ≠ 0 →
        ∃ mu : (Fin r → ℤ), Dominant mu ∧ newtonPolytope f = orbitPolytope mu)

end D5.S3.Geometry.NewtonPolytopes.TwistedSchurSingleOrbitRefutation

set_option maxHeartbeats 30000000
set_option maxRecDepth 20000
namespace D5.S3.Geometry.NewtonPolytopes.TwistedSchurSingleOrbitRefutation
open D5.S3.Arith.InterlaceFan.Cyclotomic
noncomputable section


private def basePolynomial : (AddMonoidAlgebra ℂ (Fin 2 → ℤ)) :=
    (1 : ℤ) • (AddMonoidAlgebra.single (![(-4),0] : Fin 2 → ℤ) (1 : ℂ)) +
    (1 : ℤ) • (AddMonoidAlgebra.single (![(-3),(-3)] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![(-3),(-1)] : Fin 2 → ℤ) (1 : ℂ)) +
    (1 : ℤ) • (AddMonoidAlgebra.single (![(-3),0] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![(-3),1] : Fin 2 → ℤ) (1 : ℂ)) +
    (1 : ℤ) • (AddMonoidAlgebra.single (![(-3),3] : Fin 2 → ℤ) (1 : ℂ)) +
    (3 : ℤ) • (AddMonoidAlgebra.single (![(-2),(-2)] : Fin 2 → ℤ) (1 : ℂ)) +
    (4 : ℤ) • (AddMonoidAlgebra.single (![(-2),0] : Fin 2 → ℤ) (1 : ℂ)) +
    (3 : ℤ) • (AddMonoidAlgebra.single (![(-2),2] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![(-1),(-3)] : Fin 2 → ℤ) (1 : ℂ)) +
    (6 : ℤ) • (AddMonoidAlgebra.single (![(-1),(-1)] : Fin 2 → ℤ) (1 : ℂ)) +
    (6 : ℤ) • (AddMonoidAlgebra.single (![(-1),1] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![(-1),3] : Fin 2 → ℤ) (1 : ℂ)) +
    (1 : ℤ) • (AddMonoidAlgebra.single (![0,(-4)] : Fin 2 → ℤ) (1 : ℂ)) +
    (1 : ℤ) • (AddMonoidAlgebra.single (![0,(-3)] : Fin 2 → ℤ) (1 : ℂ)) +
    (4 : ℤ) • (AddMonoidAlgebra.single (![0,(-2)] : Fin 2 → ℤ) (1 : ℂ)) +
    (10 : ℤ) • (AddMonoidAlgebra.single (![0,0] : Fin 2 → ℤ) (1 : ℂ)) +
    (4 : ℤ) • (AddMonoidAlgebra.single (![0,2] : Fin 2 → ℤ) (1 : ℂ)) +
    (1 : ℤ) • (AddMonoidAlgebra.single (![0,3] : Fin 2 → ℤ) (1 : ℂ)) +
    (1 : ℤ) • (AddMonoidAlgebra.single (![0,4] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![1,(-3)] : Fin 2 → ℤ) (1 : ℂ)) +
    (6 : ℤ) • (AddMonoidAlgebra.single (![1,(-1)] : Fin 2 → ℤ) (1 : ℂ)) +
    (6 : ℤ) • (AddMonoidAlgebra.single (![1,1] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![1,3] : Fin 2 → ℤ) (1 : ℂ)) +
    (3 : ℤ) • (AddMonoidAlgebra.single (![2,(-2)] : Fin 2 → ℤ) (1 : ℂ)) +
    (4 : ℤ) • (AddMonoidAlgebra.single (![2,0] : Fin 2 → ℤ) (1 : ℂ)) +
    (3 : ℤ) • (AddMonoidAlgebra.single (![2,2] : Fin 2 → ℤ) (1 : ℂ)) +
    (1 : ℤ) • (AddMonoidAlgebra.single (![3,(-3)] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![3,(-1)] : Fin 2 → ℤ) (1 : ℂ)) +
    (1 : ℤ) • (AddMonoidAlgebra.single (![3,0] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![3,1] : Fin 2 → ℤ) (1 : ℂ)) +
    (1 : ℤ) • (AddMonoidAlgebra.single (![3,3] : Fin 2 → ℤ) (1 : ℂ)) +
    (1 : ℤ) • (AddMonoidAlgebra.single (![4,0] : Fin 2 → ℤ) (1 : ℂ))

private def baseSupport : Finset ((Fin 2 → ℤ)) :=
    {(![(-4),0] : Fin 2 → ℤ), (![(-3),(-3)] : Fin 2 → ℤ), (![(-3),(-1)] : Fin 2 → ℤ), (![(-3),0] : Fin 2 → ℤ), (![(-3),1] : Fin 2 → ℤ), (![(-3),3] : Fin 2 → ℤ), (![(-2),(-2)] : Fin 2 → ℤ), (![(-2),0] : Fin 2 → ℤ), (![(-2),2] : Fin 2 → ℤ), (![(-1),(-3)] : Fin 2 → ℤ), (![(-1),(-1)] : Fin 2 → ℤ), (![(-1),1] : Fin 2 → ℤ), (![(-1),3] : Fin 2 → ℤ), (![0,(-4)] : Fin 2 → ℤ), (![0,(-3)] : Fin 2 → ℤ), (![0,(-2)] : Fin 2 → ℤ), (![0,0] : Fin 2 → ℤ), (![0,2] : Fin 2 → ℤ), (![0,3] : Fin 2 → ℤ), (![0,4] : Fin 2 → ℤ), (![1,(-3)] : Fin 2 → ℤ), (![1,(-1)] : Fin 2 → ℤ), (![1,1] : Fin 2 → ℤ), (![1,3] : Fin 2 → ℤ), (![2,(-2)] : Fin 2 → ℤ), (![2,0] : Fin 2 → ℤ), (![2,2] : Fin 2 → ℤ), (![3,(-3)] : Fin 2 → ℤ), (![3,(-1)] : Fin 2 → ℤ), (![3,0] : Fin 2 → ℤ), (![3,1] : Fin 2 → ℤ), (![3,3] : Fin 2 → ℤ), (![4,0] : Fin 2 → ℤ)}

private theorem mm (a b c d : ℤ) : (AddMonoidAlgebra.single (![a,b] : Fin 2 → ℤ) (1 : ℂ)) * (AddMonoidAlgebra.single (![c,d] : Fin 2 → ℤ) (1 : ℂ)) = (AddMonoidAlgebra.single (![(a+c),(b+d)] : Fin 2 → ℤ) (1 : ℂ)) := by
  simp [AddMonoidAlgebra.single_mul_single]

private def mb : Matrix (Fin 7) (Fin 7) ((AddMonoidAlgebra ℂ (Fin 2 → ℤ))) :=
  !![0,1,0,0,0,0,1;
     1,0,0,1,0,1,0;
     0,0,1,0,1,0,0;
     (AddMonoidAlgebra.single (![10,0] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![9,0] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![5,0] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![4,0] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![2,0] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![1,0] : Fin 2 → ℤ) (1 : ℂ)),1;
     (AddMonoidAlgebra.single (![(-10),0] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![(-9),0] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![(-5),0] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![(-4),0] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![(-2),0] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![(-1),0] : Fin 2 → ℤ) (1 : ℂ)),1;
     (AddMonoidAlgebra.single (![0,10] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![0,9] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![0,5] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![0,4] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![0,2] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![0,1] : Fin 2 → ℤ) (1 : ℂ)),1;
     (AddMonoidAlgebra.single (![0,(-10)] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![0,(-9)] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![0,(-5)] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![0,(-4)] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![0,(-2)] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![0,(-1)] : Fin 2 → ℤ) (1 : ℂ)),1]

private def md : Matrix (Fin 7) (Fin 7) ((AddMonoidAlgebra ℂ (Fin 2 → ℤ))) :=
  !![1,0,0,1,0,0,1;
     0,0,1,0,0,1,0;
     0,1,0,0,1,0,0;
     (AddMonoidAlgebra.single (![6,0] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![5,0] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![4,0] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![3,0] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![2,0] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![1,0] : Fin 2 → ℤ) (1 : ℂ)),1;
     (AddMonoidAlgebra.single (![(-6),0] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![(-5),0] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![(-4),0] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![(-3),0] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![(-2),0] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![(-1),0] : Fin 2 → ℤ) (1 : ℂ)),1;
     (AddMonoidAlgebra.single (![0,6] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![0,5] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![0,4] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![0,3] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![0,2] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![0,1] : Fin 2 → ℤ) (1 : ℂ)),1;
     (AddMonoidAlgebra.single (![0,(-6)] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![0,(-5)] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![0,(-4)] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![0,(-3)] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![0,(-2)] : Fin 2 → ℤ) (1 : ℂ)),(AddMonoidAlgebra.single (![0,(-1)] : Fin 2 → ℤ) (1 : ℂ)),1]
private def nb : (AddMonoidAlgebra ℂ (Fin 2 → ℤ)) :=
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-10),(-4)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-10),(-2)] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![(-10),(-1)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![(-10),1] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-10),2] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-10),4] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-9),(-7)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-9),(-5)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-9),(-4)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-9),(-2)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-9),2] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-9),4] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-9),5] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-9),7] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![(-8),(-8)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![(-8),(-5)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-8),(-4)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-8),(-2)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-8),2] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-8),4] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![(-8),5] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![(-8),8] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-7),(-9)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-7),(-6)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-7),(-3)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-7),3] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-7),6] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-7),9] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-6),(-7)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-6),(-5)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-6),(-4)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-6),(-2)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-6),2] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-6),4] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-6),5] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-6),7] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-5),(-9)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![(-5),(-8)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-5),(-6)] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![(-5),(-5)] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![(-5),(-4)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-5),(-3)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![(-5),(-1)] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![(-5),1] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-5),3] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![(-5),4] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![(-5),5] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-5),6] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![(-5),8] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-5),9] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-4),(-10)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-4),(-9)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-4),(-8)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-4),(-6)] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![(-4),(-5)] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![(-4),(-4)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-4),(-3)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-4),3] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![(-4),4] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![(-4),5] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-4),6] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-4),8] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-4),9] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-4),10] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-3),(-7)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-3),(-5)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-3),(-4)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-3),(-2)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-3),2] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-3),4] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-3),5] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-3),7] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-2),(-10)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-2),(-9)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-2),(-8)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-2),(-6)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-2),(-3)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![(-2),(-1)] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![(-2),1] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-2),3] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-2),6] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-2),8] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-2),9] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-2),10] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![(-1),(-10)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![(-1),(-5)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![(-1),(-2)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-6 : ℤ) • (AddMonoidAlgebra.single (![(-1),(-1)] : Fin 2 → ℤ) (1 : ℂ)) +
    (6 : ℤ) • (AddMonoidAlgebra.single (![(-1),1] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![(-1),2] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![(-1),5] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![(-1),10] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![1,(-10)] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![1,(-5)] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![1,(-2)] : Fin 2 → ℤ) (1 : ℂ)) +
    (6 : ℤ) • (AddMonoidAlgebra.single (![1,(-1)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-6 : ℤ) • (AddMonoidAlgebra.single (![1,1] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![1,2] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![1,5] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![1,10] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![2,(-10)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![2,(-9)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![2,(-8)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![2,(-6)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![2,(-3)] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![2,(-1)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![2,1] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![2,3] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![2,6] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![2,8] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![2,9] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![2,10] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![3,(-7)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![3,(-5)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![3,(-4)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![3,(-2)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![3,2] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![3,4] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![3,5] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![3,7] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![4,(-10)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![4,(-9)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![4,(-8)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![4,(-6)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![4,(-5)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![4,(-4)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![4,(-3)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![4,3] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![4,4] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![4,5] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![4,6] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![4,8] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![4,9] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![4,10] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![5,(-9)] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![5,(-8)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![5,(-6)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![5,(-5)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![5,(-4)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![5,(-3)] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![5,(-1)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![5,1] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![5,3] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![5,4] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![5,5] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![5,6] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![5,8] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![5,9] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![6,(-7)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![6,(-5)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![6,(-4)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![6,(-2)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![6,2] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![6,4] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![6,5] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![6,7] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![7,(-9)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![7,(-6)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![7,(-3)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![7,3] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![7,6] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![7,9] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![8,(-8)] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![8,(-5)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![8,(-4)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![8,(-2)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![8,2] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![8,4] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![8,5] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![8,8] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![9,(-7)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![9,(-5)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![9,(-4)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![9,(-2)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![9,2] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![9,4] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![9,5] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![9,7] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![10,(-4)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![10,(-2)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![10,(-1)] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![10,1] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![10,2] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![10,4] : Fin 2 → ℤ) (1 : ℂ))

private def nd : (AddMonoidAlgebra ℂ (Fin 2 → ℤ)) :=
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-6),(-4)] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-6),(-2)] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![(-6),(-1)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![(-6),1] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-6),2] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-6),4] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![(-5),(-5)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-4 : ℤ) • (AddMonoidAlgebra.single (![(-5),(-2)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![(-5),(-1)] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![(-5),1] : Fin 2 → ℤ) (1 : ℂ)) +
    (4 : ℤ) • (AddMonoidAlgebra.single (![(-5),2] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![(-5),5] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-4),(-6)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![(-4),(-4)] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![(-4),(-3)] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![(-4),(-2)] : Fin 2 → ℤ) (1 : ℂ)) +
    (4 : ℤ) • (AddMonoidAlgebra.single (![(-4),(-1)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-4 : ℤ) • (AddMonoidAlgebra.single (![(-4),1] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![(-4),2] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![(-4),3] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![(-4),4] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-4),6] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![(-3),(-4)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![(-3),(-2)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-4 : ℤ) • (AddMonoidAlgebra.single (![(-3),(-1)] : Fin 2 → ℤ) (1 : ℂ)) +
    (4 : ℤ) • (AddMonoidAlgebra.single (![(-3),1] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![(-3),2] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![(-3),4] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![(-2),(-6)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-4 : ℤ) • (AddMonoidAlgebra.single (![(-2),(-5)] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![(-2),(-4)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![(-2),(-3)] : Fin 2 → ℤ) (1 : ℂ)) +
    (6 : ℤ) • (AddMonoidAlgebra.single (![(-2),(-2)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-6 : ℤ) • (AddMonoidAlgebra.single (![(-2),2] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![(-2),3] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![(-2),4] : Fin 2 → ℤ) (1 : ℂ)) +
    (4 : ℤ) • (AddMonoidAlgebra.single (![(-2),5] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![(-2),6] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![(-1),(-6)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![(-1),(-5)] : Fin 2 → ℤ) (1 : ℂ)) +
    (4 : ℤ) • (AddMonoidAlgebra.single (![(-1),(-4)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-4 : ℤ) • (AddMonoidAlgebra.single (![(-1),(-3)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-6 : ℤ) • (AddMonoidAlgebra.single (![(-1),(-1)] : Fin 2 → ℤ) (1 : ℂ)) +
    (6 : ℤ) • (AddMonoidAlgebra.single (![(-1),1] : Fin 2 → ℤ) (1 : ℂ)) +
    (4 : ℤ) • (AddMonoidAlgebra.single (![(-1),3] : Fin 2 → ℤ) (1 : ℂ)) +
    (-4 : ℤ) • (AddMonoidAlgebra.single (![(-1),4] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![(-1),5] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![(-1),6] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![1,(-6)] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![1,(-5)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-4 : ℤ) • (AddMonoidAlgebra.single (![1,(-4)] : Fin 2 → ℤ) (1 : ℂ)) +
    (4 : ℤ) • (AddMonoidAlgebra.single (![1,(-3)] : Fin 2 → ℤ) (1 : ℂ)) +
    (6 : ℤ) • (AddMonoidAlgebra.single (![1,(-1)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-6 : ℤ) • (AddMonoidAlgebra.single (![1,1] : Fin 2 → ℤ) (1 : ℂ)) +
    (-4 : ℤ) • (AddMonoidAlgebra.single (![1,3] : Fin 2 → ℤ) (1 : ℂ)) +
    (4 : ℤ) • (AddMonoidAlgebra.single (![1,4] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![1,5] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![1,6] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![2,(-6)] : Fin 2 → ℤ) (1 : ℂ)) +
    (4 : ℤ) • (AddMonoidAlgebra.single (![2,(-5)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![2,(-4)] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![2,(-3)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-6 : ℤ) • (AddMonoidAlgebra.single (![2,(-2)] : Fin 2 → ℤ) (1 : ℂ)) +
    (6 : ℤ) • (AddMonoidAlgebra.single (![2,2] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![2,3] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![2,4] : Fin 2 → ℤ) (1 : ℂ)) +
    (-4 : ℤ) • (AddMonoidAlgebra.single (![2,5] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![2,6] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![3,(-4)] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![3,(-2)] : Fin 2 → ℤ) (1 : ℂ)) +
    (4 : ℤ) • (AddMonoidAlgebra.single (![3,(-1)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-4 : ℤ) • (AddMonoidAlgebra.single (![3,1] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![3,2] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![3,4] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![4,(-6)] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![4,(-4)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![4,(-3)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![4,(-2)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-4 : ℤ) • (AddMonoidAlgebra.single (![4,(-1)] : Fin 2 → ℤ) (1 : ℂ)) +
    (4 : ℤ) • (AddMonoidAlgebra.single (![4,1] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![4,2] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![4,3] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![4,4] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![4,6] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![5,(-5)] : Fin 2 → ℤ) (1 : ℂ)) +
    (4 : ℤ) • (AddMonoidAlgebra.single (![5,(-2)] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![5,(-1)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![5,1] : Fin 2 → ℤ) (1 : ℂ)) +
    (-4 : ℤ) • (AddMonoidAlgebra.single (![5,2] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![5,5] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![6,(-4)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![6,(-2)] : Fin 2 → ℤ) (1 : ℂ)) +
    (-2 : ℤ) • (AddMonoidAlgebra.single (![6,(-1)] : Fin 2 → ℤ) (1 : ℂ)) +
    (2 : ℤ) • (AddMonoidAlgebra.single (![6,1] : Fin 2 → ℤ) (1 : ℂ)) +
    (AddMonoidAlgebra.single (![6,2] : Fin 2 → ℤ) (1 : ℂ)) +
    (-1 : ℤ) • (AddMonoidAlgebra.single (![6,4] : Fin 2 → ℤ) (1 : ℂ))

private theorem nb_det : mb.det = nb := by
  unfold mb
  eval_det
  simp only [mm]
  norm_num only [Int.reduceAdd, Int.reduceMul, Int.reduceNeg]
  unfold nb
  abel

private theorem nd_det : md.det = nd := by
  unfold md
  eval_det
  simp only [mm]
  norm_num only [Int.reduceAdd, Int.reduceMul, Int.reduceNeg]
  unfold nd
  abel


private theorem base_product : basePolynomial * nd = nb := by
  unfold basePolynomial nd nb
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mm]
  norm_num only [Int.reduceAdd, Int.reduceMul, Int.reduceNeg]
  abel


private theorem literal_zeta (t : ℕ) :
    Complex.exp (((2 * Real.pi / (t : ℝ)) : ℂ) * Complex.I) = zeta t := by
  unfold zeta
  congr 1
  push_cast
  ring

private theorem zeta_cube : zeta 3 ^ 3 = 1 := by
  exact (Complex.isPrimitiveRoot_exp 3 (by decide)).pow_eq_one

private theorem pi_single_zero (b : ℤ) : Pi.single (0 : Fin 2) b = (![b,0] : Fin 2 → ℤ) := by
  exact List.ofFn_inj.mp rfl

private theorem pi_single_one (b : ℤ) : Pi.single (1 : Fin 2) b = (![0,b] : Fin 2 → ℤ) := by
  exact List.ofFn_inj.mp rfl

private def ix : Fin 7 ≃ (Fin 3 ⊕ (Fin 2 ⊕ Fin 2)) where
  toFun := ![.inl 0, .inl 1, .inl 2, .inr (.inl 0), .inr (.inr 0),
    .inr (.inl 1), .inr (.inr 1)]
  invFun j := ⟨sourceIndex j, by
    rcases j with a | (k | k)
    · fin_cases a <;> decide
    · fin_cases k <;> decide
    · fin_cases k <;> decide⟩
  left_inv := by decide
  right_inv := by decide

private def baseBeta : (Fin 3 ⊕ (Fin 2 ⊕ Fin 2)) → ℤ
  | .inl a => ![10,9,5] a
  | .inr (.inl k) => ![4,1] k
  | .inr (.inr k) => ![2,0] k

private theorem base_normalized : NormalizedBeta 3 2 baseBeta := by
  unfold NormalizedBeta
  decide


private def ma : Matrix (Fin 7) (Fin 7) ((AddMonoidAlgebra ℂ (Fin 2 → ℤ))) :=
  !![1,1,1,0,0,0,0;
     1,(AddMonoidAlgebra.single (0 : Fin 2 → ℤ) (zeta 3)),(AddMonoidAlgebra.single (0 : Fin 2 → ℤ) (zeta 3 ^ 2)),0,0,0,0;
     1,(AddMonoidAlgebra.single (0 : Fin 2 → ℤ) (zeta 3 ^ 2)),(AddMonoidAlgebra.single (0 : Fin 2 → ℤ) (zeta 3)),0,0,0,0;
     0,0,0,1,0,0,0;
     0,0,0,0,1,0,0;
     0,0,0,0,0,1,0;
     0,0,0,0,0,0,1]

private theorem matrix_mb :
    (fun i j : Fin 7 => alphabetPower 3 2 (baseBeta (ix j)) (ix i)) = ma * mb := by
  funext i j
  simp only [alphabetPower, literal_zeta]
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, ma, mb, ix,
      baseBeta, alphabetPower, pi_single_zero, pi_single_one, AddMonoidAlgebra.one_def]
  all_goals first | rfl | simp only [pow_eq_pow_mod 4 zeta_cube, pow_eq_pow_mod 5 zeta_cube, pow_eq_pow_mod 8 zeta_cube, pow_eq_pow_mod 9 zeta_cube, pow_eq_pow_mod 10 zeta_cube, pow_eq_pow_mod 18 zeta_cube, pow_eq_pow_mod 20 zeta_cube,
    Nat.reduceMod, pow_zero, pow_one]
  all_goals rfl


private theorem matrix_md :
    (fun i j : Fin 7 => alphabetPower 3 2 (delta 3 2 (ix j)) (ix i)) = ma * md := by
  funext i j
  simp only [alphabetPower, literal_zeta]
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, ma, md, ix,
      delta, N, sourceIndex, alphabetPower, pi_single_zero, pi_single_one, AddMonoidAlgebra.one_def]
  all_goals first | rfl | simp only [pow_eq_pow_mod 3 zeta_cube, pow_eq_pow_mod 4 zeta_cube, pow_eq_pow_mod 5 zeta_cube, pow_eq_pow_mod 6 zeta_cube, pow_eq_pow_mod 8 zeta_cube, pow_eq_pow_mod 10 zeta_cube, pow_eq_pow_mod 12 zeta_cube,
    Nat.reduceMod, pow_zero, pow_one]
  all_goals rfl


private theorem numerator_factor : numerator 3 2 baseBeta = ma.det * mb.det := by
  calc
    _ = Matrix.det (fun i j : Fin 7 => alphabetPower 3 2 (baseBeta (ix j)) (ix i)) :=
      (Matrix.det_reindex_self ix.symm
        (fun i j : (Fin 3 ⊕ (Fin 2 ⊕ Fin 2)) => alphabetPower 3 2 (baseBeta j) i)).symm
    _ = _ := by rw [matrix_mb, Matrix.det_mul]

private theorem denominator_factor : denominator 3 2 = ma.det * md.det := by
  calc
    _ = Matrix.det (fun i j : Fin 7 => alphabetPower 3 2 (delta 3 2 (ix j)) (ix i)) :=
      (Matrix.det_reindex_self ix.symm
        (fun i j : (Fin 3 ⊕ (Fin 2 ⊕ Fin 2)) => alphabetPower 3 2 (delta 3 2 j) i)).symm
    _ = _ := by rw [matrix_md, Matrix.det_mul]

private theorem zeta_square_ne : zeta 3 ^ 2 ≠ zeta 3 := by
  intro h
  have h21 : (2 : ℕ) = 1 :=
    (Complex.isPrimitiveRoot_exp 3 (by decide)).pow_inj
      (by decide) (by decide) (by simpa only [zeta, pow_one] using h)
  norm_num at h21

private theorem ma_det : ma.det = (AddMonoidAlgebra.single (0 : Fin 2 → ℤ) (3*(zeta 3 ^ 2-zeta 3))) := by
  let C : ℂ →+* (AddMonoidAlgebra ℂ (Fin 2 → ℤ)) := AddMonoidAlgebra.singleZeroRingHom
  have hc : C (zeta 3) ^ 3 = 1 := by
    rw [← map_pow, zeta_cube, map_one]
  change Matrix.det
    !![1,1,1,0,0,0,0;
       1,C (zeta 3),C (zeta 3 ^ 2),0,0,0,0;
       1,C (zeta 3 ^ 2),C (zeta 3),0,0,0,0;
       0,0,0,1,0,0,0;
       0,0,0,0,1,0,0;
       0,0,0,0,0,1,0;
       0,0,0,0,0,0,1] = C (3*(zeta 3 ^ 2-zeta 3))
  simp only [map_mul, map_sub, map_pow, map_ofNat]
  eval_det
  linear_combination -C (zeta 3) * hc


private theorem denominator_ne : denominator 3 2 ≠ 0 := by
  intro hz
  have h := congrArg (fun f : (AddMonoidAlgebra ℂ (Fin 2 → ℤ)) => f.coeff ((![6,4] : Fin 2 → ℤ))) hz
  rw [denominator_factor, ma_det, nd_det] at h
  change (AddMonoidAlgebra.single (0 : Fin 2 → ℤ) (3*(zeta 3 ^ 2-zeta 3)) * nd).coeff ((![6,4] : Fin 2 → ℤ)) = 0 at h
  rw [AddMonoidAlgebra.coeff_single_zero_mul] at h
  norm_num [nd, AddMonoidAlgebra.coeff_single, Finsupp.single_apply] at h
  exact zeta_square_ne (sub_eq_zero.mp h)

private theorem base_identity :
    basePolynomial * denominator 3 2 = numerator 3 2 baseBeta := by
  rw [denominator_factor, numerator_factor, nd_det, nb_det]
  rw [mul_left_comm basePolynomial, base_product]

private theorem base_isPhi : IsPhi 3 2 baseBeta basePolynomial :=
  ⟨denominator_ne, base_identity⟩

private theorem base_support : basePolynomial.coeff.support = baseSupport := by
  ext a
  simp only [Finsupp.mem_support_iff, baseSupport, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro ha
    by_contra h
    push Not at h
    simp_all [basePolynomial, AddMonoidAlgebra.coeff_single]
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals subst a; norm_num [basePolynomial, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

private theorem linear_hull_bound (S : Set (Fin 2 → ℝ)) (a b c : ℝ)
    (h : ∀ x ∈ S, a*x 0+b*x 1 ≤ c) :
    ∀ x ∈ convexHull ℝ S, a*x 0+b*x 1 ≤ c := by
  apply convexHull_min h
  apply convex_halfSpace_le (f := fun x : Fin 2 → ℝ => a*x 0+b*x 1)
  constructor
  · intro x y; simp only [Pi.add_apply]; ring
  · intro r x; simp only [Pi.smul_apply, smul_eq_mul]; ring

private theorem base_bound (a b c : ℝ)
    (h : ∀ x ∈ baseSupport, a*(x 0 : ℝ)+b*(x 1 : ℝ) ≤ c) :
    ∀ x ∈ newtonPolytope basePolynomial, a*x 0+b*x 1 ≤ c := by
  apply linear_hull_bound
  rintro _ ⟨x,hx,rfl⟩
  exact h x (by simpa [base_support] using hx)

private theorem base_bounds (x : Fin 2 → ℝ) (hx : x ∈ newtonPolytope basePolynomial) :
    x 0 ≤ 4 ∧ x 0+x 1 ≤ 6 ∧ 3*x 0+x 1 ≤ 12 := by
  have hb (a b c : ℝ)
      (h : ∀ y ∈ baseSupport, a*(y 0 : ℝ)+b*(y 1 : ℝ) ≤ c) :=
    base_bound a b c h x hx
  have h1 := hb 1 0 4 (by
    intro y hy
    simp only [baseSupport, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals subst y; norm_num)
  have h2 := hb 1 1 6 (by
    intro y hy
    simp only [baseSupport, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals subst y; norm_num)
  have h3 := hb 3 1 12 (by
    intro y hy
    simp only [baseSupport, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals subst y; norm_num)
  simpa using And.intro h1 (And.intro h2 h3)

private theorem base_vertices :
    (fun k => ((![4,0] : Fin 2 → ℤ) k : ℝ)) ∈ newtonPolytope basePolynomial ∧
    (fun k => ((![3,3] : Fin 2 → ℤ) k : ℝ)) ∈ newtonPolytope basePolynomial := by
  constructor
  all_goals apply subset_convexHull ℝ; refine ⟨_, ?_, rfl⟩
  · rw [base_support]; simp [baseSupport]
  · rw [base_support]; simp [baseSupport]

private theorem dominant_mem (mu : (Fin 2 → ℤ)) :
    (fun k => (mu k : ℝ)) ∈ orbitPolytope mu := by
  apply subset_convexHull ℝ
  exact ⟨Equiv.refl _, fun _ => 1, by simp, by simp⟩

private theorem orbit_bounds (mu : (Fin 2 → ℤ)) (hm : Dominant mu)
    (x : Fin 2 → ℝ) (hx : x ∈ orbitPolytope mu) :
    x 0 ≤ mu 0 ∧ x 0+x 1 ≤ (mu 0 : ℝ)+mu 1 := by
  have hb (y : Fin 2 → ℝ) (hy : y ∈ signedOrbit mu) :
      y 0 ≤ mu 0 ∧ y 0+y 1 ≤ (mu 0 : ℝ)+mu 1 := by
    obtain ⟨sigma,eps,he,hy⟩ := hy
    have he' (k : Fin 2) : y k ≤ (mu (sigma k) : ℝ) := by
      rw [hy k]
      rcases he k with h | h
      · simp [h]
      · simp only [h, Int.cast_neg, Int.cast_one, neg_one_mul]
        have hp : (0 : ℝ) ≤ mu (sigma k) := by exact_mod_cast hm.1 (sigma k)
        linarith
    have hmu : (mu (sigma 0) : ℝ) ≤ mu 0 := by
      exact_mod_cast hm.2 (Fin.zero_le (sigma 0))
    have hs : (mu (sigma 0) : ℝ)+mu (sigma 1) = (mu 0 : ℝ)+mu 1 := by
      simpa [Fin.sum_univ_two] using (Equiv.sum_comp sigma (fun k => (mu k : ℝ)))
    exact ⟨(he' 0).trans hmu, by linarith [he' 0, he' 1]⟩
  constructor
  · have h := linear_hull_bound (signedOrbit mu) 1 0 (mu 0) (by
      intro y hy; simpa using (hb y hy).1) x hx
    simpa using h
  · have h := linear_hull_bound (signedOrbit mu) 1 1 ((mu 0 : ℝ)+mu 1) (by
      intro y hy; simpa using (hb y hy).2) x hx
    simpa using h

private theorem base_not_orbit :
    ¬ ∃ mu : (Fin 2 → ℤ), Dominant mu ∧
      newtonPolytope basePolynomial = orbitPolytope mu := by
  rintro ⟨mu,hm,heq⟩
  have hmu := dominant_mem mu
  rw [← heq] at hmu
  obtain ⟨h4,h6,h12⟩ := base_bounds _ hmu
  obtain ⟨hv,hv'⟩ := base_vertices
  rw [heq] at hv hv'
  have h4' := (orbit_bounds mu hm _ hv).1
  have h6' := (orbit_bounds mu hm _ hv').2
  norm_num at h4' h6'
  linarith


private theorem base_nonzero : basePolynomial ≠ 0 := by
  intro hz
  have h := congrArg (fun f : (AddMonoidAlgebra ℂ (Fin 2 → ℤ)) => f.coeff ((![4,0] : Fin 2 → ℤ))) hz
  norm_num [basePolynomial, AddMonoidAlgebra.coeff_single, Finsupp.single_apply] at h

theorem result : ¬ claim := by
  intro hc
  exact base_not_orbit ((hc 3 2 (by decide) (by decide) baseBeta base_normalized).2
    basePolynomial base_isPhi base_nonzero)

end
end D5.S3.Geometry.NewtonPolytopes.TwistedSchurSingleOrbitRefutation
