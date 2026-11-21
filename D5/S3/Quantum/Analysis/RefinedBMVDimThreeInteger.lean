/- GID: D5/S3/Quantum/Analysis/RefinedBMVDimThreeInteger
   generality: G
   mirror-B: none(waiver:internal-sparse-polynomial-representation)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact integer coefficient checks for the three-dimensional refined BMV bounds. -/

import Lean

/-! # Exact integer coefficients for the dimension-three refined BMV bounds -/

namespace RefinedBMV.DimThree

/-- Ordered triples of exponents of the first factor between the three second factors. -/
def gaps (p : Nat) : List (Nat × Nat × Nat) :=
  (List.range (p + 1)).flatMap fun i =>
    (List.range (p + 1 - i)).map fun j => (i, j, p - i - j)

/-- The unnormalized deficit of the mean over compositions at three cube roots. -/
def defect {R : Type u} [Add R] [Sub R] [Mul R] [Pow R Nat] [NatCast R] [Zero R]
    (p : Nat) (a b c : R) : R :=
  ((gaps p).map fun g => (a ^ 3) ^ g.1 * (b ^ 3) ^ g.2.1 * (c ^ 3) ^ g.2.2).sum -
    (↑(gaps p).length : R) * (a * b * c) ^ p

/-- A quartic certificate for the sum of square roots in Hägele's pairing. -/
def criterion {R : Type u} [Add R] [Sub R] [Mul R] [Pow R Nat] [NatCast R] [Zero R]
    (p : Nat) (a b c : R) : R :=
  let x := defect p a a c
  let y := defect p b b c
  let z := defect p a b c
  let q := defect p b b a * defect p c c a + defect p a a b * defect p c c b
  let w := x * y
  (↑(4 : Nat) : R) * q * w - (z ^ 2 - q - w) ^ 2

namespace Certificate

structure Term where
  exponents : Nat × Nat × Nat
  coefficient : Int

def Term.mul (a b : Term) : Term :=
  ⟨(a.exponents.1 + b.exponents.1, a.exponents.2.1 + b.exponents.2.1,
    a.exponents.2.2 + b.exponents.2.2), a.coefficient * b.coefficient⟩

def Term.neg (a : Term) : Term :=
  ⟨a.exponents, -a.coefficient⟩

structure Sparse where
  terms : List Term

def Term.orderKey (a : Term) : Nat :=
  128 * (128 * a.exponents.1 + a.exponents.2.1) + a.exponents.2.2

def mergeInsert (x : Term) (xs : List Term) (next : List Term → List Term) :
    (ys : List Term) → List Term
  | [] => x :: xs
  | y :: ys =>
    if x.exponents = y.exponents then
      ⟨x.exponents, x.coefficient + y.coefficient⟩ :: next ys
    else if x.orderKey ≤ y.orderKey then
      x :: next (y :: ys)
    else
      y :: mergeInsert x xs next ys

def mergeTerms : (xs ys : List Term) → List Term
  | [], ys => ys
  | x :: xs, ys => mergeInsert x xs (mergeTerms xs) ys

def mergePairs : List (List Term) → List (List Term)
  | xs :: ys :: rest => mergeTerms xs ys :: mergePairs rest
  | ps => ps

def mergeProducts : Nat → List (List Term) → List Term
  | 0, ps => ps.foldr mergeTerms []
  | _ + 1, [] => []
  | _ + 1, [p] => p
  | k + 1, ps@(_ :: _ :: _) => mergeProducts k (mergePairs ps)

def multiply (xs ys : List Term) : List Term :=
  mergeProducts 10 (xs.map fun x => ys.map (Term.mul x))

def Sparse.constant (n : Nat) : Sparse :=
  ⟨[⟨(0, 0, 0), n⟩]⟩

instance : Zero Sparse := ⟨⟨[]⟩⟩
instance : NatCast Sparse := ⟨Sparse.constant⟩
instance : Add Sparse := ⟨fun p q => ⟨mergeTerms p.terms q.terms⟩⟩
instance : Sub Sparse :=
  ⟨fun p q => ⟨mergeTerms p.terms (q.terms.map Term.neg)⟩⟩
instance : Mul Sparse := ⟨fun p q => ⟨multiply p.terms q.terms⟩⟩

def Sparse.power (p : Sparse) : Nat → Sparse
  | 0 => Sparse.constant 1
  | n + 1 => p.power n * p

instance : Pow Sparse Nat := ⟨Sparse.power⟩

def orderedPolynomial (p : Nat) : Sparse :=
  let s : Sparse := ⟨[⟨(1, 0, 0), 1⟩]⟩
  let t : Sparse := ⟨[⟨(0, 1, 0), 1⟩]⟩
  let u : Sparse := ⟨[⟨(0, 0, 1), 1⟩]⟩
  criterion p s (s + t) (s + t + u)

end Certificate

end RefinedBMV.DimThree
