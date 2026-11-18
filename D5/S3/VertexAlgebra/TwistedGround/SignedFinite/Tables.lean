/- GID: D5/S3/VertexAlgebra/TwistedGround/SignedFinite/Tables
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/SignedFinite/Tables
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal finite signed Gaussian coefficient tables. -/
import D5.S3.VertexAlgebra.TwistedGround.SignedFinite.Source
import D5.S3.VertexAlgebra.TwistedGround.SignedFinite.JInverse
import D5.S3.VertexAlgebra.TwistedGround.SignedFinite.Polynomial
import D5.S3.VertexAlgebra.TwistedGround.SignedFinite.Convolution
import D5.S3.VertexAlgebra.TwistedGround.Signed.JSpatial

noncomputable section
open scoped BigOperators
namespace D5.S3.VertexAlgebra.TwistedGround.SignedFinite
open OriginalGaussianFiniteCandidateModes (a h h2 k)

/-- The literal product of the finite signed source coefficients. -/
def d (e f : Bool) (r : ℂ) (p q : ℕ) : ℂ := m e p r * m f q r

def jNumerator (e f : Bool) (r : ℂ) : Poly := fun i j =>
  if e = f then
    let c := if e then 1 else A r
    let b := if e then A r else 1
    match i.val,j.val with
    | 1,0 | 0,1 => c
    | 2,0 | 0,2 => -b
    | 1,1 => -2*c
    | 2,1 | 1,2 => b
    | _,_ => 0
  else
    match i.val,j.val with
    | 0,0 | 2,2 => -1
    | 1,0 | 2,1 => if e then A r else 1
    | 0,1 | 1,2 => if e then 1 else A r
    | 1,1 => -2*A r
    | _,_ => 0

def rhoTable (same : Bool) : ℕ → ℕ → ℂ :=
  if same then fun p q => atom 1 0 1 p q + atom 0 1 1 p q
  else fun p q => -atom 0 0 1 p q - atom 1 1 1 p q

def jS (e f : Bool) (r : ℂ) (p q : ℕ) : ℂ :=
  mulPoly (jNumerator e f r) (d e f r) p q - rhoTable (e == f) p q

/-- Only finite sums, finite binomial polynomials and the actual period correction occur. -/
def jSigned (e f : Bool) (p q : ℕ) (r : ℂ) : ℂ :=
  (OriginalGaussianExternalSignedCandidate.Qconstant e f r - k r) * d e f r p q +
    jInverse (e == f) (jS e f r) p q

def tConstant (e f : Bool) (r : ℂ) : ℂ := if e || f then 1 else A r
def tAlpha (e f : Bool) (r : ℂ) : ℂ := if e && !f then A r else 1
def tBeta (e f : Bool) (r : ℂ) : ℂ := if !e && f then A r else 1
def tDelta (e f : Bool) (r : ℂ) : ℂ := if e && f then A r else 1

def ePolynomial (e f : Bool) (r : ℂ) : Poly := fun i j =>
  match i.val,j.val with
  | 0,0 => tConstant e f r
  | 1,0 => -tAlpha e f r
  | 0,1 => -tBeta e f r
  | 1,1 => tDelta e f r
  | _,_ => 0

def nPolynomial (e f : Bool) (r : ℂ) : Poly := fun i j =>
  if e = f then
    match i.val,j.val with
    | 0,0 => if e then 1 else A r
    | 1,1 => if e then A r else 1
    | _,_ => 0
  else
    match i.val,j.val with
    | 1,0 => -(if e then A r else 1)
    | 0,1 => -(if e then 1 else A r)
    | _,_ => 0

/-- Finite denominator inverses; transformed h parameters have no norm restriction. -/
def H (square : Bool) (e f : Bool) (r : ℂ) (p q : ℕ) : ℂ :=
  let c := tConstant e f r
  let α := tAlpha e f r
  let β := tBeta e f r
  let δ := tDelta e f r
  c⁻¹ ^ (if square then 2 else 1) * (α/c)^p * (β/c)^q *
    (if square then h2 p q ((α*β-c*δ)/(α*β)) else h p q ((α*β-c*δ)/(α*β)))

/-- E*N*d*r/2 plus the literal r^2*uv*d, with guarded shifts. -/
def tU (e f : Bool) (r : ℂ) (p q : ℕ) : ℂ :=
  r/2 * mulPoly (ePolynomial e f r) (mulPoly (nPolynomial e f r) (d e f r)) p q +
    r^2 * shift 1 1 (d e f r) p q

def tSigned (e f : Bool) (p q : ℕ) (r : ℂ) : ℂ :=
  conv (H true e f r) (tU e f r) p q - k r * d e f r p q

theorem eval_jNumerator (e f : Bool) (u v r : ℂ) :
    evalPoly (jNumerator e f r) u v = OriginalGaussianExternalSignedCandidate.jN e f u v r := by
  cases e <;> cases f <;>
    norm_num [evalPoly, jNumerator, Fin.sum_univ_succ, A,
      OriginalGaussianExternalSignedCandidate.jN, OriginalGaussianExternalSignedCandidate.h,
      OriginalGaussianExternalAnalyticCandidate.b] <;> ring

theorem eval_ePolynomial (e f : Bool) (u v r : ℂ) :
    evalPoly (ePolynomial e f r) u v = OriginalGaussianExternalSignedCandidate.E e f u v r := by
  cases e <;> cases f <;>
    norm_num [evalPoly, ePolynomial, Fin.sum_univ_succ, A, tConstant, tAlpha, tBeta, tDelta,
      OriginalGaussianExternalSignedCandidate.E, OriginalGaussianExternalSignedCandidate.K,
      OriginalGaussianExternalAnalyticCandidate.b] <;> ring

theorem eval_nPolynomial (e f : Bool) (u v r : ℂ) :
    evalPoly (nPolynomial e f r) u v = OriginalGaussianExternalSignedCandidate.N e f u v r := by
  cases e <;> cases f <;>
    norm_num [evalPoly, nPolynomial, Fin.sum_univ_succ, A,
      OriginalGaussianExternalSignedCandidate.N] <;> ring

end D5.S3.VertexAlgebra.TwistedGround.SignedFinite
