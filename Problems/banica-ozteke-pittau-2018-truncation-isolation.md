---
slug: banica-ozteke-pittau-2018-truncation-isolation
bibkey: banicaoztekepittau2018isolated
doi: 10.1142/S1230161218500099
url: https://arxiv.org/abs/1706.00986v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.result
---

# Isolation of dense partial Fourier matrices

## Problem

T. Banica, D. Özteke and L. Pittau, *Isolated partial Hadamard matrices, and
related topics*, Open Systems & Information Dynamics 25 (2018),
DOI 10.1142/S1230161218500099, arXiv:1706.00986v2, Conjecture 1.14:

> There exists a constant ε>0 such that F_{S,p} is isolated, for any p prime, once S ⊂ Z_p satisfies |S| ≥ (1−ε)p.

The formal target is the analytic specialization of this conjecture: a positive
real ε must work for every prime p and every finite row set S in ZMod p. The
matrix has all p columns and entries exp(2 pi i s.val j.val / p). Isolation
quantifies over globally real analytic curves through the matrix which are
partial Hadamard near zero. A trivial curve has entries
H[s,j] exp(i (a[s,t]+b[j,t])) near zero, with arbitrary real row and column
phase functions and no regularity assumption. This enlarges the source's
Definition 1.3 trivial class, including its fixed-exponent curves by taking
linear phase functions. Source isolation implies encoded isolation, so the
encoded negation implies that the source conjecture is false.
Here `ContDiff ℝ ⊤` is the analytic order `ω` in the pinned Mathlib.

## Motivation

Deleting two Fourier rows at arbitrarily large prime moduli gives actual
nontrivial analytic deformations at densities tending to one.
`BanicaTruncationRefutation.result : ¬ claim` disproves every positive uniform
density margin. Analytic curves are smooth, so these counterexamples also
refute the source's smooth version, since the encoded trivial class contains
the source's trivial deformations.

## Gap

Density alone does not control isolation. Removing a vertex cuts each nonzero
step cycle into paths, making its incidence map surjective. Fourier inversion
then makes the orthogonality differential surjective, while deleting two rows
leaves more kernel directions than row-column phase parameters. Thus the
failure occurs even at a regular point of the actual phase equations; it is
not caused by a spurious kernel of a singular linearization.

The remaining boundary is the p-1 row case, where the dimension excess vanishes.
No isolation or nonisolation theorem for that case is supplied here.

## Route

For a nonzero a at prime modulus p, addition by a visits every vertex of ZMod p.
Choose a missing vertex of a proper row set and integrate arbitrary edge values
by cumulative sums along the cut circle. This constructs vertex potentials
with every prescribed difference, without assuming a right inverse.

Apply this construction at each nonzero Fourier frequency and use inverse DFT
to solve the linearized orthogonality equations. The reverse-pair conjugation
condition ensures that taking real parts preserves the prescribed differences.
For m rows, the resulting surjectivity gives

$$
\dim_{\mathbb R}\ker J=mp-m(m-1).
$$

The row-column phase space has dimension at most m+p. For m=p-2, the kernel
dimension is 3(p-2), exceeding this bound 2p-2 by p-4>0 for p at least five.
The analytic implicit-function theorem realizes an outside kernel direction
as a local level-set curve. A bounded analytic reparameterization makes the
curve global, retaining a positive multiple of the tangent. A purported trivial
representation forces equality of cross-products of the smooth phase
exponentials: row and column factors cancel. Differentiating that identity at
zero makes every tangent cross-difference vanish. Choosing a fixed row and
column then reconstructs additive row-column tangent parameters, a contradiction.
This differentiates only the constructed analytic phases, never the arbitrary
phase functions in the trivial representation. Both index sets are nonempty;
the row set has cardinality p-2 at least three.

## Falsifier

For every real ε>0, choose a prime p at least five with εp>2 and delete two rows.
The resulting strict row subset has cardinality p-2 and satisfies
(1-ε)p ≤ p-2. `two_row_truncation_not_isolated` proves nonisolation for every
such row set. Arbitrarily large primes therefore give a counterexample to
every proposed ε; `result` proves the closed negation of `claim`.

## Evidence

The four Lean modules under `D5/S3/Quantum/Tomography/Hadamard/` are
`BanicaCycleForestIncidence`, `BanicaLevelSetCurve`,
`BanicaTruncationJacobian`, and `BanicaTruncationRefutation`.
They provide the incidence construction, global analytic level-set curve,
actual phase derivative and surjectivity, and the final counterexample family.
The derivative comes from the exponential orthogonality equations themselves,
and residual zero is converted back to the full partial Hadamard condition.
The proof directly reuses Mathlib's implicit-function theorems, inverse DFT,
`AddChar.map_neg_eq_conj`, character orthogonality, and rank-nullity.
The corresponding four Blueprint Scribes describe these declarations; the
Refutation Scribe attributes Definition 1.1 to the source and identifies the
analytic specializations of its deformation and isolation definitions.

## Triage

- **Lean 已证:** `result` refutes the analytically specialized Conjecture 1.14.
  Its proof expands through the incidence and curve constructions, so both
  `result` and `two_row_truncation_not_isolated` have `proof_shape: content`.
  The named external-conjecture basis is `admission_basis: open-problem-resolution`,
  with supplied preregistration [#30041](https://github.com/the-omega-institute/trureturing/issues/30041).
  The explicit conjecture is Tier 1; independent literature status is bounded
  as stated in `ASSUMED-UNVERIFIED`.
- **Lean 已证:** every prime p at least five and every row set of cardinality
  p-2 admit a nontrivial analytic deformation. The construction uses a tangent
  outside the row-column phase space, not a nonlinear common-phase loophole.
- **Lean 已证:** the exact kernel dimension follows from surjectivity and
  rank-nullity; the proof needs only the upper bound m+p on row-column phases.
- **数学推导未形式化:** for nonempty row and column sets, the sharp row-column
  dimension is m+p-1. The parameter map has the one-dimensional kernel
  consisting of a constant row parameter and its negative column parameter.
  For m=p-2 this gives the sharper excess p-3; it is not needed by the Lean proof.
- **Lean 已证:** the outside tangent excludes representations by arbitrary
  row-column phase functions, including discontinuous ones: the proof
  differentiates the cross-product identity of the constructed analytic phases.
- **数学推导未形式化:** analyticity implies smoothness, so these analytic
  counterexamples also refute the source's smooth conjecture; source isolation
  implies encoded isolation because its trivial class is contained in ours.
- **数学推导未形式化:** the source's proposed isolation with p-2 rows for
  sufficiently large primes is false, since the counterexample family covers
  every prime p at least five. Consequences premised on Conjecture 1.14 cannot
  retain that premise. The source's evidence for isolation of F_{p-1,p} is
  unaffected by this family, which deletes two rows.
- **数学推导未形式化:** for m=p-1, the kernel and sharp row-column dimensions
  are both 2p-2. This dimension comparison alone proves neither isolation nor
  nonisolation.
- **未决:** 在行列相位平凡性（几何孤立性）下，F_{p−1,p} 的孤立性未决；
  源文给出该方向的证据。A replacement sufficient condition for isolation must
  exclude the two-row-deletion family; density alone cannot provide it.

## ASSUMED-UNVERIFIED

The source quotation, definition numbers and preregistration identity are
supplied bibliographic inputs. The linked Library note records that the source
text was not independently retrieved in the offline scope. Neither the contents
of #30041 nor subsequent literature were independently checked here; no worldwide
priority or exhaustive absence-of-prior-refutation claim follows.

The encoded triviality predicate includes nonlinear common phases such as
exp(i t^2): take a[s,t]=t^2 and b[j,t]=0. Arbitrary row-column phase functions
are already covered by the Lean nontriviality proof. The analytic-to-smooth
implication and the comparison with the source's trivial class are mathematical
deductions described in Triage, not separate Lean equivalence theorems. The supporting level-set
result assumes an analytic residual, verified for the actual phase equations;
it does not assert a theorem for an arbitrary merely smooth residual.
