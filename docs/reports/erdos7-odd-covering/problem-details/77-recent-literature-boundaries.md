# Recent covering-system results and the remaining odd-cover bridge

This note records the 2024--2026 primary sources checked against the
unrestricted Erdős--Selfridge assertion

\[
  \text{no finite cover of }\mathbb Z\text{ has pairwise distinct odd
  moduli greater than }1.
\]

The relevant project interface is stronger than a numerical necessary
condition.  A global repair must preserve the original labels and phases,
use one common CRT source, cover the entire deleted liability, and strictly
decrease the EB1 lexicographic cost.  In the notation of report
[76](76-global-repair-literature-audit.md), this is (G1)--(G2).  The sources
below are reused at the level of their stated theorems; none supplies that
whole-cover implication.

## Results that sharpen finite or restricted ranges

* **Harrington--Klein--Lowrance--Trifonov,**
  [arXiv:2605.18644](https://arxiv.org/abs/2605.18644), Theorems 1.9 and
  1.12.  For a divisor palette with LCM \(2^a3^b5^c\), Theorem 1.9 gives
  an inclusion--exclusion density upper bound, and Theorem 1.12 proves that
  any distinct cover whose every prime divisor is among \(2,3,5\) has least
  modulus at most \(9\).  The hypotheses are finite and have restricted
  prime support.  In the all-odd subcase with support contained in
  \(\{3,5\}\), the full divisor palette has reciprocal mass
  \[
    \sum_{d\mid 3^b5^c,\ d>1}\frac1d
      < \frac{3}{2}\frac{5}{4}-1=\frac78,
   \]
  so that subcase is excluded by the elementary density bound.  This does
  not address odd moduli with unrestricted prime support; the paper itself
  asks whether the LCM restriction in Theorem 1.9 can be removed.

* **Zhang--Zhang,** [arXiv:2607.19029](https://arxiv.org/abs/2607.19029),
  proves \(L_{\min}(7)=10080\) for arbitrary distinct covering systems with
  least modulus \(7\).  The construction and the finite exclusions use
  even moduli (the displayed construction includes \(8\)), and the proof
  does not impose oddness.  It is useful as a finite LCM/filtering pattern,
  but it neither excludes an all-odd system nor yields a phase-preserving
  replacement.

* **Gyarmati,** [arXiv:2606.05251](https://arxiv.org/abs/2606.05251), gives
  an elementary boundedness argument for the second smallest modulus.  It
  assumes an existing bound \(C_1\) for the smallest modulus and uses the
  spread replacement
  \[
    a_1\pmod {m_1}\ \rightsquigarrow
    \{a_1+b_sm_1\pmod {m_1T_s}\}_s.
  \]
  Thus it bounds the scale of \(m_2\) in a general distinct cover.  The move
  increases the selected family and does not give an EB1 strict descent; it
  also does not establish a common odd, phase-preserving replacement for an
  arbitrary hypothetical odd cover.  A bound on the first two moduli leaves
  the number of classes, the LCM, and the remaining prime support unbounded.

* **Filaseta--Kalogirou,** [arXiv:2407.15280](https://arxiv.org/abs/2407.15280),
  gives a uniform positive reciprocal excess for finite distinct covers with
  minimum modulus greater than (4), and their stated Δ-extension applies
  this bound to the all-odd specialization (including a possible modulus
  (3)).  The proof also yields an actual bounded intersecting pair.  The
  exact transfer boundary to the
  project's private-fibre flow is already recorded in
  [843](../profile-notes/arithmetic/800-849/843-filaseta-excess-owner-flow-bridge-audit.md):
  whole-cover overlap mass lies on the multiplicity-at-least-two stratum,
  whereas the required repair consumes source-preserving private fibres.
  No theorem in that paper transports the former to the latter.

* **Mian--Siddique,** [arXiv:2607.25628](https://arxiv.org/abs/2607.25628),
  supplies the checked finite exclusion
  \(\operatorname{lcm}(D)>10000\) for every finite distinct odd cover.  The
  exact Lean theorem and its first unexcluded odd abundant candidates are
  already recorded in
  [`Library/Arith/mian2026lcm10000.md`](../../../../Library/Arith/mian2026lcm10000.md).
  This is a reusable lower boundary for finite search, not an unrestricted
  proof; the candidates beginning at \(10395\) remain outside that
  certificate.

* **Cummings--Filaseta--Trifonov** (Acta Math. Hungar. 175 (2025)) bounds
  the least modulus in squarefree distinct covers by \(118\), while the
  BBMST squarefree result already rules out the all-odd squarefree case.
  Neither result controls arbitrary prime powers, so it does not close the
  unrestricted odd problem.

* **Dalton--Jones,**
  [arXiv:2506.11359](https://arxiv.org/abs/2506.11359), rules out a distinct
  cover whose entire modulus set lies in \([n,10n]\) for any \(n\ge3\).
  A hypothetical odd cover may span arbitrarily many scales, so this interval
  obstruction is not a global repair or a noncoverage theorem.

* **Klein,** [arXiv:2508.18062](https://arxiv.org/abs/2508.18062)
  (the paper *On a conjecture of Krukenberg and a problem of Dalton and
  Trifonov*) proves the sharp general-cover bounds \(M\ge108\) and
  \(\operatorname{lcm}\ge1440\) at minimum modulus \(5\), and
  \(\operatorname{lcm}\ge5040\) at minimum modulus \(6\).  These are
  unrestricted-phase but not odd-only statements and leave all larger LCMs
  open.  They are finite LCM data, not a source-preserving replacement.

## Results that change the model rather than solve it

* **Bispels--Cohen--Harrington--Lowrance--Pontes--Schaumann--Wong,**
  [arXiv:2507.16135](https://arxiv.org/abs/2507.16135), studies systems in
  which one odd modulus may be repeated.  Repetition is outside the target's
  injective-modulus quantifier, so its constructions cannot be counterexamples
  and its exclusions cannot be imported as a distinct-label theorem.

* **Adenwalla** [arXiv:2501.15170](https://arxiv.org/abs/2501.15170) and
  **Jia--Li--Liu** [arXiv:2504.09579](https://arxiv.org/abs/2504.09579)
  characterize residue assignments on the *complete divisor palette* under
  the pairwise-coprime-overlap condition.  An odd covering uses an arbitrary
  subset of divisors and need not satisfy that overlap condition.  The
  hierarchical CRT construction therefore does not produce (G1)--(G2).

* **Cremona--Koymans,** [arXiv:2601.03212](https://arxiv.org/abs/2601.03212),
  gives a lattice-cover divisor cut.  Under the natural homogeneous lift of
  a congruence cover, its additional prime-support term is exactly paid by
  the added boundary lattices; the source- and phase-preserving projection
  recovers Simpson's cut and no strict repair.  The cancellation computation
  is recorded in report [76](76-global-repair-literature-audit.md).

* **McNew--Setty,** [arXiv:2507.23041](https://arxiv.org/abs/2507.23041),
  studies covering numbers and their density.  The project's citation note
  records literal finite counterexamples to two printed v2 bounds and keeps
  only the separately verified branches.  The density of covering numbers is
  not a theorem that every odd non-deficient LCM is a covering number or that
  every cover admits an EB1 repair.

* **Hashimoto,** [arXiv:2603.26043](https://arxiv.org/abs/2603.26043), proves
  finiteness for disjoint systems with one repeated largest modulus.  Both
  disjointness and the repeated-label allowance change the target interface,
  so this result does not decide the injective, arbitrary-phase problem.

## Remaining bridge

The checked sources now give several independent finite floors, restricted
prime-support exclusions, reciprocal excess, and a kernel-replayed period
bridge.  They still do not supply either of the two required global moves:

\[
\begin{aligned}
&\text{whole cover + actual phases + distinct odd labels}\\
&\qquad\Longrightarrow\text{ a strict, fresh, source-preserving EB1 repair};
\end{aligned}
\]

or a phase-sensitive density inequality that is forced for every such cover.
The unresolved quantifiers include arbitrary prime support, arbitrary prime
power heights, all original residue phases, and one common CRT realization.
Consequently, the unrestricted Erdős--Selfridge problem remains open in this
audit. The useful next use of these papers is compositional: consume their
finite certificates and restricted cuts, then prove the missing joint
transport rather than re-deriving any of the cited bounds.
