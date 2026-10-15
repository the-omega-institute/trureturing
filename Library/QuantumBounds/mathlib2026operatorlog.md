---
bibkey: mathlib2026operatorlog
authors: Mathlib contributors
year: 2026
title: Operator logarithms through the continuous functional calculus
doi: null
url: https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog
claim: Real CFC logarithms are continuous on self-adjoint invertible operators and operator monotone on strictly positive operators.
strata_touched:
  - D5/S3/Quantum/Analysis/TraceClass/LogRegularization
  - D5/S3/Quantum/Analysis/TraceClass/SpectralEnergy
  - D5/S3/Quantum/Analysis/TraceClass/KernelEnergy
  - D5/S3/Quantum/Analysis/TraceClass/OrderedEnergy
license: Apache-2.0
triage: anchor
---

# Operator logarithms and trace regularization

## Verified locator

https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog

## Suppliers

The pinned Mathlib revision is `db584cd6d46c92f209a44c0f1c829460d327499d`.
The primary source declarations are
[`CFC.log_le_log`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog/Order.lean#L96)
and
[`CFC.continuousOn_log`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog/Basic.lean#L179).
The former uses Loewner order without requiring the two arguments to commute.
The latter is restricted to the self-adjoint invertible locus.

For a positive contraction T and epsilon greater than zero, T + epsilon I is
strictly positive. Thus log(1 + epsilon) I minus log(T + epsilon I) is a
bounded positive operator, continuous in T's operator norm. The trace-class
Banach inclusion is continuous from trace norm to operator norm, and the
actual observable trace pairing is continuous. Together these give continuity
of every regularized trace energy in the trace norm of T. Positive trace
pairing transfers the noncommutative order inequality to these energies.

The supremum over epsilon_n = 1/(n+1), after applying ENNReal.ofReal, is lower
semicontinuous. This auxiliary operator-defined supremum does not by itself
supply a spectral representation, its singular kernel interpretation, scaling,
or an entropy identity. No novelty is claimed for operator logarithm
monotonicity, spectral entropy, or the adopted analytic trace-class suppliers.


## Eigenvectors, parameter order and scaling

`ContinuousMap.induction_on_of_compact` in
`Mathlib/Topology/ContinuousMap/StoneWeierstrass.lean` supplies density induction
for continuous real functions on the compact spectrum. The closed equality
locus for action on an actual eigenvector contains constants, the coordinate
function, sums and products. This proves the operator CFC action formula
without a full eigenbasis. A nonzero eigenvector supplies actual spectrum
membership through the bounded-operator and linear-endomorphism spectra;
the zero vector is handled separately.

For spectral x in [0,1] and 0<a<=b, cross multiplication gives
(1+b)/(x+b)<=(1+a)/(x+a). Scalar logarithm monotonicity and `cfc_le_iff`
therefore compare the actual B_b(T) and B_a(T). The increasing inverse-natural
grid permits `ENNReal.iSup_add_iSup_of_monotone` to lift finite nonnegative
trace linearity to the auxiliary supremum, including zero weights and
infinite values. This assertion does not imply a countable decomposition.

For 0<w<=1, the actual shifted operator T+(epsilon/w)I is strictly positive.
The supplied `CFC.log_smul'` applies there and yields
B_epsilon(wT)=B_(epsilon/w)(T)+log((1+epsilon)/(w+epsilon))I.
The positive grid w/(n+1) is cofinal at zero, and its scalar correction
increases to -log w. The same auxiliary supremum consequently scales by
adding Re Tr(rho) times -log w in ENNReal. No unshifted singular logarithm
or inverse is used in this derivation.

These are formal compositions of attributed standard CFC, Stone-Weierstrass,
trace pairing and monotone-supremum suppliers, with no claim of mathematical
priority for a spectral theorem or an entropy-continuity conjecture.


## Singular spectral energy

`TraceClass/Spectral.exists_nonneg_trace_spectral_data` supplies the actual full
basis of every positive trace-class operator. Its arbitrary full index includes
all zero eigenspaces. The analytic trace-class summability and basis-independent
trace are attributed to Tom Ole Diem's Apache-2.0 Physlib, as detailed in
`Library/QuantumBounds/diem2026traceclass.md`; no supplier proof is duplicated.

`SpectralEnergy` defines ell(0)=infinity and ell(t)=ofReal(-log t) for nonzero t,
and the actual nonnegative series of rho's basis diagonals times ell(s(i)).
The genuine trace-class product B_e(T)rho has a summable unconditional diagonal.
CFC eigenvector action evaluates it by the scalar regularized logarithm.
Scalar monotone convergence, including zero and one, and arbitrary-index
nonnegative sum/supremum interchange identify this series with the SAME
regularizedSupremum. Choosing the full native basis defines spectralEnergy;
the actual operator identity proves its basis independence.

The separate entropy series is sum of ofReal(-s(i) log s(i)), with zero term at
s(i)=0. The actual eigenvector equation identifies it with self energy. Positive
trace-one rho satisfies rho<=I. If 0<w<=1 and w rho<=tau, noncommuting order,
reference scaling and the trace mass one give
E_tau(rho)<=S(rho)+ofReal(-log w). In particular, finite actual entropy gives
finite dominated cross energy. Nonnegative two-term first-slot linearity
includes zero coefficients and infinite energies; no countable first-slot
identity is inferred from it. The energy is lower semicontinuous in the
reference's genuine trace-norm topology.

`KernelEnergy` uses the actual bounded orthogonal projection onto ker T. Its
trace pairing with rho equals the unconditional sum of the zero-fiber diagonals.
Positive kernel mass forces infinite energy. Finite energy annihilates every
zero eigenvector under rho, since its positive diagonal is the squared norm of
the action of sqrt(rho). Full basis density then gives rho kernelProjection(T)=0
and ker T<=ker rho. Support inclusion alone is not asserted to imply finite energy.

## Ordered increments

For an actually strictly positive A and c>=0, scalar logarithm and genuine
single-operator CFC prove
log(A+cI)-log(A)=log(I+c Ring.inverse(A)).
The suppliers are `cfc_comp'`, `cfc_ringInverse_id`,
`CStarAlgebra.ringInverse_le_ringInverse`, and `CFC.log_le_log` in the pinned
Mathlib revision. This is a composition of established functional-calculus and
order results, with no claim of new logarithm or spectral theory.

For 0<=P<=Q and 0<a<=b, actual inverse order applied to the a-shifts and the
single-operator formula with c=b-a show R_b<=R_a, where
R_e=log(Q+eI)-log(P+eI)>=0. No commutativity between P and Q is assumed.
The nonnegative trace-pairing supremum F_(P,Q) is lower semicontinuous in rho's
trace norm. The bounded identity B_e(P)=R_e+B_e(Q) and synchronized monotone
suprema prove E_P(rho)=F_(P,Q)(rho)+E_Q(rho) globally in ENNReal.
Both energies may be infinite. For P=Q, F is exactly zero even in that case;
no unrestricted subtraction is used.

These results supply singular operator energy and its ordered decomposition.
They do not prove the original Shirokov local entropy-center construction,
one common continuous reference energy or the full densely defined
self-adjoint all-temperature Hamiltonian. The stronger complementary Orlicz
premises do not replace the original finite continuous entropy hypothesis.
