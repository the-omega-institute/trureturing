---
slug: volkoff-2016-pair-tunneling-ansatz-ground-state-refutation
bibkey: volkoff2016pairtunnelling
doi: null
url: https://arxiv.org/abs/1610.05807v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/PairTunnelingAnsatzGroundStateRefutation.result
---

# Volkoff's exact-ground-state pair-tunnelling ansatz

## Problem

T. J. Volkoff, arXiv:1610.05807v1, Section V.A, Eq. (20), pp. 6–7, fixes even particle number and writes:

> We conjecture that for each N ≥ 4 there exists a value c_N for which |ω_+(c_N)⟩ or |ω_−(c_N)⟩ is the exact ground state.

The sector has basis $|N-k,k\rangle$, indexed by $k\in\operatorname{Fin}(N+1)$, and Hamiltonian
$H=a_0^{\dagger 2}a_1^2+a_1^{\dagger 2}a_0^2$.
With $M=N/2$ and real $c$, the unnormalized ansatz is the coefficient vector of
$(x^2+2icxy-y^2)^M\pm(x^2-2icxy-y^2)^M$, multiplied coordinatewise by
$\sqrt{(N-k)!k!}$. Normalization is irrelevant for a nonzero eigenvector.
An exact ground state has the least real eigenvalue among all nonzero eigenvectors in the full sector.
Issue #11667 preregisters this quantified reading and its refutation at $N=8$.

## Motivation

The frozen declaration `D5/S3/Quantum/Dynamics/PairTunnelingAnsatzGroundStateRefutation.result`
refutes the assertion that this one-parameter family contains a ground state at every even $N\ge4$.
It separates exact eigenstate representation from the paper's numerical high fidelity and metrological usefulness.

## Gap

Tier 1: an explicitly stated conjecture of the 2016 source, with the bounded literature check in #11667.
That check reports only arXiv v1, the four-mode follow-up arXiv:1901.00879 and the exact-solution paper
arXiv:1609.05581 without a settlement of this ansatz conjecture, and no relevant formal-conjectures
or repository hit. These are preregistration-reported readings, `not-found-in-searched-scope`;
they do not establish exhaustive worldwide novelty or priority. The APS cited-by coverage is incomplete.

## Route

The proof specializes the universal conjecture to $N=8$, expands the fourth powers, and uses
strictly positive factorial weights to conjugate matrix action to coefficient action.
The off-diagonal entries follow from two successive annihilations in one mode and two creations
in the other: $\sqrt{k(k-1)}\sqrt{(N-k+1)(N-k+2)}$; shifting $k$ by two gives
$\sqrt{(N-k-1)(N-k)(k+1)(k+2)}$. The adjoint supplies the reverse entry.

For the sum state, writing $t=c^2$, the eigen-equations at coordinates 0, 2 and 4 force
$e=-48t-8$, $10t^2-2t-1=0$ and $12t^3+38t^2-12t-3=0$.
Elimination forces $68t-26=0$, hence $t=13/34$, where the quadratic equals $-175/578$.
Thus the sum state is not an eigenvector for any real parameter.

For the difference state, $c=0$ is the zero vector. Otherwise its eigen-equations force
$e=-24t-18$ and $6t^2+4t-3=0$. With $t\ge0$ this implies $t<9/20$, hence $e>-144/5$.
The coefficient vector $(1,0,-4\sqrt{13},0,30,0,-4\sqrt{13},0,1)$, multiplied by the
factorial weights, is a nonzero eigenvector at $-8\sqrt{13}<-144/5$.
The proof also eliminates the even and odd three-term chains. Their annihilating polynomials are
$\lambda(\lambda^2-832)(\lambda^2-112)$ and $\lambda^4-904\lambda^2+63504$.
If $\lambda<-8\sqrt{13}$, then $\lambda^2>832$; both polynomials are nonzero,
forcing the two endpoint coordinates, and then all coordinates, to vanish.
Thus every real eigenvalue is at least $-8\sqrt{13}$, and the displayed eigenvector
attains this bound. The kernel-certified ground energy is exactly $-8\sqrt{13}$.
A ground-state ansatz must attain that energy, which the difference state cannot do.

## Falsifier

A mismatch between the polynomial coefficients, factorial weights, matrix entries or the
source's sector and sign conventions would invalidate source fidelity. The displayed formulas
bind all parameters, preserve the natural-to-real casts before each square root, and use the
full sector rather than a parity-restricted definition of ground state.

## Evidence

Canonical Lean source: `D5/S3/Quantum/Dynamics/PairTunnelingAnsatzGroundStateRefutation.lean`.
The authored public surface is exactly `ansatzFactor`, `ansatzPolynomial`, `omega`, `pairTunnel`,
`IsGroundState`, `claim` and the one theorem `result : ¬ claim`.
All polynomial identities, the universal real-eigenvalue lower bound and its attainment occur within
the proof of `result`. The bound is used to identify the energy that a ground-state ansatz must attain.
No authored private theorem, new axiom or `native_decide` is introduced.
Lean also generates `Nat.factorial.eq_def` and a private factorial splitter when unfolding factorial;
these are upstream equation auxiliaries rather than authored companion declarations.

The following independent SymPy computation constructs the same matrix, computes its spectrum,
and checks the surviving $N=4,6$ sum states. The ordering of eigenvalues uses numerical sorting;
the full spectrum list and the positive $N=4,6$ cases are computed readings.
The $N=8$ spectral minimum is independently proved within `result` by the lower bound and its attainment.

```sh
uv run --with sympy python - <<'PY'
import sympy as s
x,y,c=s.symbols('x y c',real=True)
for N,t in [(4,(s.sqrt(3)-1)/2),(6,s.sqrt(6)/6),(8,None)]:
 H=s.zeros(N+1)
 for k in range(N-1): H[k,k+2]=H[k+2,k]=s.sqrt((N-k-1)*(N-k)*(k+1)*(k+2))
 spectrum=sorted(H.eigenvals().items(),key=lambda q:float(q[0]))
 print('N=',N,'spectrum=',spectrum,'minimum=',spectrum[0][0])
 if t is not None:
  P=s.Poly((x*x+2*s.I*c*x*y-y*y)**(N//2)+(x*x-2*s.I*c*x*y-y*y)**(N//2),x,y)
  v=s.Matrix([s.sqrt(s.factorial(N-k)*s.factorial(k))*P.coeff_monomial(x**(N-k)*y**k) for k in range(N+1)]).subs(c,s.sqrt(t))
  residual=(H*v-spectrum[0][0]*v).applyfunc(s.simplify)
  assert residual==s.zeros(N+1,1) and v!=s.zeros(N+1,1)
  print('c^2=',t,'nonzero=True; ground_eigen_residual=0')
PY
```

Computed readings: for $N=4$, the minimum is $-4\sqrt3$ and the sum state at
$c^2=(\sqrt3-1)/2$ is nonzero with zero eigen-equation residual; for $N=6$, the minimum is
$-6-4\sqrt6$ and the sum state at $c^2=\sqrt6/6$ is nonzero with zero residual.
For $N=8$, the computed spectrum is
$\{0,\pm8\sqrt{13},\pm4\sqrt7,\pm(10+4\sqrt{22}),\pm(10-4\sqrt{22})\}$.
The minimum $-8\sqrt{13}$ is kernel-certified within `result`.

## Triage

`theorem`; resolution `Refuted`, under #11667. The settling theorem has
`proof_shape: bind-only`, `escape_witness: none`, and `admission_basis: open-problem-resolution`.
Utility is `certified-instance` with the explicit `refutes` edge from `result` to `claim`.
There is no atom or digestion coverage edge. Information-escape registration is paused under CLAUDE.md §3.9.

### What the settlement shows

- **Proved within `result`**: at $N=8$, the sum branch fails the eigen-equation itself,
  while the exact full-sector spectral minimum is $-8\sqrt{13}$ and a nonzero
  difference-branch eigenstate has strictly greater energy.
  Even particle number and an adjustable real parameter do not suffice for exact ground-state representation.
- **Computed with the Evidence command**: the specified $N=4,6$ sum states survive, and $N=8$
  is the first failing even sector within $4\le N\le8$. These positive cases are not new Lean results.
- **Open**: classification of all higher even sectors and a corrected exact-state ansatz with additional parameters.
- **Open boundary for the source's other results**: the universal exactness conjecture cannot justify
  exact ground-state identification for this family. The refutation does not decide the source's
  numerical fidelity, near-optimal QFI, asymptotic estimates, or independent results in other sections.

## ASSUMED-UNVERIFIED

The bounded literature search is not exhaustive. The supplied search-seat APS cited-by count
has incomplete interface coverage. Correspondence of the creation/annihilation action to the
finite matrix is explained from the source, without a separate formal Fock-space operator construction.
The full $N=8$ spectrum list and the positive $N=4,6$ cases are independent computed readings.
The $N=8$ spectral minimum is proved inside the one exported settling theorem,
whose public conclusion is the negation of the quantified source conjecture.
