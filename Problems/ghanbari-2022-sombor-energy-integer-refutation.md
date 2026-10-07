---
slug: ghanbari-2022-sombor-energy-integer-refutation
bibkey: ghanbari2022somborenergy
doi: 10.1007/s40314-022-01957-5
url: https://arxiv.org/abs/2108.08552v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/SomborEnergyIntegerRefutation.result
---

# Ghanbari's integer Sombor energy conjecture

## Problem

N. Ghanbari, *On the Sombor characteristic polynomial and Sombor energy of a graph*,
Computational and Applied Mathematics 41 (2022), article 242, Conjecture 3.8:

> There is no graph with integer-valued Sombor energy.

The paper studies finite simple graphs. For a graph $G$, the Sombor matrix has entry
$\sqrt{d_i^2+d_j^2}$ on an adjacent pair and zero otherwise, and the Sombor energy is the
sum of the absolute values of its eigenvalues.

## Motivation

The frozen declaration
`D5/S3/Combinatorics/Graph/SomborEnergyIntegerRefutation.result`
refutes the universal conjecture with three copies of $C_4$ sharing one vertex. The witness is
connected, bipartite, has ten vertices and twelve edges, and has Sombor energy $48$.

## Gap

Preregistration issue #13388 records the source quotation, the finite-simple-graph scope, the
fully quantified Lean claim, the literature search, and the expected $C_4$ bouquet witness.
The paper asks either for a proof of Conjecture 3.8 or a graph with integer-valued Sombor energy.
The delivered result supplies the latter. The recorded searches are bounded and do not establish
worldwide novelty or publication priority.

## Route

Represent the graph on $\operatorname{Fin} 10$ by three four-cycles
$0-1-2-3-0$, $0-4-5-6-0$, and
$0-7-8-9-0$. Vertex $0$ has degree six and every other vertex has degree two,
so the six edges incident with $0$ have weight $\sqrt{40}$ and the other six edges have weight
$\sqrt{8}$. The Lean proof writes an explicit matrix $P$, proves $P^\mathsf{T}P$ is diagonal, constructs
its inverse $Q$, and proves the similarity identity with diagonal spectrum
$(16,-16,4,-4,4,-4,0,0,0,0)$. The Hermitian characteristic-polynomial theorem then identifies
the eigenvalue multiset, and the absolute-value sum is $48$.

## Falsifier

A failure of the finite matrix identities, the characteristic-polynomial factorisation, or the
energy calculation would falsify the delivered witness. A graph with a different integer energy
would be a further witness but is not needed for this refutation.

## Evidence

The canonical source is
`D5/S3/Combinatorics/Graph/SomborEnergyIntegerRefutation.lean`.
Its public surface is `somborMatrix`, `claim`, and `result`; the private proof contains the graph,
degree calculation, matrix certificate, characteristic polynomial, and energy calculation. The
Scribe mirror describes all three declarations and attaches `OpenProblemResolutionClaim(Refuted)`
with this dossier's slug. The axiom closure of every public declaration is contained in
`{propext, Classical.choice, Quot.sound}`.

The cited library note is
`Library/GraphInvariants/ghanbari2022somborenergy.md`; its DOI and arXiv locator are verified.

## Triage

Tier 1 external named conjecture, preregistered in #13388. Resolution **Refuted** by the frozen
`result`. The module is `proof_shape: bind-only`, with `escape_witness: none` and
`admission_basis: open-problem-resolution (#13388; Refuted)`. Its utility is a certified instance
refuting the module's `claim`. Information-escape registration is paused under CLAUDE.md section 3.9.

### What the settlement shows

- **Proved in this module:** the bouquet of three copies of $C_4$ has Sombor spectrum
  $(16,-16,4,-4,4,-4,0,0,0,0)$ and energy $48$, so Ghanbari's universal Conjecture 3.8 is
  false. The failure mechanism is an explicit connected bipartite simple graph with a degree-six
  shared vertex; the source's finite-simple-graph hypotheses all hold.
- **Computed for $1\leq k\leq 10$:** for $B_k$, the bouquet of $k$ four-cycles sharing one
  vertex, the script below constructs the weighted Sombor matrix, factors its characteristic
  polynomial, and computes the exact energy. The energies are
  $8\sqrt{2}$, $8+8\sqrt{6}$, $48$, $24+8\sqrt{35}$, $32+8\sqrt{66}$,
  $40+32\sqrt{7}$, $48+32\sqrt{11}$, $56+24\sqrt{29}$, $64+8\sqrt{370}$, and
  $72+8\sqrt{506}$, respectively. Within this tested scope, $k=3$ is the only integral value.
  Any uniform statement for all $k$ is open.
  Command: `python3 /tmp/sombor_bouquet_scan.py`; exit code 0.
  Script SHA-256: `92f13a47c7e63f4e91e9573a4ef9ccb98591a3cd5008a38e7be04a95343efc89`.
  The exact script source is:

  ```python
  import sympy as sp

  x = sp.symbols('x')

  def bouquet_matrix(k):
      n = 3*k + 1
      M = sp.zeros(n)
      a = sp.sqrt((2*k)**2 + 2**2)
      b = sp.sqrt(2**2 + 2**2)
      for t in range(k):
          u, v, w = 1 + 3*t, 2 + 3*t, 3 + 3*t
          for i, j, q in ((0, u, a), (u, v, b), (v, w, b), (w, 0, a)):
              M[i, j] = q
              M[j, i] = q
      return M

  for k in range(1, 11):
      M = bouquet_matrix(k)
      poly = sp.factor(M.charpoly(x).as_expr(), extension=[sp.sqrt(2), sp.sqrt(k*k+1)])
      vals = M.eigenvals()
      energy = sp.simplify(sum(mult * abs(sp.N(val, 50)) for val, mult in vals.items()))
      exact_terms = []
      for val, mult in vals.items():
          if val.is_real and val.is_positive:
              exact_terms.append(mult * val)
      exact = sp.simplify(2 * sum(exact_terms))
      print(f"k={k} vertices={3*k+1} charpoly={poly} energy={exact} numeric={sp.N(exact, 18)}")
  ```
- **Open:** the separate regular-graph conjecture discussed by Ramane–Kitturmath
  (DOI: [10.1016/j.exco.2023.100115](https://doi.org/10.1016/j.exco.2023.100115)) is not the
  universal Conjecture 3.8 settled here and receives no claim in this module.
- **Open:** the minimum vertex count of a finite simple graph with integer Sombor energy is not
  established by this delivery. The computed $B_k$ table is only the tested range $1\leq k\leq 10$.
- **Surviving source boundary:** the source's characteristic-polynomial and energy calculations for
  graph classes other than the refuted universal claim are unaffected; only the universal
  no-integer-energy conjecture is refuted.

## ASSUMED-UNVERIFIED

The literature search and the absence of an earlier published counterexample are bounded by the
checks recorded in #13388. No claim is made about worldwide priority. A uniform classification of
all $B_k$, the regular-graph conjecture, and the minimum-vertex problem remain open here.
