---
slug: dutta-tushar-2026-wigner-distance-factored-deficit
bibkey: dutta2026wignerdistance
doi: 10.48550/arXiv.2603.20792
url: https://arxiv.org/abs/2603.20792v4
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Magic/QubitWignerDeficitFactorRefutation.result
---

# The positive-branch Wigner-distance deficit does not factor through the equatorial input

## Problem

S. Dutta and Tushar, *A Phase-Space Geometric Measure of Magic in Qubit Systems*, arXiv:2603.20792v4,
Section 5.4, Conjecture 5.5 (Factored deficit): "For equatorial magic states $\rho$ and qubit states
$\sigma$ with $s(\sigma)>0$: $\mathrm{deficit}(\rho,\sigma)=C(\rho)\cdot f(\sigma)$ for a universal function
$f\geq0$ of the Pauli invariants $(|r_x|,|r_y|,|r_z|)$ of $\sigma$, vanishing iff $s(\sigma)\leq0$." Here
$C$ is the $\ell_1$ distance of the Wootters Wigner function to the stabilizer Wigner polytope,
$s(\sigma)=\operatorname{sgn}(r_xr_yr_z)$ and $\mathrm{deficit}(\rho,\sigma)=(1+C(\rho))(1+C(\sigma))-1-C(\rho\otimes\sigma)$.
The verbatim statements are in [the literature note](../Library/QuantumStates/dutta2026wignerdistance.md).

Issue [#14651](https://github.com/the-omega-institute/trureturing/issues/14651) reads the factorization
clause: there is a function $f$ of $\sigma$ with $\mathrm{deficit}(\rho,\sigma)=C(\rho)f(\sigma)$ for every
density matrix $\rho$ with $\langle Z\rangle_\rho=0$ and $C(\rho)>0$ and every density matrix $\sigma$
with $r_xr_yr_z>0$. Any $f$ satisfying the conjecture satisfies this clause.

## Motivation

The paper's tetrahedral dichotomy makes $C$ multiplicative in the form $(1+C(\rho))(1+C(\sigma))-1$
when both Bloch products are nonpositive and strictly smaller otherwise. Conjecture 5.5 would reduce
the positive branch with an equatorial input to the single scalar $C(\rho)$ times a property of $\sigma$.

## Gap

The repository proves the paper's Conjectures 5.6 and 5.7 in
[the equatorial-multiplicativity dossier](dutta-tushar-2026-wigner-distance-equatorial-multiplicativity.md)
and lists the positive Bloch-product branch and its tensor deficit as open. Issue #14651 records the
literature check before any Lean: the paper reports numerical linearity in $C(\rho)$ on meridian slices
without a closed form; no citing work or same-author paper settles the conjecture;
`not-found-in-searched-scope`.

## Route

Take the pure states with Bloch vectors $\rho_a=(3/5,4/5,0)$, $\rho_b=(5/13,12/13,0)$ and
$\sigma=(1/9,4/9,8/9)$. Then $C(\rho_a)=1/5$, $C(\rho_b)=2/13$, $C(\sigma)=2/9$,
$C(\rho_a\otimes\sigma)=7/18$ and $C(\rho_b\otimes\sigma)=79/234$. The joint lower bounds come from the sign
vector $q=(1,1,-1,1,-1,-1,1,-1,1,-1,-1,-1,1,-1,-1,-1)$, which satisfies $q\cdot W_\tau\le1/2$ on all sixty
two-qubit stabilizer states; the upper bounds from explicit five-stabilizer mixtures. Hence
$\mathrm{deficit}(\rho_a,\sigma)=7/90$ and $\mathrm{deficit}(\rho_b,\sigma)=17/234$, and the factorization
would force $f(\sigma)=7/18$ and $f(\sigma)=17/36$.

## Falsifier

An error in one of the five exact distances, or a reading of "equatorial magic state" that excludes
the pure equatorial states $\rho_a$, $\rho_b$; the paper takes $\rho_T$ to be "any equatorial
single-qubit magic state".

## Evidence

The canonical source is `D5/S3/Quantum/Magic/QubitWignerDeficitFactorRefutation.lean`, with public
`deficit`, `claim` and `result : ¬ claim`, reusing the frozen `COne`, `CTwo`, `Stab`, `Wfree` and
`bloch` and the stabilizer classifications of `QubitWignerDistanceTensorRules`. The axiom closure of
`result` is exactly `propext`, `Classical.choice` and `Quot.sound`; there is no `sorry` or
`native_decide`.
The module statement is `sha256:b8affea68dafd1592007a09ae2baa1ac21aef4cdc342d199859bf92c5c67cd53`, the
`result` statement `sha256:91365f9f75ea041d52383f5e473f981790516e4fc97e91cc50db0be2275a2d55`, the `claim`
statement `sha256:1bcaf6bd6f18929078fb3ac566621827fa9e7f2a7eba82bcd8ce9c55c700af37` and the `deficit`
statement `sha256:a53413645512fd72b59fcf37ea231816e7ca5065abd1753e9b9e30a82efa82e8`. The Freeze event is
`sha256:063b84bdc809233ec015f70aa0d72454fd5786141ab7b9ff36b573bbba6e4076`; its project-level prerequisite is
the re-pinned node `sha256:e9ab5464f731a1fcb9115cf39f46e9a145304f9ea5f06b5ca6e292d0ff1af7f5` of
`D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules`.

## Triage

Tier 1 named conjecture of a 2026 paper, present in its latest version, preregistered in issue #14651
before any Lean. `theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | content | the dual bound $q\cdot W_\tau\le1/2$ and the two joint distances | open-problem-resolution |

The content is the new sign functional $q$ with its bound on the two-qubit stabilizer polytope and the
exact joint distances $7/18$ and $79/234$ it certifies with the attaining mixtures. The stabilizer
classifications and the weak-duality lower bound for the distance to a free set that it uses are the frozen
proofs of `QubitWignerDistanceTensorRules`, extracted there into public lemmas. The settlement is admitted as an external open-problem resolution.

Utility is `kind=certified-instance; basis=refutes` (the claim and its refutation). There is no
digestion atom.

### What the refutation shows

**Proved by `result`:** no function of $\sigma$ alone, with any further properties, factors the deficit
over all equatorial magic $\rho$: for one pure $\sigma$ with $r_xr_yr_z>0$, two pure equatorial $\rho$
give the ratios $7/18$ and $17/36$.

**Argued, not formalized (bounded numerics).**

- *Not a boundary effect.* Linear programming over the sixty stabilizer vertices, for $40$ random
  $\sigma$ with $r_x,r_y,r_z>0$ against four equatorial $\rho$, finds the ratio
  $\mathrm{deficit}/C(\rho)$ constant for some $\sigma$ and varying by up to $0.16$ for others, at
  latitudes $z=0.09$, $0.78$ and $0.96$. Where it is constant, the paper's meridian-slice linearity is
  consistent with these readings; the conjecture fails as a universal statement.
- *Mechanism (the certificates).* The optimal mixtures for $\rho_a\otimes\sigma$ and $\rho_b\otimes\sigma$
  use the same five stabilizer vertices: four product vertices and one entangled vertex stabilized by
  $XY$ and $YZ$, with weight $2/45$ and $4/117$ respectively. Product mixtures alone give only the upper
  bound $(1+C(\rho))(1+C(\sigma))-1$; the entangled vertex lowers it by an amount that is not
  proportional to $C(\rho)$.

**Open.** For which $\sigma$ with $r_xr_yr_z>0$ the ratio is independent of the equatorial $\rho$, and a
closed form for the deficit on that set.

## ASSUMED-UNVERIFIED

The literature search and the exact certificate files of #14651 are seat-reported inputs that the module
recomputes in Lean. MathDB returned HTTP 403 and Semantic Scholar was rate-limited. The bounded check
does not establish exhaustive worldwide novelty, priority, or the absence of an independent refutation.
