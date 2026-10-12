---
slug: wang-2026-hypercube-disorder-free-localization
bibkey: wang2026hypercubelocalization
doi: null
url: https://arxiv.org/abs/2609.07267v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/SpinCoupledEvenHypercubeGroverFixedPoint.result
---

# Disorder-free localization on even hypercubes

## Problem

Wang, arXiv:2609.07267v1, Conjecture 4.1 asks whether every even $d\ge4$ has disorder-free localization for the spin-coupled Grover walk with $\phi_\sigma=|\sigma|\pi/d$ and all spins $+1$. Its equivalent clause asks for a nonzero fixed point with nonuniform position distribution. The source identity and locators are in `Library/QuantumChannels/wang2026hypercubelocalization.md`.

## Motivation

`D5/S3/Quantum/Dynamics/SpinCoupledEvenHypercubeGroverFixedPoint.result` proves the equivalent fixed-point clause for every even $d\ge4$. Corollary 4.4 of the paper converts that clause to disorder-free localization. This implication is a paper argument; the quantum Bernoulli noise Hilbert-space framework and the general spectral criterion are not encoded in this module.

## Gap

The source gives explicit constructions in dimensions four and six, and numerical evidence at dimension eight. The quantified fixed-point clause is supplied by `result`. Odd dimensions, dimension two, and the structure of other eigenspaces remain outside this conclusion.

## Route

Put $d=2m$, $z=e^{-i\pi/d}$ and $c=1/(m(1+z))$. Pair coordinates as $(2j,2j+1)$ and set

$$f(\sigma)=\prod_{j<m}\left(1_{2j\in\sigma}-1_{2j+1\in\sigma}\right).$$

The vector is

$$u(\sigma,k)=\begin{cases}
cf(\sigma)&|\sigma|=m,\ k\in\sigma,\\
zcf(\sigma)&|\sigma|=m,\ k\notin\sigma,\\
z^{m+1}cf(\sigma\triangle\{k\})&|\sigma|=m-1,\ k\notin\sigma,\\
z^mcf(\sigma\triangle\{k\})&|\sigma|=m+1,\ k\in\sigma,\\
0&\text{otherwise}.
\end{cases}$$

The private lemmas `pair_cancel`, `neighbour_sum` and `f_support` give pair cancellation, zero neighbour sums and middle-layer support. `S_eq_f` and `edge_identity` establish the coin sum and edge recurrence. `fixed_point`, `u_nonzero` and `marginal_nonconstant` discharge the three conjuncts of `claim`; `result` assembles them. These are kernel-checked statements in the settling module.

## Falsifier

The exact conclusion would fail if an even $d\ge4$ had no nonzero fixed vector with unequal position weights for the specified operator. The delivered claim uses the predecessor $\tau\triangle\{k\}$ both in the phase and in every coin component, with coefficient $2/d$. No normalized-vector assumption or additional dimension restriction is imposed. Normalization of a nonzero vector preserves inequality of the position weights.

## Evidence

The public `result : claim` supplies the universal fixed-point statement. Its axiom closure is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$. Numerical checks below are independent cross-checks on the explicitly stated finite dimensions, not evidence for an unbounded quantifier. Source fidelity is the comparison to the reduced operator, Grover coin and equivalent clause of Conjecture 4.1.

## Triage

### What the settlement shows

- **Mechanism — proved in this module.** `pair_cancel` pairs opposite signs, and `neighbour_sum` proves zero neighbour sum at every vertex, including layers $m-1$ and $m+1$. `f_support` puts the support in layer $m$. `edge_identity` and `fixed_point` prove that the three-layer vector is fixed, using $z^{2m}=-1$ (`z_power`) and $m(1+z)c=1$ (`c_coefficient`). `u_nonzero` and `marginal_nonconstant` prove that it is nonzero and has nonconstant marginal. The coordinate pairing requires even $d$; no impossibility for odd $d$ follows from this requirement.
- **Layer masses — proved by the counting argument here, and computed for $d=4,6,8,10,12$.** There are $2^m$ middle transversals, each with $2m$ nonzero coin components. A lower-layer supported vertex chooses one empty pair and one coordinate in every other pair, hence there are $m2^{m-1}$ such vertices, each with two nonzero components. The upper layer has the same count, with one double pair. Every nonzero component has modulus $|c|$ because $|z|=1$ and the nonzero signs are $\pm1$. The layer squared norms are therefore $m2^m|c|^2$, $2m2^m|c|^2$ and $m2^m|c|^2$, giving normalized masses $1/4,1/2,1/4$. This counting argument is not a separate Lean theorem. The finite computation below checks those fractions to absolute tolerance $10^{-13}$.
- **The $d=8$ remark — computed.** The vector has 80 supported position vertices and every nonzero coin amplitude has modulus $|c|=0.1274488947760398$ (modulus error $2.78\times10^{-17}$). Rescaling by $1/c$ gives a sparse fixed vector with unit-modulus nonzero coin amplitudes; its position weights remain nonuniform. The exhaustive operator check has residual $3.7367087251761353\times10^{-17}$. This supplies an explicit construction addressing the source's remark that such a sparse vector had not been found. The support count and modulus reading here concern $d=8$; the universal fixed-point clause is proved separately by `result`.
- **Odd $d$ and $d=2$ — open.** The source suggests absence of disorder-free localization in these cases. A perfect coordinate pairing is unavailable for odd $d$, while the proof requires $m\ge2$. Neither case is settled here; they are follow-up candidates.
- **Other eigenvalues — proved by the paper argument for sufficiency.** The source's spectral criterion also allows other eigenspaces. Corollary 4.4 already makes this fixed point sufficient for disorder-free localization. The construction does not classify other eigenspaces or modify the source's spectral criterion. It extends the fixed-point conclusion of Propositions 4.5–4.6 to every even $d\ge4$; no conclusion about the remaining spectrum follows.

### Exhaustive operator check

Command: `python3 /tmp/op-wang/check.py`; exit 0. Requires Python and NumPy. SHA-256: `9dc70698e2767ca960e89377b77da396f0d7b80df73927e670e7b9cbfe2db001`.

| $d$ | maximum fixed-point residual | supported vertices | maximum normalized position weight |
| --- | --- | --- | --- |
| 4 | 8.886119947416683e-17 | 12 | 0.12500000000000003 |
| 6 | 9.71445146547012e-17 | 32 | 0.06249999999999998 |
| 8 | 3.7367087251761353e-17 | 80 | 0.03125 |
| 10 | 5.721958498152797e-17 | 192 | 0.015624999999999991 |
| 12 | 3.122502256758253e-17 | 448 | 0.007812500000000042 |

The minimum position weight is zero in all five cases. The exact source follows; it is sufficient to reproduce the computation without access to its host path.

```python
import itertools, cmath, numpy as np
def check(d):
    m=d//2; z=cmath.exp(-1j*cmath.pi/d); c=1/(m*(1+z))
    V=list(range(1<<d))
    pc=lambda s: bin(s).count('1')
    def f(s):
        r=1
        for j in range(m):
            a=(s>>(2*j))&1; b=(s>>(2*j+1))&1
            r*= (a-b)
        return r
    u=np.zeros((1<<d,d),dtype=complex)
    for s in V:
        w=pc(s)
        for k in range(d):
            t=s^(1<<k); ink=(s>>k)&1
            if w==m and ink: u[s,k]=c*f(s)
            elif w==m and not ink: u[s,k]=z*c*f(s)
            elif w==m-1 and not ink: u[s,k]=z**(m+1)*c*f(t)
            elif w==m+1 and ink: u[s,k]=z**m*c*f(t)
    # apply W: (Wu)(s,k)=e^{-i pi |t|/d}((2/d) sum_j u(t,j) - u(t,k)), t=s^{k}
    Wu=np.zeros_like(u)
    for s in V:
        for k in range(d):
            t=s^(1<<k)
            Wu[s,k]=cmath.exp(-1j*cmath.pi*pc(t)/d)*((2/d)*u[t].sum()-u[t,k])
    res=np.abs(Wu-u).max(); nrm=np.linalg.norm(u)
    probs=(np.abs(u)**2).sum(axis=1)/nrm**2
    return res, nrm, probs.max(), probs.min(), (probs>1e-15).sum()
for d in [4,6,8,10,12]:
    print(d, check(d))
```

### Layer and modulus check

Command: `python3 /tmp/op-wang/triage.py`; exit 0. SHA-256: `ed3a0bcb6888ea37967a51544baca4674009db1fc105cdf2d3e42502d9aead02`. The tested scope is exactly $d=4,6,8,10,12$; all three layer fractions differ from $1/4,1/2,1/4$ by less than $2.4\times10^{-15}$, and the largest amplitude-modulus error is $5.56\times10^{-17}$. The exact source follows.

```python
import cmath, json, numpy as np
for d in (4, 6, 8, 10, 12):
    m = d // 2
    z = cmath.exp(-1j * cmath.pi / d)
    c = 1 / (m * (1 + z))
    def sign(s):
        r = 1
        for j in range(m):
            r *= ((s >> (2*j)) & 1) - ((s >> (2*j+1)) & 1)
        return r
    u = np.zeros((1 << d, d), dtype=complex)
    for s in range(1 << d):
        w = s.bit_count()
        for k in range(d):
            t, inside = s ^ (1 << k), (s >> k) & 1
            if w == m:
                u[s, k] = c * sign(s) * (1 if inside else z)
            elif w == m-1 and not inside:
                u[s, k] = z**(m+1) * c * sign(t)
            elif w == m+1 and inside:
                u[s, k] = z**m * c * sign(t)
    weights = np.sum(np.abs(u)**2, axis=1)
    layers = [sum(weights[s] for s in range(1 << d)
                  if s.bit_count() == w) / sum(weights)
              for w in (m-1, m, m+1)]
    supported = int(np.count_nonzero(weights > 1e-15))
    modulus_error = float(np.max(np.abs(np.abs(u[np.abs(u)>1e-15])-abs(c))))
    assert np.allclose(layers, [0.25, 0.5, 0.25], rtol=0, atol=1e-13)
    assert supported == (m+1)*2**m
    assert modulus_error < 1e-14
    print(json.dumps(dict(d=d, layers=layers, supported=supported,
                         abs_c=abs(c), modulus_error=modulus_error)))
```

## ASSUMED-UNVERIFIED

The preregistration's literature readings found no earlier settlement in their searched scope; global absence of prior work is not established. The source-to-DFL implication uses the paper's Corollary 4.4 and is not separately kernel-formalized. The layer-mass counting argument is mathematical prose, while the finite numerical checks cover only the five listed even dimensions. Odd dimensions, dimension two and the other eigenspaces remain open here. Information-escape registration is paused under CLAUDE.md §3.9.
