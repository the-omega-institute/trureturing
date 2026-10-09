---
slug: dirr-helmke-kleinsteuber-schulte-herbrueggen-2008-block-shift
bibkey: dirr2008relative
doi: 10.1080/03081080701535898
url: https://arxiv.org/abs/math-ph/0702005v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/LocalPermutationBlockShiftRefutation.result
---

# Extended local permutations do not suffice for block-shift form

## Problem

G. Dirr, U. Helmke, M. Kleinsteuber and T. Schulte-Herbrüggen,
*Relative C-numerical ranges for applications in quantum control and quantum information*,
Linear and Multilinear Algebra 56 (2008), 27–51, arXiv:math-ph/0702005v1,
Conjecture 3.6, pp. 26–27:

> Every element of $E(t_{\mathrm{loc}})$ is similar to a block-shift matrix via an element of
> $\Pi^{\mathrm{ex}}_{\mathrm{loc}} := \Pi_{\mathrm{loc}}\cdot\Pi_{\mathrm{out}}$.

The definitions and source quotations are in
[the literature note](../Library/QuantumBounds/dirr2008relative.md).
Issue [#14776](https://github.com/the-omega-institute/trureturing/issues/14776)
fixes DHKS-1 and the literal Lean conventions. The universal claim ranges over every
$n\ge2$ and every complex matrix in the union of the nonzero root spaces of the local
diagonal torus. The tensor basis has its first factor as its most significant bit.

## Motivation

Conjecture 3.6 would strengthen unrestricted unitary block-shift similarity to the prescribed
product of signed local flips and adjacent signed swaps. The counterexample separates
these two transformation classes.

## Gap

The preregistration records the source and literature checks: the companion paper
math-ph/0701035, the classical unrestricted block-shift results of Li–Tsing, Tam and
Tam–Yang, and screened citing works do not supply similarity by the prescribed extended
local permutations. MathDB p/376871 records no solution in that reading.
The search conclusion is `not-found-in-searched-scope`; it is not a proof of exhaustive
absence of prior settlements.

## Route

For three qubits take $A=\sum_{j=0}^{2}|\bar e_j\rangle\langle e_j|$ and
$\Delta=i\sum_{k=0}^{2}Z_k$. The commutator is $[\Delta,A]=-2iA$, so
$A\in E(t_{\mathrm{loc}})$. Every prescribed conjugator has a nonvanishing monomial
support action $x\mapsto\pi(x)\oplus a$. Some supported row lies above its column
in Kronecker order. Contiguous block-shift form requires the opposite strict order.

## Falsifier

The refutation would fail if the source permitted an arbitrary basis permutation in the
block partition, or if a prescribed extended local permutation sent this $A$ to block-shift
form. Corollary 2.19 allows arbitrary unitaries; that different statement is compatible
with the counterexample.

## Evidence

The settling declaration is
`D5/S3/Quantum/Information/LocalPermutationBlockShiftRefutation.result : ¬ claim`.
The public definitions are the source's literal signed matrices, product set, torus,
root-space union and monotone block index. The module directly reuses the frozen
`StabilizerPairLocalUnitaryInequivalence.tensorOp`, `FiniteDimensional.qubitZ` and
`PositiveOneModeWilliamson.physicalJ2` in its elaborated definitions and proofs.
Its proof uses the private reciprocal monomial inverse construction, subgroup-closure
support invariant and support transport under conjugation. The axiom closure of every
public declaration is contained in {propext, Classical.choice, Quot.sound}.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

## Triage

Tier 1; resolution **Refuted**; `admission_basis: open-problem-resolution (#14776)`.
Utility is `kind=certified-instance; basis=refutes`: the fixed three-qubit root vector
is a certified instance contradicting the literal universal claim.

### What the settlement shows

1. **Mechanism — proved in the module.** `extended_support` and `affine_xor` show that
   every element of $\Pi^{\mathrm{ex}}_{\mathrm{loc}}$ acts on basis strings as
   $x\mapsto\pi(x)\oplus a$. `blockShift_lower` shows that contiguous block-shift
   form is strictly lower triangular in Kronecker order. `affine_obstruction` shows,
   at $n=3$, that the first bits of the transformed columns $\pi(e_j)\oplus a$
   take both values. `A_entry` and `conjugate_support` preserve the corresponding
   nonzero arcs $(\bar e_j,e_j)$; `no_blockShift` excludes every permitted conjugator.
   `A_mem` and `result` give the root-space witness and the universal refutation.

2. **Family $n\ge3$ — proved by the following paper argument; computed for $n=3,4,5$.**
   With all $c_j\ne0$, put $A_n=\sum_j c_j|\bar e_j\rangle\langle e_j|$ and
   $\Delta_n=i\sum_k Z_k$. Its diagonal entry at $x$ is $i(n-2|x|)$.
   Since $|e_j|=1$ and $|\bar e_j|=n-1$, each support entry satisfies
   $[\Delta_n,A_n]=-2i(n-2)A_n$. Thus the real frequency $-2(n-2)$ is nonzero.
   Coordinate permutations and bit flips send complementary strings to complementary
   strings. At the first position, $\pi(e_j)$ has bit 1 for exactly one $j$ and bit 0
   for the other $n-1$ indices. Both values remain present after xor with $a$.
   One transformed column has first bit 1 and its complementary row has first bit 0,
   hence that nonzero entry is above the diagonal. This excludes block-shift form for
   every prescribed conjugator. This uniform argument is not a Lean theorem of this module.
   The numerical check below tests nonzero coefficients $c_j=1+0.37j$, uses floating
   `numpy.allclose` for the commutator, and enumerates all $2^n n!$ support actions;
   signs do not affect the nonzero pattern. It finds zero strictly lower-triangular
   conjugates among 48, 384 and 3840 actions for $n=3,4,5$, respectively.

3. **$n=2$ — open in this delivery; consistent with the source.** The source's
   four-by-four Cases 1–16 classify its root vectors into the permitted block-shift
   forms. That classification is not re-proved here. For the family above,
   $-2(n-2)=0$, so this particular torus witness supplies no nonzero root frequency
   at $n=2$. The universal conjecture is refuted at $n=3$ without changing the
   source's two-qubit result.

4. **Remark 2(a) — proved false as an elementwise assertion by exact matrix arithmetic.**
   For $L=J\otimes I_2$, its first row is $(0,0,1,0)$, so
   $(LP_{\mathrm{out}})_{01}=(P_{\mathrm{out}})_{21}=-1$, whereas
   $(P_{\mathrm{out}}L)_{01}=L_{01}=0$. Thus the signed matrices do not commute
   elementwise. On supports, coordinate permutations normalize the bit-flip group:
   moving a swap past a flip relabels the flipped coordinate. Their product is the
   affine support group, not an elementwise commuting direct product.
   This paper calculation is separate from the module's settling theorem.

5. **Smallest sufficient subgroup — open.** The source's proposed
   $\Pi^{\mathrm{ex}}_{\mathrm{loc}}$ is too small for $n\ge3$. Determining a
   smallest or natural sufficient signed-permutation subgroup remains open,
   including the proposed class of all signed permutations commuting with the
   local torus action. No sufficiency assertion for that class is made here.

6. **Consequences for the source — literature reading.** Corollary 2.18 retains its
   relative-numerical-range characterization via $E(t)$; Corollary 2.19 retains
   unrestricted unitary block-shift similarity. Neither depends on the conjectured
   restriction. Conjecture 3.6 and the minimality expectation in Remark 2 lose that
   proposed restriction; no other source theorem is refuted by this delivery.

### Reproducible finite computation

The exact source of the orchestrator's check follows. Dependencies: Python 3 and NumPy.
Command: `python3 /tmp/op-dhks/check.py`; exit code **0**.
SHA-256: `593fe84f1dfd7d939a51c4bad4884974c06866bac6df8f7fa7b2807a91b48839`.
Save the code verbatim as `check.py` and run `python3 check.py`.

```python
# Dirr–Helmke–Kleinsteuber–Schulte-Herbrüggen Conjecture 3.6 (math-ph/0702005): refutation check.
import itertools, numpy as np
def check(n):
    N=2**n; bits=lambda x:[(x>>(n-1-k))&1 for k in range(n)]   # bit k = tensor factor k (first factor = most significant)
    idx=lambda b:sum(bb<<(n-1-k) for k,bb in enumerate(b))
    full=N-1
    A=np.zeros((N,N),dtype=complex)
    for j in range(n):
        e=1<<(n-1-j); A[e^full,e]=1.0+0.37*j   # A = sum_j c_j |ebar_j><e_j|
    lam=np.array([sum(1-2*b for b in bits(x)) for x in range(N)],dtype=float)  # Delta = i*diag(n-2|x|)
    D=np.diag(1j*lam)
    comm=D@A-A@D
    phi=-2*(n-2)
    assert np.allclose(comm,1j*phi*A), "not in E(t_loc)"
    # group: basis maps x -> pi(x) xor a (support level; signs irrelevant)
    ok=0; total=0
    for perm in itertools.permutations(range(n)):
        for a in range(N):
            total+=1
            g=lambda x:idx([bits(x)[perm[k]] for k in range(n)])^a
            sup=[(g(r),g(c)) for r in range(N) for c in range(N) if abs(A[r,c])>0]
            if all(r>c for r,c in sup): ok+=1
    return total, ok
for n in (2,3,4,5):
    if n==2:
        print("n=2: phi=0, A not in E(t_loc) via this Delta (family starts at n=3)"); continue
    t,ok=check(n); print(f"n={n}: group elements(support level)={t}, conjugates strictly lower triangular={ok}")
```

## ASSUMED-UNVERIFIED

Absence of a prior published settlement beyond the preregistration's searched scope is
unverified; unavailable texts and search endpoints are not evidence of absence.
The $n\ge3$ family argument and Remark 2(a) calculation are paper arguments;
only the three-qubit refutation and its consumed private lemmas are kernel-checked here.
The source's complete $n=2$ classification and the smallest sufficient subgroup question
remain outside this module's formal scope.
