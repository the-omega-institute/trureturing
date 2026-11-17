---
slug: oeis-a124056-positive-integer-occurrence
bibkey: quet2006a124056
doi: null
triage: theorem
motivation_gids:
  - D5/S3/Arith/Recurrence/A124056Occurrence.missing_residue_of_finite_three
url: https://mathoverflow.net/questions/515669
---

# Positive-integer occurrence in A124056

## Problem

Let $a_1=1$ and, for every $n\ge1$, let

$$a_{n+1}=\#\{i:1\le i\le n,\ a_i\mid a_n\}.$$

The target is that for every positive integer $k$ there exists a positive index
$n$ with $a_n=k$. Indices, multiplicities and the self index are all retained.
The source is Quet's A124056, Della Corte's question 376929 and Sommacal's
question 515669; see `Library/RecurrenceComposition/quet2006a124056.md`.

## Exact representation

`values N` contains exactly the first $N+1$ terms. Internal `term N` is
$a_{N+1}$, while `sourceTerm n = term (n-1)` is used at positive source
indices. `source_specification` proves the original initialization and the
closed-interval, one-based recurrence; zero never occurs among its indices.

`count N d` counts internal indices strictly below $N$. `prefixMax N` takes
the maximum through internal index $N$, inclusive. Thus the multiplicity bound
available at $N$ is applied only to predecessors of this prefix maximum.

## Formal occurrence theorem

The formal source proves that infinitely many threes imply the full target,
and that finitely many threes force a fixed missing residue class modulo some
$q\ge2$. It also proves that there can be no globally uniform positive $C,\delta$
with $c_N(d)\le C M_N^{1-\delta}$ for all positive $d$ and all $N$.
This last result directly reuses
`D5/S3/Arith/Divisors/DivisorSubpower.card_divisors_subpower` at
$\epsilon=\delta/2$.

For `AvoidsResidue q N`, every internal index through $N$ whose value exceeds
one has remainder different from one modulo $q$. With $q\ge2$, $t\le N$ and
$v\ge2$, `contributor_rank_bound` proves
$D_t(v)\le q\sum_{d\mid v,\ d<v}c_t(d)$. This time range keeps the successor
of every counted contributor inside the avoided prefix. Empty prefixes and the
first rank are included; $v=1$ is handled by its two initial occurrences.

The finite set `primeWords v` contains the distinct permutations of the prime
factor list of positive $v$. Its cardinality is $b(v)$ and its common length is
$\Omega(v)$. The empty word gives $b(1)=1$. `prime_word_split` proves the exact
split convolution at every rank from zero through $\Omega(v)$. With
$W_A(v)=A^{\Omega(v)}b(v)$ and $A=q+1$, `prime_word_weight_bound` absorbs the
proper-divisor weight sum. Strong induction in
`divisor_card_le_prime_word_weight` gives $D_t(v)\le2W_A(v)$ for positive $v$.

For $d\ge2$, `count_le_prime_word_bounds` gives both $c_t(d)\le2W_A(d)$ and
an injection of its occurrences into the positive predecessor values
$v\le M_N$ with $d\le2W_A(v)$. Consecutive-pair injectivity makes these
predecessor values distinct. These are the finite inputs to the remaining
frequency estimate.

`prime_word_first_letter` proves the exact recurrence

$$W_C(v)=C\sum_{p\mid v,\ p\text{ prime}}W_C(v/p)\qquad(v>1).$$

Using the convergent square reciprocal series and geometric decay,
`prime_word_polynomial_bound` chooses one $r>1$ from $A$ alone with
$W_{2A}(v)\le v^r$ for every positive $v$. In fact its parameter construction
makes $2A\sum_{p\in T}p^{-r}\le1$ for every finite prime set $T$.
Set $s=1/(2r)$, so $0<s<1/2$ and $rs=1/2$.

For each $\sigma>1$, a finite set $S$ is chosen so that every finite prime set
outside $S$ has weighted reciprocal sum at most one half. The actual
first-letter recurrence gives a finite rough-prefix sum $R_X\le1+R_X/2$,
hence $R_X\le2$. Every positive $v$ splits by its prime-factor support into
$m n=v$, with $m$ supported on $S$ and every prime divisor of $n$ outside $S$.
The product inequality

$$W_A(mn)\le W_{2A}(m)W_{2A}(n)$$

is proved directly from the first-letter recurrence for all positive $m,n$;
no multiplicativity assumption is used. It yields

$$W_A(v)^s v^{-\sigma}\le
  m^{-(\sigma-1/2)}W_{2A}(n)n^{-\sigma}.$$

The finite-prime Euler-product supplier bounds the smooth factor using only
local prime-power convergence at $\tau=\sigma-1/2>0$. The decomposition is
injective because multiplication recovers $v$. Enlarging to the finite product
of the smooth and rough prefixes proves `prime_word_finite_moment`:

$$\forall\sigma>1\ \exists H_\sigma>0\ \forall F\subseteq\mathbb N_{>0}
\text{ finite},\qquad
\sum_{v\in F}W_A(v)^s v^{-\sigma}\le H_\sigma.$$

Thus the same fixed $s$ works for every $\sigma$, with each tail set and
constant selected before $F$. All rearrangements used here are finite.

The finite Markov inequality on the actual distinct predecessor set gives

$$c_N(d)d^s\le2^s H_\sigma M_N^\sigma\qquad(d\ge2).$$

With $\delta=s^2/2$ and $\sigma=1+\delta$, the split at $d\le M_N^s$
combines this with $c_N(d)\le2d^r$. The low range has exponent one half;
the high range has exponent $1-\delta$. The two initial ones handle $d=1$,
and $M_N\ge1$ includes every small prefix. This proves
`uniform_count_bound_of_avoidance`, with constants independent of $N,d$.

If three occurred finitely often, `missing_residue_of_finite_three` would
supply one fixed modulus avoided by every prefix. The uniform count bound
would then contradict `no_uniform_sublinear_count_bound`. The three fiber
is therefore infinite and cofinal in the natural indices.
`full_positive_occurrence` consumes `full_occurrence_of_infinite_three` to
prove exactly the original all-positive-integer occurrence assertion. No
extra analytic hypothesis, infinite-fiber premise or cutoff remains in its
type.

## Admission boundary

The exact source representation and the infinite-three implication use new finite-tuple,
cardinality and threshold arguments. The missing-residue result uses the
earliest seed divisor and one finite LCM. The sublinear-count contradiction
uses the actual recurrence, the injectivity of consecutive pairs, and the
existing uniform divisor supplier. No novelty or priority assertion is made.
The compiled unconditional theorem
requires distinct source-fidelity and per-declaration proof-shape review before
freezing or publication; the implementation worker supplies no self-approval.

The matching Reg source provides dependent-family realization, equivalence,
variation, sensitivity and observational-dependence evidence for the four
original public theorems. Its four `Contract.Registration` attempts have no
`sourceSelection`. The missing evidence is the complete original-source
reconstruction and its readout path and coordinate bindings. The thirteen
additional contributor, prime-word, analytic and unconditional theorems have no
completed registration; their complete source-family realization, selected readouts, coordinate bindings
and family-wide evidence remain required. The concrete linked exception is
[issue 31349](https://github.com/the-omega-institute/trureturing/issues/31349#issuecomment-6957913334).
No public theorem is claimed to have a completed `declared_validated`
registration. Independent source-fidelity and per-declaration proof-shape
approval of the complete intended unit remains required before freezing.
