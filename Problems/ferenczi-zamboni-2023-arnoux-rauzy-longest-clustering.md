---
slug: ferenczi-zamboni-2023-arnoux-rauzy-longest-clustering
bibkey: ferenczizamboni2024arnouxrauzy
doi: 10.1016/j.aam.2023.102621
url: https://arxiv.org/abs/2305.18986v1
triage: theorem
motivation_gids:
  - D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.result
---

# Ferenczi–Zamboni Conjecture 1 on longest clustering words

## Problem

S. Ferenczi and L. Q. Zamboni, *Clustering and Arnoux–Rauzy words*,
arXiv:2305.18986v1, Advances in Applied Mathematics 153 (2024) 102621,
DOI 10.1016/j.aam.2023.102621, state Conjecture 1:

> In a given AR language $\Lambda$ satisfying $(Rabc)$, the word in Proposition
> [14] is the longest clustering word, or, if this fails, the longest clustering
> word conjugate to a standard AR word.

The formal statement uses the source's three-letter Arnoux–Rauzy blocks,
languages, standard words, conjugacy, Burrows–Wheeler transform and clustering
definitions. It records the second alternative of the conjecture as `claim`.

### Statement echo

The alphabet is $\mathrm{Fin}\,3$, with $a=0$, $b=1$, and $c=2$; words
are lists. The three AR rules are the pointwise update that fixes the selected
block and appends it to each other block. `arBlocks` uses `Nat.rec` and
`Function.update` for that recurrence. `InfOften` is the universal occurrence
condition expressed using `Filter.Frequently` at `Filter.atTop`, equivalent to
$\forall x\,N,\ \exists k\ge N,\ d(k)=x$. The boundary $\mu$ is
`Nat.findGreatest` of the positions $j$ with $d(j-1)\ne d(\mu_y-1)$,
bounded by $\mu_y$; the value is $0$ when no such positive position exists.
Stage blocks are enumerated by `List.ofFn` and sorted by length. For BWT,
the non-strict permutation-rank order is the negation of reverse `List.lex`;
`List.insertionSort` sorts the rotations and `List.getLast?` extracts their
last letters. The quantified conditions in `claim` are exactly the weaker
standard-conjugacy alternative of Conjecture 1.

## Motivation

Issue [#15366](https://github.com/the-omega-institute/trureturing/issues/15366)
preregistered the source question, the $(Rabc)$ convention, the directive
$abcacba(abc)^\omega$, and the $m=1$ witness. The settling declaration
`D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.result` has type
$\lnot\mathit{claim}$ and carries `OpenProblemResolutionClaim(Refuted)`.

## Gap

The source proves that its Proposition 14 word is primitive, perfectly
clustering and conjugate to a standard Arnoux–Rauzy word, but Conjecture 1
asserts that the word is longest among the relevant clustering factors. The
settlement supplies a longer factor in the language for a directive satisfying
$(Rabc)$, so that maximality assertion fails.

## Route

Fix $m\ge1$. Let $\Lambda_m$ have directive prefix $a^m b c a c b a$,
followed by any directive in which every letter occurs infinitely often.
Define $\sigma_x(x)=x$ and $\sigma_x(y)=yx$ for $y\ne x$, and put
$\varphi=\sigma_a^m\circ\sigma_b\circ\sigma_c$. The blocks at stage
$m+2$ are

$$
A=\varphi(a)=a b a^m c a^m b a^m,\qquad
B=\varphi(b)=b a^m c a^m b a^m,\qquad
C=\varphi(c)=c a^m b a^m.
$$

Thus $aB=A$. Set $D=CA$ and $U_m=A^2DAD$.

1. **The source's word.** The first $c$ occurs at
   $\lambda_2=m+1$, and the first subsequent $a$ and $b$ occur at
   $\mu_a=m+2$ and $\mu_b=m+4$. Hence $x=a$, $y=b$, and the preceding
   run of $c$ starts at $\mu=m+3$. The source recurrence at stage
   $\mu_y$ gives $S_{\mu_y}=D$, $M_{\mu_y}=AD$, and $L_{\mu_y}=BAD$.
   Since $|D|=5m+6$ and $|A|=3m+4$, the Proposition 14 word is
   $v_m=D^2AD$, with $|v_m|=2(5m+6)+(8m+10)=18m+22$.
2. **Membership.** The following $b$ and $a$ rules give, successively,
   $(AD(BAD),BAD,D(BAD))$ and a $c$-block
   $C_{m+6}=D(BAD)(AD)(BAD)$. The last letter of $D$ is $a$. Starting
   there yields the factor
   $a(BAD)(AD)=(aB)ADAD=A^2DAD=U_m$. This standard block depends only on
   the prescribed prefix, so membership holds for every permitted continuation.
3. **BWT transport and clustering.** Let $w$ be primitive of length $n$,
   with $k=|w|_x$. There are $n$ positions labelled $x$ in the cyclic word
   $\sigma_x(w)$: each original letter supplies its image's final $x$.
   The row starting at that $x$ is $x\sigma_x(s)$ cyclically, where $s$
   is the original rotation starting just after the corresponding original
   letter. Its last letter is that original letter. The ordering of these
   $n$ rows is the ordering of $s$: common original prefixes have identical
   images, and at the first distinct letter the images begin with those
   distinct letters. Therefore the last-column subword on the $x$-starting
   rows is exactly $B(w)$. The remaining $n-k$ rows start at non-$x$
   letters and end in $x$. When $x$ is least, the first group precedes all
   remaining rows; when $x$ is greatest, it follows them. Thus

   $$
   B(\sigma_x(w))=B(w)x^{n-k}\quad(x\text{ least}),\qquad
   B(\sigma_x(w))=x^{n-k}B(w)\quad(x\text{ greatest}).
   $$

   For $H=aacaaca$, its sorted rotations are
   $aaacaac$, $aacaaac$, $aacaaca$, $acaaaca$, $acaacaa$, $caaacaa$,
   $caacaaa$, so $B(H)=ccaaaaa$. Its counts are $(5,0,2)$.
   Since $c$ is greatest on its support, the first transport gives
   $B(\sigma_c(H))=c^7a^5$, with counts $(5,0,7)$.
   Next $b$ is greatest, giving
   $B(\sigma_b\sigma_c(H))=b^{12}c^7a^5$.
   Each of the $m$ substitutions by the least letter $a$ adds
   $12+7=19$ terminal $a$ letters. Since
   $\varphi(H)=AACAACA=A^2DAD$, this proves
   $B(U_m)=b^{12}c^7a^{19m+5}$ for $a<c<b$.
   The base word has counts $(5,0,2)$ and is primitive. The successive
   images have counts $(5,0,7)$, $(5,12,7)$, and finally
   $(19m+5,12,7)$; each gcd is $1$, so each is primitive. The displayed
   reverse-order blocks prove perfect clustering.
4. **Standard conjugate and length.** Write $H=aQ$ with $Q=acaaca$.
   Direct substitution gives $Qa=\sigma_a^2\sigma_c^2(a)$.
   Moving the initial block $\varphi(a)=A$ of $\varphi(aQ)$ to the end
   gives $\varphi(Qa)=\varphi\sigma_a^2\sigma_c^2(a)$, a standard
   block for the directive prefix $a^m b c a^2 c^2$ with any infinitely
   recurrent continuation. Finally,
   $|U_m|=3(3m+4)+2(5m+6)=19m+24$ exceeds $|v_m|=18m+22$ by $m+2$.

These four steps are a paper derivation in this dossier. The kernel-checked
instance is the $m=1$ endpoint in `result`; the family statement and its
transport argument are not claimed as Lean theorems here.

## Falsifier

A directive satisfying $(Rabc)$ and $InfOften$, together with a language word
that is clustering, conjugate to a standard word, and no longer than the
Proposition 14 word, would not refute the conjecture. The delivered instance
instead has $|U_1|=43$ and $|v_1|=40$ with all hypotheses kernel-checked.

## Evidence

The kernel-checked declaration is
`D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.result`; its axiom closure
is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
Its proof uses the directive conditions, language membership, clustering,
standard conjugacy and strict length comparison at $m=1$. The exact BWT and
perfect-clustering block structure are the computation and prose conclusions
below.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The exact computation is recorded in the experiment entry
[`docs/reports/ferenczi-zamboni-2023-arnoux-rauzy-longest-clustering/check.py`](https://github.com/the-omega-institute/trureturing-experiments/tree/03ed7e9bd34d0762f74d4ce290a98120ce3d7b6f/docs/reports/ferenczi-zamboni-2023-arnoux-rauzy-longest-clustering)
at commit `03ed7e9bd34d0762f74d4ce290a98120ce3d7b6f`. From that directory,
`python3 check.py` exits `0`, reports `bad= 0`, and has script SHA-256
`3841366d6e40869b7165f37c2dd0d67cc532db7076991382295b32ca23f613b0`.
Its tested scope is exactly $m=1,2,3,4$.

| $m$ | $(\lambda_2,\mu_a,\mu_b,\mu)$ | $|v_m|$ | $|U_m|$ | $B(U_m)$ for $a<c<b$ |
| --- | --- | ---: | ---: | --- |
| $1$ | $(2,3,5,4)$ | $40$ | $43$ | $b^{12}c^7a^{24}$ |
| $2$ | $(3,4,6,5)$ | $58$ | $62$ | $b^{12}c^7a^{43}$ |
| $3$ | $(4,5,7,6)$ | $76$ | $81$ | $b^{12}c^7a^{62}$ |
| $4$ | $(5,6,8,7)$ | $94$ | $100$ | $b^{12}c^7a^{81}$ |

For these four instances the computation verifies that $v_m$ is perfectly
clustering, $U_m$ is a factor of the stated standard block, primitive and
conjugate to a standard AR word, and $|U_m|>|v_m|$. These readings do not
extend the computational scope beyond the four listed values.

## Triage

The settlement is `Refuted` for Conjecture 1 under
`admission_basis: open-problem-resolution (#15366; Refuted)`.

| item | status | evidence kind and boundary |
| --- | --- | --- |
| The $m=1$ refutation | proved | Kernel-checked declaration `result` states $\lnot\mathit{claim}$. Its proof uses `dir_rabc`, `dir_inf`, `witness_mem`, `witness_cluster`, `witness_conjugate` and `prop_len`; `prop_len` states $|v_1|=40$. Exact witness lengths, BWT and primitivity are computed in the experiment entry. |
| Extreme-letter BWT transport and the boundary-occurrence mechanism | proved | Paper derivation in Route steps 1–4: the least/greatest-letter substitution identities and the occurrence across standard-block boundaries. The mechanism is not a separate Lean theorem. |
| The family $U_m=A^2DAD$ and its BWT formula | proved | Paper derivation in Route steps 1–4 gives $B(U_m)=b^{12}c^7a^{19m+5}$, standard conjugacy, and $|U_m|=19m+24>|v_m|=18m+22$ for every $m\ge1$. This uniform family is not claimed as a Lean theorem. |
| Exact checks for $m=1,2,3,4$ | computed | Pinned experiment entry above; `python3 check.py`, exit `0`, script SHA-256 as recorded, with `bad= 0`. |
| Proposition 14's surviving property | proved | The source's Proposition 14 remains valid: its word is primitive, perfectly clustering, and conjugate to a standard AR word. This is a source reading, not a new Lean declaration. |
| The longest clustering word of $\Lambda_m$, including whether $U_m$ is longest | open | The refutation supplies a longer word than Proposition 14 but does not identify the global maximum. |
| The general longest-word value under $(Rabc)$ | open | No uniform maximum is established by the kernel instance, the paper derivation, or the finite computation. |

### What the settlement shows

The conjectured maximality of the Proposition 14 word is false already at
$m=1$, and the paper derivation gives a longer family for every $m\ge1$.
Proposition 14 itself survives with its stated primitive, perfect-clustering
and standard-conjugacy conclusions. Any later argument that uses Conjecture 1
as a longest-word conclusion must be restricted or withdrawn; arguments using
only the surviving Proposition 14 properties are unaffected.

## ASSUMED-UNVERIFIED

The openness and priority assessment is bounded by the cited arXiv version,
the published article, and preregistration #15366. Exhaustive worldwide
priority, later versions, and independent unpublished settlements are not
certified by this dossier.
