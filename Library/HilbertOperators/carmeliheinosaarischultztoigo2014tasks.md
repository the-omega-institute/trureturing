---
bibkey: carmeliheinosaarischultztoigo2014tasks
authors: Claudio Carmeli, Teiko Heinosaari, Jussi Schultz, and Alessandro Toigo
year: 2014
title: Tasks and premises in quantum state determination
doi: 10.1088/1751-8113/47/7/075302
url: https://arxiv.org/abs/1308.5502v2
claim: Distinguishing every rank-at-most-t state from every state is equivalent to a minimum positive and negative sign rank of at least t+1 for each nonzero self-adjoint observable-annihilator element.
strata_touched: []
license: citation-only
triage: anchor
---

# Low-rank states compared with all states

The primary text is [arXiv:1308.5502v2](https://arxiv.org/html/1308.5502v2),
version of 17 January 2014, §4.1, Lemma 1(b,c), Lemma 2(a) and
Theorem 1(a). The journal reference is *Journal of Physics A:
Mathematical and Theoretical* **47** (2014), 075302, with the DOI
in the frontmatter.

For a self-adjoint matrix $T$, let $n_+(T)$ and $n_-(T)$ count
strictly positive and strictly negative eigenvalues with multiplicity.
The source's $\operatorname{rank}_{\downarrow}(T)$ is their minimum,
and $\operatorname{rank}_{\uparrow}(T)$ their maximum. For an
observable on a $d$-dimensional complex Hilbert space and
$1\le t\le d$, Theorem 1(a) characterizes distinguishing every
state of rank at most $t$ from every state by

$$
\min\{n_+(T),n_-(T)\}\ge t+1
\quad\text{for every nonzero self-adjoint annihilator element }T.
$$

The annihilator is taken with respect to the observable's real
operator system, which contains the identity; its elements are
therefore traceless. Lemma 1 and Lemma 2(a) describe the spectral
difference sets underlying this criterion.

The exact consumers are [VIII, Proposition 111.1, Corollary 111.2 and
Proposition 112.1](../../docs/develop/theory/QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_VIII.md).
That source uses the elementary spectral argument directly for a
traceless real-linear kernel $N=\ker\pi$, without declaring $\pi$
an observable. Its actual-face equality first proves entire positive
preimages. This gives a singleton fiber among **all** density states
for every source density matrix of rank one or two. For $0\ne A\in N$,
the states $A_+/s$ and $A_-/s$, with
$s=\operatorname{Tr}A_+=\operatorname{Tr}A_->0$, have the same image.
Neither can have rank at most two. Thus both sign ranks are at least
three, the $t=2$ obstruction, and $n\le5$ forces $N=0$.

Injectivity only between rank-restricted states is a different task.
The all-state comparison above cannot be replaced by a bound on
the maximum sign rank or by pure-only injectivity. In the consumer,
pure-label injectivity alone does not supply strict completeness;
the actual entire pair-face and positive-preimage arguments are
indispensable to its inference.

This is attribution of the mature sign-rank criterion, not a new
tomography theorem. No POVM, measurement implementation, native effect
menu or physical state-determination procedure is supplied. The note
contains citation and paraphrase only, with no copied code or full
paper text; citation-only licensing does not grant redistribution
rights to the paper.
