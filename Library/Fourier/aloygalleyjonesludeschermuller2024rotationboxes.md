---
bibkey: aloygalleyjonesludeschermuller2024rotationboxes
authors: Albert Aloy; Thomas D. Galley; Caroline L. Jones; Stefan L. Ludescher; Markus P. Müller
year: 2024
title: Spin-Bounded Correlations — Rotation Boxes Within and Beyond Quantum Theory
doi: 10.1007/s00220-024-05123-2
url: https://arxiv.org/abs/2312.09278v2
claim: Section 4.2.3 asks whether quantum and general spin-one rotation correlations coincide for every finite outcome set of cardinality at least three.
strata_touched:
  - D5/S3/Quantum/Measurement/RotationBoxes/SpinOneRotationBoxes
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.1007/s00220-024-05123-2

Source: https://arxiv.org/abs/2312.09278v2

The question is the final paragraph of §4.2.3, page 17 of the versioned PDF.
Definition 1 is on page 7; Definition 2 is on page 9. Equation (4) orders
frequency blocks by j = −J, …, J and permits arbitrary finite multiplicities.

## Source statements

Section 4.2.3, page 17:

> Hence, even though the set of spin correlations ℛ₁ and 𝒬₁ agree, the corresponding GPT systems have genuinely different information-theoretic and physical behaviors. This is also the reason why we do not currently know whether 𝒬₁ᴬ = ℛ₁ᴬ for |𝒜| ≥ 3.

The source TeX of the question and its two definitions is reproduced below.

```tex
Hence, even though the set of spin correlations $\mathcal{R}_1$ and $\mathcal{Q}_1$ agree, the corresponding GPT systems have genuinely different information-theoretic and physical behaviors. This is also the reason why we do not currently know whether $\mathcal{Q}_1^\mathcal{A}=\mathcal{R}_1^\mathcal{A}$ for $|\mathcal{A}|\geq 3$.
```

```tex
\begin{definition}
\label{DefQuantum}
The set of quantum spin-$J$ correlations with outcome set $\mathcal{A}$, where $|\mathcal{A}|\geq 2$, will be denoted $\mathcal{Q}_J^{\mathcal{A}}$, and is defined as follows. It is the collection of all $\mathcal{A}$-tuples of probability functions
\[
   \left(\strut \theta\mapsto P(a|\theta)\right)_{a\in\mathcal{A}},
\]
such that there exists a Hilbert space with a projective representation of ${\rm SO}(2)$ of the form~(\ref{eqRepDef}), some quantum state (i.e.\ density matrix) $\rho$, and a POVM $\{E_a\}_{a\in\mathcal{A}}$ on that Hilbert space such that
\[
   P(a|\theta)=\Tr(U_\theta\rho U_\theta^\dagger E_a).
\]
The special case of two outcomes, $\mathcal{A}=\{-1,+1\}$, will be denoted $\mathcal{Q}_J$ (without the $\mathcal{A}$-superscript). Instead of pairs of probability functions, we can equivalently describe this set by the collection of functions $P(+1|\theta)$ only, because $P(-1|\theta)=1-P(+1|\theta)$ follows from it.
\end{definition}
```

```tex
\begin{definition}\label{def:spin_J_gen_cor}
The set of (general) spin-$J$ correlations with outcome set $\mathcal{A}$, where $|\mathcal{A}|\geq 2$, will be denoted $\mathcal{R}_J^\mathcal{A}$, and is defined as follows. It is the collection of all $\mathcal{A}$-tuples of functions
\[
\left(\theta\mapsto P(a|\theta)\right)_{a\in\mathcal{A}}
\]
such that every one of the functions is a trigonometric polynomial of degree at most $2J$ in $\theta$, and $0\leq P(a|\theta)\leq 1$ as well as $\sum_{a\in\mathcal{A}} P(a|\theta)=1$ for all $\theta$.

The special case of two outcomes, $\mathcal{A}=\{-1,+1\}$, will be denoted $\mathcal{R}_J$ (without the $\mathcal{A}$-superscript). Instead of pairs of probability functions, we can equivalently describe this set by the collection of functions $P(+1|\theta)$ only, because $P(-1|\theta)=1-P(+1|\theta)$ follows from it.
\end{definition}
```

```tex
\begin{lemma}
\label{LemmReal2Complex}
Suppose that $P$ is a real trigonometric polynomial of degree $2J$, and write it as
\begin{eqnarray*}
P(\theta)&=& c_0 + \sum_{j=1}^{2J} \left(\strut c_j\cos(j\theta)+s_j\sin(j\theta)\right)=\sum_{k=-2J}^{2J} a_k e^{ik\theta}.
\end{eqnarray*}
Then $a_{-j}=\overline{a_j}$, $a_0=c_0$,  and for all $j\geq 1$, we have $c_j=2\, {\rm Re}(a_j)$ and $s_j=-2\, {\rm Im}(a_j)$.
\label{lemma:inequality}
\end{lemma}
```

## Scope

The formal statement uses a finite sigma type with frequencies −1, 0, 1,
a density state of trace one, and one family of positive semidefinite
measurement effects summing to the identity. The same state and measurement
serve every real angle. The general family is given by its five real Fourier
coefficient functions, together with pointwise probability bounds and
normalization. These are independently defined predicates.

The construction supplies one copy of each frequency and a pure state that
can depend on the probability family. It does not assert an embedding of the
whole general probabilistic theory into one fixed quantum system. The
source's inequivalence of those systems and its higher-spin gaps are separate
statements.

## Experiments and literature boundary

The independent exact experiment is in
https://github.com/the-omega-institute/trureturing-experiments at commit
25ea29e05ee22f1b0da6ac37e64a553b6b1ef961, in
`docs/reports/aloy-et-al-spin-one-rotation-boxes/`. The file `check.py` has
SHA-256 d8952849a7eb1251eca2cf091b4f9f4401b5216ff5396a36205896f7d9dde0e9.
Its recorded command is `/tmp/op-spin1box/venv/bin/python docs/reports/aloy-et-al-spin-one-rotation-boxes/check.py`;
the recorded exit code is 0 and the terminal result is `ALL_CHECKS_OK`.
These are the readings reported in preregistration issue #22872; they do not
replace the universal Lean proof.

Literature completeness is ASSUMED-UNVERIFIED. Issue #22872 records the
inspected citing works and later author papers. In particular,
arXiv:2507.06912v2, equations (45)–(48), retains a diagonal-sum condition in
its semidefinite characterization; that condition alone does not supply the
universal normalization construction used here.
