---
bibkey: howard2013stabilizercontextuality
authors: Mark Howard; Eoin Brennan; Jiri Vala
year: 2013
title: "Quantum Contextuality with Stabilizer States"
doi: 10.3390/e15062340
url: https://arxiv.org/abs/1501.04342v1
claim: "The paper decomposes qudit Bell and noncontextuality inequalities into rank-one stabilizer projectors, builds the orthogonality graph of these projectors, and conjectures from the cases d = 2, 3, 5, 7 that the graph Γ_CHSH obtained from the qudit CHSH inequality is (2d − 1)(d − 1)-regular."
strata_touched:
  - D5/S3/Quantum/Contextuality/StabilizerCHSHGraphRegularity
license: citation-only
triage: anchor
---

# Quantum Contextuality with Stabilizer States

Mark Howard, Eoin Brennan and Jiri Vala, Entropy 15 (2013) 2340–2362; arXiv:1501.04342v1 (quant-ph), 2015-01-18. Quotations are from the v1 TeX source.

The setting (Section 2):

> Throughout, we always assume the dimension, $d$, of a single qudit to be a prime number. Because of the mathematics involved, most of the subscripts, superscripts and arithmetic will use elements \linebreak from $\Zd$---the set of integers modulo $d$. Occasionally we will also need to use $\Zd^*$---the set of non-zero integers modulo $d$. Define the generalized Pauli ``shift'' and ``phase'' operators, respectively, as
> \begin{align}
> X\ket{j}=\ket{j+1}, \quad Z\ket{j}=\omega^j\ket{j} \quad \text{where} \quad\omega= \exp(2 \pi i/d)
> \end{align}

The spectral projectors (Section 2):

> \begin{align}
> \Pi_{(x_1|z_1)[k]}=\sum_{j\in \Zd}\omega^{-jk}(P_{(x_1|z_1)})^j \label{eqn:Qproj}
> %\Pi_{(x_1|z_1)[k]}=\frac{1}{d}\left(I+\omega^{-k}P_{(x_1|z_1)}+\ldots +\omega^{-(d-1)k}(P_{(x_1|z_1)})^{d-1}\right)=\sum_{j\in \Zd}\omega^{-jk}(P_{(x_1|z_1)})^j \label{eqn:Qproj}

> \begin{align}
> \Pi_{(x_1,x_2|z_1,z_2)[k]}=\sum_{j\in \Zd}\omega^{-jk}(P_{(x_1,x_2|z_1,z_2)})^j \label{eqn:TwoQProj}
> %\Pi_{(x_1,x_2|z_1,z_2)[k]}=\frac{1}{d}\big(I+\omega^{-k}P_{(x_1,x_2|z_1,z_2)}
> %\ldots +\omega^{-(d-1)k}(P_{(x_1,x_2|z_1,z_2)})^{d-1}\big)=\sum_{j\in \Zd}\omega^{-jk}(P_{(x_1,x_2|z_1,z_2)})^j. \label{eqn:TwoQProj}
> \end{align}
> This projector can be decomposed into a sum of $d$ rank-1 projectors via,
> \begin{align}
> \Pi_{(x_1,x_2|z_1,z_2)[k]}=\sum_{a+b=k}\left(\Pi_{(x_1|z_1)[a]} \otimes \Pi_{(x_2|z_2)[b]}\right) \label{eqn:SumRank1}
> \end{align}

The graph convention (Section 3):

> Graphically, we can represent this scenario as a pentagonal graph $\Gamma$ (\emph{i.e}., a $5$-cycle) where vertices correspond to tests, and adjacent (connected) vertices correspond to compatible and exclusive tests. Define the operator $\Sigma_{\Gamma}$ to be

The qudit CHSH operators (Section 5):

> In order to generalize the above example to qudits, we first rewrite the $d=2$ CHSH inequality in the following form, where as usual $\omega=e^{\tfrac{2 \pi i}{d}}$,
> \begin{align}
> \langle \mathcal{B}\rangle \leq 2\ \text{ where }\ \mathcal{B}=\sum_{j,k \in \mathbb{Z}_2}\omega^{jk}A_j\otimes B_k \quad\left(A_0,B_0=X, A_1,B_1=Y\right) \label{eqn:BellQubit}
> \end{align}
> Ji \emph{et al.} \cite{Ji:2008} (with a subsequent reexamination by Liang \emph{et al.} \cite{Liang:2010}) have shown that the form of the Bell inequality in Equation~\eqref{eqn:BellQubit} can be generalized to work for qudits too. They introduced a natural modification of the sum comprising the Bell operator, along with a careful choice of measurement operators e.g.,
> \begin{align}
> A_j=\omega^{j(j+1)}XZ^j,\ B_k=\omega^{(2^{-1})^2(k^2+2k)}XZ^{2^{-1}k}
> \end{align}
> 
> 

> For $d=3$ \emph{i.e}., qutrits we have
> \begin{align}
> \langle \mathcal{B}\rangle \leq 9\ \text{ where }\ \mathcal{B}=\sum_{\substack{n \in \mathbb{Z}^*_3\\ j,k \in \mathbb{Z}_3}}\omega^{njk}A^n_j\otimes B^n_k \label{eqn:QutritCHSH}%\qquad
> %(A_j=\omega^{j(j+1)}XZ^j,\ B_k=\omega^{k(k+2)}XZ^{2k})

> %&-3\mathbb{I}_9\bigg)
> \end{align*}
> Breaking up this expression even further into $27$ distinct rank-one projectors, via Equation~\eqref{eqn:SumRank1}, we get a 10-regular graph $\Gamma_{\textrm{CHSH}}$ of order $27$ \cite{GammaCHSH27}, with $\alpha(\Gamma_{\textrm{CHSH}}) =6$ and $\vartheta(\Gamma_{\textrm{CHSH}}) \approx 7.098 $. The corresponding non-contextuality inequality is thus
> \begin{align}

The conjecture (Section 5):

> Observe that for all $d \in \{2,3,5,7\}$ that we have discussed, we see some structure in the graphs $\Gamma_{\textrm{CHSH}}$ obtained from qudit CHSH inequalities. Whereas it is quite easy to see that all graphs will have order $|\Gamma_{\textrm{CHSH}}|=d^3$, we conjecture based on the examples here that
> \begin{align}
> \Gamma_{\textrm{CHSH}} \text{ is a }(2d-1)(d-1)\text{{-regular graph}}
> \end{align}

## Verified locator

- URL: https://arxiv.org/abs/1501.04342v1 (v1, 2015-01-18; source `entropy-33181-English-layout_corrected.tex`, md5 `c93c244aca4289a8c877ac0eaa42d450`): the setting (l. 189–192), the projectors (l. 226–244), the graph convention (l. 365), the CHSH operators (l. 718–749) and the conjecture (l. 767–770).
- DOI: 10.3390/e15062340 (Entropy 15, 2340–2362). The published text was not read.
