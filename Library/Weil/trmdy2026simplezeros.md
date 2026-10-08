---
bibkey: trmdy2026simplezeros
authors: "Vivaswat Ojha; Tormod Haugland; contributors to trmdy/zeta-simple-zeros-673137"
year: 2026
title: "Local zero-overlap certificates, finite trace-energy envelopes, and exact window-pressure assembly"
doi: null
url: https://github.com/trmdy/zeta-simple-zeros-673137/blob/1610b97b7895ff34982260f8dcaf04a0f7b82cf7/README.md
claim: A fixed research-repository revision assembles a nine-point kernel certificate into a 0.673312742272245998 simple-critical zero-proportion candidate; retaining the envelope chord coefficient in the exact window-pressure count gives a stronger conditional consumer of the same inputs.
strata_touched: []
license: citation-only
triage: anchor
---

# Local overlap certificates and their exact assembly boundary

The primary source is the [trmdy repository README at the fixed revision](https://github.com/trmdy/zeta-simple-zeros-673137/blob/1610b97b7895ff34982260f8dcaf04a0f7b82cf7/README.md). Every trmdy statement in this note refers to commit **1610b97b7895ff34982260f8dcaf04a0f7b82cf7**. The source describes its assembled proportion as a research candidate. Its mathematical dependencies and finite computational inputs are distinct from journal acceptance or a complete formalization.

The [paper source](https://github.com/trmdy/zeta-simple-zeros-673137/blob/1610b97b7895ff34982260f8dcaf04a0f7b82cf7/paper/main.tex) credits Vivaswat Ojha for the retuned seven-point contributor draft. The repository also preserves the previous contributions and numerical-certificate work. Its [refined deduction](https://github.com/trmdy/zeta-simple-zeros-673137/blob/1610b97b7895ff34982260f8dcaf04a0f7b82cf7/docs/refined-deduction.md) explicitly attributes the finite-dimensional trace-energy envelope and window-in-frame pressure count to [tawanerguo-cn, fixed revision 45149f6d403059a71be73c5e3f884cee7cd62b20](https://github.com/tawanerguo-cn/zeta-simple-zeros/blob/45149f6d403059a71be73c5e3f884cee7cd62b20/docs/trace_energy_envelope.md). These ingredients are prior results, not new foundational claims of the present repository.

## The common analytic interface

For an admissible profile $v$ on $[-1/2,1/2]$, let
$$
 k_v(x)=\frac{\int_{-1/2}^{1/2}v(s)\cos(2\pi xs)\,ds}
 {\int_{-1/2}^{1/2}v(s)\,ds},\qquad w(x)=k_v(x)^2.
$$
The [proof outline](https://github.com/trmdy/zeta-simple-zeros-673137/blob/1610b97b7895ff34982260f8dcaf04a0f7b82cf7/docs/proof.md) imports the stability form
$$
 S_T\ge H(v)N_T+\operatorname{tr}\Psi(M_T)-o(N_T),
 \qquad
 \Psi(t)=
 \begin{cases}(t-1)^2,&0\le t\le2,\\2t-3,&t\ge2.\end{cases}
$$
Here $S_T$ counts simple critical-line zeros in $(T,2T]$, $N_T$ counts all zeros there with multiplicity, and $M_T$ is the positive semidefinite Gram of simple-zero atoms. Its fixed-size, bounded-span blocks tend uniformly to the kernel Gram. The analytic source is the Alpöge–Furman framework together with the stability refinement in [ainta's full proof at 040c5e8](https://github.com/ainta/zeta-simple-zeros/blob/040c5e8/paper/riemann.tex). This note does not replace that analytic input with a finite matrix analogy.

The fixed trmdy profile is
$$
 v(s)=\cos(\sqrt2\,s)+10^{-9}\sum_{j=1}^{6}c_j\cos(2\pi js),
 \quad
 (c_1,\ldots,c_6)=(3322500,-7609135,1190194,-731476,-1680572,1141360).
$$
The supplied window certificate gives
$$
 H(v)\ge H_{\mathrm{cert}}=\frac{3362285207}{5000000000}=0.6724570414.
$$
This baseline belongs to this perturbed window. It cannot be replaced by Wang's larger optimized baseline while retaining the trmdy kernel, local weights, or overlap certificate.

## The local certificate and successive consumers

For $q+1$ ordered real points $y_0,\ldots,y_q$, the local certificate has the form
$$
 p(y_q-y_0)+\sum_{i<j}a_{ij}w(y_j-y_i)\ge\varepsilon,
 \qquad
 a_{ij}\ge0,\quad
 \sum_{i=0}^{q-r}a_{i,i+r}=2\quad(1\le r\le q).
$$
The exact nine-point weights and window coefficients are in the [candidate data](https://github.com/trmdy/zeta-simple-zeros-673137/blob/1610b97b7895ff34982260f8dcaf04a0f7b82cf7/data/candidate-nine-point-final.json).

The complete profile can equivalently be recorded by its seven frequencies and numerators:
$$
 (\omega_0,\ldots,\omega_6)=(\sqrt2,2\pi,4\pi,6\pi,8\pi,10\pi,12\pi),
$$
$$
 v(s)=10^{-9}\sum_{j=0}^{6}b_j\cos(\omega_js),\qquad
 (b_0,\ldots,b_6)=(1000000000,3322500,-7609135,1190194,-731476,-1680572,1141360).
$$
The full 36 local pair weights are $a_{ij}=n_{ij}/10^7$, with numerators below. A dash marks an index outside $i<j$; an explicit zero is an actual zero weight.

| $i$ / $j$ | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 0 | 1802576 | 4832031 | 5411933 | 10000000 | 10000000 | 10000000 | 10000000 | 20000000 |
| 1 | · | 2694869 | 2295599 | 1780844 | 0 | 0 | 0 | 10000000 |
| 2 | · | · | 2714860 | 0 | 2807223 | 0 | 0 | 10000000 |
| 3 | · | · | · | 2787695 | 5744740 | 2807223 | 0 | 10000000 |
| 4 | · | · | · | · | 2787695 | 0 | 1780844 | 10000000 |
| 5 | · | · | · | · | · | 2714860 | 2295599 | 5411933 |
| 6 | · | · | · | · | · | · | 2694869 | 4832031 |
| 7 | · | · | · | · | · | · | · | 1802576 |

All numerators are nonnegative. For every index separation $r=1,\ldots,8$, summing the displayed numerators on that diagonal gives $20\,000\,000$, so each span capacity is exactly two. These weights, the displayed profile, $p$, $\varepsilon$, and $H_{\mathrm{cert}}$ form one fixed source packet.

The pressure and threshold parameters are
$$
 q=8,\qquad p=\frac1{2500},\qquad\varepsilon=\frac{15211}{2500000}.
$$
The [nine-point deduction](https://github.com/trmdy/zeta-simple-zeros-673137/blob/1610b97b7895ff34982260f8dcaf04a0f7b82cf7/docs/nine-point.md) identifies the final candidate with the [split certificate log](https://github.com/trmdy/zeta-simple-zeros-673137/blob/1610b97b7895ff34982260f8dcaf04a0f7b82cf7/certificates/nine-point-final-grid4000.txt). That log reports two disjoint shard ranges covering all 96 initial shards, matching table hashes, and a combined 116,272,426 visited nodes. It is an external computational input; this note supplies no independent replay of that interval certificate. The data file's earlier discovery flags are not themselves a proof; the separate source report links the final certificate to this candidate.

Write
$$
 \Phi_m(E)=
 \begin{cases}
 E,&E\le m/(m-1),\\
 2\sqrt{(m-1)E/m}-1+E/m,&E\ge m/(m-1).
 \end{cases}
$$
For a unit-diagonal positive semidefinite $m$-point Gram, $E=\operatorname{tr}(G-I)^2$ and $D=\operatorname{tr}\Psi(G)$ satisfy $D\ge\Phi_m(E)$. Summing local windows in an $m$-point block gives $E+P\ge A=\varepsilon(m-q)$. Exact containment counts charge averaged pressure $(m-q)qp/m$ per unit total normalized span. The fixed source uses $D+P\ge\Phi_m(A)$ and obtains
$$
 \frac{mH_{\mathrm{cert}}-(m-q)qp}{m-\Phi_m(A)}.
$$
Its final nine-point choice $m=177$ yields
$0.673312742272245998143847403168\ldots$.
The older paper source concerns a seven-point retuning; the subsequent seven-point and nine-point refinements are stated in the linked repository documents, not attributed to that older paper theorem.

The earlier seven-point certificate has $q=6$, $p=1/2736$, $\varepsilon=891/200000$. The same refined formula at $m=235$ gives $0.67324258935589670294\ldots$. The source explicitly retains the analytic interface and local certificate as dependencies.

## Scope of the earlier three-point and seven-point work

| Source | Supplied mathematical input | Scope relevant here |
|---|---|---|
| [Wang, arXiv:2609.24167v1](https://arxiv.org/html/2609.24167v1) | Lemma 3.1 extracts clipped spectral defect from disjoint triples; Lemma 3.2 gives a closed three-point energy bound; Section 4 uses fixed-length cells | Its small improvement concerns simple critical zeros and distinct zeros through two related finite-multiset inequalities |
| [ainta README at 040c5e8](https://github.com/ainta/zeta-simple-zeros/blob/040c5e8/README.md), with the [full seven-point proof](https://github.com/ainta/zeta-simple-zeros/blob/040c5e8/paper/riemann.tex) | Three-consecutive-point certificate and later seven-point local pressure; shifted block pinching | The README lists $67.2519767\%$ for its three-point route; its seven-point proof gives $67.3008527927\ldots\%$ simple critical zeros |
| [trmdy refined deduction](https://github.com/trmdy/zeta-simple-zeros-673137/blob/1610b97b7895ff34982260f8dcaf04a0f7b82cf7/docs/refined-deduction.md) and [nine-point deduction](https://github.com/trmdy/zeta-simple-zeros-673137/blob/1610b97b7895ff34982260f8dcaf04a0f7b82cf7/docs/nine-point.md) | Finite-dimensional envelope and exact window containment applied to imported interval certificates | Seven-point $67.3242589355\ldots\%$ and nine-point $67.3312742272\ldots\%$ are candidate consumers in this fixed revision |
| [Knausgård, arXiv:2609.33043v1](https://arxiv.org/html/2609.33043v1) | Mixed-multiplicity Gram refinement and a seven-point pressure input | Its main theorem concerns distinct zeros, with lower proportion $16260119298029/19426831050000=0.83699288145242\ldots$; this is not a theorem putting that proportion on the critical line or a new simple-critical proportion |

These are different consumers, windows, and counting functions. The table is a comparison of identified primary sources, not an assertion of a worldwide record or an exhaustive priority search.

Knausgård's reference [9] identifies the [two-certificate source](https://doi.org/10.5281/zenodo.21926962), whose manuscript is signed Yuhang Shi, with [repository revision 1aeda8e](https://github.com/yuhangshi888/zeta-simple-zeros-673316977/tree/1aeda8e). Its stated simple-critical proportion, $67.3316977\%$, is higher than the $67.3314101589\ldots\%$ single-certificate consumer below. Thus that consumer is a comparison with the pinned trmdy assembly, not a claim to the best known simple-critical proportion.

The [full Shi manuscript at that revision](https://github.com/yuhangshi888/zeta-simple-zeros-673316977/blob/1aeda8e/main.tex), Section 2, already states the scaled finite-dimensional envelope $D+[\Phi_m(A)/A]P\ge\Phi_m(A)$ for its stated range $\Phi_m(A)<2$, and explicitly carries the smaller pressure coefficient into the shifted-block deduction. Its following remark also proves the coefficient's optimality in the abstract $E+P\ge A$ interface. Consequently, the single-certificate chord-plus-counting combination and that optimality argument have a direct predecessor; they are not new claims here. The full-range projection proof provides a unified presentation, while the separately stated $\tau=12/5$ mixed-multiplicity consumer uses a different counting interface.

## Relation to the finite Gram section and the coupled consumer

The three-point spectral bound in Section 17 of the [finite-structure theory volume](../../docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md) is exactly the existing envelope under a change of normalization:
$$
 F(e)=2e-\bigl(2\sqrt{e/3}-1\bigr)_+^2=\Phi_3(2e).
$$
Here $e=\sum_{i<j}|G_{ij}|^2$ and the envelope's energy is $E=2e$. The finite three-point formula is therefore an attributed specialization, not a newly discovered universal spectral bound. Its use for a particular kernel perturbation or cyclic phase remains a separate consumer.

Section 19 of the same volume applies the already available scaled-pressure principle to the envelope's chord coefficient
$\eta=\Phi_m(A)/A$ to the exact window-pressure count. This gives
$$
 D+\eta P\ge\Phi_m(A),\qquad
 \frac{mH_{\mathrm{cert}}-\eta(m-q)qp}{m-\Phi_m(A)}.
$$
For the same nine-point certificate, $m=189$ gives
$0.673314101589328672733916842945\ldots>6733141015/10^{10}$.
The finite coupling is an attributed use of the scaled-pressure principle with a full-range projection proof, and the rational arithmetic is explicit; the zero-proportion statement is a conditional consumer of the supplied local interval certificate and the same-window analytic interface. This is a comparison with the fixed trmdy source's stated assembly, without a novelty claim for the single-certificate combination. A positive proportion estimate does not exclude every exceptional off-line zero and does not prove RH.

Section 19.5 separately consumes [Knausgård's mixed-multiplicity theorem and Section 3, equation (1)](https://arxiv.org/html/2609.33043v1). That source uses the identical window and energy baseline, but counts all distinct zeros with $0<\gamma\le T$. With $\tau=12/5$, $c=17/5$, the same nine-point certificate, and $m=972$, the scaled-pressure calculation gives the conditional lower proportion
$$
 \liminf_{T\to\infty}\frac{N_d(T)}{N(T)}
 \ge0.837167490822524242030905102366\ldots
 >\frac{8371674908}{10^{10}}.
$$
The deduction retains the source's counts of high-multiplicity on-line points and off-line pairs, checks their remaining coefficients are nonnegative, and takes the limit in $T$ before removing the smoothing. It compares with the stated Knausgård v1 proportion $0.83699288145242\ldots$. The mixed-multiplicity theorem remains an attributed input; the nine-point interval certificate remains external. This distinct-zero consumer is different from the simple-critical comparison above and is not an assertion about every zero's location.
