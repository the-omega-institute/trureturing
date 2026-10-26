---
slug: mukherjee-ganguly-2025-non-unital-network-condition-implication
bibkey: mukherjeeganguly2025network
doi: 10.48550/arXiv.2510.26417
url: https://arxiv.org/abs/2510.26417v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/NonUnitalNetworkConditionImplication.result
---

# The non-unital channel conditions imply both network bounds

## Problem

K. Mukherjee and N. Ganguly, *Network nonlocality breaking channels*, arXiv:2510.26417v1 (2025), Section IV.B, `Network_Nonlocality.tex`, lines 733–734:

> Comparing Eq.(\ref{resnon1}) with that of the conditions provided by Eq.(\ref{nu3}) over the channel $\mathcal{N}_{NU},$ it is observed that there exist no region in parameter space for which Eq.(\ref{resnon1}) is violated whereas Eq.(\ref{nu3}) is satisfied. However, a formal proof of the same is beyond the scope of present work. We thus provide the following conjecture:

Conjecture 1 reads:

> Any non-unital channel from $\mathcal{N}_{NU}$( Eqs.(\ref{nu1},\ref{nu2})) acts as a non $n$-locality breaking channel in $\mathbf{N}_{lin}.$

The quotations retain the source's TeX reference labels. The corresponding PDF passage is on page 12; `nu3` is Eq. (6), `resnon1` is Eq. (38), and `nu1`, `nu2` are Eqs. (4), (5). The source TeX has MD5 `6bb7806236c7d6b0bcaa73d3eed0bc28`.

Issue [#20159](https://github.com/the-omega-institute/trureturing/issues/20159) fixes the statement to be settled: for every real $t,\lambda_1,\lambda_3$, the three conditions

$|\lambda_1|\leq1$, $|\lambda_3|+|t|\leq1$, and $\lambda_1^2+t^2\leq(1-|\lambda_3|)^2$

imply both

$(|t|+|\lambda_3|)^2+\lambda_1^2\leq1$

and

$2t^2\lambda_1^2+\lambda_1^4+(|t|+|\lambda_3|)^4\leq1$.

This parameter implication is proved. Applying it to channels requires the source's Theorem 3, which is not formalized here. The source passage and parameter correspondence are also recorded in [the literature note](../Library/QuantumContext/mukherjeeganguly2025network.md).

## Motivation

Theorem 3 of Mukherjee and Ganguly (2025), arXiv:2510.26417v1, Section IV.B, supplies Eq. (38) as a sufficient condition for the specified channel class to be $k$-use non $n$-locality breaking with respect to the linear-network inequality Eq. (11), for the setting $0<k\leq2n$. Establishing the implication from Eq. (6) removes the additional parameter test in Eq. (38) throughout the three-parameter domain used in that section. The source's terminology concerns detection by its chosen inequality; it does not establish an explicit $n$-local hidden-variable model.

## Gap

The bounded literature check is recorded in #20159:

- The arXiv record lists only v1 and calls it a preliminary version. Its TeX retains the observation and Conjecture 1 quoted above; these readings were reproduced directly.
- The search contributor reports that INSPIRE lists one citing work, Chitambar–Zhang, arXiv:2610.06642, which cites the source as background, and that Mukherjee's arXiv:2603.20035v2 does not settle the conjecture. These are attributed readings from the preregistration, not independently reproduced literature checks.
- The preregistration's orchestrator reports no existing record on `dev` in `Problems/`, `Library/`, or the issue search for the arXiv identifier.

`not-found-in-searched-scope`.

## Route

Fix a real triple satisfying the three hypotheses. Put $A=\lambda_1^2$, $x=|\lambda_3|$, $y=|t|$, $u=x+y$, and $D=(1-x)^2-y^2-A$. Squares and absolute values give $A,x,y\geq0$; the hypotheses give $u\leq1$ and $D\geq0$.

1. **Quadratic remainder.** The identity $1-(A+u^2)=D+2x(1-u)$ has a nonnegative right-hand side. Hence $0\leq A+u^2\leq1$.
2. **Quartic remainder.** The identity $(A+u^2)^2-(A^2+2y^2A+u^4)=2Ax(x+2y)$ also has a nonnegative right-hand side. Therefore $A^2+2y^2A+u^4\leq(A+u^2)^2\leq1$.
3. **Substitution.** Replace $A,x,y,u$ by their definitions and use $|t|^2=t^2$. These are exactly the two conclusions of `claim`.

## Falsifier

A real triple satisfying all three hypotheses but making either conclusion exceed one would refute `claim`. The source correspondence would be wrong if its conditions or bounds differed from those encoded in Lean. Here `l1` denotes $\lambda_1$, `l3` denotes $\lambda_3$, and the hypotheses and conclusions match the formulas in the v1 TeX, lines 211–215 and 716–719, respectively.

The proposition quantifies over real triples, including $t=0$ and boundary equality. It contains no channel, state, measurement, network, $n$, $k$, or $\lambda_2$ variable. In particular, it does not prove complete positivity, sufficiency of Eq. (6) for channel realization, or the network conclusion of Theorem 3.

## Evidence

The canonical source is `D5/S3/Quantum/QuantumChannels/NonUnitalNetworkConditionImplication.lean` (61 lines).

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/QuantumChannels/NonUnitalNetworkConditionImplication.lean.json`, statement `sha256:98e6d7f39b4285dd3ce515b7113834558eaa56b75960e7a088a7f0b669795a84`.

Declaration statements:

- `result`: `sha256:72d723f4a8718252e174f48d598e3e5a497e7369ea74256a353e5f3b6ff6e679`;
- `claim`: `sha256:99a5c6226f9c1055c41155b924e6259c425d4e0eb967817a2440cd96a4d5a537`.

## Triage

Tier 1 unproved numerical observation and conjecture of a 2025 preprint, preregistered in issue #20159 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every real $t,\lambda_1,\lambda_3$ satisfying $|\lambda_1|\leq1$, $|\lambda_3|+|t|\leq1$, and $\lambda_1^2+t^2\leq(1-|\lambda_3|)^2$, both $(|t|+|\lambda_3|)^2+\lambda_1^2\leq1$ and $2t^2\lambda_1^2+\lambda_1^4+(|t|+|\lambda_3|)^4\leq1$.

**Computed, not formalized** (SymPy and exact integer/rational arithmetic):

- Both remainder identities in the route have symbolic expansion residual zero.
- Among all $68\,921$ triples $(i/20,j/20,k/20)$ with integers $-20\leq i,j,k\leq20$, $16\,681$ satisfy the three hypotheses. For this tested family, a violation of either conclusion was not observed; each conclusion is an equality at $90$ admissible triples.
- At $(t,\lambda_1,\lambda_3)=(3/5,4/5,0)$ and $(1/3,0,2/3)$, the hypotheses are satisfied and both conclusion expressions equal one.
- At $(1/5,4/5,2/5)$, the two conclusion expressions are $1$ and $369/625$, but $\lambda_1^2+t^2=17/25>9/25=(1-|\lambda_3|)^2$. This is an exact check of one triple, not a classification of channel parameters.

**Argued, not formalized.**

- *Decisive mechanism and extension.* The two bounds follow from nonnegative remainders. The hypothesis $|\lambda_1|\leq1$ is unused in the proof. It is also redundant: $0\leq x\leq1$ and $A\leq(1-x)^2-y^2\leq1$ imply $|\lambda_1|\leq1$. Thus the second and third hypotheses suffice. This relaxed statement is not a separate conclusion of `result`.
- *The quartic condition follows from the quadratic one.* For any real triple, write $B=A+u^2$ and $Q=A^2+2y^2A+u^4$. Nonnegativity of $A,x,y$ gives $0\leq Q\leq B^2$. If $B\leq1$, then $0\leq B\leq1$ gives $Q\leq1$, independently of the channel hypotheses. Thus the first bound alone implies the second as an inequality about real parameters.
- *Sharpness in the real parameter domain.* If $\lambda_3=0$ and $\lambda_1^2+t^2=1$, all three hypotheses are satisfied, $B=1$, and $Q=(\lambda_1^2+t^2)^2=1$. If $\lambda_1=0$ and $|\lambda_3|+|t|=1$, the third hypothesis is an equality and $B=u^2=Q=u^4=1$. These families prevent a uniform replacement of either right-hand side by a constant below one on this domain. Their interpretation as channels is not established by `result`.
- *Effect on the source.* Conditional on the source's Theorem 3 for the three-parameter class used in Section IV.B, the proved implication supplies its Eq. (38) hypotheses whenever Eq. (6) is satisfied, for the theorem's linear-network setting $0<k\leq2n$ and its chosen inequality Eq. (11). This supplies the missing algebraic step behind Conjecture 1 in that reading. No later theorem explicitly takes Conjecture 1 as a premise. The channel theorem, including the treatment of $\lambda_2$ displayed in Eq. (5), remains an external input.
- *Neighbouring network criteria.* The star-network condition in Section V.B, Eq. (42), has right-hand side $2^{(2-n)(m_1+m_2)/2}$, which is below one for $n>2$ and $m_1+m_2>0$. At either saturating triple above, $Q^{m_2}B^{m_1}=1$, so the present parameter implication cannot supply that stronger condition throughout its domain. This is a limitation of the sufficient criterion, not a nonlocality witness. The source's separate star-network and full-network statements are not settled here; neither are its questions about explicit $n$-local models and larger channel classes.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The INSPIRE citation count, the readings of Chitambar–Zhang arXiv:2610.06642 and Mukherjee arXiv:2603.20035v2, and the preregistration's repository and issue searches were not independently reproduced. The preregistration's orchestrator-reported random sample of $200\,000$ triples and search-contributor-reported exact grid of $133\,649$ admissible triples were not reproduced; they are not the grid reported above.

Everything in “Computed, not formalized” and “Argued, not formalized” lacks a separate Lean declaration in this settlement. Theorem 3, the realization of the three-parameter domain as quantum channels, and the reduction involving the $\lambda_2$ coordinate in Eq. (5) are not verified by the Lean module. The physical consequence of combining the implication with Theorem 3 is conditional on that external theorem and its scope. No conclusion about all non-unital qubit channels, all network topologies, all nonlocality tests, or existence of an $n$-local hidden-variable model is formalized here.
